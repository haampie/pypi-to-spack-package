#!/usr/bin/env spack-python

# Copyright 2013-2021 Lawrence Livermore National Security, LLC and other
# Spack Project Developers. See the top-level COPYRIGHT file for details.
#
# SPDX-License-Identifier: (Apache-2.0 OR MIT)

import argparse
import ast
import gzip
import io
import itertools
import json
import os
import pathlib
import re
import shutil
import sqlite3
import sys
import urllib.error
import urllib.request
from collections import defaultdict
from typing import Dict, FrozenSet, List, Optional, Set, Tuple, Type, Union

import packaging.version as pv
import spack.package_base
import spack.paths
import spack.repo
import spack.util.naming as nm
import spack.version as vn
from packaging.markers import Marker, Op, Value, Variable
from packaging.requirements import InvalidRequirement, Requirement
from packaging.specifiers import InvalidSpecifier, SpecifierSet
from spack.build_systems.python import PythonExtension, PythonPackage
from spack.error import UnsatisfiableSpecError
from spack.parser import SpecSyntaxError
from spack.spec import Spec
from spack.util.naming import mod_to_class
from spack.version.common import ALPHA, BETA, FINAL, PRERELEASE_TO_STRING, RC
from spack.version.version_types import VersionStrComponent

# If a marker on python version satisfies this range, we statically evaluate it as true.
UNSUPPORTED_PYTHON = vn.VersionRange(
    vn.StandardVersion.typemin(), vn.StandardVersion.from_string("3.5")
)

# The prefix to use for Pythohn package names in Spack.
SPACK_PREFIX = "py-"

NAME_REGEX = re.compile(r"[-_.]+")

DB_URL = "https://github.com/haampie/pypi-to-spack-package/releases/download/latest/data.db.gz"

MAX_VERSIONS = 1

KNOWN_PYTHON_VERSIONS = (
    (3, 6, 15),
    (3, 7, 17),
    (3, 8, 18),
    (3, 9, 18),
    (3, 10, 13),
    (3, 11, 7),
    (3, 12, 1),
    (3, 13, 0),
    (4, 0, 0),
)

HEADER = """\
# Copyright 2013-2024 Lawrence Livermore National Security, LLC and other
# Spack Project Developers. See the top-level COPYRIGHT file for details.
#
# SPDX-License-Identifier: (Apache-2.0 OR MIT)

from spack.package import *

"""

MOVE_UP = "\033[1A"
CLEAR_LINE = "\x1b[2K"


class VersionsLookup:
    def __init__(self, cursor: sqlite3.Cursor):
        self.cursor = cursor
        self.cache: Dict[str, List[pv.Version]] = {}

    def _query(self, name: str) -> List[pv.Version]:
        # Todo, de-duplicate identical versions e.g. "3.7.0" and "3.7".
        query = self.cursor.execute("SELECT version FROM versions WHERE name = ?", (name,))
        return sorted({vv for v, in query if (vv := _acceptable_version(v))})

    def _python_versions(self) -> List[pv.Version]:
        return [
            pv.Version(f"{major}.{minor}.{patch}")
            for major, minor, patch in KNOWN_PYTHON_VERSIONS
            # for p in range(1, patch + 1)
        ]

    def __getitem__(self, name: str) -> List[pv.Version]:
        result = self.cache.get(name)
        if result is not None:
            return result
        if name == "python":
            result = self._python_versions()
        else:
            result = self._query(name)
        self.cache[name] = result
        return result


def _eval_python_version_marker(
    variable: str, op: str, value: str, version_lookup: VersionsLookup
) -> Optional[vn.VersionList]:
    # TODO: there might be still some bug caused by python_version vs python_full_version
    # differences.
    # Also `in` and `not in` are allowed, but difficult to get right. They take the rhs as a
    # string and do string matching instead of version parsing... so we don't support them now.
    if op not in ("==", ">", ">=", "<", "<=", "!="):
        return None

    try:
        specifier = SpecifierSet(f"{op}{value}")
    except InvalidSpecifier:
        print(f"could not parse `{op}{value}` as specifier", file=sys.stderr)
        return None

    return _pkg_specifier_set_to_version_list("python", specifier, version_lookup)


def _eval_constraint(node: tuple, version_lookup: VersionsLookup) -> Union[None, bool, List[Spec]]:
    # TODO: os_name, platform_machine, platform_release, platform_version, implementation_version

    # Operator
    variable, op, value = node
    assert isinstance(op, Op)

    # Flip the comparison if the value is on the left-hand side.
    if isinstance(variable, Value) and isinstance(value, Variable):
        flipped_op = {
            ">": "<",
            "<": ">",
            ">=": "<=",
            "<=": ">=",
            "==": "==",
            "!=": "!=",
            "~=": "~=",
        }.get(op.value)
        if flipped_op is None:
            print(f"do not know how to evaluate `{node}`", file=sys.stderr)
            return None
        variable, op, value = value, Op(flipped_op), variable

    assert isinstance(variable, Variable)
    assert isinstance(value, Value)

    # Statically evaluate implementation name, since all we support is cpython
    if variable.value == "implementation_name":
        if op.value == "==":
            return value.value == "cpython"
        elif op.value == "!=":
            return value.value != "cpython"
        return None

    if variable.value == "platform_python_implementation":
        if op.value == "==":
            return value.value.lower() == "cpython"
        elif op.value == "!=":
            return value.value.lower() != "cpython"
        return None

    platforms = ("linux", "cray", "darwin", "windows", "freebsd")

    if variable.value == "platform_system" and op.value in ("==", "!="):
        platform = value.value.lower()
        if platform in platforms:
            return [
                Spec(f"platform={p}")
                for p in platforms
                if p != platform and op.value == "!=" or p == platform and op.value == "=="
            ]
        return op.value == "!="  # we don't support it, so statically true/false.

    if variable.value == "sys_platform" and op.value in ("==", "!="):
        platform = value.value.lower()
        if platform == "win32":
            platform = "windows"
        elif platform == "linux2":
            platform = "linux"
        if platform in platforms:
            return [
                Spec(f"platform={p}")
                for p in platforms
                if p != platform and op.value == "!=" or p == platform and op.value == "=="
            ]
        return op.value == "!="  # we don't support it, so statically true/false.

    try:
        if variable.value == "extra":
            if op.value == "==":
                return [Spec(f"+{value.value}")]
            elif op.value == "!=":
                return [Spec(f"~{value.value}")]
    except (SpecSyntaxError, ValueError) as e:
        print(f"could not parse `{value}` as variant: {e}", file=sys.stderr)
        return None

    # Otherwise we only know how to handle constraints on the Python version.
    if variable.value not in ("python_version", "python_full_version"):
        return None

    versions = _eval_python_version_marker(variable.value, op.value, value.value, version_lookup)

    if versions is None:
        return None

    simplify_python_constraint(versions)

    if not versions:
        # No supported versions for python remain, so statically false.
        return False
    elif versions == vn.any_version:
        # No constraints on python, so statically true.
        return True
    else:
        spec = Spec("^python")
        spec.dependencies("python")[0].versions = versions
        return [spec]


def _eval_node(node, version_lookup: VersionsLookup) -> Union[None, bool, List[Spec]]:
    if isinstance(node, tuple):
        return _eval_constraint(node, version_lookup)
    return _do_evaluate_marker(node, version_lookup)


def _intersection(lhs: List[Spec], rhs: List[Spec]) -> List[Spec]:
    """Expand: (a or b) and (c or d) = (a and c) or (a and d) or (b and c) or (b and d)
    where `and` is spec intersection."""
    specs: List[Spec] = []
    for l in lhs:
        for r in rhs:
            intersection = l.copy()
            try:
                intersection.constrain(r)
            except UnsatisfiableSpecError:
                # empty intersection
                continue
            specs.append(intersection)
    return list(set(specs))


def _union(lhs: List[Spec], rhs: List[Spec]) -> List[Spec]:
    """This case is trivial: (a or b) or (c or d) = a or b or c or d, BUT do a simplification
    in case the rhs only expresses constraints on versions."""
    if len(rhs) == 1 and not rhs[0].variants and not rhs[0].architecture:
        python, *_ = rhs[0].dependencies("python")
        for l in lhs:
            l.versions.add(python.versions)
        return lhs

    return list(set(lhs + rhs))


def _eval_and(group: List, version_lookup):
    lhs = _eval_node(group[0], version_lookup)
    if lhs is False:
        return False

    for node in group[1:]:
        rhs = _eval_node(node, version_lookup)
        if rhs is False:  # false beats none
            return False
        elif lhs is None or rhs is None:  # none beats true / List[Spec]
            lhs = None
        elif rhs is True:
            continue
        elif lhs is True:
            lhs = rhs
        else:  # Intersection of specs
            lhs = _intersection(lhs, rhs)
            if not lhs:  # empty intersection
                return False
    return lhs


def _do_evaluate_marker(
    node: list, version_lookup: VersionsLookup
) -> Union[None, bool, List[Spec]]:
    """A marker is an expression tree, that we can sometimes translate to the Spack DSL."""

    assert isinstance(node, list) and len(node) > 0

    # Inner array is "and", outer array is "or".
    groups = [[node[0]]]
    for i in range(2, len(node), 2):
        op = node[i - 1]
        if op == "or":
            groups.append([node[i]])
        elif op == "and":
            groups[-1].append(node[i])
        else:
            assert False, f"unexpected operator {op}"

    lhs = _eval_and(groups[0], version_lookup)
    if lhs is True:
        return True
    for group in groups[1:]:
        rhs = _eval_and(group, version_lookup)
        if rhs is True:
            return True
        elif lhs is None or rhs is None:
            lhs = None
        elif lhs is False:
            lhs = rhs
        elif rhs is not False:
            lhs = _union(lhs, rhs)
    return lhs


def _evaluate_marker(m: Marker, version_lookup: VersionsLookup) -> Union[bool, None, List[Spec]]:
    """Evaluate the marker expression tree either (1) as a list of specs that constitute the when
    conditions, (2) statically as True or False given that we only support cpython, (3) None if
    we can't translate it into Spack DSL."""
    return _do_evaluate_marker(m._markers, version_lookup)


def _normalized_name(name):
    return re.sub(NAME_REGEX, "-", name).lower()


def _best_upperbound(curr: vn.StandardVersion, next: vn.StandardVersion) -> vn.StandardVersion:
    """Return the most general upperound that includes curr but not next. Invariant is that
    curr < next."""
    i = 0
    m = min(len(curr), len(next))
    while i < m and curr.version[0][i] == next.version[0][i]:
        i += 1
    if i == len(curr) < len(next):
        release, _ = curr.version
        release += (0,)  # one zero should be enough 1.2 and 1.2.0 are not distinct in packaging.
        seperators = (".",) * (len(release) - 1) + ("",)
        as_str = ".".join(str(x) for x in release)
        return vn.StandardVersion(as_str, (tuple(release), (FINAL,)), seperators)
    elif i == m:
        return curr  # include pre-release of curr
    else:
        return curr.up_to(i + 1)


def _best_lowerbound(prev: vn.StandardVersion, curr: vn.StandardVersion) -> vn.StandardVersion:
    i = 0
    m = min(len(curr), len(prev))
    while i < m and curr.version[0][i] == prev.version[0][i]:
        i += 1
    if i + 1 >= len(curr):
        return curr
    else:
        return curr.up_to(i + 1)


def _acceptable_version(version: str) -> Optional[pv.Version]:
    """Maybe parse with packaging"""
    try:
        v = pv.parse(version)
        # do not support post releases of prereleases etc.
        if v.pre and (v.post or v.dev or v.local):
            return None
        return v
    except pv.InvalidVersion:
        return None


local_separators = re.compile(r"[\._-]")


def _packaging_to_spack_version(v: pv.Version) -> vn.StandardVersion:
    # TODO: better epoch support.
    release = []
    prerelease = (FINAL,)
    if v.epoch > 0:
        print(f"warning: epoch {v} isn't really supported", file=sys.stderr)
        release.append(v.epoch)
    # release can be None here when the version is parsed as a LegacyVersion
    if v.release is not None:
        release.extend(v.release)
    else:
        # Return a StandardVersion from str(v)
        return spack.version.ver(str(v)).lo  # Just pick lo
    separators = ["."] * (len(release) - 1)

    if v.pre is not None:
        type, num = v.pre
        if type == "a":
            prerelease = (ALPHA, num)
        elif type == "b":
            prerelease = (BETA, num)
        elif type == "rc":
            prerelease = (RC, num)
        separators.extend(("-", ""))

        if v.post or v.dev or v.local:
            print(f"warning: ignoring post / dev / local version {v}", file=sys.stderr)

    else:
        if v.post is not None:
            release.extend((VersionStrComponent("post"), v.post))
            separators.extend((".", ""))
        if v.dev is not None:  # dev is actually pre-release like, spack makes it a post-release.
            release.extend((VersionStrComponent("dev"), v.dev))
            separators.extend((".", ""))
        if v.local is not None:
            local_bits = [
                int(i) if i.isnumeric() else VersionStrComponent(i)
                for i in local_separators.split(v.local)
            ]
            release.extend(local_bits)
            separators.append("-")
            separators.extend("." for _ in range(len(local_bits) - 1))

    separators.append("")

    # Reconstruct a string.
    string = ""
    for i in range(len(release)):
        string += f"{release[i]}{separators[i]}"
    if v.pre:
        string += f"{PRERELEASE_TO_STRING[prerelease[0]]}{prerelease[1]}"

    return vn.StandardVersion(string, (tuple(release), tuple(prerelease)), separators)


def _condensed_version_list(
    _subset_of_versions: List[pv.Version], _all_versions: List[pv.Version]
) -> vn.VersionList:
    # Sort in Spack's order, which should in principle coincide with packaging's order, but may
    # not in unforseen edge cases.
    subset = sorted(_packaging_to_spack_version(v) for v in _subset_of_versions)
    all = sorted(_packaging_to_spack_version(v) for v in _all_versions)

    # Find corresponding index
    i, j = all.index(subset[0]) + 1, 1
    new_versions: List[vn.ClosedOpenRange] = []

    # If the first when entry corresponds to the first known version, use (-inf, ..] as lowerbound.
    if i == 1:
        lo = vn.StandardVersion.typemin()
    else:
        lo = _best_lowerbound(all[i - 2], subset[0])

    while j < len(subset):
        if all[i] != subset[j]:
            hi = _best_upperbound(subset[j - 1], all[i])
            new_versions.append(vn.VersionRange(lo, hi))
            i = all.index(subset[j])
            lo = _best_lowerbound(all[i - 1], subset[j])
        i += 1
        j += 1

    # Similarly, if the last entry corresponds to the last known version,
    # assume the dependency continues to be used: [x, inf).
    if i == len(all):
        hi = vn.StandardVersion.typemax()
    else:
        hi = _best_upperbound(subset[j - 1], all[i])

    new_versions.append(vn.VersionRange(lo, hi))
    return vn.VersionList(new_versions)


def simplify_python_constraint(versions: vn.VersionList) -> None:
    """Modifies a version list of python versions in place to remove redundant constraints
    implied by UNSUPPORTED_PYTHON."""
    # First delete everything implied by UNSUPPORTED_PYTHON
    vs = versions.versions
    while vs and vs[0].satisfies(UNSUPPORTED_PYTHON):
        del vs[0]

    if not vs:
        return

    # Remove any redundant lowerbound, e.g. @3.7:3.9 becomes @:3.9 if @:3.6 unsupported.
    union = UNSUPPORTED_PYTHON._union_if_not_disjoint(vs[0])
    if union:
        vs[0] = union


evalled = dict()


def _pkg_specifier_set_to_version_list(
    pkg: str, specifier_set: SpecifierSet, version_lookup: VersionsLookup
) -> vn.VersionList:
    key = (pkg, specifier_set)
    if key in evalled:
        return evalled[key]
    all = version_lookup[pkg]
    matching = [s for s in all if specifier_set.contains(s, prereleases=True)]
    result = vn.VersionList() if not matching else _condensed_version_list(matching, all)
    evalled[key] = result
    return result


def _make_when_spec(spec: Optional[Spec], when_versions: vn.VersionList) -> Spec:
    spec = Spec() if spec is None else spec
    spec.versions.intersect(when_versions)
    return spec


def _format_when_spec(spec: Spec) -> str:
    parts = [spec.format("{name}{@versions}{variants}")]
    if spec.architecture:
        parts.append(f"platform={spec.platform}")
    for dep in spec.dependencies():
        parts.append(dep.format("^{name}{@versions}"))
    return " ".join(p for p in parts if p)


def download_db():
    print("Downloading latest database (~1GB, may take a while...)", file=sys.stderr)
    with urllib.request.urlopen(DB_URL) as response, open("data.db", "wb") as f:
        with gzip.GzipFile(fileobj=response) as gz:
            shutil.copyfileobj(gz, f)


def _validate_requirements(
    name: str, version: pv.Version, requires_dist: str, version_lookup
) -> Optional[List[Requirement]]:
    requirements: List[Requirement] = []
    for requirement_str in json.loads(requires_dist):
        try:
            r = Requirement(requirement_str)
        except InvalidRequirement:
            print(f"{name}@{version}: invalid requirement {requirement_str}", file=sys.stderr)
            return None

        # Normalize the name for good measture
        r.name = _normalized_name(r.name)

        # If the requirement is on an unknown package, we error out.
        if not version_lookup[r.name]:
            print(f"{name}@{version}: unknown dependency {r.name}", file=sys.stderr)
            return None

        requirements.append(r)
    return requirements


def _get_node(name: str, sqlite_cursor: sqlite3.Cursor, version_lookup: VersionsLookup):
    name = _normalized_name(name)
    query = sqlite_cursor.execute(
        """
        SELECT version, requires_dist, requires_python, sha256, path
        FROM distributions
        WHERE name = ?
        """,
        (name,),
    )

    data = [
        (v, requires_dist, requires_python, sha256, path)
        for version, requires_dist, requires_python, sha256, path in query
        if (v := _acceptable_version(version))
    ]

    requirement_to_when: Dict[
        Tuple[str, SpecifierSet, FrozenSet[str]],
        List[Tuple[pv.Version, Optional[Marker], Optional[List[Spec]]]],
    ] = defaultdict(list)

    # Generate a dictionary of requirement -> versions.
    version_data: Dict[pv.Version, Tuple[str, str]] = {}
    python_constraints: Dict[vn.VersionList, Set[pv.Version]] = defaultdict(set)

    for version, requires_dist, requires_python, sha256_blob, path in data:
        # Sometimes 1.54.0 and 1.54 are both in the database.
        if version in version_data:
            copy = next(v for v in version_data if v == version)
            print(
                f"warning: {name}@={version} and {name}@={copy} are identical, but separately in the PyPI db",
                file=sys.stderr,
            )
            continue

        if requires_python:
            try:
                specifier_set = SpecifierSet(requires_python)
            except InvalidSpecifier:
                print(
                    f"{name}@{version}: invalid python specifier {requires_python}",
                    file=sys.stderr,
                )
                continue

            python_versions = _pkg_specifier_set_to_version_list(
                "python", specifier_set, version_lookup
            )

            # Delete everything implied by UNSUPPORTED_PYTHON
            simplify_python_constraint(python_versions)

            if not python_versions:
                print(
                    f"{name}@{version}: no supported python versions: {requires_python}",
                    file=sys.stderr,
                )
                continue
        else:
            python_versions = vn.any_version

        # go over the edges
        requirements = _validate_requirements(name, version, requires_dist, version_lookup)

        # Invalid requirements, skip this version.
        if requirements is None:
            continue

        for r in requirements:
            child_name = _normalized_name(r.name)

            if r.marker is not None:
                evalled = _evaluate_marker(r.marker, version_lookup)

                # If statically false, or if we don't have any of the required variants, skip.
                if evalled is False:
                    continue

                if evalled is True:
                    r.marker = None
                    evalled = None

                elif evalled is not None:
                    r.marker = None
            else:
                evalled = None

            requirement_to_when[(child_name, r.specifier, frozenset(r.extras))].append(
                (version, r.marker, evalled)
            )

        sha256 = "".join(f"{x:02x}" for x in sha256_blob)
        version_data[version] = (sha256, path)

        if python_versions != vn.any_version:
            python_constraints[python_versions].add(version)

    return version_data, requirement_to_when, python_constraints


class Node:
    #: All known versions of this package. Keys are versions, values are (sha256, path) tuples.
    versions: Dict[pv.Version, Tuple[str, str]]

    #: Subset of the versions that we define in the package.py file.
    used_versions: Set[pv.Version]

    #: Edges to dependencies, keyed by (name, specifier, extras), with values being a list of
    #: (version, marker, when) tuples.
    edges: Dict[
        Tuple[str, SpecifierSet, FrozenSet[str]],
        List[Tuple[pv.Version, Optional[Marker], Optional[List[Spec]]]],
    ]

    #: Set of all variants of this package, needed by a dependent.
    variants: Set[str]

    #: Dependencies on Python versions. Key is a list of Python versions, value the set of versions
    #: of the package that depend on them.
    pythons: Dict[vn.VersionList, Set[pv.Version]]

    #: This is a simplified version of edges, for the purpose of generating the package.py file.
    #: It is an ordered list of (dependency_spec, when_spec, marker) tuples. The marker is only
    #: present if we cannot translate it into a when spec.
    children: List[Tuple[Spec, Spec, Optional[Marker]]]

    def __init__(self) -> None:
        self.versions = {}
        self.used_versions = set()
        self.edges = {}
        self.variants = set()
        self.pythons = defaultdict(set)
        self.children = []


def _generate(
    queue: List[Tuple[str, SpecifierSet, FrozenSet[str], int]],
    sqlite_cursor: sqlite3.Cursor,
    no_new_versions: bool = False,
):
    visited = set()
    lookup = VersionsLookup(sqlite_cursor)
    graph: Dict[str, Node] = {}

    if no_new_versions:
        usable_versions: Dict[str, Set[pv.Version]] = defaultdict(set)
        for name, specifier, extras, _ in queue:
            usable_versions[name].add(pv.Version(list(specifier)[0].version))

    i = 0

    while queue:
        i += 1
        name, specifier, extras, depth = queue.pop()
        print(f"[{i:5}/{i+len(queue):5}] {' ' * depth}{name} {specifier}", file=sys.stderr)
        # Populate package info if we haven't seen it yet.
        if name not in graph:
            node = Node()
            versions, edges, python_constraints = _get_node(name, sqlite_cursor, lookup)
            node.versions = versions
            node.edges = edges
            node.pythons = python_constraints
            graph[name] = node
        else:
            node = graph[name]

        node.variants.update(extras)

        # Pick at most MAX_VERSIONS versions
        version_iterator = lambda: (
            v
            for v in sorted(node.versions, reverse=True, key=lambda v: (not v.is_prerelease, v))
            if specifier.contains(v, prereleases=True)
        )
        if not no_new_versions or name not in usable_versions:
            # Generate new versions
            used_versions = [v for v, _ in zip(version_iterator(), range(MAX_VERSIONS))]
        else:
            used_versions = [
                v
                for v in sorted(
                    node.versions, reverse=True, key=lambda v: (not v.is_prerelease, v)
                )
                if specifier.contains(v, prereleases=True) and v in usable_versions[name]
            ]

            if not used_versions:
                used_versions = [v for v, _ in zip(version_iterator(), range(1))]
                print(f"{name} {specifier}: adding {used_versions} instead", file=sys.stderr)

        node.used_versions.update(used_versions)

        # Now go over the edges.
        for key, value in node.edges.items():
            # Do not visit the same edge twice.
            if key in visited:
                continue
            # See if this edge applies to any of the selected versions.
            for version, marker, marker_specs in value:
                if version not in used_versions:
                    continue
                if marker_specs is None or any(
                    extras.issuperset(s.variants) for s in marker_specs
                ):
                    break
            else:
                continue

            # Enqueue the edge.
            visited.add(key)
            queue.append((*key, depth + 1))

    print("simplifying edges...", file=sys.stderr)

    # Condense edges to (depends on spec, marker condition) -> versions. Notice that in some cases
    # distinct specifiers may lead to the same spec constraint, e.g. >3 and >=3 if there is no
    # version exactly 3.
    for name, node in graph.items():

        dep_to_when: Dict[Tuple[Spec, Optional[Marker], Optional[Spec]], Set[pv.Version]] = (
            defaultdict(set)
        )
        for (child, specifier, extras), data in node.edges.items():
            # Skip specifiers for which we don't have the versions and variants.
            if not any(
                v in node.used_versions
                and (not ms or any(node.variants.issuperset(m.variants) for m in ms))
                for v, _, ms in data
            ):
                continue
            # TODO: skip if we don't have any variants.
            variants = "".join(f"+{v}" for v in extras)
            spec = Spec(f"{SPACK_PREFIX}{child}{variants}")
            spec.versions = _pkg_specifier_set_to_version_list(child, specifier, lookup)

            to_add: List[Tuple[Tuple[Spec, Optional[Marker], Optional[Spec]], pv.Version]] = []
            for version, marker, marker_specs in data:
                if isinstance(marker_specs, list):
                    for marker_spec in marker_specs:
                        if node.variants.issuperset(marker_spec.variants):
                            to_add.append(((spec, marker, marker_spec), version))
                else:
                    to_add.append(((spec, marker, None), version))

            if to_add and not spec.versions:
                print(f"{name} -> {child} {specifier} has no matching versions", file=sys.stderr)
                spec.versions = vn.any_version

            for key, value in to_add:
                dep_to_when[key].add(value)

        # Restrict the set of all versions to about 10 releases back from the oldest used version,
        # so that when conditions are not too long.
        if node.used_versions:
            all_versions = sorted(node.versions.keys())
            min_version = min(node.used_versions)
            from_index = max(0, all_versions.index(min_version) - 10)
            versions_we_care_about = all_versions[from_index:]
        else:
            versions_we_care_about = []

        # Finally create an list of edges in the format and order we can use in package.py
        for (spec, marker, marker_spec), versions in dep_to_when.items():
            # With certain OR conditions in markers we can still end up with a when condition that
            # does not touch any of the versions we care about.
            if versions.isdisjoint(node.used_versions):
                continue
            node.children.append(
                (
                    spec,
                    _make_when_spec(
                        marker_spec,
                        _condensed_version_list(
                            versions.intersection(versions_we_care_about), versions_we_care_about
                        ),
                    ),
                    marker,
                )
            )

        # Order by (name ASC, when spec DESC, spec DESC)
        def when_spec_key(data: Tuple[Spec, Spec, Optional[Marker]]):
            when_spec = data[1]
            pythons = when_spec.dependencies("python")
            parts = (
                when_spec.name,
                when_spec.versions,
                when_spec.variants,
                when_spec.architecture,
            )
            if not pythons:
                return parts
            else:
                python, *_ = pythons
                return (*parts, python.name, python.versions, python.variants)

        node.children.sort(key=lambda x: (x[0]), reverse=True)
        node.children.sort(key=when_spec_key, reverse=True)
        node.children.sort(key=lambda x: (x[0].name))

        # Prepend dependencies on Python versions.
        for python_constraints, versions in sorted(node.pythons.items(), key=lambda x: x[0]):
            if versions.isdisjoint(node.used_versions):
                continue
            when_spec = Spec()
            when_spec.versions = _condensed_version_list(
                versions.intersection(versions_we_care_about), versions_we_care_about
            )
            depends_on = Spec("python")
            depends_on.versions = python_constraints
            node.children.insert(0, (depends_on, when_spec, None))

    return graph


def _print_package(name: str, node: Node, f: io.StringIO):
    if not node.used_versions:
        print("    # No versions available.", file=f)
        print("    pass", file=f)
        return
    wheel_only = (
        " [WHEEL ONLY]"
        if all(node.versions[v][1].endswith(".whl") for v in node.used_versions)
        else ""
    )
    print(f"    # BEGIN VERSIONS{wheel_only}", file=f)
    for version in sorted(node.used_versions, reverse=True):
        sha256, path = node.versions[version]
        spack_v = _packaging_to_spack_version(version)
        print(
            f'    version("{spack_v}", sha256="{sha256}", url="https://pypi.org/packages/{path}")',
            file=f,
        )
    print("    # END VERSIONS", file=f)
    print(file=f)
    print("    # BEGIN VARIANTS", file=f)
    for variant in sorted(node.variants):
        print(f'    variant("{variant}", default=False, description="{variant}")', file=f)
    print("    # END VARIANTS", file=f)
    if node.variants:
        print(file=f)

    uncommented_lines: List[str] = []
    commented_lines: List[Tuple[str, str]] = []

    for spec, when_spec, marker in node.children:
        when_spec_str = _format_when_spec(when_spec)
        if when_spec_str:
            depends_on = f'depends_on("{spec}", when="{when_spec_str}")'
        else:
            depends_on = f'depends_on("{spec}")'

        if marker is not None:
            commented_lines.append((depends_on, f"marker: {marker}"))
        elif spec.name == f"{SPACK_PREFIX}{name}":
            # TODO: could turn this into a requirement: requires("+x", when="@y")
            commented_lines.append((depends_on, "self-dependency"))
        else:
            uncommented_lines.append(depends_on)

    print("    # BEGIN DEPENDENCIES", file=f)
    if uncommented_lines:
        print('    with default_args(type=("build", "run")):', file=f)
    elif commented_lines:
        print('    # with default_args(type=("build", "run")):', file=f)

    for line in uncommented_lines:
        print(f"        {line}", file=f)
    print("    # END DEPENDENCIES", file=f)
    print(file=f)

    # Group commented lines by comment
    commented_lines.sort(key=lambda x: x[1])
    for comment, group in itertools.groupby(commented_lines, key=lambda x: x[1]):
        print(f"\n        # {comment}", file=f)
        for line, _ in group:
            print(f"        # {line}", file=f)


def is_pypi(pkg: Type[spack.package_base.PackageBase], c: sqlite3.Cursor):
    if PythonPackage not in pkg.__bases__ and PythonExtension not in pkg.__bases__:
        return False
    name = pkg.name[3:] if pkg.name.startswith("py-") else pkg.name
    return c.execute("SELECT * FROM versions WHERE name = ?", (name,)).fetchone() is not None


def dump_requirements(
    cursor: sqlite3.Cursor, new_pkgs: Optional[Set[str]] = None, f: io.StringIO = sys.stdout
):
    """Dump all Spack packages are requirements to a file."""
    count = 0
    packages = spack.repo.PATH.all_package_names()
    total_pkgs = len(packages)
    skip = []
    print()
    for i, name in enumerate(packages):
        pkg = spack.repo.PATH.get_pkg_class(name)
        percent = int(100 * (i + 1) / total_pkgs)
        print(f"{MOVE_UP}{CLEAR_LINE} [{percent:3}%] {name}")
        if not is_pypi(pkg, cursor):
            continue
        count += 1
        pypi_name = name[3:] if name.startswith("py-") else name

        variants = ",".join(s for s in pkg.variants if s != "build_system")
        variants = variants if not variants else f"[{variants}]"

        if new_pkgs and name in new_pkgs:
            print(f"{pypi_name}{variants}", file=f)

        for version in pkg.versions:
            try:
                pv.Version(str(version))
            except:
                skip.append(f"{pypi_name}=={version}")
                continue
            print(f"{pypi_name}{variants} =={version}", file=f)
    for s in skip:
        print(f"skipped: {s}", file=sys.stderr)
    print(f"total: {count} pypi packages")


def export_repo(repo_in: str, repo_out: str):
    """Update the Spack package.py files in repo_out with the package.py files in repo_in."""

    repo_in = os.path.join(repo_in, "packages")
    repo_out = os.path.join(repo_out, "packages")

    begin_versions = "    # BEGIN VERSIONS [WHEEL ONLY]"
    end_versions = "    # END VERSIONS"
    begin_variants = "    # BEGIN VARIANTS"
    end_variants = "    # END VARIANTS"
    begin_deps = "    # BEGIN DEPENDENCIES"
    end_deps = "    # END DEPENDENCIES"

    for dir in sorted(os.listdir(repo_in)):
        in_package = os.path.join(repo_in, dir, "package.py")
        out_package = os.path.join(repo_out, dir, "package.py")

        if not os.path.exists(out_package):
            try:
                os.mkdir(os.path.join(repo_out, dir))
            except OSError:
                pass

            shutil.copy(in_package, out_package)
            continue

        try:
            with open(in_package, "r") as f:
                contents = f.read()
        except OSError:
            print(f"failed to read {in_package}", file=sys.stderr)
            continue

        try:
            versions = contents[
                contents.index(begin_versions)
                + len(begin_versions)
                + 1 : contents.index(end_versions)
            ].split("\n")
            variants = contents[
                contents.index(begin_variants)
                + len(begin_variants)
                + 1 : contents.index(end_variants)
            ].split("\n")
            deps = contents[
                contents.index(begin_deps) + len(begin_deps) + 1 : contents.index(end_deps)
            ].split("\n")
            assert versions
        except (ValueError, AssertionError):
            continue

        with open(out_package, "r") as f:
            src = f.read()

        lines = src.split("\n")

        # keep bits that are between `# <<< ...` and # ... >>>` comments:
        lines_to_keep: Set[int] = set()
        start = None
        start_regex, end_regex = re.compile(r"\s*# <<<"), re.compile(r"\s*# .*>>>")
        for i, line in enumerate(lines):
            if start_regex.match(line):
                start = i
            elif start is not None and end_regex.match(line):
                lines_to_keep.update(range(start, i + 1))

        tree = ast.parse(src)
        clasname = nm.mod_to_class(dir)

        for n in ast.walk(tree):
            if isinstance(n, ast.ClassDef) and n.name == clasname:
                break
        else:
            print(f"failed to find class {clasname} in {out_package}", file=sys.stderr)
            continue

        lines_to_delete: Set[int] = set()

        for node in n.body:
            # delete with expressions and loops
            if isinstance(node, (ast.With, ast.For)):
                lines_to_delete.update(range(node.lineno - 1, node.end_lineno))
                continue

            # delete build instructions
            if isinstance(node, ast.FunctionDef):
                if node.name in (
                    "setup_build_environment",
                    "url_for_version",
                    "install",
                    "build_directory",
                    "patch",
                ) or any(
                    isinstance(d, ast.Call)
                    and isinstance(d.func, ast.Name)
                    and d.func.id in ("run_before", "run_after")
                    for d in node.decorator_list
                ):
                    lines_to_delete.update(range(node.lineno - 1, node.end_lineno))
                    for d in node.decorator_list:
                        lines_to_delete.update(range(d.lineno - 1, d.end_lineno))
                continue

            if not isinstance(node, ast.Expr):
                continue

            expr = node.value

            # delete any version, depends_on, or variant directive
            if (
                isinstance(expr, ast.Call)
                and isinstance(expr.func, ast.Name)
                and expr.func.id in ("version", "depends_on", "variant", "patch")
            ):
                for i in range(expr.lineno - 1, expr.end_lineno):
                    lines_to_delete.add(i)
                if expr.func.id == "variant":
                    pattern = f'variant("{expr.args[0].s}"'

                    # Preserve variants from the original package as they contain a description.
                    for i, line in enumerate(variants):
                        if pattern in line:
                            variants[i] = "\n".join(lines[expr.lineno - 1 : expr.end_lineno])
                # Remove patch files
                if expr.func.id == "patch":
                    arg = expr.args[0]
                    assert isinstance(arg, ast.Constant)
                    patch = os.path.join(repo_out, dir, arg.value)
                    try:
                        os.unlink(patch)
                    except OSError:
                        pass

        # delete lines that are only comments or empty
        for line in range(min(lines_to_delete), len(lines)):
            stripped = lines[line].strip()
            if not stripped or stripped.startswith("#"):
                lines_to_delete.add(line)

        # preserve special comments
        delete = sorted(lines_to_delete - lines_to_keep, reverse=True)

        for i in delete:
            del lines[i]

        lines.insert(
            delete[-1],
            "\n".join(l for l in ("\n".join(versions), "\n".join(variants), "\n".join(deps)) if l),
        )

        with open(out_package, "w") as f:
            f.write("\n".join(lines))


def main():

    parser = argparse.ArgumentParser(
        prog="PyPI to Spack package.py", description="Convert PyPI data to Spack data"
    )
    parser.add_argument("--db", default="data.db", help="The PyPI sqlite database to read from")
    subparsers = parser.add_subparsers(dest="command", required=True)
    parser_generate = subparsers.add_parser(
        "generate", help="Generate package.py files from spack_requirements.txt [step 2]"
    )
    parser_generate.add_argument("--repo", "-o", help="Output repo directory", default="repo")
    parser_generate.add_argument(
        "--clean", action="store_true", help="Clean output repo before generating"
    )
    parser_generate.add_argument(
        "--no-new-versions", action="store_true", help="Do not add new versions when possible"
    )
    parser_generate.add_argument(
        "--requirements", help="requirements.txt file", default="spack_requirements.txt"
    )
    subparsers.add_parser("update-db", help="Download the latest database")
    parser_requirements = subparsers.add_parser(
        "update-requirements",
        help="Populate spack_requirements.txt from Spack's builtin repo [step 1]",
    )
    # exclusive
    new_group = parser_requirements.add_mutually_exclusive_group()
    new_group.add_argument(
        "--new",
        action="store_true",
        help="Include new versions. This generates an additional plain requirement `name` apart "
        "from `name ==version` for all versions in Spack",
    )
    new_group.add_argument("--new-from-file", help="List the packages that need to be bumped")
    parser_export = subparsers.add_parser(
        "export", help="Update Spack's repo with the generated package.py files [step 3]"
    )
    parser_export.add_argument(
        "--input", help="Input repo that contains repo.yaml (default: ./repo)", default="repo"
    )
    parser_export.add_argument(
        "--output",
        help="Output repo that contains repo.yaml (default: Spack builtin)",
        default=spack.paths.packages_path,
    )
    subparsers.add_parser("info", help="Show basic info about database or package")

    args = parser.parse_args()

    if args.command == "update-db":
        download_db()
        sys.exit(0)

    if args.command == "export":
        export_repo(args.input, args.output)
        sys.exit(0)

    elif not os.path.exists(args.db):
        if input("Database does not exist, download? (y/n) ") not in ("y", "Y", "yes"):
            sys.exit(1)
        download_db()

    sqlite_connection = sqlite3.connect(args.db)
    sqlite_cursor = sqlite_connection.cursor()

    if args.command == "update-requirements":
        if args.new_from_file:
            with open(args.new_from_file) as f:
                new_pkgs = set(line.strip() for line in f.readlines() if line.strip())
        elif args.new:
            new_pkgs = set(spack.repo.PATH.all_package_names())
        else:
            new_pkgs = None
        with open("spack_requirements.txt", "w") as f:
            dump_requirements(sqlite_cursor, new_pkgs, f)

    elif args.command == "info":
        print(
            "Total packages:",
            sqlite_cursor.execute("SELECT COUNT(DISTINCT name) FROM versions").fetchone()[0],
        )
        print(
            "Total versions:", sqlite_cursor.execute("SELECT COUNT(*) FROM versions").fetchone()[0]
        )

    elif args.command == "generate":
        # Parse requirements.txt
        with open(args.requirements) as f:
            requirements = [
                Requirement(v) for line in f.readlines() if (v := line.split("#")[0].strip())
            ]

        queue = [
            (_normalized_name(r.name), r.specifier, frozenset(r.extras), 0) for r in requirements
        ]

        graph = _generate(queue, sqlite_cursor, args.no_new_versions)

        output_dir = pathlib.Path(args.repo)
        packages_dir = output_dir / "packages"

        if args.clean:
            shutil.rmtree(packages_dir, ignore_errors=True)
            try:
                os.unlink(output_dir / "repo.yaml")
            except OSError:
                pass

        if not output_dir.exists():
            packages_dir.mkdir(parents=True)

        if not (output_dir / "repo.yaml").exists():
            with open(output_dir / "repo.yaml", "w") as f:
                f.write("repo:\n  namespace: python\n")

        for name, node in graph.items():
            spack_name = f"{SPACK_PREFIX}{name}"
            package_dir = packages_dir / spack_name
            package_dir.mkdir(parents=True, exist_ok=True)
            with open(package_dir / "package.py", "w") as f:
                f.write(HEADER)
                print(f"class {mod_to_class(spack_name)}(PythonPackage):", file=f)
                _print_package(name, node, f)


if __name__ == "__main__":
    main()
