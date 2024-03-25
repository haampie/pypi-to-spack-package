# Copyright 2013-2021 Lawrence Livermore National Security, LLC and other
# Spack Project Developers. See the top-level COPYRIGHT file for details.
#
# SPDX-License-Identifier: (Apache-2.0 OR MIT)

import argparse
import gzip
import json
import os
import re
import shutil
import sqlite3
import sys
import urllib.request
from collections import defaultdict
from typing import Dict, FrozenSet, List, Optional, Set, Tuple, Union

import packaging.version as pv
import spack.version as vn
from packaging.markers import Marker, Op, Value, Variable
from packaging.requirements import InvalidRequirement, Requirement
from packaging.specifiers import InvalidSpecifier, SpecifierSet
from spack.error import UnsatisfiableSpecError
from spack.parser import SpecSyntaxError
from spack.spec import Spec
from spack.util.naming import mod_to_class
from spack.version.common import ALPHA, BETA, FINAL, PRERELEASE_TO_STRING, RC
from spack.version.version_types import VersionStrComponent

# If a marker on python version satisfies this range, we statically evaluate it as true.
UNSUPPORTED_PYTHON = vn.VersionRange(
    vn.StandardVersion.typemin(), vn.StandardVersion.from_string("3.7")
)

# The prefix to use for Pythohn package names in Spack.
SPACK_PREFIX = "py-"

NAME_REGEX = re.compile(r"[-_.]+")

DB_URL = "https://github.com/haampie/pypi-to-spack-package/releases/download/latest/data.db.gz"

MAX_VERSIONS = 10

KNOWN_PYTHON_VERSIONS = (
    (3, 7, 17),
    (3, 8, 18),
    (3, 9, 18),
    (3, 10, 13),
    (3, 11, 7),
    (3, 12, 1),
    (3, 13, 0),
)

DepToWhen = Tuple[str, vn.VersionList, Optional[Spec], Optional[Marker], FrozenSet[str]]


class Node:
    __slots__ = ("name", "dep_to_when", "version_info", "ordered_versions")

    def __init__(
        self,
        name: str,
        dep_to_when: Dict[DepToWhen, vn.VersionList],
        version_info: Dict[pv.Version, str],
        ordered_versions: List[pv.Version],
    ):
        self.name = name
        self.dep_to_when = dep_to_when
        self.version_info = version_info
        self.ordered_versions = ordered_versions


class VersionsLookup:
    def __init__(self, cursor: sqlite3.Cursor):
        self.cursor = cursor
        self.cache: Dict[str, List[pv.Version]] = {}

    def _query(self, name: str) -> List[pv.Version]:
        query = self.cursor.execute("SELECT version FROM versions WHERE name = ?", (name,))
        return sorted(vv for v, in query if (vv := _acceptable_version(v)))

    def _python_versions(self) -> List[pv.Version]:
        return [
            pv.Version(f"{major}.{minor}.{p}")
            for major, minor, patch in KNOWN_PYTHON_VERSIONS
            for p in range(patch + 1)
        ]

    def __getitem__(self, name: str) -> List[pv.Version]:
        result = self.cache.get(name)
        if result is not None:
            return result
        result = self._query(name) if name != "python" else self._python_versions()
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

    return _pkg_specifier_set_to_version_list(
        "python", SpecifierSet(f"{op}{value}"), version_lookup
    )


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
    except SpecSyntaxError as e:
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
        return pv.parse(version)
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
    release.extend(v.release)
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
    matching = [s for s in specifier_set.filter(all, prereleases=True)]
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
    print("Downloading latest database (~500MB, may take a while...)", file=sys.stderr)
    with urllib.request.urlopen(DB_URL) as response, open("data.db", "wb") as f:
        with gzip.GzipFile(fileobj=response) as gz:
            shutil.copyfileobj(gz, f)


MAX_VERSIONS = 10


def _get_node(
    name: str,
    specifier: SpecifierSet,
    extras: FrozenSet[str],
    sqlite_cursor: sqlite3.Cursor,
    version_lookup: VersionsLookup,
):
    name = _normalized_name(name)
    query = sqlite_cursor.execute(
        """
        SELECT version, requires_dist, requires_python, sha256, path, is_sdist
        FROM versions
        WHERE name = ?""",
        (name,),
    )

    data = [
        (v, requires_dist, requires_python, sha256, path, sdist)
        for version, requires_dist, requires_python, sha256, path, sdist in query
        if (v := _acceptable_version(version))
    ]

    # prioritize final versions
    data.sort(key=lambda x: (not x[0].is_prerelease, x[0]), reverse=True)

    requirement_to_when: Dict[
        Tuple[str, SpecifierSet, FrozenSet[str]],
        List[Tuple[pv.Version, Optional[Marker], Optional[Spec]]],
    ] = defaultdict(list)

    # Generate a dictionary of requirement -> versions.
    count = 0
    used_versions: Set[Tuple[pv.Version, str, str]] = set()
    python_constraints: Dict[vn.VersionList, Set[pv.Version]] = defaultdict(set)

    for version, requires_dist, requires_python, sha256_blob, path, sdist in data:
        if not specifier.contains(version, prereleases=True):
            continue

        count += 1
        if count > MAX_VERSIONS:
            break

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
        valid = True
        for requirement_str in json.loads(requires_dist):
            try:
                r = Requirement(requirement_str)
            except InvalidRequirement:
                print(f"{name}@{version}: invalid requirement {requirement_str}", file=sys.stderr)
                valid = False
                break

            if r.marker is not None:
                evalled = _evaluate_marker(r.marker, version_lookup)

                # If statically false, or if we don't have any of the required variants, skip.
                if (
                    evalled is False
                    or isinstance(evalled, list)
                    and not any(all(v in extras for v in spec.variants) for spec in evalled)
                ):
                    continue

                if evalled is True:
                    r.marker = None
                    evalled = None

                elif evalled is not None:
                    r.marker = None
            else:
                evalled = None

            requirement_to_when[
                (_normalized_name(r.name), r.specifier, frozenset(r.extras))
            ].append((version, r.marker, evalled))

        # Drop versions that have invalid requirements.
        if not valid:
            continue

        sha256 = "".join(f"{x:02x}" for x in sha256_blob)
        used_versions.add((version, sha256, path))

        if python_versions != vn.any_version:
            python_constraints[python_versions].add(version)

    return used_versions, requirement_to_when, python_constraints


class MyNode:
    versions: Set[Tuple[pv.Version, str, str]]
    edges: Dict[
        Tuple[str, SpecifierSet, FrozenSet[str]],
        List[Tuple[pv.Version, Optional[Marker], Optional[Spec]]],
    ]
    variants: Set[str]

    # maps unique python constraints to versions that impose them
    pythons: Dict[vn.VersionList, Set[pv.Version]]

    def __init__(self) -> None:
        self.versions = set()
        self.edges = {}
        self.variants = set()
        self.pythons = defaultdict(set)


def main():

    parser = argparse.ArgumentParser(
        prog="PyPI to Spack package.py", description="Convert PyPI data to Spack data"
    )
    parser.add_argument("--db", default="data.db", help="The database file to read from")
    subparsers = parser.add_subparsers(dest="command", help="The command to run")
    p_new_generate = subparsers.add_parser("generate", help="Generate a package.py file")
    p_new_generate.add_argument("--directory", "-o", help="Output directory")
    p_new_generate.add_argument("requirements", help="requirements.txt file")
    p_info = subparsers.add_parser("info", help="Show basic info about database or package")
    p_info.add_argument("package", nargs="?", help="package name on PyPI")
    p_update = subparsers.add_parser("update", help="Download the latest database")

    args = parser.parse_args()

    if args.command == "update":
        download_db()
        sys.exit(0)

    elif not os.path.exists(args.db):
        if input("Database does not exist, download? (y/n) ") not in ("y", "Y", "yes"):
            sys.exit(1)
        download_db()

    sqlite_connection = sqlite3.connect(args.db)
    sqlite_cursor = sqlite_connection.cursor()

    if args.command == "info":
        if args.package:
            raise Exception("todo")
        else:
            print(
                "Total packages:",
                sqlite_cursor.execute("SELECT COUNT(DISTINCT name) FROM versions").fetchone()[0],
            )
            print(
                "Total versions:",
                sqlite_cursor.execute("SELECT COUNT(*) FROM versions").fetchone()[0],
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

        # map from package name to set of versions
        visited = set()
        lookup = VersionsLookup(sqlite_cursor)
        graph = defaultdict(MyNode)

        # explore the graph
        while queue:
            name, specifier, extras, depth = queue.pop()
            print(f"{' ' * depth}{name} {specifier}", file=sys.stderr)
            versions, edges, python_constraints = _get_node(
                name, specifier, extras, sqlite_cursor, lookup
            )
            node = graph[name]
            node.versions.update(versions)
            node.variants.update(extras)
            for python_constraints, versions in python_constraints.items():
                node.pythons[python_constraints].update(versions)
            for key in edges:
                node.edges[key] = edges[key]
                if key in visited:
                    continue
                visited.add(key)
                queue.append((*key, depth + 1))

        # dump the graph as spack package
        for name, node in sorted(graph.items(), key=lambda x: x[0]):
            print(name)
            for version, sha256, path in sorted(node.versions, reverse=True):
                spack_v = _packaging_to_spack_version(version)
                print(
                    f'  version("{spack_v}", sha256="{sha256}", url="https://pypi.org/packages/{path}")'
                )
            print()
            for variant in sorted(node.variants):
                print(f'  variant("{variant}", default=False)')
            if node.variants:
                print()

            # Condense edges to (depends on spec, marker condition) -> versions
            dep_to_when = defaultdict(set)

            for (child, specifier, extras), data in node.edges.items():
                child_versions = [v for v, _, _ in graph[child].versions]
                variants = "".join(f"+{v}" for v in extras)
                spec = Spec(f"py-{child}{variants}")
                try:
                    spec.versions = _condensed_version_list(
                        [v for v in child_versions if specifier.contains(v, prereleases=True)],
                        child_versions,
                    )
                except IndexError:
                    spec.versions = vn.VersionList([":"])

                for version, marker, marker_specs in sorted(
                    data, key=lambda x: x[0], reverse=True
                ):
                    if isinstance(marker_specs, list):
                        for marker_spec in marker_specs:
                            dep_to_when[(spec, marker, marker_spec)].add(version)
                    else:
                        dep_to_when[(spec, marker, None)].add(version)

            unique_versions = [v for v, _, _ in node.versions]

            # First dump Python constraints.
            for python_constraints, versions in node.pythons.items():
                when_spec = Spec()
                when_spec.versions = _condensed_version_list(versions, unique_versions)
                depends_on = Spec("python")
                depends_on.versions = python_constraints
                print(f' depends_on("{depends_on}", when="{when_spec}")')
            print()

            # Then show further dependencies.

            children = [
                (
                    spec,
                    _make_when_spec(
                        marker_spec, _condensed_version_list(versions, unique_versions)
                    ),
                    marker,
                )
                for (spec, marker, marker_spec), versions in dep_to_when.items()
            ]

            # Order by (name ASC, when spec DESC, spec DESC)
            children.sort(key=lambda x: (x[0]), reverse=True)
            children.sort(key=lambda x: (x[1]), reverse=True)
            children.sort(key=lambda x: (x[0].name))

            for spec, when_spec, marker in children:
                when_spec_str = _format_when_spec(when_spec)
                if when_spec_str:
                    depends_on = f'  depends_on("{spec}", when="{when_spec_str}")'
                else:
                    depends_on = f'  depends_on("{spec}")'
                if marker is not None:
                    depends_on += f" # {marker}"
                print(depends_on)
            print()


if __name__ == "__main__":
    main()
