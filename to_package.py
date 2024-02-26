# Copyright 2013-2021 Lawrence Livermore National Security, LLC and other
# Spack Project Developers. See the top-level COPYRIGHT file for details.
#
# SPDX-License-Identifier: (Apache-2.0 OR MIT)

import argparse
import json
import os
import re
import sqlite3
import sys
from collections import defaultdict
from typing import Dict, FrozenSet, Optional, Set, Tuple, Union

import packaging.version as pv
import spack.version as vn
from packaging.markers import Marker, Op, Value, Variable
from packaging.requirements import Requirement
from packaging.specifiers import Specifier, SpecifierSet
from spack.parser import SpecSyntaxError
from spack.spec import Spec
from spack.version.version_types import VersionStrComponent, prev_version_str_component


def prev_version_for_range(v: vn.StandardVersion) -> vn.StandardVersion:
    """Translate Specifier <x into a Spack range upperbound :y"""
    # TODO: <0 is broken.
    if len(v.version) == 0:
        return v
    elif isinstance(v.version[-1], VersionStrComponent):
        prev = prev_version_str_component(v.version[-1])
    elif v.version[-1] == 0:
        return prev_version_for_range(v.up_to(len(v) - 1))
    else:
        prev = v.version[-1] - 1

    # Construct a string-version for printing
    string_components = []
    for part, sep in zip(v.version[:-1], v.separators):
        string_components.append(str(part))
        string_components.append(str(sep))
    string_components.append(str(prev))

    return vn.StandardVersion(
        "".join(string_components), v.version[:-1] + (prev,), v.separators
    )


def specifier_to_spack_version(s: Specifier):
    # The "version" 1.2.* is only allowed with operators != and ==, in which case it can follow the
    # same code path. However, the PyPI index is filled with >=1.2.* nonsense -- ignore it, it
    # would error in the else branch anyways as * is not a valid version component in Spack.
    if s.version.endswith(".*") and s.operator in ("!=", "=="):
        v = vn.StandardVersion.from_string(s.version[:-2])
    else:
        v = vn.StandardVersion.from_string(s.version)

    if s.operator == ">=":
        return vn.VersionRange(v, vn.StandardVersion.typemax())
    elif s.operator == ">":
        return vn.VersionRange(vn.next_version(v), vn.StandardVersion.typemax())
    elif s.operator == "<=":
        return vn.VersionRange(vn.StandardVersion.typemin(), v)
    elif s.operator == "<":
        return vn.VersionRange(vn.StandardVersion.typemin(), prev_version_for_range(v))
    elif s.operator == "~=":
        return vn.VersionRange(v, v.up_to(len(v) - 1))
    elif s.operator == "==":
        return vn.VersionRange(v, v)
    elif s.operator == "!=":
        return vn.VersionList(
            [
                vn.VersionRange(
                    vn.StandardVersion.typemin(), prev_version_for_range(v)
                ),
                vn.VersionRange(vn.next_version(v), vn.StandardVersion.typemax()),
            ]
        )

    return v


def _eval_python_version_marker(op, value) -> Optional[vn.VersionList]:
    # Do everything in terms of ranges for simplicity.
    if op == "==":
        v = vn.StandardVersion.from_string(value)
        return vn.VersionList([vn.VersionRange(v, v)])
    elif op == ">":
        v = vn.StandardVersion.from_string(value)
        return vn.VersionList(
            [vn.VersionRange(vn.next_version(v), vn.StandardVersion.typemax())]
        )
    elif op == ">=":
        v = vn.StandardVersion.from_string(value)
        return vn.VersionList([vn.VersionRange(v, vn.StandardVersion.typemax())])
    elif op == "<":
        v = vn.StandardVersion.from_string(value)
        return vn.VersionList(
            [vn.VersionRange(vn.StandardVersion.typemin(), prev_version_for_range(v))]
        )
    elif op == "<=":
        v = vn.StandardVersion.from_string(value)
        return vn.VersionList([vn.VersionRange(vn.StandardVersion.typemin(), v)])
    elif op == "!=":
        v = vn.StandardVersion.from_string(value)
        return vn.VersionList(
            [
                vn.VersionRange(
                    vn.StandardVersion.typemin(), prev_version_for_range(v)
                ),
                vn.VersionRange(vn.next_version(v), vn.StandardVersion.typemax()),
            ]
        )
    else:
        # We don't support this comparison.
        return None


def _eval_constraint(
    node: tuple, drop_extras_re: re.Pattern
) -> Union[None, bool, Spec]:
    # Operator
    variable, op, value = node
    assert isinstance(variable, Variable)
    assert isinstance(op, Op)
    assert isinstance(value, Value)

    # Statically evaluate implementation_name, since all we support is Python
    if variable.value == "implementation_name":
        if op.value == "==":
            return value.value == "cpython"
        elif op.value == "!=":
            return value.value != "cpython"

    try:
        if variable.value == "extra" and op.value == "==":
            # Evaluate extra == "test*" expressions statically as False.
            if drop_extras_re.match(value.value):
                return False
            # Otherwise turn into a Spack variant.
            return Spec(f"+{value.value}")
    except SpecSyntaxError as e:
        print(f"could not parse `{value}` as variant: {e}", file=sys.stderr)
        return None

    # Otherwise put a constraint on ^python.
    if variable.value not in ("python_version", "python_full_version"):
        return None

    versions = _eval_python_version_marker(op.value, value.value)

    if versions is None:
        return None

    spec = Spec("^python")
    spec.dependencies("python")[0].versions = versions
    return spec


def _eval_node(node, drop_extras_re: re.Pattern) -> Union[None, bool, Spec]:
    if isinstance(node, tuple):
        return _eval_constraint(node, drop_extras_re)
    return _marker_to_spec(node, drop_extras_re)


def _marker_to_spec(node: list, drop_extras_re: re.Pattern) -> Union[None, bool, Spec]:
    """A marker is an expression tree, that we can sometimes translate to the Spack DSL."""
    # Format is like this.
    # python_version > "3.6" or (python_version == "3.6" and os_name == "unix")
    # parsed to
    # [
    #     (<Variable('python_version')>, <Op('>')>, <Value('3.6')>),
    #     'and',
    #     [
    #         (<Variable('python_version')>, <Op('==')>, <Value('3.6')>),
    #         'or',
    #         (<Variable('os_name')>, <Op('==')>, <Value('unix')>)
    #     ]
    # ]
    # Apparently it's flattened.

    assert isinstance(node, list) and len(node) > 0

    lhs = _eval_node(node[0], drop_extras_re)

    # Reduce
    for i in range(2, len(node), 2):
        op = node[i - 1]
        assert op in ("and", "or")
        # TODO: short-circuit evaluation.
        rhs = _eval_node(node[i], drop_extras_re)

        if op == "and":
            if lhs is False or rhs is False:
                print(node, "evaluated to false", lhs, rhs)
                return False
            elif lhs is None or rhs is None:
                lhs = None
            if lhs is True or rhs is True:
                lhs = rhs
            else:  # Intersection of specs
                lhs.constrain(rhs)
        elif op == "or":
            if lhs is True or rhs is True:
                return True
            elif lhs is None or rhs is None:
                lhs = None
            elif lhs is False:
                lhs = rhs
            elif rhs is not False:
                # Union: currently only python versions can be unioned. The rest would need
                # multiple depends_on statements -- not supported yet.
                if lhs.variants or rhs.variants:
                    return None
                lhs_p, rhs_p = lhs.dependencies("python"), rhs.dependencies("python")
                if not (lhs_p and rhs_p):
                    return None
                lhs_p[0].versions.add(rhs_p[0].versions)
    return lhs


def marker_to_spec(m: Marker, drop_extras_re: re.Pattern) -> Union[bool, None, Spec]:
    """Evaluate the marker expression tree either (1) as a Spack spec if possible, (2) statically
    as True or False given that we only support cpython, (3) None if we can't translate it into
    Spack DSL."""
    # TODO: simplify expression we can evaluate statically partially.
    return _marker_to_spec(m._markers, drop_extras_re)


def version_list_from_specifier(ss: SpecifierSet) -> vn.VersionList:
    versions = vn.any_version
    for s in ss:
        versions = versions.intersection(
            vn.VersionList([specifier_to_spack_version(s)])
        )
    return versions


def generate(
    name: str, sqlite_cursor: sqlite3.Cursor, drop_extras_re: re.Pattern
) -> None:
    dep_to_when: Dict[
        Tuple[str, vn.VersionList, Optional[Marker], FrozenSet[str]], vn.VersionList
    ] = defaultdict(vn.VersionList)
    version_to_shasum: Dict[vn.StandardVersion, str] = {}
    for (
        name,
        version,
        requires_dist,
        requires_python,
        sha256_blob,
    ) in sqlite_cursor.execute(
        """
    SELECT name, version, requires_dist, requires_python, sha256 
    FROM versions
    WHERE name LIKE ?""",
        (name,),
    ):
        # We skip alpha/beta/rc etc releases, cause Spack's version ordering for them is wrong.
        try:
            packaging_version = pv.parse(version)
        except pv.InvalidVersion:
            continue
        if (
            packaging_version.pre is not None
            or packaging_version.dev is not None
            or packaging_version.post is not None
        ):
            continue

        spack_version = vn.StandardVersion.from_string(version)

        # Skip older uploads of identical versions.
        if spack_version in version_to_shasum:
            continue

        try:
            to_insert = []
            if requires_python:
                # Add the python dependency separately
                to_insert.append(
                    (
                        (
                            "python",
                            version_list_from_specifier(SpecifierSet(requires_python)),
                            None,
                            None,
                            frozenset(),
                        ),
                        spack_version,
                    )
                )

            for requirement_str in json.loads(requires_dist):
                r = Requirement(requirement_str)

                # Translate markers to ^python@ constraints if possible.
                if r.marker is not None:
                    marker_when_spec = marker_to_spec(r.marker, drop_extras_re)
                    if marker_when_spec is False:
                        # Statically evaluate to False: do not emit depends_on.
                        continue
                    elif marker_when_spec is True:
                        # Statically evaluated to True: emit unconditional depends_on.
                        r.marker = None
                        marker_when_spec = None
                    if marker_when_spec is not None:
                        # Translated to a Spec: conditional depends_on.
                        r.marker = None
                else:
                    marker_when_spec = None

                to_insert.append(
                    (
                        (
                            r.name,
                            version_list_from_specifier(r.specifier),
                            marker_when_spec,
                            r.marker,
                            frozenset(r.extras),
                        ),
                        spack_version,
                    )
                )

            # Delay registering a version until we know that it's valid.
            for k, v in to_insert:
                dep_to_when[k].add(v)
            version_to_shasum[spack_version] = "".join(f"{x:02x}" for x in sha256_blob)
        except ValueError as e:
            print(f"dropping version {spack_version}: {e}", file=sys.stderr)

    # Next, simplify a list of specific version to a range if they are consecutive.
    known_versions = sorted(version_to_shasum.keys())

    for when in dep_to_when.values():
        if when == vn.any_version:
            continue

        # It's guaranteed to be a sorted list of StandardVersion now.
        lo = when[0]

        # Find corresponding index
        i, j = known_versions.index(lo) + 1, 1
        new_list = []

        # If the first when entry corresponds to the first known version,
        # use (-inf, ..] as lowerbound.
        if i == 0:
            lo = vn.StandardVersion.typemin()

        while j < len(when):
            if known_versions[i] == when[j]:
                # Consecutive: absorb in range.
                i += 1
            else:
                # Not consecutive: emit a range.

                # If the last entry is say 1.2.3, and the next known version 1.3.0, we'd like to
                # use @:1.2 instead of @:1.2.3, since it leads to smaller diffs if a patch version
                # is added later.
                last = when[j - 1]
                version_range = vn.VersionRange(lo, last.up_to(len(last) - 1))
                if known_versions[i].satisfies(version_range):
                    version_range = vn.VersionRange(lo, last)
                new_list.append(version_range)
                lo = when[j]
                i = known_versions.index(lo) + 1

            j += 1

        # Similarly, if the last entry corresponds to the last known version,
        # assume the dependency continues to be used: [x, inf).
        if i == len(known_versions):
            version_range = vn.VersionRange(lo, vn.StandardVersion.typemax())
        else:
            last = when[j - 1]
            version_range = vn.VersionRange(lo, last.up_to(len(last) - 1))
            if known_versions[i].satisfies(version_range):
                version_range = vn.VersionRange(lo, last)

        new_list.append(version_range)
        when.versions = new_list

    # First dump the versions. TODO: checksums.
    for v in sorted(known_versions, reverse=True):
        print(f'version("{v}", sha256="{version_to_shasum[v]}")')

    if known_versions:
        print()

    first_variant_printed = False

    # Then the depends_on bits.
    if dep_to_when:
        print('with default_args(deptype=("build", "run")):')
        for k in sorted(
            dep_to_when.keys(),
            key=lambda x: (
                bool(x[3]),
                bool(x[4]),
                x[0] != "python",
                x[2] and x[2].variants,
                x[0],
                x[1],
                x[2],
            ),
        ):
            name, version_list, when_spec, marker, extras = k
            when = dep_to_when[k]
            version_list_str = (
                "" if version_list == vn.any_version else f"@{version_list}"
            )

            if marker is not None or extras:
                print()
                if marker is not None:
                    print(f"    # marker: {marker}")
                if extras:
                    print(f"    # extras: {','.join(extras)}")

            when_spec = Spec() if when_spec is None else when_spec
            when_spec.versions.intersect(when)

            # If this is the first when spec with variants, print a newline
            if when_spec.variants and not first_variant_printed:
                print()
                first_variant_printed = True

            if when_spec == Spec("@:"):
                when_str = ""
            else:
                when_str = f', when="{when_spec}"'

            comment = "# " if marker else ""
            spack_name = f"py-{name}" if name != "python" else "python"
            print(
                f'    {comment}depends_on("{spack_name}{version_list_str}"{when_str})'
            )

    # Return the possible dependency names
    return [k[0] for k in dep_to_when.keys()]


def get_possible_deps(
    name: str,
    sqlite_cursor: sqlite3.Cursor,
    drop_extras_re: re.Pattern,
    seen: Set[str],
    depth=0,
):
    print("  " * depth + name)
    seen.add(name)
    deps = set()

    for (requires_dist,) in sqlite_cursor.execute(
        """
    SELECT DISTINCT requires_dist
    FROM versions
    WHERE name = ?""",
        (name,),
    ):
        for requirement_str in json.loads(requires_dist):
            try:
                r = Requirement(requirement_str)
            except ValueError:
                continue
            if r.name in seen or r.name in deps:
                continue
            # Anything that is statically false is not a dependency in Spack anyways.
            if r.marker and marker_to_spec(r.marker, drop_extras_re) is False:
                continue
            deps.add(r.name)

    seen.update(deps)

    for dep in deps:
        get_possible_deps(dep, sqlite_cursor, drop_extras_re, seen, depth + 1)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        prog="to_spack.py", description="Convert PyPI data to Spack data"
    )
    parser.add_argument(
        "--db", default="data.db", help="The database file to read from"
    )
    parser.add_argument(
        "--drop-extras", default=".*", help="Drop extras matching this regex"
    )
    subparsers = parser.add_subparsers(dest="command")
    c_generate = subparsers.add_parser(
        "generate", help="Generate package.py for a PyPI package"
    )
    c_generate.add_argument("package", help="The package name on PyPI")
    c_generate.add_argument(
        "-r", "--recursive", action="store_true", help="Recurse into dependencies"
    )
    c_tree = subparsers.add_parser(
        "tree", help="List all possible dependencies for a PyPI package"
    )
    c_tree.add_argument("package", help="The package name on PyPI")

    args = parser.parse_args()

    if not os.path.exists(args.db):
        print(f"Database file {args.db} does not exist", file=sys.stderr)
        sys.exit(1)

    sqlite_connection = sqlite3.connect(args.db)
    sqlite_cursor = sqlite_connection.cursor()
    drop_extras_re = re.compile(args.drop_extras, re.IGNORECASE)

    if args.command == "generate":
        if not args.recursive:
            generate(args.package, sqlite_cursor, drop_extras_re)
        else:
            seen = set()
            queue = [args.package]
            while queue:
                package = queue.pop()
                if package in seen or package == "python":
                    continue
                seen.add(package)
                print()
                print(f"{package}")
                queue.extend(generate(package))
    elif args.command == "tree":
        seen = set()
        get_possible_deps(args.package, sqlite_cursor, drop_extras_re, seen)
        print("Total:", len(seen))
