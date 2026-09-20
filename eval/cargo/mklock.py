#!/usr/bin/env python3
"""Write OUR Cargo resolution out as a Cargo.lock, so cargo can be asked
to verify it.

The inverse of the reading run_goal.py does: `pac cargo --print-parents`
prints the resolved crate set and the parent relation over it, which is
exactly the two things a lockfile records -- one [[package]] per node,
and each node's `dependencies` list naming its children.  Nothing else
in the file is a choice: `source` is the one registry every non-root
node came from, and `checksum` is the index's own cksum for that exact
version, copied rather than computed, because the body played no part in
picking the version and cargo only checks it on download.

The root is the goal crate itself, built as a path package by
run_goal.py's build_manifest, so its [[package]] carries neither source
nor checksum -- that absence is what tells cargo which node is the
workspace member.

Dependency entries are written "name version" rather than bare "name":
both are legal in lockfile v4, but the bare form is only unambiguous
while one version of a name is in the lock, and a cargo resolution may
legitimately carry two majors of one crate.

usage: mklock.py <pac --print-parents output> <out Cargo.lock>
"""
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from run_goal import crate_path  # noqa: E402

REGISTRY = "registry+https://github.com/rust-lang/crates.io-index"


def cksum(name, version):
    path = crate_path(name)
    if not os.path.exists(path):
        raise RuntimeError(f"no index file for {name}")
    with open(path) as f:
        for raw in f:
            raw = raw.strip()
            if not raw:
                continue
            j = json.loads(raw)
            if j.get("vers") == version:
                return j.get("cksum")
    raise RuntimeError(f"{name} {version} is not in the index")


def parse(text):
    m = re.search(r"^root (\S+) (\S+)", text, re.M)
    if not m:
        raise RuntimeError("no root line in pac output")
    root = (m.group(1), m.group(2))

    crates, edges = [], []
    section = None
    for line in text.splitlines():
        if line.startswith("crates ("):
            section = "c"
            continue
        if line.startswith("encoded solution:"):
            section = None
            continue
        if line.strip() == "parent-edges:":
            section = "e"
            continue
        if line.startswith("loaded:"):
            section = None
            continue
        if section == "c":
            mm = re.match(r"^  (\S+) (\S+)(?: \[(.*)\])?$", line)
            if mm:
                crates.append((mm.group(1), mm.group(2)))
        elif section == "e":
            # "<parent> <pver> -> <alias>(<package>) <cver>"; the lock
            # names the package, not the alias a rename gave it here
            mm = re.match(r"^  (\S+) (\S+) -> (\S+)\((\S+)\) (\S+)$", line)
            if mm:
                pn, pv, _alias, cn, cv = mm.groups()
                edges.append(((pn, pv), (cn, cv)))
    if not crates:
        raise RuntimeError("no crates section in pac output")
    return root, crates, edges


def quote(s):
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'


def main():
    src, dst = sys.argv[1], sys.argv[2]
    with open(src) as f:
        root, crates, edges = parse(f.read())

    kids = {}
    for p, c in edges:
        kids.setdefault(p, set()).add(c)

    out = ["version = 4", ""]
    for name, version in sorted(crates):
        out.append("[[package]]")
        out.append("name = " + quote(name))
        out.append("version = " + quote(version))
        if (name, version) != root:
            out.append("source = " + quote(REGISTRY))
            c = cksum(name, version)
            if c:
                out.append("checksum = " + quote(c))
        deps = sorted(kids.get((name, version), ()))
        if deps:
            out.append("dependencies = [")
            for dn, dv in deps:
                out.append(" " + quote(f"{dn} {dv}") + ",")
            out.append("]")
        out.append("")
    with open(dst, "w") as f:
        f.write("\n".join(out))
    print(f"{dst}: {len(crates)} packages, {len(edges)} edges, root {root[0]} {root[1]}")


if __name__ == "__main__":
    main()
