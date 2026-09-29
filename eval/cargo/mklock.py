#!/usr/bin/env python3
"""Write pac's Cargo answer out as a Cargo.lock, so that cargo can be asked
to verify it: a [[package]] per crate of `pac cargo --print-parents`, its
dependencies its children there, written "name version", as a lock may
hold two versions of a name.  The root, the path package run_query.py's
build_manifest writes, has neither source nor checksum; every other
crate has the one registry and the index's own cksum, copied, since cargo
compares a locked checksum with the index's (Resolve::merge_from).

usage: mklock.py <pac --print-parents output> <out Cargo.lock>
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from run_query import index_line, parse_answer  # noqa: E402

REGISTRY = "registry+https://github.com/rust-lang/crates.io-index"


def cksum(name, version):
    j = index_line(name, version)
    if j is None:
        raise RuntimeError(f"{name} {version} is not in the index")
    return j.get("cksum")


def parse(text):
    root, crates, _, edges = parse_answer(text)
    if root == (None, None):
        raise RuntimeError("no root line in pac output")
    if not crates:
        raise RuntimeError("no packages section in pac output")
    # the lock names the package, not the alias a rename gave it here
    return root, [tuple(c) for c in crates], [((pn, pv), (cn, cv)) for pn, pv, _, cn, cv in edges]


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
