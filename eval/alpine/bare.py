#!/usr/bin/env python3
"""Fail if a dependency of the answer, or an atom of the query, is met only
by a bare provides (p:name, no version) of a package with no provider
priority (k:) whose own name nothing asks for.

apk lets such a provider count only once something names its owner
(is_provider_auto_selectable, solver.c): a world entry or a dependency of
a selected package.  check.sh puts the whole answer in the world, which
names every owner, so apk alone would pass what this refuses; the owner
must be named by the query or by a package of the answer.  A dependency
no package of the answer meets at all is apk's to reject, not this.

usage: bare.py <APKINDEX> <answer rows, "name=version"> <query atom>...
Exits 3 on a breach, so that a crash, which exits 1, is not read as one.
"""
import re
import sys

NAME = re.compile(r"^([^<>=~]+)(.*)$")


def atoms(field):
    """(name, versioned?) of each positive atom"""
    out = []
    for t in field.split():
        if t.startswith("!"):
            continue
        m = NAME.match(t)
        if m:
            out.append((m[1], bool(m[2])))
    return out


def main():
    index, rows, query = sys.argv[1], sys.argv[2], sys.argv[3:]
    want = {l.strip() for l in open(rows) if l.strip()}
    pkgs = {}
    for st in open(index, encoding="utf-8", errors="replace").read().split("\n\n"):
        f = {}
        for l in st.split("\n"):
            if l[1:2] == ":":
                f.setdefault(l[0], []).append(l[2:])
        p, v = f.get("P", [""])[0], f.get("V", [""])[0]
        if p + "=" + v in want:
            pkgs[p] = {"D": atoms(" ".join(f.get("D", []))),
                       "p": [NAME.match(t).groups() for t in " ".join(f.get("p", [])).split()],
                       "k": int((f.get("k") or ["0"])[0] or 0)}
    deps = [(a, "query") for a in atoms(" ".join(query))]
    deps += [(a, x) for x, d in pkgs.items() for a in d["D"]]
    named = {n for (n, _), _ in deps}
    bad = 0
    for (n, versioned), who in deps:
        if versioned or n in pkgs:
            continue
        prov = [(x, ver) for x, d in pkgs.items() for m, ver in d["p"] if m == n]
        if not prov or any(ver or pkgs[x]["k"] > 0 or x in named for x, ver in prov):
            continue
        print("%s needs %s, met only by bare provides of %s, which nothing names"
              % (who, n, " ".join(sorted(x for x, _ in prov))))
        bad = 3
    return bad


if __name__ == "__main__":
    sys.exit(main())
