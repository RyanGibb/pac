#!/usr/bin/env python3
"""Queries for a scale.sh run with FOREIGN, mined from the native (amd64) and
foreign indexes, one "pool<TAB>query" per line, seeded.

  targeted: queries whose answers turn on a choice across architectures,
    each pool a sample of at most N (default 300):
    named       foreign packages people install by name, those the indexes hold
    same        a Multi-Arch: same package at the foreign architecture
    same-both   one at both architectures at once, pkg pkg:<b>
    tool-nat    a native package depending on an architecture-specific
                Multi-Arch: foreign package the foreign index builds too
    tool-for    a foreign package depending on an architecture-specific
                Multi-Arch: foreign package
    any-nat     a native package with a dependency written name:any
    any-for     the same at the foreign architecture
    all-for     a foreign package depending on an Architecture: all package,
                Multi-Arch: foreign or not
    qualified   every package with a relation qualified by an architecture
                (not :any), at each architecture it is built for
    mixed       a native package and another at the foreign architecture
  sample: N (default 2000) packages built for the foreign architecture,
    each as pkg:<b>

usage: multiarch.py <native Packages> <foreign Packages> <seed> targeted|sample [N]"""
import random, re, sys

NAMED = ["libc6", "libstdc++6", "wine32", "wine", "libgl1", "libgl1-mesa-dri", "libvulkan1",
         "mesa-vulkan-drivers", "libasound2t64", "libpulse0", "libx11-6", "libgtk-3-0t64",
         "libsdl2-2.0-0", "libcurl4t64", "libssl3t64", "zlib1g", "python3", "perl", "bash",
         "coreutils", "gcc", "g++", "build-essential", "libc6-dev", "libncurses6", "busybox"]
ATOM = re.compile(r"\s*([^\s(:\[<]+)(?::([^\s(\[<]+))?")


def stanzas(path):
    for st in open(path, encoding="utf-8", errors="replace").read().split("\n\n"):
        f = dict(re.findall(r"^(\S+): (.*(?:\n[ \t].*)*)", st, re.M))
        if "Package" in f:
            yield f


def atoms(f, fields=("Pre-Depends", "Depends")):
    """every alternative of the fields, as (name, qualifier or None)"""
    for k in fields:
        for c in f.get(k, "").split(","):
            for a in c.split("|"):
                m = ATOM.match(a)
                if m and m[1]:
                    yield m[1], m[2]


def main():
    nat_path, for_path, seed, what = sys.argv[1:5]
    rng = random.Random(int(seed))
    nat, fo = {}, {}  # name -> stanza, of the architecture-specific packages
    alls = {}  # name -> Architecture: all stanza
    for path, into in ((nat_path, nat), (for_path, fo)):
        for f in stanzas(path):
            if f.get("Architecture") == "all":
                alls.setdefault(f["Package"], f)
            else:
                into.setdefault(f["Package"], f)
    b = next(iter(fo.values()))["Architecture"]
    if what == "sample":
        n = int(sys.argv[5]) if len(sys.argv) > 5 else 2000
        for p in sorted(rng.sample(sorted(fo), min(n, len(fo)))):
            print("sample\t%s:%s" % (p, b))
        return
    n = int(sys.argv[5]) if len(sys.argv) > 5 else 300

    def ma(f):
        return f.get("Multi-Arch", "no")

    def pool(name, qs):
        qs = sorted(set(qs))
        for q in sorted(rng.sample(qs, min(n, len(qs)))):
            print("%s\t%s" % (name, q))

    def tool(name, idx):
        f = idx.get(name)
        return f is not None and ma(f) == "foreign"

    pool("named", [p + ":" + b for p in NAMED if p in fo] + [p + " " + p + ":" + b for p in NAMED
                                                             if p in fo and p in nat])
    pool("same", [p + ":" + b for p, f in fo.items() if ma(f) == "same"])
    pool("same-both", [p + " " + p + ":" + b for p, f in fo.items() if ma(f) == "same" and p in nat])
    pool("tool-nat", [p for p, f in nat.items()
                      if any(q is None and tool(a, nat) and a in fo for a, q in atoms(f))])
    pool("tool-for", [p + ":" + b for p, f in fo.items() if any(q is None and tool(a, fo) for a, q in atoms(f))])
    pool("any-nat", [p for p, f in nat.items() if any(q == "any" for _, q in atoms(f))])
    pool("any-for", [p + ":" + b for p, f in fo.items() if any(q == "any" for _, q in atoms(f))])
    pool("all-for", [p + ":" + b for p, f in fo.items() if any(q is None and a in alls for a, q in atoms(f))])
    fields = ("Pre-Depends", "Depends", "Recommends", "Conflicts", "Breaks")
    qual = [(p, idx is fo) for idx in (nat, fo) for p, f in idx.items()
            if any(q not in (None, "any") for _, q in atoms(f, fields))]
    qual += [(p, False) for p, f in alls.items() if any(q not in (None, "any") for _, q in atoms(f, fields))]
    for q in sorted(set(p + ":" + b if foreign else p for p, foreign in qual)):
        print("qualified\t" + q)
    ns, fs = sorted(nat), sorted(fo)
    pool("mixed", [rng.choice(ns) + " " + rng.choice(fs) + ":" + b for _ in range(n)])


main()
