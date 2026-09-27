#!/usr/bin/env python3
"""How our answer compares with Yarn Berry's own for the same query, as
scale.sh compares it with npm's.

prepare  writes a Berry project asking for the query alone, against
         berryreg.py, for `yarn install --mode=update-lockfile` to resolve.
compare  reads the yarn.lock Berry wrote and our answer: the packages each
         resolves (name and version), and the dependency edges, each a
         requirer's package and a directory with the version it gets.
         Berry's lockfile holds no peer resolution, so peers are left out,
         and so is a name a package both depends and peers on, whose own
         descriptor Berry resolves and locks even where its depender
         provides the name instead.  exact: both agree on every package
         and every edge.

usage: berryown.py prepare <dir> <port> <query...>
       berryown.py compare <snapshot> <our --tree output> <dir>
"""
import json
import os
import sys

from berrylock import ROOT, manifest, query_specs
from core import normalize
from tree import parse_tree


def prepare(d, port, args):
    os.makedirs(d, exist_ok=True)
    deps = {k: raw for k, raw in query_specs(args).items()}
    with open(os.path.join(d, "package.json"), "w") as f:
        json.dump({"name": ROOT, "version": "0.0.0", "private": True,
                   "dependencies": deps}, f, indent=2)
    with open(os.path.join(d, ".yarnrc.yml"), "w") as f:
        f.write('npmRegistryServer: "http://127.0.0.1:%s"\n'
                'unsafeHttpWhitelist: ["127.0.0.1"]\n'
                "nodeLinker: pnp\nenableTelemetry: false\nenableGlobalCache: false\n"
                "cacheFolder: ./.yarn/cache\nenableScripts: false\n"
                "enableImmutableInstalls: false\nenableProgressBars: false\n"
                "httpTimeout: 600000\n" % port)
    open(os.path.join(d, "yarn.lock"), "w").close()


def unq(s):
    s = s.strip()
    return s[1:-1] if len(s) >= 2 and s[0] == s[-1] == '"' else s


def split_at(desc):
    """name and the rest of name@rest, a scope's @ kept in the name"""
    i = desc.find("@", 1)
    return desc[:i], desc[i + 1:]


def read_lock(path):
    """{descriptor: (name, version)} and {(name, version): {key: spec}}"""
    res, deps = {}, {}
    with open(path) as f:
        text = f.read()
    for block in text.split("\n\n"):
        lines = block.split("\n")
        if not lines or not lines[0].endswith(":") or lines[0].startswith(("#", "__metadata")):
            continue
        keys = [unq(k) for k in unq(lines[0][:-1]).split(", ")]
        loc, sect, dmap = None, None, {}
        for l in lines[1:]:
            if l.startswith("    ") and sect == "dependencies":
                k, v = l.strip().split(": ", 1)
                dmap[unq(k)] = unq(v)
            elif l.startswith("  ") and not l.startswith("   "):
                k, _, v = l.strip().partition(":")
                sect = k
                if k == "resolution":
                    loc = unq(v)
        if loc is None:
            continue
        name, rest = split_at(loc)
        if rest.startswith("workspace:"):
            node = ("", "")
        elif rest.startswith("npm:"):
            node = (name, rest[4:])
        else:
            continue
        for k in keys:
            res[k] = node
        deps[node] = dmap
    return res, deps


def berry_spec(spec):
    return spec if ":" in spec else "npm:" + spec


def compare(cache, ours, d):
    res, bdeps = read_lock(os.path.join(d, "yarn.lock"))
    bnodes = {n for n in bdeps if n != ("", "")}
    bedges = {}
    for n, dmap in bdeps.items():
        for k, spec in dmap.items():
            got = res.get("%s@%s" % (k, berry_spec(spec)))
            if got is not None:
                bedges[(n, k)] = got
    with open(ours) as f:
        root, nodes, edges = parse_tree(f.read())
    pnodes = {(n[0], n[1]) for n in nodes if n != root}
    pedges, both = {}, set()
    mans = {}
    for r, key, c in edges:
        rn = ("", "") if r == root else (r[0], r[1])
        if rn != ("", ""):
            if rn not in mans:
                m = normalize(manifest(cache, r[0], r[1]), r[0], r[1])
                deps = set(m.get("dependencies") or {}) | set(m.get("optionalDependencies") or {})
                mans[rn] = (deps, set(m.get("peerDependencies") or {}))
            deps, peers = mans[rn]
            if key not in deps:
                continue
            if key in peers:
                both.add((rn, key))
                continue
        pedges[(rn, key)] = (c[0], c[1])
    for n in list(bedges):
        if n[0] != ("", "") and n[0] not in mans:
            try:
                m = normalize(manifest(cache, n[0][0], n[0][1]), n[0][0], n[0][1])
                mans[n[0]] = (set(), set(m.get("peerDependencies") or {}))
            except (OSError, KeyError):
                mans[n[0]] = (set(), set())
        if n[0] != ("", "") and n[1] in mans[n[0]][1]:
            del bedges[n]
    agree = sum(1 for e, v in pedges.items() if bedges.get(e) == v)
    exact = pnodes == bnodes and pedges == bedges
    print("berry-own nodes ours=%d berry=%d agree=%d edges ours=%d berry=%d agree=%d exact=%s"
          % (len(pnodes), len(bnodes), len(pnodes & bnodes), len(pedges), len(bedges),
             agree, "yes" if exact else "no"))


if __name__ == "__main__":
    if sys.argv[1] == "prepare":
        prepare(sys.argv[2], sys.argv[3], sys.argv[4:])
    elif sys.argv[1] == "compare":
        compare(sys.argv[2], sys.argv[3], sys.argv[4])
    else:
        sys.exit("usage: berryown.py prepare|compare ...")
