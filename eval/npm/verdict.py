#!/usr/bin/env python3
"""Classify each npm-only edge of a divergence as a preference gap, npm's
version being one pac's instance admits, or an instance gap.  range: the
version meets the range the requirer declares, or the root's flat
override, read by npm's own semver; gate: the version is in the snapshot,
and its os, cpu and libc admit this host.  Both pass: a preference gap,
marked (engines) where the version's engines exclude npm-version's node
or npm, which both sides rank by (npm-pick-manifest lib/index.js:165-179).
A failed range is a row read differently; a failed gate, a regression or
a version the snapshot lacks.  An edge with an end inBundle was never
resolved, and is out of scope.

usage: verdict.py <run-dir> <query> <out-prefix> [root package.json]
"""
import json
import os
import sys

from tree import manifest, satisfies


def resolve_host():
    """npm-version: npm's version then node's"""
    host = {"os": "linux", "cpu": "x64", "libc": "glibc"}
    try:
        with open(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                               "npm-version")) as f:
            npm, node = [l.strip().lstrip("v=") for l in f][:2]
        host["npm"], host["node"] = npm, node
    except (OSError, ValueError):
        host["npm"], host["node"] = "", ""
    return host


HOST = resolve_host()


def known(cache, name, ver):
    """name@ver's manifest, or None where the snapshot lacks it"""
    try:
        return manifest(cache, name, ver)
    except (OSError, KeyError, ValueError, RuntimeError):
        return None


def listed(m, field, host):
    l = m.get(field)
    if isinstance(l, str):
        l = [l]
    if not l or l == ["any"]:
        return True
    if any(x[1:] == host for x in l if x.startswith("!")):
        return False
    pos = [x for x in l if not x.startswith("!")]
    return not pos or host in pos


def declared(m, d, root=False):
    """the range the manifest declares for directory d.  arborist loads
    peers, then dependencies, then optionalDependencies, then a root's
    devDependencies, and a later entry of a name replaces the earlier"""
    fields = ("optionalDependencies", "dependencies", "peerDependencies")
    for field in (("devDependencies",) if root else ()) + fields:
        spec = m.get(field, {}).get(d)
        if isinstance(spec, str):
            if spec.startswith("npm:"):
                body = spec[4:]
                i = max((j for j in range(1, len(body)) if body[j] == "@"),
                        default=-1)
                return body[i + 1:] if i >= 0 else "*"
            return spec
    return None


def wanted(m, d, root, is_root):
    """the range npm resolves d's edge from m against: a flat override in
    the root's package.json, keyed by the edge's name, else m's own"""
    o = (root or {}).get("overrides", {}).get(d)
    if isinstance(o, str) and o not in ("", "*"):
        return o
    return declared(m, d, is_root)


def main():
    run, pkg, prefix = sys.argv[1], sys.argv[2], sys.argv[3]
    cache = os.path.join(run, "cache")
    # the query is published nowhere, so its manifest is the project's
    root = None
    if len(sys.argv) > 4:
        with open(sys.argv[4]) as f:
            root = json.load(f)
    try:
        with open(prefix + ".edges.bundled") as f:
            bundled = {tuple(l.rstrip("\n").split("\t")) for l in f}
    except OSError:
        bundled = set()

    rows = []
    with open(prefix + ".edges.npmonly") as f:
        for line in f:
            rn, rv, d, vn, vv = line.rstrip("\n").split("\t")
            is_root = (rn, rv) == ("", "")
            rm = root if is_root else known(cache, rn, rv)
            vm = known(cache, vn, vv)
            rg = wanted(rm, d, root, is_root) if rm else None
            eng = (vm or {}).get("engines", {})
            # the old array form, ["node >= 0.4"], is no requirement to
            # checkEngine, which reads engines.node and engines.npm alone
            if not isinstance(eng, dict):
                eng = {}
            eng = {k: v for k, v in eng.items()
                   if k in ("node", "npm") and isinstance(v, str) and HOST[k]}
            rows.append((rn, rv, d, vn, vv, rg, vm, eng))

    counts, lines = {}, []
    for rn, rv, d, vn, vv, rg, vm, eng in rows:
        if (rn, rv, d, vn, vv) in bundled:
            why = "out of scope (bundled)"
        elif vm is None:
            why = "instance gap (gate): version absent from snapshot"
        elif not all(listed(vm, f, HOST[f]) for f in ("os", "cpu", "libc")):
            why = "instance gap (gate): os/cpu/libc"
        elif rg is None:
            why = "unclassified: requirer's row not found"
        elif satisfies(vv, rg, "strict") is not True:
            why = "instance gap: row read differently"
        elif not all(satisfies(HOST[k], v, "strict") for k, v in eng.items()):
            why = "preference gap (engines)"
        else:
            why = "preference gap"
        counts[why] = counts.get(why, 0) + 1
        lines.append("%s\t%s %s -> %s = %s@%s\tdeclared %s" %
                     (why, rn, rv, d, vn, vv, rg))

    with open(prefix + ".verdict", "w") as f:
        f.write("\n".join(sorted(lines)) + ("\n" if lines else ""))
    print("%-24s %s" % (pkg, json.dumps(counts, sort_keys=True)))


if __name__ == "__main__":
    main()
