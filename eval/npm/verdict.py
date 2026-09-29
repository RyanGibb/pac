#!/usr/bin/env python3
"""Classify each divergent edge as a preference gap or an instance gap.

The question a divergence poses is whether npm's answer was one our
instance already admitted -- in which case only our preference ordering
ranked it second -- or one our instance forbids outright.  For an npm-only
edge (R wants directory d, npm resolved it to V) that is two tests:

  range   does V satisfy the range R's manifest declares for d?  The check
          runs against npm's own bundled semver, against the root's flat
          override for d where there is one, and npm usually chose V so
          it satisfies; it does not when npm keeps an invalid optional peer.
          Otherwise a failure means our reading of the requirer's
          declaration differs from npm's -- an alias or an override read
          differently, or the edge attributed to the wrong requirer -- and
          is not a preference at all.
  gate    is V in the snapshot, and does its os/cpu/libc admit the run
          host (linux/x64/glibc)?  A failure here would be our instance
          being strictly smaller than npm's.

range and gate both pass  ->  preference gap
gate fails                ->  instance gap (gate)
range fails               ->  instance gap (row read differently)
either end inBundle       ->  out of scope (bundled)

The last is decided before either test.  A lock entry marked inBundle was
never resolved: npm grafts a bundling package's node_modules in from its
tarball verbatim, so the version there is whatever the publisher packed,
published or not, and neither test says anything about it.

The gate test is a tripwire rather than a classification: our frontend
applies no os/cpu/libc gate, since npm-pick-manifest reads none of them,
so it reads the manifests and not our instance.  A "gate" verdict means
either a regression or a version the snapshot simply lacks.

engines is deliberately not a gate on either side.  npm-pick-manifest
sorts on it (lib/index.js:165-179) and installs an unrunnable version
when nothing else matches, and so do we, so npm picking a version this
host cannot run is an ordinary preference gap.  It is named separately
because engines is the one preference key whose input is a host
constant: both sides have to be given the same node and npm versions, or
they rank by different rules and every such edge diverges.  The host
here is npm-version, which is what scale.sh passes our side.

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
