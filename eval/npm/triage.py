#!/usr/bin/env python3
"""Classify a scale.sh run, closed and not-closed queries apart, and cluster
its divergences by primary divergence: a requirer both answers install at
the same version, and a directory of it the two resolve differently.  Most
of a divergence's edges lie below a handful of these.  Each is described by
what could decide it: the kind of dependency, which side took the newer
version, whether npm's version is one its tree already holds for another
requirer, and the dist-tag, deprecated and prerelease status of each pick.
usage: triage.py <run-dir>"""
import collections, json, os, re, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
from triage_lib import first_incompatibility, lines, report, show

run = sys.argv[1]
pk_cache = {}


def packument(n):
    if n not in pk_cache:
        try:
            pk_cache[n] = json.load(open(os.path.join(run, "cache", n.replace("/", "%2F") + ".json")))
        except (OSError, ValueError):
            pk_cache[n] = {}
    return pk_cache[n]


def vkey(v):
    m = re.match(r"(\d+)\.(\d+)\.(\d+)(?:-(.*))?", v or "")
    return (int(m[1]), int(m[2]), int(m[3]), not m[4], m[4] or "") if m else (-1,)


def kind(rn, rv, d):
    m = packument(rn).get("versions", {}).get(rv, {})
    for field, k in (("optionalDependencies", "optional"), ("dependencies", "dep")):
        if d in (m.get(field) or {}):
            return k
    if d in (m.get("peerDependencies") or {}):
        return "optional peer" if ((m.get("peerDependenciesMeta") or {}).get(d) or {}).get("optional") else "peer"
    # pac and --peer-parent both hang a child's peer on the
    # package that selected the child
    return "peer of a child"


def primaries(o):
    edges = {s: [tuple(l.split("\t")) for l in lines(o + ".edges." + s)] for s in ("npm", "ours")}
    nodes = {s: {e[:2] for e in es} | {e[3:] for e in es} for s, es in edges.items()}
    slot = {s: collections.defaultdict(set) for s in edges}
    for s, es in edges.items():
        for rn, rv, d, pn, pv in es:
            slot[s][rn, rv, d].add((pn, pv))
    for k in sorted(set(slot["npm"]) | set(slot["ours"])):
        n, u = sorted(slot["npm"].get(k, ())), sorted(slot["ours"].get(k, ()))
        if k[:2] not in nodes["npm"] & nodes["ours"] or n == u:
            continue
        target, vn, vo = (n or u)[0][0], n[0][1] if n else None, u[0][1] if u else None
        held = sum(1 for e in edges["npm"] if e[3:] == (target, vn)) > 1
        rel = ("npm only" if vo is None else "ours only" if vn is None else
               ("npm older" if vkey(vn) < vkey(vo) else "npm newer") + (", held by another requirer" if held else ""))
        tags = [side + tag for side, v in (("npm", vn), ("ours", vo)) if v for tag, on in (
            ("=latest", v == packument(target).get("dist-tags", {}).get("latest")),
            (" deprecated", packument(target).get("versions", {}).get(v, {}).get("deprecated")),
            (" prerelease", "-" in v)) if on]
        yield "%s; %s; %s" % (kind(*k), rel, " ".join(tags) or "-")


def npm_code(p):
    return next((l.split()[-1] for l in lines(p) if l.startswith("npm error code ")), "?")


rows = report(run, by="closed")
for closed in ("yes", "no"):
    rs = [r for r in rows if r["closed"] == closed]
    for c in ("preference-gap", "error"):
        g = collections.defaultdict(list)
        for r in rs:
            if r["class"] == c:
                for p in set(primaries(os.path.join(run, "out", r["query"]))) or ["?"]:
                    g[p].append(r["query"])
        show("%s, closed %s, by primary divergence (a query counts once per kind)" % (c, closed), g)
    for c in ("tool-declines", "both-refuse", "instance-gap"):
        g = collections.defaultdict(list)
        for r in rs:
            if r["class"] == c:
                o = os.path.join(run, "out", r["query"])
                pac = first_incompatibility(o + ".out") if r["pac"] == "unsat" else "ours " + r["valid"]
                g["npm %s | %s" % (npm_code(o + ".npm"), pac)].append(r["query"])
        show("%s, closed %s, by each side's reason" % (c, closed), g)
