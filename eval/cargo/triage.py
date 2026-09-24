#!/usr/bin/env python3
"""Classify a scale.sh run and cluster its divergences by the shallowest
names whose versions differ, in either side's graph, since the rest usually
follow from them.  Each carries which side took the newer version, whether
the two lie in different compatibility classes, and, where the MSRV
preference could have decided it, which versions fit the root's toolchain.
Errors are grouped by what cargo changed in our lock.
usage: triage.py <run-dir>"""
import collections, json, os, re, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path[:0] = [HERE, os.path.join(HERE, "..")]
from triage_lib import first_incompatibility, report, show
from run_query import crate_path
from scale import compat_class, msrv_ok, read_rows, vkey

run = sys.argv[1]
msrv = {}


def rust_version(n, v):
    if n not in msrv:
        msrv[n] = {j["vers"]: j.get("rust_version") for j in read_rows(crate_path(n))} \
            if os.path.exists(crate_path(n)) else {}
    return msrv[n].get(v)


def depths(root, edges):
    kids = collections.defaultdict(set)
    for e in edges:
        kids[tuple(e[:2])].add(tuple(e[-2:]))
    d, todo = {tuple(root): 0}, [tuple(root)]
    for x in todo:
        for k in kids[x] - set(d):
            d[k] = d[x] + 1
            todo.append(k)
    return d


def divergence(res):
    vs = {s: collections.defaultdict(set) for s in ("pac", "cargo")}
    for s in vs:
        for n, v in res[s]["crates"]:
            vs[s][n].add(v)
    dp, dc = depths(res["pac"]["root"], res["pac"]["edges"]), depths(res["cargo"]["root"], res["cargo"]["edges"])
    out = []
    for n in {n for n in vs["pac"].keys() | vs["cargo"].keys() if vs["pac"][n] != vs["cargo"][n]}:
        o, c = sorted(vs["pac"][n] - vs["cargo"][n], key=vkey), sorted(vs["cargo"][n] - vs["pac"][n], key=vkey)
        depth = min([dp.get((n, v), 99) for v in o] + [dc.get((n, v), 99) for v in c])
        s = "%s %s -> %s" % (n, ",".join(o) or "-", ",".join(c) or "-")
        if o and c:
            s += " ours " + ("newer" if vkey(o[-1]) > vkey(c[-1]) else "older")
            s += "" if {compat_class(v) for v in o} == {compat_class(v) for v in c} else ", other class"
            fit = ["".join("y" if msrv_ok(rust_version(n, v), res["root_rust_version"]) else "n" for v in x)
                   for x in (o, c)]
            s += "" if "n" not in "".join(fit) else ", fits %s: ours %s, cargo %s" % (res["root_rust_version"], *fit)
        out.append((depth, s))
    return "; ".join(s for d, s in sorted(out) if d == min(out)[0]) if out else "edges only"


def repaired(v):
    names = lambda ps: " ".join("%s@%s" % tuple(p) for p in ps[:4]) or "-"
    return "cargo adds %s, drops %s; edges +%d -%d" % (
        names(v["added"]), names(v["lost"]), len(v["added_edges"]), len(v["lost_edges"]))


def cargo_reason(res):
    c = res.get("cargo") or {}
    e = c.get("stderr") or c.get("error") or "?"
    return re.sub(r"`[^`]*`", "_", next((l for l in e.split("\n") if l.startswith("error:")), e.strip()[-80:]))[:100]


rows = report(run)
out = lambda r, ext: os.path.join(run, "out", r["query"] + ext)
for c, label in (("preference-gap", lambda r: divergence(json.load(open(out(r, ".json"))))),
                 ("error", lambda r: repaired(json.load(open(out(r, ".valid.json"))))),
                 ("tool-declines", lambda r: "ours %s | cargo: %s" % (r["valid"], cargo_reason(json.load(open(out(r, ".json")))))),
                 ("instance-gap", lambda r: first_incompatibility(out(r, ".out"))),
                 ("both-refuse", lambda r: "cargo: %s | pac: %s" % (
                     cargo_reason(json.load(open(out(r, ".json")))), first_incompatibility(out(r, ".out"))))):
    g = collections.defaultdict(list)
    for r in rows:
        if r["class"] == c:
            g[label(r)].append(r["query"])
    show(c, g)
