#!/usr/bin/env python3
"""Classify a scale.sh run and cluster its divergences by contested name: a
name the part both answers share, or the world, asks for, and that a
package only one side installed answers.  Clustering there rather than on
the whole difference folds what a choice pulled in downstream into the
choice itself.
usage: triage.py <run-dir>"""
import collections, os, re, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
from triage_lib import first_incompatibility, group, lines, report, show, unkey

run = sys.argv[1]
INDEX = os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../repos/alpine/APKINDEX")
NAME = re.compile(r"^!?([^<>=~]+)")


def load():
    pkgs = {}
    for st in open(INDEX, encoding="utf-8", errors="replace").read().split("\n\n"):
        f = collections.defaultdict(list)
        for l in st.split("\n"):
            if l[1:2] == ":":
                f[l[0]] += l[2:].split(" ")
        if f["P"]:
            # a negated dependency asks for nothing
            pkgs[f["P"][0]] = {k: {NAME.match(t)[1] for t in f[k] if t and t[0] != "!"} for k in "Dpi"}
    return pkgs


def contested(pkgs, side, answer, world):
    """{contested name: packages of side answering it}; an install_if package
    the shared part triggers is contested under its own name"""
    rest = set(answer) - set(side)
    none = {"D": set(), "p": set(), "i": set()}
    asked = set(world).union(*(pkgs.get(y, none)["D"] for y in rest))
    have = rest.union(*(pkgs.get(y, none)["p"] for y in rest))
    out = collections.defaultdict(set)
    for x in side:
        d = pkgs.get(x, none)
        for n in ({x} | d["p"]) & asked:
            out[n].add(x)
        if d["i"] and d["i"] <= have:
            out["install_if:" + x].add(x)
    return out or ({"?": set(side)} if side else {})


rows = report(run)
pkgs = load()
for c in ("preference-gap", "error", "exact-invalid"):
    cl = {}
    for r in (r for r in rows if r["class"] == c):
        o = os.path.join(run, "out", r["query"])
        world = [NAME.match(t)[1] for t in unkey(r["query"]).split() if t[0] != "!"]
        oo, ao = (sorted(set(lines(o + a)) - set(lines(o + b))) for a, b in
                  ((".ours", ".theirs"), (".theirs", ".ours")))
        to, ta = contested(pkgs, oo, lines(o + ".ours"), world), contested(pkgs, ao, lines(o + ".theirs"), world)
        few = lambda xs: "+".join(sorted(xs)[:3]) + ("+%d more" % (len(xs) - 3) if len(xs) > 3 else "") or "-"
        cl[r["query"]] = "; ".join("%s: ours %s, apk %s" % (n, few(to.get(n, ())), few(ta.get(n, ())))
                                  for n in sorted(set(to) | set(ta)))
    show(c + ", by contested name", group([r for r in rows if r["query"] in cl], lambda r: cl[r["query"]]))
for c in ("instance-gap", "both-refuse"):
    show(c + ", by pac's first incompatibility", group(
        [r for r in rows if r["class"] == c], lambda r: first_incompatibility(os.path.join(run, "out", r["query"] + ".out"))))


def apk_reason(r):
    """the first problem apk names, reduced to its kind"""
    body = [l.strip() for l in lines(os.path.join(run, "out", r["query"] + ".apk")) if not l.startswith("ERROR")]
    for s in body:
        if s.startswith(("conflicts:", "breaks:", "satisfies:")):
            return s.split(":")[0]
        for kind in ("no such package", "virtual"):
            if "(%s)" % kind in s:
                return kind
    return (body or ["?"])[0][:80]


for c in ("tool-declines", "both-refuse"):
    show(c + ", by apk's reason", group([r for r in rows if r["class"] == c], apk_reason))
