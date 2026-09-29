#!/usr/bin/env python3
"""Classify a scale.sh run, per mode, and cluster its divergences by
contested clause: a Depends or Recommends of a package both answers install
that some package only one answer installs satisfies.  Clustering there
rather than on the whole difference folds what a choice pulled in
downstream into the choice itself.  Satisfaction is read by name, with
version constraints ignored, and architecture too: a package is named as
apt names it, name:arch at a foreign architecture, and an atom is met by
its name at any architecture.
usage: triage.py <run-dir>"""
import collections, os, re, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
from triage_lib import first_incompatibility, lines, report, show

run = sys.argv[1]
# a run with a foreign architecture reads both indexes as one, which it keeps
PACKAGES = os.path.join(run, "Packages")
if not os.path.exists(PACKAGES):
    PACKAGES = os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../repos/debian/Packages")
ATOM = re.compile(r"\s*([^\s(:\[<]+)(?::([^\s(\[<]+))?\s*(?:\(\s*([<>=]+)\s*([^)\s]+)\s*\))?")


def clauses(field):
    """each clause as its alternatives, an alternative as (name, any?, op, version)"""
    return [[(m[1], m[2] == "any", m[3], m[4]) for m in map(ATOM.match, c.split("|")) if m]
            for c in field.split(",") if c.strip()]


def load():
    idx, prov, archs = {}, collections.defaultdict(set), set()
    for st in open(PACKAGES, encoding="utf-8", errors="replace").read().split("\n\n"):
        f = dict(re.findall(r"^(\S+): (.*(?:\n[ \t].*)*)", st, re.M))
        a = f.get("Architecture", "amd64")
        p = f.get("Package", "") + ("" if a in ("amd64", "all") else ":" + a)
        if "Package" in f and p not in idx:
            archs.add(a)
            idx[p] = {"dep": clauses(f.get("Pre-Depends", "")) + clauses(f.get("Depends", "")),
                      "rec": clauses(f.get("Recommends", ""))}
            for c in clauses(f.get("Provides", "")):
                prov[c[0][0]].add(p)
    return idx, prov, sorted(archs - {"amd64", "all"})


idx, prov, foreign = load()


def sat(ans, cl):
    return {x for a in cl for x in ({a[0]} | {a[0] + ":" + b for b in foreign} | prov[a[0]]) & ans}


def decisions(ours, apt, query):
    shared = ours & apt
    for p in sorted(shared | {query}):
        for kind in ("dep", "rec"):
            for cl in idx.get(p, {}).get(kind, []):
                so, sa = sat(ours, cl), sat(apt, cl)
                if (so | sa) - shared:
                    yield "%s ours=%s apt=%s  [%s: %s]" % (
                        kind, "+".join(sorted(so)) or "-", "+".join(sorted(sa)) or "-",
                        p, " | ".join(a[0] for a in cl))


def apt_reason(r):
    ls = lines(os.path.join(run, "out", r["query"] + ".apt"))
    for l in ls:
        m = re.match(r"\s*\S+ : (\S+): \S+(.*)", l)
        if m:
            return "%s: %s" % (m[1], re.sub(r"\([^)]*\)", "", m[2]).strip()[:60])
    return re.sub(r"'[^']*'", "_", next((l for l in ls if l.startswith(("E: ", "Note, selecting"))), "?"))[:90]


rows = report(run)
for c in ("preference-gap", "invalid", "exact-invalid"):
    for m in dict.fromkeys(r["mode"] for r in rows):
        groups = collections.defaultdict(list)
        for r in rows:
            if r["class"] == c and r["mode"] == m:
                o = os.path.join(run, "out", r["query"])
                ds = set(decisions(set(lines(o + "." + m + ".ours")), set(lines(o + ".theirs")), r["query"]))
                for d in ds or ["?"]:
                    groups[d].append(r["query"])
        if groups:
            show("%s, mode %s, by contested clause (a query counts once per clause)" % (c, m), groups)
for c in ("instance-gap", "unconfirmed", "both-refuse", "tool-declines", "tool-error"):
    for m in dict.fromkeys(r["mode"] for r in rows):
        rs = [r for r in rows if r["class"] == c and r["mode"] == m]
        if rs:
            g = collections.defaultdict(list)
            for r in rs:
                why = first_incompatibility(os.path.join(run, "out", r["query"] + "." + m + ".out"))
                g["pac: %s | apt: %s" % (why, apt_reason(r))].append(r["query"])
            show("%s, mode %s, by each side's reason" % (c, m), g)
