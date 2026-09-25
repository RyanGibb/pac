#!/usr/bin/env python3
"""Classify a scale.sh run, per mode, and cluster its divergences by how the
other search mode fares on the query (0install-order agreeing exactly marks
a gap of decision order alone), which compiler each side took, and which
versions flagged avoid-version or deprecated only 0install took.  Errors
are grouped by what check.sh's opam runs had to change, refusals by each
side's reason.
usage: triage.py <run-dir>"""
import collections, os, re, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
from triage_lib import first_incompatibility, lines, report, show

run = sys.argv[1]
REPO = os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../repos/opam-repository")
out = lambda r, ext: os.path.join(run, "out", r["query"] + ext)


def flagged(nv):
    n = nv.partition(".")[0]
    t = "\n".join(lines(os.path.join(REPO, "packages", n, nv, "opam")))
    m = re.search(r"^flags:\s*(\[[^\]]*\]|\S+)", t, re.M)
    return bool(m and re.search(r"avoid-version|deprecated", m[1]))


def divergence(r, rows):
    ours = dict(x.partition(".")[::2] for x in lines(out(r, "." + r["mode"] + ".ours")))
    theirs = dict(x.partition(".")[::2] for x in lines(out(r, ".theirs")))
    others = ", ".join("%s %s" % (o["mode"], o["corr"]) for o in rows
                       if o["query"] == r["query"] and o["mode"] != r["mode"])
    flags = [n for n, v in theirs.items() if ours.get(n) != v and flagged(n + "." + v)]
    return "%s; ocaml %s -> %s; 0install alone takes flagged: %s" % (
        others or "-", ours.get("ocaml", "-"), theirs.get("ocaml", "-"), " ".join(sorted(flags)) or "-")


def invalid(r):
    """what check.sh's install and fixup had to do"""
    d = out(r, "." + r["mode"] + ".check")
    t = "\n".join(l for f in ("install", "fixup") for l in lines(os.path.join(d, f)))
    verbs = set(re.findall(r"^\s*- (\w+) ", t, re.M))
    return ("removes a conflicting package" if "[conflicts with" in t else
            "changes versions" if verbs & {"remove", "downgrade", "upgrade"} else
            "adds packages" if "install" in verbs else " ".join(sorted(verbs)) or "?")


def refused(r):
    t = "\n".join(lines(out(r, ".0i")))
    why = ("cycle" if "cyclic dependencies" in t else
           "unavailable" if re.search(r"unmet availability", t) else
           "no solution" if "No solution" in t or "Package conflict" in t else t.strip()[-60:])
    s = "0install: %s; mccs %s" % (why, r["mccs"])
    return s if r["pac"] == "ok" else s + "; pac: " + first_incompatibility(out(r, "." + r["mode"] + ".out"))


rows = report(run)
for m in dict.fromkeys(r["mode"] for r in rows):
    for c, label in (("error", lambda r: invalid(r) if r["tool"] == "ok" else
                      "%s; %s" % (invalid(r), refused(r))),
                     ("preference-gap", lambda r: divergence(r, rows)),
                     ("instance-gap", lambda r: divergence(r, rows) if r["pac"] == "ok" else
                      "pac: " + first_incompatibility(out(r, "." + r["mode"] + ".out"))),
                     ("unconfirmed", lambda r: "pin %s; pac: %s" % (
                         r["pin"], first_incompatibility(out(r, "." + r["mode"] + ".out")))),
                     ("unchecked", lambda r: "valid %s, pin %s" % (r["valid"], r["pin"])),
                     ("tool-declines", refused),
                     ("both-refuse", refused)):
        g = collections.defaultdict(list)
        for r in rows:
            if r["class"] == c and r["mode"] == m:
                g[label(r)].append(r["query"])
        show("%s, mode %s" % (c, m), g)
