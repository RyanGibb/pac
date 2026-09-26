"""Shared by each eval/<eco>/triage.py: a scale.sh run's result lines, the
class each query falls in, and the tables every ecosystem prints.  Also the
one spelling of a query as a file name, which scale-lib.sh asks for:

  triage_lib.py keys < queries-file    key<TAB>query per line, a query being
                                       a line's last tab-separated field
  triage_lib.py unkey <key>            the query
"""
import collections
import os
import re
import sys


def lines(p):
    try:
        return [l for l in open(p, errors="replace").read().split("\n") if l]
    except FileNotFoundError:
        return []


def key(g):
    return g.replace("%", "%25").replace("+", "%2B").replace("/", "%2F").replace(" ", "+")


def unkey(k):
    return k.replace("+", " ").replace("%2F", "/").replace("%2B", "+").replace("%25", "%")


def classify(r):
    pac, tool, valid, pin = r["pac"], r["tool"], r["valid"], r.get("pin", "-")
    if pac == "harness":
        return "harness-error"
    if pac in ("timeout", "crash", "refuse", "io-error"):
        return "pac-" + pac
    if tool == "unrecorded":
        return tool
    if tool in ("timeout", "error"):
        return "tool-" + tool
    # a resolution the tool cannot then install, for a cycle in its install
    # order, is not an error of the resolution
    if pac == "ok" and valid == "CYCLIC":
        return "post-resolution"
    if pac == "ok" and valid not in ("VALID", "INVALID"):
        return "unchecked"
    # an answer the tool rejects is pac's error whether or not the tool had
    # one of its own
    if pac == "ok" and valid == "INVALID":
        return "exact-invalid" if tool == "ok" and r["corr"] == "exact" else "invalid"
    if pac == "ok" and tool == "ok":
        if r["corr"] == "exact":
            return "exact"
        if r["corr"] != "diff":
            return "unchecked"
        # only a pin that ran says which gap this is; an ecosystem with no
        # pin check has none to say it
        if pin == "unsat":
            return "instance-gap"
        return "preference-gap" if pin in ("ok", "-") else "unchecked"
    if pac == "ok":
        return "tool-declines"
    # pac's refusal is a gap of the instance only once pac also refuses the
    # tool's own answer
    if tool == "ok":
        return "instance-gap" if pin == "unsat" else "unconfirmed"
    return "both-refuse"


def group(rows, label):
    g = collections.defaultdict(list)
    for r in rows:
        g[label(r)].append(r["query"])
    return g


def show(title, groups):
    if not groups:
        return
    print("\n== " + title)
    for label, ks in sorted(groups.items(), key=lambda x: (-len(x[1]), str(x[0]))):
        print("%6d  %s  e.g. %s" % (len(ks), label, " | ".join(unkey(k) for k in ks[:5])))


def first_incompatibility(out):
    """pac's first derived incompatibility, with names and versions blanked
    so that like refusals collect."""
    ls = lines(out)
    i = next((j for j, l in enumerate(ls) if l.startswith("unsatisfiable")), None)
    why = ls[i + 1] if i is not None and i + 1 < len(ls) else "?"
    why = re.sub(r"(?<!\S)(?!->)\S+ (\([^)]*\)|∅|[^\s,]*\d[^\s,]*)|\S+@\d\S*", "_", why)
    return re.sub(r"_( [_|])+", "_", why)[:120]


def report(run, by="mode"):
    """Print the class counts per mode (or per value of another field), per
    pool of the queries file, and between modes, and return the rows, each
    with its class."""
    rows = [dict(f.split("=", 1) for f in l.split()) for l in lines(os.path.join(run, "results.txt"))]
    for r in rows:
        r["class"] = classify(r)
    parts = sorted(dict.fromkeys(r[by] for r in rows), key=lambda m: m != "tool")
    for m in parts:
        show("classes, %s %s" % (by, m), group([r for r in rows if r[by] == m], lambda r: r["class"]))
        # the tool's own fixed point is no part of validity, so it is shown apart
        show("minimal, of the valid answers, %s %s" % (by, m), group(
            [r for r in rows if r[by] == m and r["valid"] == "VALID"],
            lambda r: "minimal=" + r.get("minimal", "-")))
    cls = {(r["query"], r[by]): r["class"] for r in rows}
    pools = [l.split("\t", 1) for l in lines(os.path.join(run, "queries.txt")) if "\t" in l]
    for m in parts if pools else []:
        print("\n== classes by pool, %s %s" % (by, m))
        t = collections.defaultdict(collections.Counter)
        for pool, g in pools:
            if (key(g), m) in cls:
                t[pool][cls[key(g), m]] += 1
        for pool in sorted(t):
            print("  %-20s %s" % (pool, " ".join("%s=%d" % kv for kv in sorted(t[pool].items()))))
    modes = parts if by == "mode" else []
    for m in modes[1:]:
        print("\n== %s -> %s" % (modes[0], m))
        n = collections.Counter((cls[g, modes[0]], c) for (g, mm), c in cls.items()
                                if mm == m and (g, modes[0]) in cls)
        for (a, b), c in n.most_common():
            print("  %-16s -> %-16s %6d" % (a, b, c))
    return rows


if __name__ == "__main__":
    if sys.argv[1] == "keys":
        for l in sys.stdin.read().split("\n"):
            if l.strip():
                q = l.split("\t")[-1]
                print(key(q) + "\t" + q)
    elif sys.argv[1] == "unkey":
        print(unkey(sys.argv[2]))
