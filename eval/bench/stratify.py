#!/usr/bin/env python3
"""A benchmark query set drawn from a finished scale.sh run, so that the
benchmarks are not only the regression set the orders were tuned on: the
queries pac, in the tool's order, and the tool both answered, less the
regression set (npm's by name, whatever the version), in ten strata by
the size of pac's answer, equal in count, and K drawn from each.

usage: stratify.py <eco> <run-dir> <seed> [K]    K per stratum, default 5
       prints stratum<TAB>query lines, a queries file bench.sh reads
"""
import os
import random
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
from triage_lib import key, lines  # noqa: E402


def name(q):
    """npm's name@spec as its name; any other query as it stands"""
    return q[:1] + q[1:].split("@", 1)[0] if " " not in q else q


def regression(eco):
    d = os.path.join(os.path.dirname(HERE), eco)
    if eco == "npm":
        return {l.split()[0] for l in lines(os.path.join(d, "baseline", "roots.txt"))}
    return {name(l) for l in lines(os.path.join(d, "queries.txt"))}


def size(out):
    for l in lines(out):
        m = re.match(r"^packages \((\d+)\):$", l)
        if m:
            return int(m.group(1))
    return None


def main():
    eco, run, seed = sys.argv[1:4]
    k = int(sys.argv[4]) if len(sys.argv) > 4 else 5
    queries = {key(q): q for q in (l.split("\t")[-1] for l in lines(os.path.join(run, "queries.txt")))}
    skip = regression(eco)
    cand = []
    for l in lines(os.path.join(run, "results.txt")):
        r = dict(f.split("=", 1) for f in l.split())
        if r["mode"] != "tool" or r["pac"] != "ok" or r["tool"] != "ok":
            continue
        q = queries.get(r["query"])
        n = size(os.path.join(run, "out", r["query"] + ".tool.out"))
        if q is not None and n is not None and name(q) not in skip:
            cand.append((n, q))
    cand.sort()
    rng = random.Random(int(seed))
    for d in range(10):
        stratum = cand[d * len(cand) // 10:(d + 1) * len(cand) // 10]
        for n, q in sorted(rng.sample(stratum, min(k, len(stratum)))):
            print("stratum%d\t%s" % (d, q))


if __name__ == "__main__":
    main()
