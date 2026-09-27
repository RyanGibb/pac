#!/usr/bin/env python3
"""Tables from a bench.sh run directory: every row into one CSV, and per
step, set, query and variant the median and interquartile range of the
measured runs (the warm-up, rep 0, left out; a cold step's one run each).
Quartiles interpolate linearly between order statistics, so over five
repetitions the IQR is the fourth value less the second.  Each pac variant
is set against the tool's median: the ratio per query, and over a set the
geometric mean of those ratios, with a 95% bootstrap interval (the
queries resampled BOOT times, the 2.5th and 97.5th percentiles of the
resampled means, seeded by step, set and variant so a table regenerates
alike), and how many queries pac was faster on.  The CSV holds the rows
bench.sh measured and, per step, set and variant, one row with rep=gm
whose ratio_gm, ci_lo and ci_hi are the mean and its interval.

usage: summary.py <run-dir> [csv-out]      prints markdown on stdout;
       the CSV defaults to <run-dir>/bench.csv
"""
import csv
import glob
import math
import random
import sys
from collections import defaultdict

COLS = ["step", "set", "query", "variant", "rep", "wall_s", "parse_s", "solve_s",
        "maxrss_kb", "rc", "end_utc", "load1"]
GM = ["ratio_gm", "ci_lo", "ci_hi"]
BOOT = 10000
TOOL = {"debian": "apt", "alpine": "apk", "opam": "opam", "cargo": "cargo", "npm": "npm"}


def q(xs, p):
    xs = sorted(xs)
    if not xs:
        return None
    k = (len(xs) - 1) * p
    f = math.floor(k)
    c = min(f + 1, len(xs) - 1)
    return xs[f] + (xs[c] - xs[f]) * (k - f)


def load(run):
    rows = []
    for f in sorted(glob.glob(f"{run}/res/*/*/*.csv")):
        rows += [dict(zip(COLS, r)) for r in csv.reader(open(f)) if r]
    return rows


def num(x):
    return float(x) if x not in (None, "") else None


class Cell:
    def __init__(self, rows):
        w = [float(r["wall_s"]) for r in rows]
        self.n = len(w)
        self.med = q(w, .5)
        self.iqr = q(w, .75) - q(w, .25)
        self.parse = q([num(r["parse_s"]) for r in rows if num(r["parse_s"]) is not None], .5)
        self.solve = q([num(r["solve_s"]) for r in rows if num(r["solve_s"]) is not None], .5)
        ms = [num(r["maxrss_kb"]) for r in rows if num(r["maxrss_kb"]) is not None]
        self.rss = q(ms, .5) / 1024 if ms else None
        self.rcs = sorted({r["rc"] for r in rows})


def s(x, d=3):
    return "" if x is None else f"{x:.{d}f}"


def boot(xs, seed):
    """the geometric mean of xs and the percentile interval of it over BOOT
    resamples of xs"""
    ls = [math.log(x) for x in xs if x > 0]
    if not ls:
        return None, None, None
    rng = random.Random(seed)
    ms = [math.exp(sum(rng.choices(ls, k=len(ls))) / len(ls)) for _ in range(BOOT)]
    return math.exp(sum(ls) / len(ls)), q(ms, .025), q(ms, .975)


def ci(g):
    return "" if g[0] is None else f"{g[0]:.2f}× (95% CI {g[1]:.2f}–{g[2]:.2f})"


def table(step, st, rows):
    tool = TOOL[step.split("-")[0]]
    cells = defaultdict(list)
    queries, variants = [], []
    for r in rows:
        if r["step"] == step and r["set"] == st:
            if r["query"] not in queries:
                queries.append(r["query"])
            if r["variant"] not in variants:
                variants.append(r["variant"])
            if r["rep"] != "0":
                cells[r["query"], r["variant"]].append(r)
    C = {k: Cell(v) for k, v in cells.items()}
    pvs = [v for v in variants if v != tool]
    hdr = ["query"]
    for v in pvs:
        hdr += [f"{v} parse / solve", f"{v} wall (IQR)", f"{v} MiB"]
    hdr += [f"{tool} wall (IQR)", f"{tool} MiB"] + [f"{v} ÷ {tool}" for v in pvs]
    out = ["| " + " | ".join(hdr) + " |", "|" + "---|" * len(hdr)]
    agg, notes = defaultdict(list), []
    for g in queries:
        t = C.get((g, tool))
        row = [g]
        for v in pvs:
            c = C.get((g, v))
            row += ["" if c is None or c.parse is None and c.solve is None else f"{s(c.parse, 2)} / {s(c.solve, 2)}",
                    "" if c is None else f"{c.med:.3f} ({c.iqr:.3f})",
                    "" if c is None or c.rss is None else f"{c.rss:.0f}"]
            if c:
                agg[v].append(c.med)
                if t:
                    agg[v, "r"].append(c.med / t.med)
        row += ["" if t is None else f"{t.med:.3f} ({t.iqr:.3f})",
                "" if t is None or t.rss is None else f"{t.rss:.0f}"]
        row += ["" if C.get((g, v)) is None or t is None else f"{C[g, v].med / t.med:.2f}" for v in pvs]
        if t:
            agg[tool].append(t.med)
        for v in variants:
            c = C.get((g, v))
            if c and c.rcs != ["0"]:
                notes.append(f"{g} {v} exit {','.join(c.rcs)}")
        out.append("| " + " | ".join(row) + " |")
    gms = {v: boot(agg[v, "r"], f"{step}:{st}:{v}") for v in pvs}
    foot = ["**median over queries**"]
    for v in pvs:
        foot += ["", s(q(agg[v], .5)), ""]
    foot += [s(q(agg[tool], .5)), ""] + [f"gm {ci(gms[v])}" for v in pvs]
    out.append("| " + " | ".join(foot) + " |")
    foot = ["**sum of medians**"]
    for v in pvs:
        foot += ["", s(sum(agg[v]), 1), ""]
    foot += [s(sum(agg[tool]), 1), ""] + [
        f"pac faster on {sum(1 for x in agg[v, 'r'] if x < 1)}/{len(agg[v, 'r'])}" for v in pvs]
    out.append("| " + " | ".join(foot) + " |")
    gm = [{"step": step, "set": st, "query": "*", "variant": v, "rep": "gm",
           **dict(zip(GM, ("" if x is None else f"{x:.6f}" for x in gms[v])))} for v in pvs]
    return "\n".join(out), notes, gm


def main():
    run = sys.argv[1]
    rows = load(run)
    tables = {k: table(*k, rows) for k in
              dict.fromkeys((r["step"], r["set"]) for r in rows if r["step"] != "floor")}
    with open(sys.argv[2] if len(sys.argv) > 2 else f"{run}/bench.csv", "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=COLS + GM)
        w.writeheader()
        w.writerows(rows)
        for _, _, gm in tables.values():
            w.writerows(gm)
    fl = defaultdict(list)
    for r in rows:
        if r["step"] == "floor" and r["rep"] != "0":
            fl[r["variant"]].append(float(r["wall_s"]))
    if fl:
        print("## floor\n")
    for v, xs in fl.items():
        print(f"- `{v} true`: median {q(xs, .5) * 1000:.2f} ms, IQR {(q(xs, .75) - q(xs, .25)) * 1000:.2f} ms, n={len(xs)}")
    for (step, st), (t, notes, _) in tables.items():
        print(f"\n## {step}, {st}\n\n{t}\n")
        for n in notes:
            print(f"- {n}")
    hi = [r for r in rows if r["step"] != "floor" and float(r["load1"]) >= 3.5]
    print(f"\nrows ending at load >= 3.5: {len(hi)} of {len(rows)}")


if __name__ == "__main__":
    main()
