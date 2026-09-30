#!/usr/bin/env python3
"""The evaluation's figures and tables, from the run directories alone.

usage: figures.py <sources.conf>... <out-dir> [--pdf]

sources.conf names every run directory read (see its header); a later
conf's rows replace an earlier's, as level2.conf's do sources.conf's.  The
outputs land in <out-dir>:

  preamble.tex           what the paper's preamble \\input's: packages,
                         colours and the \\ev* macros the rest use
  fig-A-outcomes.tex     correspondence and validity, one stacked bar per
                         set and order
  tab-B-correspondence.tex, tab-C-validity.tex, tab-C-fuzz.tex,
  tab-D-npm.tex, tab-G-time.tex
  fig-E-timing.tex       pac ÷ tool per comparison, warm, cold start and
                         first run
  fig-F-scatter.tex      per query, the tool's time against pac's
  (each figure and table again with -<set> for every further bench set)
  provenance.tex/.md     each source: its run, pac binary, commit, date,
                         and whether it is stale (its commit is not the
                         configured current one)
  missing.md             every cell printed as missing, and why
  data/*.tsv             the numbers behind every figure
  eval-figures.pdf, fig-*.pdf     with --pdf and pdflatex on PATH

Every cell carries a superscript naming its source in the provenance
table; a stale source's is red.  Data a source lacks prints as a red
"missing", never as a number from elsewhere.
"""
import collections
import glob
import hashlib
import math
import os
import shutil
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, ".."))
sys.path.insert(0, os.path.join(HERE, "..", "bench"))
sys.path.insert(0, os.path.join(HERE, "..", "debian"))
from triage_lib import classify, lines, results, unkey  # noqa: E402
from multiarch import stanzas  # noqa: E402
import summary  # noqa: E402

ORDERS = ("tool", "pubgrub")
ORDER_NAME = {"tool": "tool", "pubgrub": "PubGrub"}


# ---------------------------------------------------------------- sources

class Conf:
    """the sources the conf files name, a later line replacing an earlier
    one of its kind and id"""
    def __init__(self, paths):
        self.current = None
        self.binaries = {}
        self.runs, self.fuzz, self.bench = {}, {}, {}
        self.totals = self.causes = None
        for path, l in ((p, l) for p in paths for l in lines(p)):
            if l.lstrip().startswith("#"):
                continue
            f = [x.strip() for x in l.split("|")]
            k = f[0]
            if k == "current":
                self.current = f[1]
            elif k == "binary":
                # a sha256 prefix, or the binary itself to hash
                h = f[1] if "/" not in f[1] else (sha(os.path.expandvars(f[1])) or "missing-binary")[:8]
                self.binaries[h] = (f[2], f[3] if len(f) > 3 else "")
            elif k in ("run", "fuzz", "bench"):
                f += [""] * (6 - len(f))
                p = os.path.expandvars(f[2])
                ent = {"id": f[1], "path": None if p in ("-", "") else p, "set": f[3],
                       "flags": f[4].split(), "note": f[5]}
                {"run": self.runs, "fuzz": self.fuzz, "bench": self.bench}[k][f[1]] = ent
            elif k == "totals":
                self.totals = os.path.expandvars(f[1])
            elif k == "causes":
                self.causes = os.path.join(os.path.dirname(os.path.abspath(path)), os.path.expandvars(f[1]))


def sha(p):
    try:
        with open(p, "rb") as f:
            return hashlib.file_digest(f, "sha256").hexdigest()
    except OSError:
        return None


class Prov:
    """the sources cells cite: a letter each, in order of first citation"""
    def __init__(self, conf):
        self.conf = conf
        self.keys = {}  # path -> letter
        self.ents = {}  # letter -> entry
        self.missing = []

    def commit(self, h):
        if not h:
            return None, ""
        for pre, (c, what) in self.conf.binaries.items():
            if h.startswith(pre):
                return c, what
        return None, ""

    def cite(self, what, path, binary_sha, date, note):
        k = path
        if k in self.keys:
            e = self.ents[self.keys[k]]
            if what not in e["what"].split(", "):
                e["what"] += ", " + what
        else:
            c, bwhat = self.commit(binary_sha)
            stale = c != self.conf.current
            letter = letters(len(self.ents))
            self.keys[k] = letter
            self.ents[letter] = {"key": letter, "what": what, "path": path, "sha": (binary_sha or "")[:8],
                                 "commit": c or "unknown", "binary": bwhat, "date": date, "stale": stale,
                                 "note": note}
        return self.keys[k]

    def stale(self, key):
        return self.ents[key]["stale"]

    def mark(self, key):
        """a cell's superscript"""
        if key is None:
            return ""
        return "\\evsrc{%s}" % key if not self.stale(key) else "\\evstale{%s}" % key

    def miss(self, where, what, why):
        self.missing.append((where, what, why))
        return "\\evmissing"


def letters(i):
    s = ""
    i += 1
    while i:
        i, r = divmod(i - 1, 26)
        s = chr(97 + r) + s
    return s


def mtime(p):
    try:
        import datetime
        t = datetime.datetime.fromtimestamp(os.path.getmtime(p), datetime.timezone.utc)
        return t.strftime("%Y-%m-%d %H:%M")
    except OSError:
        return ""


def run_source(prov, ent, what):
    p = ent["path"]
    return prov.cite(what, os.path.realpath(p), sha(os.path.join(p, "pac.exe")),
                     mtime(os.path.join(p, "results.txt")), ent["note"])


def bench_source(prov, ent, step):
    """a bench step's rows: the bench RUN its res/<step> links into, and
    the pac binary that RUN's machine.txt records"""
    d = os.path.realpath(os.path.join(ent["path"], "res", step))
    run = os.path.dirname(os.path.dirname(d))
    m = {}
    for l in lines(os.path.join(run, "machine.txt")):
        if ":" in l:
            a, b = l.split(":", 1)
            m.setdefault(a.strip(), b.strip())
    return prov.cite("bench " + step, run, m.get("pac", "").split(" ")[0], m.get("date", ""), ent["note"])


# ---------------------------------------------------------------- reading runs

def have(ent):
    return ent is not None and ent["path"] is not None and os.path.exists(os.path.join(ent["path"], "results.txt"))


def reask(path, mode):
    p = "%s.reask-%s" % (path.rstrip("/"), mode)
    return {r["query"]: r for r in results(p) if r.get("mode") == mode}


def berry(path):
    return ({(f["query"], f["mode"]): f.get("berry") for f in results(path, "berry.txt")},
            {(f["query"], f["mode"]): f.get("exact") for f in results(path, "berryown.txt")})


def cmpf(r, what):
    for part in r.get("cmp", "").split(";"):
        if part.startswith(what + "="):
            return part.split("=", 1)[1]
    return None


def num(x):
    try:
        return float(x)
    except (TypeError, ValueError):
        return None


def q(xs, p):
    return summary.q([x for x in xs if x is not None], p)


def wilson(k, n, z=1.96):
    if not n:
        return None
    p = k / n
    d = 1 + z * z / n
    c = (p + z * z / (2 * n)) / d
    h = z * math.sqrt(p * (1 - p) / n + z * z / (4 * n * n)) / d
    return 100 * (c - h), 100 * (c + h)


def esc(s):
    s = str(s)
    for a, b in (("\\", "\\textbackslash{}"), ("&", "\\&"), ("%", "\\%"), ("$", "\\$"), ("#", "\\#"),
                 ("_", "\\_"), ("{", "\\{"), ("}", "\\}"), ("~", "\\textasciitilde{}"),
                 ("^", "\\textasciicircum{}"), ("--", "-{}-")):
        s = s.replace(a, b)
    return s


def cause_of(cs, eco, g):
    """a query's cause, by the query or its last word (--with-test q is q)"""
    return cs.get((eco, g)) or cs.get((eco, g.split()[-1] if g.split() else g))


def causes(conf):
    c = {}
    for l in lines(conf.causes) if conf.causes else []:
        if l.lstrip().startswith("#"):
            continue
        f = [x.strip() for x in l.split("|")]
        if len(f) >= 3:
            c[f[0], f[1]] = f[2]
    return c


# ---------------------------------------------------------------- the sets

# id, ecosystem label, how the reading is judged (npm, placement, berry)
ROWS_A = [("debian", "Debian, amd64"), ("debian-ma-tgt", "Debian, amd64+i386"),
          ("debian-ma-sample", "Debian, amd64+i386"),
          ("alpine", "Alpine"), ("opam", "opam"), ("opam-wt", "opam"),
          ("cargo", "Cargo"), ("cargo-heldout", "Cargo"), ("cargo-newindex", "Cargo"),
          ("npm", "npm, npm reading"), ("npm-shared", "npm, shared reading"),
          ("npm-placement", "npm, placement reading")]
ROWS_BC = ROWS_A[:7] + [("cargo-tgt", "Cargo")] + ROWS_A[7:] + \
    [("npm-tgt", "npm, npm reading"), ("npm-shared-tgt", "npm, shared reading"),
     ("npm-placement-tgt", "npm, placement reading")]


def eco_of(i):
    return i.split("-")[0]


def reading(i):
    return "shared" if "shared" in i else "placement" if "placement" in i else "npm" if i.startswith("npm") else None


def judge_label(i):
    return {"shared": "judged by Berry", "placement": "judged by npm", "npm": "judged by npm"}.get(reading(i), "")


SEGS = [("exact", "exact", "evexact"),
        ("relexact", "exact by relation, layout differs", "evrel"),
        ("gap", "preference gap (valid, different)", "evgap"),
        ("refuse", "both refuse", "evrefuse"),
        ("invalid", "invalid", "evinvalid"),
        ("platform", "platform-excluded (npm)", "evplatform"),
        ("timeout", "timeouts", "evtimeout"),
        ("other", "other", "evother")]


OTHER_WORD = {"post-resolution": "cyclic", "unconfirmed": "unconfirmed", "tool-error": "tool error",
              "pac-refuse": "pac refuses", "unchecked": "unchecked", "instance-gap": "instance gap",
              "tool-declines": "tool declines", "pac-unsat (Berry not asked)": "not asked of Berry",
              "pac-crash": "crash", "pac-io-error": "i/o error", "harness-error": "harness error"}


def segment(r, c, placement):
    """Figure A's segment of r, of class c"""
    if placement and c == "preference-gap" and cmpf(r, "relation") == "exact":
        return "relexact"
    # pac refusing the query itself (apt's "Unable to locate package") is
    # a refusal too, when the tool refuses it
    if c == "pac-refuse" and r["tool"] == "refuse":
        return "refuse"
    return {"exact": "exact", "preference-gap": "gap", "both-refuse": "refuse", "invalid": "invalid",
            "exact-invalid": "invalid", "platform-excluded": "platform", "pac-timeout": "timeout",
            "tool-timeout": "timeout"}.get(c, "other")


def berry_class(r, b, o):
    """the shared reading's class against Berry: its check, then its own
    answer"""
    if r["pac"] == "timeout":
        return "pac-timeout"
    if r["pac"] != "ok":
        return "pac-" + r["pac"] + " (Berry not asked)"
    v = b.get((r["query"], r["mode"]))
    if v == "INVALID":
        return "invalid"
    if v != "VALID":
        return "Berry check error"
    e = o.get((r["query"], r["mode"]))
    return {"yes": "exact", "no": "preference-gap"}.get(e, "Berry-own error")


# ---------------------------------------------------------------- output helpers

class Out:
    def __init__(self, d):
        self.d = d
        os.makedirs(os.path.join(d, "data"), exist_ok=True)

    def write(self, name, s):
        with open(os.path.join(self.d, name), "w") as f:
            f.write(s)

    def tsv(self, name, hdr, body):
        self.write(os.path.join("data", name), "\n".join("\t".join(str(c) for c in r) for r in [hdr] + body) + "\n")


def pct(k, n, d=1):
    return "" if not n else "%.*f" % (d, 100 * k / n)


def cnt(n):
    return "{:,}".format(n).replace(",", "\\,")


def header(hdr, k):
    """a table's header row, its first k cells bold"""
    return " & ".join("\\textbf{%s}" % h if i < k else h for i, h in enumerate(hdr)) + " \\\\"


def order_label(ent, m):
    s = ORDER_NAME[m]
    if "provisional:" + m in ent["flags"]:
        s += "\\evprov"
    return s


def row_title(ent, eco, rid):
    j = judge_label(rid)
    return "%s\\\\%s%s" % (eco, esc(ent["set"]), (", " + j) if j and rid.endswith(("shared", "shared-tgt")) else "")


# ---------------------------------------------------------------- A and B

def outcome_counts(conf, prov):
    """per A row and order: the segments' counts; also B's classes"""
    res = []
    for rid, eco in ROWS_BC:
        ent = conf.runs.get(rid) or {"id": rid, "path": None, "set": "?", "flags": [], "note": ""}
        if not have(ent):
            res.append({"id": rid, "eco": eco, "ent": ent, "src": None, "orders": {}})
            continue
        src = run_source(prov, ent, "run " + rid)
        rs = results(ent["path"])
        rd = reading(rid)
        b, o = berry(ent["path"]) if rd == "shared" else ({}, {})
        orders = {}
        for m in ORDERS:
            mr = [r for r in rs if r["mode"] == m]
            if not mr:
                continue
            seg, other = collections.Counter(), collections.Counter()
            for r in mr:
                c = berry_class(r, b, o) if rd == "shared" else classify(r)
                sg = segment(r, c, rd == "placement")
                seg[sg] += 1
                if sg == "other":
                    other[c] += 1
            cls = collections.Counter(classify(r) for r in mr)
            bcls = collections.Counter(berry_class(r, b, o) for r in mr) if rd == "shared" else None
            ans = sum(1 for r in mr if r["tool"] == "ok" and r["corr"] != "ERR")
            ex = sum(1 for r in mr if r["tool"] == "ok" and r["corr"] == "exact")
            ra = reask(ent["path"], m)
            orders[m] = {"n": len(mr), "seg": seg, "other": other, "cls": cls, "bcls": bcls,
                         "tool_ok": sum(1 for r in mr if r["tool"] == "ok"), "ans": ans, "exact": ex,
                         "reask": (sum(1 for r in ra.values() if r["pac"] == "ok"),
                                   sum(1 for r in ra.values() if r["corr"] == "exact"),
                                   sum(1 for r in ra.values() if r["pac"] == "timeout"), len(ra)) if ra else None,
                         "berry_asked": sum(1 for r in mr if (r["query"], m) in o),
                         "berry_exact": sum(1 for r in mr if o.get((r["query"], m)) == "yes")}
        res.append({"id": rid, "eco": eco, "ent": ent, "src": src, "orders": orders})
    return res


def fig_a(out, prov, oc):
    rowsA = [x for x in oc if x["id"] in dict(ROWS_A)]
    rowsA.sort(key=lambda x: [r for r, _ in ROWS_A].index(x["id"]))
    data, bars, groups = [], [], []
    y = 0.0
    for x in reversed(rowsA):  # pgfplots counts y upwards
        ent = x["ent"]
        ys = []
        for m in reversed(ORDERS):
            o = x["orders"].get(m)
            y += 1
            ys.append(y)
            if o is None:
                bars.append((y, None, x, m))
                prov.miss("A", "%s %s %s" % (x["id"], ent["set"], m), "no run" if not have(ent) else "no %s-order lines" % m)
                continue
            bars.append((y, o, x, m))
            data.append([x["id"], ent["set"], m, o["n"]] + [o["seg"].get(s, 0) for s, _, _ in SEGS])
        groups.append((sum(ys) / len(ys), x))
        y += 0.6
    out.tsv("fig-A-outcomes.tsv", ["id", "set", "order", "queries"] + [s for s, _, _ in SEGS], list(reversed(data)))
    h = y
    t = ["% Figure A: every query of each set, by outcome, in each order.  Generated by eval/paper/figures.py.",
         "\\begin{tikzpicture}",
         "\\begin{axis}[evbars, xbar stacked, scale only axis, width=\\linewidth-265pt, height=%.1fpt, ymin=0.3, ymax=%.1f," % (h * 11, h),
         "  xmin=0, xmax=100, xlabel={share of the set's queries (\\%)},",
         "  ytick={%s}, yticklabels={%s}]" % (
             ",".join("%.1f" % b[0] for b in bars),
             ",".join("{%s}" % order_label(b[2]["ent"], b[3]) for b in bars))]
    for s, label, col in SEGS:
        co = " ".join("(%.4f,%.1f)" % (100 * (b[1]["seg"].get(s, 0) / b[1]["n"]) if b[1] else 0, b[0]) for b in bars)
        pat = ", postaction={pattern=north east lines, pattern color=black!45}" if s == "other" else ""
        t.append("\\addplot[fill=%s, draw=white, line width=0.3pt%s] coordinates {%s};" % (col, pat, co))
        t.append("\\addlegendentry{%s}" % label)
    for yv, o, x, m in bars:
        if o is None:
            t.append("\\node[anchor=west, font=\\scriptsize] at (axis cs:0,%.1f) {\\evmissing};" % yv)
            continue
        small = []
        for s, word in (("invalid", "invalid"), ("platform", "platform-excl."), ("timeout", "timeout")):
            k = o["seg"].get(s, 0)
            if k and k / o["n"] < 0.01:
                small.append("%d %s" % (k, word))
        if o["seg"].get("other", 0) / o["n"] < 0.01:
            small += ["%d %s" % (k, OTHER_WORD.get(c, c)) for c, k in o["other"].most_common()]
        lab = "%s\\,\\%%" % pct(o["seg"].get("exact", 0), o["n"])
        if small:
            lab += "\\enspace{\\color{evink2}%s}" % esc(", ".join(small))
        t.append("\\node[anchor=west, font=\\scriptsize, inner sep=1pt] at (axis cs:100,%.1f) {%s};" % (yv, lab))
    for yv, x in groups:
        t.append("\\node[anchor=east, font=\\footnotesize, align=right, xshift=-32pt] at (axis cs:0,%.2f) "
                 "{%s%s};" % (yv, row_title(x["ent"], x["eco"], x["id"]), prov.mark(x["src"])))
    t += ["\\end{axis}", "\\end{tikzpicture}", ""]
    out.write("fig-A-outcomes.tex", "\n".join(t))


def tab_b(out, prov, oc, conf):
    cols = [c for c in ["exact", "preference-gap", "instance-gap", "unconfirmed", "invalid", "exact-invalid",
                        "post-resolution", "platform-excluded", "tool-declines", "both-refuse", "pac-timeout",
                        "tool-timeout", "pac-refuse", "pac-crash", "pac-io-error", "tool-error", "harness-error",
                        "unchecked", "unrecorded"]
            if any(o["cls"].get(c) for x in oc for o in x["orders"].values())]
    short = {"exact": "exact", "preference-gap": "pref.\\ gap", "instance-gap": "inst.\\ gap",
             "unconfirmed": "unconf.", "invalid": "invalid", "exact-invalid": "exact-inv.",
             "post-resolution": "cyclic", "platform-excluded": "platf.", "tool-declines": "tool decl.",
             "both-refuse": "both ref.", "pac-timeout": "pac t/o", "tool-timeout": "tool t/o",
             "pac-refuse": "pac ref.", "pac-crash": "crash", "pac-io-error": "i/o err.", "tool-error": "tool err.",
             "harness-error": "harn.", "unchecked": "unchk.", "unrecorded": "unrec."}
    hdr = ["set", "order", "queries", "tool ans.", "exact \\%", "95\\% Wilson"] + [short[c] for c in cols] + \
        ["re-ask 3600\\,s"]
    data = []
    t = ["% Table B: correspondence per set and order (triage_lib.classify).  Generated by eval/paper/figures.py.",
         "\\begin{tabular}{@{}ll" + "r" * (len(hdr) - 2) + "@{}}", "\\toprule",
         header(hdr, 2), "\\midrule"]
    last_eco = None
    for x in oc:
        ent = x["ent"]
        if last_eco is not None and eco_of(x["id"]) != last_eco:
            t.append("\\addlinespace")
        last_eco = eco_of(x["id"])
        title = "%s, %s%s" % (x["eco"], esc(ent["set"]), prov.mark(x["src"]))
        if not x["orders"]:
            prov.miss("B", "%s %s" % (x["id"], ent["set"]), "no run")
            t.append("%s & & \\multicolumn{%d}{l}{\\evmissing} \\\\" % (title, len(hdr) - 2))
            continue
        for i, m in enumerate(ORDERS):
            o = x["orders"].get(m)
            first = title if i == 0 else ""
            if not o:
                t.append("%s & %s & \\multicolumn{%d}{l}{\\evmissing} \\\\" % (first, order_label(ent, m), len(hdr) - 2))
                prov.miss("B", "%s %s %s" % (x["id"], ent["set"], m), "no %s-order lines" % m)
                continue
            w = wilson(o["exact"], o["ans"])
            ra = o["reask"]
            cells = [first, order_label(ent, m), cnt(o["n"]), cnt(o["tool_ok"]), pct(o["exact"], o["ans"]),
                     "%.1f--%.1f" % w if w else "--"] + [cnt(o["cls"].get(c, 0)) if o["cls"].get(c) else "\\evzero"
                                                          for c in cols] + \
                ["%d/%d/%d of %d" % ra if ra else "--"]
            t.append(" & ".join(cells) + " \\\\")
            data.append([x["id"], ent["set"], m, o["n"], o["tool_ok"], o["ans"], o["exact"],
                         "%.2f" % (100 * o["exact"] / o["ans"]) if o["ans"] else "",
                         "%.2f-%.2f" % w if w else ""] + [o["cls"].get(c, 0) for c in cols] +
                        ["%d/%d/%d/%d" % ra if ra else ""])
        if reading(x["id"]) == "shared":
            # the same answers judged by Berry, as Figure A shows them
            for i, m in enumerate(ORDERS):
                o = x["orders"].get(m)
                if not o:
                    continue
                bc = o["bcls"]
                w = wilson(o["berry_exact"], o["berry_asked"])
                rest = ", ".join("%s %d" % (k, v) for k, v in sorted(bc.items())
                                 if k not in ("exact", "preference-gap"))
                t.append("%s & %s & %s & %s & %s & %s & %s & %s & \\multicolumn{%d}{l}{\\footnotesize %s} \\\\" % (
                    "\\quad against Berry's own answer" if i == 0 else "", order_label(ent, m), cnt(o["n"]),
                    cnt(o["berry_asked"]), pct(o["berry_exact"], o["berry_asked"]),
                    "%.1f--%.1f" % w if w else "--", cnt(bc.get("exact", 0)), cnt(bc.get("preference-gap", 0)),
                    len(hdr) - 8, esc(rest)))
                data.append([x["id"] + ":berry", ent["set"], m, o["n"], o["berry_asked"], o["berry_asked"],
                             o["berry_exact"], pct(o["berry_exact"], o["berry_asked"], 2),
                             "%.2f-%.2f" % w if w else ""] + [bc.get(c, 0) for c in cols] + [rest])
    # opam against builtin-mccs, which optimises: divergence, not correspondence
    ent = conf.runs.get("opam")
    t += ["\\midrule", "\\multicolumn{%d}{@{}l}{\\emph{Divergence from an optimising solver, not correspondence:} "
          "opam against builtin-mccs+glpk, opam's default} \\\\" % len(hdr)]
    mc = results(ent["path"], "mccs.txt") if have(ent) else []
    if not mc:
        prov.miss("B", "opam vs builtin-mccs", "no mccs.txt in the opam run")
        t.append("opam, full & & \\multicolumn{%d}{l}{\\evmissing} \\\\" % (len(hdr) - 2))
    else:
        src = run_source(prov, ent, "run opam")
        st = collections.Counter(r["mccs"] for r in mc)
        acc = results(ent["path"], "mccs-accept.txt")
        a = collections.Counter(r["accepted"] for r in acc)
        for i, m in enumerate(ORDERS):
            both = [r for r in mc if r.get(m) in ("exact", "diff")]
            ex = sum(1 for r in both if r[m] == "exact")
            w = wilson(ex, len(both))
            note = ("mccs refuses %d, errs %d, times out %d; of %d differences drawn, 0install takes mccs's "
                    "answer for %d" % (st.get("refuse", 0), st.get("error", 0), st.get("timeout", 0), len(acc),
                                       a["yes"])) if i == 0 else ""
            t.append("%s & %s & %s & %s & %s & %s & \\multicolumn{%d}{l}{\\footnotesize %s} \\\\" % (
                ("opam, " + esc(ent["set"]) + prov.mark(src)) if i == 0 else "", ORDER_NAME[m], cnt(len(mc)),
                cnt(len(both)), pct(ex, len(both)), "%.1f--%.1f" % w if w else "--", len(hdr) - 6, esc(note)))
            data.append(["opam:mccs", ent["set"], m, len(mc), st["ok"], len(both), ex, pct(ex, len(both), 2),
                         "%.2f-%.2f" % w if w else ""] + [""] * len(cols) + [dict(st)])
    t += ["\\bottomrule", "\\end{tabular}", ""]
    out.tsv("tab-B-correspondence.tsv", ["id", "set", "order", "queries", "tool answered", "compared", "exact",
                                         "exact %", "wilson 95%"] + cols + ["re-ask answered/exact/timeout/of"], data)
    out.write("tab-B-correspondence.tex", "\n".join(t))


# ---------------------------------------------------------------- C

def tab_c(out, prov, oc, conf):
    cs = causes(conf)
    hdr = ["set", "order", "answers", "checked", "valid", "invalid", "cause of the invalid", "platf.-excl.",
           "cyclic", "check t/o", "minimal", "reproduced"]
    t = ["% Table C: validity by the tool's own check.  Generated by eval/paper/figures.py.",
         "\\begin{tabular}{@{}llrrrrp{0.24\\linewidth}rrrrr@{}}", "\\toprule",
         header(hdr, 2), "\\midrule"]
    data = []
    last = None
    for x in oc:
        ent = x["ent"]
        if last is not None and eco_of(x["id"]) != last:
            t.append("\\addlinespace")
        last = eco_of(x["id"])
        title = "%s, %s%s" % (x["eco"], esc(ent["set"]), prov.mark(x["src"]))
        if not x["orders"]:
            prov.miss("C", "%s %s" % (x["id"], ent["set"]), "no run")
            t.append("%s & & \\multicolumn{%d}{l}{\\evmissing} \\\\" % (title, len(hdr) - 2))
            continue
        rs = results(ent["path"])
        for i, m in enumerate(ORDERS):
            ok = [r for r in rs if r["mode"] == m and r["pac"] == "ok"]
            if not ok:
                continue
            v = collections.Counter(r["valid"] for r in ok)
            inv = [unkey(r["query"]) for r in ok if r["valid"] == "INVALID"]
            cause = collections.Counter(cause_of(cs, eco_of(x["id"]), g) for g in inv)
            cz = "; ".join("%s%s" % (esc(c) if c else "\\evnocause{}",
                                     (" (%d)" % k) if k > 1 or len(cause) > 1 else "")
                           for c, k in cause.items())
            if inv and len(inv) <= 3:
                cz = esc(", ".join(inv)) + ": " + cz
            if None in cause:
                prov.miss("C", "%s %s cause" % (x["id"], m),
                          "INVALID with no line in causes.txt: " +
                          ", ".join(g for g in inv if not cause_of(cs, eco_of(x["id"]), g)))
            mi = sum(1 for r in ok if r["valid"] == "VALID" and r.get("minimal") == "yes")
            mi_asked = sum(1 for r in ok if r["valid"] == "VALID" and r.get("minimal") in ("yes", "no"))
            re_ = sum(1 for r in ok if r.get("reproduced") == "yes")
            ra = sum(1 for r in ok if r.get("reproduced") in ("yes", "no"))
            checked = v["VALID"] + v["INVALID"]
            t.append(" & ".join([title if i == 0 else "", ORDER_NAME[m],
                                 cnt(len(ok)), cnt(checked), cnt(v["VALID"]),
                                 cnt(v["INVALID"]) if v["INVALID"] else "\\evzero", cz or "",
                                 cnt(v["PLATFORM"]) if v["PLATFORM"] else "\\evzero",
                                 cnt(v["CYCLIC"]) if v["CYCLIC"] else "\\evzero",
                                 cnt(v["ERR"]) if v["ERR"] else "\\evzero",
                                 "%s/%s" % (cnt(mi), cnt(mi_asked)) if mi_asked else "--",
                                 "%s/%s" % (cnt(re_), cnt(ra)) if ra else "--"]) + " \\\\")
            data.append([x["id"], ent["set"], m, len(ok), checked, v["VALID"], v["INVALID"], " ".join(inv),
                         v["PLATFORM"], v["CYCLIC"], v["ERR"], mi, mi_asked, re_, ra])
    t += ["\\bottomrule", "\\end{tabular}", ""]
    out.tsv("tab-C-validity.tsv", ["id", "set", "order", "answers", "checked", "VALID", "INVALID", "invalid queries",
                                   "PLATFORM", "CYCLIC", "ERR", "minimal", "minimal asked", "reproduced",
                                   "reproduced asked"], data)
    out.write("tab-C-validity.tex", "\n".join(t))


FUZZ_ROWS = [("debian-reg", "Debian, amd64"), ("debian", "Debian, amd64"), ("debian-ma", "Debian, amd64+i386"),
             ("alpine-reg", "Alpine"), ("alpine", "Alpine"), ("opam-reg", "opam"), ("opam", "opam"),
             ("cargo-reg", "Cargo"), ("cargo", "Cargo"), ("npm-reg", "npm, npm reading"), ("npm", "npm, npm reading")]


def rechecks(path):
    """the 3600 s re-checks of a fuzz run's ERR lines, by (query, seed),
    from the recheck-<run>-* runs beside it"""
    d, name = os.path.split(path.rstrip("/"))
    got = {}
    for p in sorted(glob.glob(os.path.join(d, "recheck-%s-*" % name))):
        if p.endswith(".portclash") or not os.path.isdir(p):
            continue
        for r in results(p):
            if r.get("valid") in ("VALID", "INVALID", "PLATFORM"):
                got[r["query"], r["mode"]] = r["valid"]
    return got


def tab_fuzz(out, prov, conf):
    cs = causes(conf)
    hdr = ["set", "queries $\\times$ seeds", "answers", "distinct per query (median / max)", "valid / checked",
           "invalid (queries)", "platf.-excl.", "check t/o (at 3600\\,s)", "valid-invalid split",
           "sat-unsat split", "pac t/o"]
    t = ["% Table C, fuzz: validity under random decision orders.  Generated by eval/paper/figures.py.",
         "\\begin{tabular}{@{}l" + "r" * (len(hdr) - 1) + "@{}}", "\\toprule",
         header(hdr, 1), "\\midrule"]
    data = []
    notes = []
    for fid, eco in FUZZ_ROWS:
        ent = conf.fuzz.get(fid) or {"path": None, "set": "?", "note": "", "flags": []}
        title = "%s, %s" % (eco, esc(ent["set"]))
        if not have(ent):
            prov.miss("C-fuzz", "%s %s" % (fid, ent["set"]), ent["note"] or "no run")
            t.append("%s & \\multicolumn{%d}{l}{\\evmissing} \\\\" % (title, len(hdr) - 1))
            continue
        src = run_source(prov, ent, "fuzz " + fid)
        rs = results(ent["path"])
        rc = rechecks(ent["path"])
        for r in rs:
            if r["valid"] == "ERR" and (r["query"], r["mode"]) in rc:
                r["valid2"] = rc[r["query"], r["mode"]]
        qs = {r["query"] for r in rs}
        seeds = {r["mode"] for r in rs}
        ok = [r for r in rs if r["pac"] == "ok"]
        v0 = collections.Counter(r["valid"] for r in ok)
        v = collections.Counter(r.get("valid2") or r["valid"] for r in ok)
        an = collections.defaultdict(set)
        for r in ok:
            if r.get("answer", "-") not in ("-", ""):
                an[r["query"]].add(r["answer"])
        per = [len(an.get(g, ())) for g in qs if g in an]
        verd = collections.defaultdict(set)
        for r in ok:
            verd[r["query"]].add(r.get("valid2") or r["valid"])
        vsplit = sum(1 for s in verd.values() if "VALID" in s and "INVALID" in s)
        iq = sorted({unkey(r["query"]) for r in ok if (r.get("valid2") or r["valid"]) == "INVALID"})
        for g in iq:
            if not cause_of(cs, eco_of(fid), g):
                prov.miss("C-fuzz", "%s cause of %s" % (fid, g), "INVALID with no line in causes.txt")
        inv_n = sum(1 for r in ok if (r.get("valid2") or r["valid"]) == "INVALID")
        err_s = cnt(v0["ERR"]) if v0["ERR"] else "\\evzero"
        if v0["ERR"] > v["ERR"]:
            err_s += " (%d still)" % v["ERR"]
        tmo = sum(1 for r in rs if r["pac"] == "timeout")
        split = len(lines(os.path.join(ent["path"], "split.txt")))
        checked = v["VALID"] + v["INVALID"]
        t.append(" & ".join([title + prov.mark(src), "%d $\\times$ %d" % (len(qs), len(seeds)), cnt(len(ok)),
                             "%s / %d" % (("%g" % q(per, .5)) if per else "--", max(per, default=0)),
                             "%s / %s" % (cnt(v["VALID"]), cnt(checked)),
                             "%s (%d)" % (cnt(inv_n), len(iq)) if inv_n else "\\evzero",
                             cnt(v["PLATFORM"]) if v["PLATFORM"] else "\\evzero", err_s,
                             str(vsplit) if vsplit else "\\evzero", str(split) if split else "\\evzero",
                             cnt(tmo) if tmo else "\\evzero"]) + " \\\\")
        if iq:
            notes.append("%s: %s" % (title, "; ".join("%s (%s)" % (esc(g), esc(cause_of(cs, eco_of(fid), g) or "")
                                                                    or "\\evnocause{}") for g in iq)))
        data.append([fid, ent["set"], len(qs), len(seeds), len(ok), sum(per), q(per, .5) if per else "",
                     max(per, default=0), v["VALID"], checked, inv_n, len(iq), " ".join(iq), v["PLATFORM"], v0["ERR"],
                     v["ERR"], vsplit, split, tmo])
    t += ["\\bottomrule", "\\end{tabular}", ""]
    out.write("tab-C-fuzz-notes.tex", "%% the invalid answers of Table C, fuzz\n" +
              ("Invalid answers: %s.\n" % ". ".join(notes) if notes else "No invalid answers.\n"))
    out.tsv("tab-C-fuzz.tsv", ["id", "set", "queries", "seeds", "answers", "distinct answers", "distinct median",
                               "distinct max", "VALID", "checked", "INVALID", "INVALID queries", "which",
                               "PLATFORM", "ERR", "ERR after recheck", "valid-invalid split", "sat-unsat split",
                               "pac timeouts"], data)
    out.write("tab-C-fuzz.tex", "\n".join(t))


# ---------------------------------------------------------------- D

def tab_d(out, prov, conf):
    hdr = ["set", "reading", "order", "queries", "answers", "npm-valid", "platf.-excl.", "Berry-valid",
           "exact vs npm's lock", "layout-exact", "Berry's own exact", "timeouts (at 3600\\,s)"]
    t = ["% Table D: npm's three readings on one query set.  Generated by eval/paper/figures.py.",
         "\\begin{tabular}{@{}lll" + "r" * (len(hdr) - 3) + "@{}}", "\\toprule",
         header(hdr, 3), "\\midrule"]
    data = []
    for si, (st, trio) in enumerate((("names", ("npm", "npm-shared", "npm-placement")),
                                     ("targeted", ("npm-tgt", "npm-shared-tgt", "npm-placement-tgt")))):
        if si:
            t.append("\\addlinespace")
        for ri, rid in enumerate(trio):
            rd = reading(rid)
            ent = conf.runs.get(rid) or {"path": None, "set": st, "flags": [], "note": ""}
            if not have(ent):
                prov.miss("D", "%s %s" % (rid, st), "no run")
                t.append("%s & %s & & \\multicolumn{%d}{l}{\\evmissing} \\\\" % (st if ri == 0 else "", rd,
                                                                                 len(hdr) - 3))
                continue
            src = run_source(prov, ent, "run " + rid)
            rs = results(ent["path"])
            b, o = berry(ent["path"]) if rd == "shared" else ({}, {})
            if rd == "shared" and not b:
                prov.miss("D", "%s Berry" % rid, "no berry.txt (berryall.sh not run)")
            for mi, m in enumerate(ORDERS):
                mr = [r for r in rs if r["mode"] == m]
                ok = [r for r in mr if r["pac"] == "ok"]
                v = collections.Counter(r["valid"] for r in ok)
                ans = sum(1 for r in mr if r["tool"] == "ok" and r["corr"] != "ERR")
                if rd == "placement":
                    rel = sum(1 for r in mr if r["tool"] == "ok" and cmpf(r, "relation") == "exact")
                    lay = sum(1 for r in mr if r["tool"] == "ok" and r["corr"] == "exact")
                else:
                    rel = sum(1 for r in mr if r["tool"] == "ok" and r["corr"] == "exact")
                    lay = None
                bv = [b.get((r["query"], m)) for r in ok if (r["query"], m) in b]
                bo = [o.get((r["query"], m)) for r in ok if (r["query"], m) in o]
                tmo = sum(1 for r in mr if r["pac"] == "timeout")
                ra = reask(ent["path"], m)
                still = sum(1 for r in ra.values() if r["pac"] == "timeout")
                bvs = "%s/%s" % (cnt(bv.count("VALID")), cnt(sum(1 for x in bv if x in ("VALID", "INVALID")))) \
                    if bv else ("\\evmissing" if rd == "shared" else "--")
                cells = [st if ri == 0 and mi == 0 else "", (rd + prov.mark(src)) if mi == 0 else "", ORDER_NAME[m],
                         cnt(len(mr)), cnt(len(ok)), "%s/%s" % (cnt(v["VALID"]), cnt(v["VALID"] + v["INVALID"])),
                         cnt(v["PLATFORM"]) if v["PLATFORM"] else "\\evzero", bvs,
                         "%s/%s" % (cnt(rel), cnt(ans)) + (" (relation)" if rd == "placement" else ""),
                         "%s/%s" % (cnt(lay), cnt(ans)) if lay is not None else "--",
                         "%s/%s" % (cnt(bo.count("yes")), cnt(len(bo))) if bo else "--",
                         ("%d (%d still)" % (tmo, still) if ra else str(tmo)) if tmo else "\\evzero"]
                t.append(" & ".join(cells) + " \\\\")
                data.append([st, rd, m, len(mr), len(ok), v["VALID"], v["VALID"] + v["INVALID"], v["PLATFORM"],
                             bv.count("VALID"), sum(1 for x in bv if x in ("VALID", "INVALID")), rel, ans,
                             "" if lay is None else lay, bo.count("yes"), len(bo), tmo, still if ra else ""])
    t += ["\\bottomrule", "\\end{tabular}", ""]
    out.tsv("tab-D-npm.tsv", ["set", "reading", "order", "queries", "answers", "npm VALID", "npm checked",
                              "PLATFORM", "Berry VALID", "Berry checked", "exact vs npm (relation for placement)",
                              "tool answered", "layout exact", "Berry own exact", "Berry own asked", "timeouts",
                              "still at 3600 s"], data)
    out.write("tab-D-npm.tex", "\n".join(t))


# ---------------------------------------------------------------- timing

# comparison id, label, bench id, step, reference, scale run for laziness,
# index totals key
COMPS = [("debian", "Debian, amd64 / apt", "amd64", "debian", "apt", "debian", "debian"),
         ("debian-ma", "Debian, amd64+i386 / apt", "debian-ma", "debian-ma", "apt", "debian-ma-sample", "debian-ma"),
         ("alpine", "Alpine / apk", "amd64", "alpine", "apk", "alpine", "alpine"),
         ("opam", "opam / 0install", "amd64", "opam", "opam", "opam", "opam"),
         ("opam-mccs", "opam / mccs", "amd64", "opam", "opam-mccs", "opam", "opam"),
         ("cargo", "Cargo / cargo", "amd64", "cargo", "cargo", "cargo", "cargo"),
         ("npm", "npm reading / npm", "amd64", "npm", "npm", "npm", "npm"),
         ("npm-shared", "shared reading / npm", "amd64", "npm-shared", "npm", "npm-shared", "npm"),
         ("npm-placement", "placement reading / npm", "amd64", "npm-placement", "npm", "npm-placement", "npm")]
MODES = [("warm", "", "warm"), ("cold", "-cold", "cold start"), ("first", "-first", "first run")]


class Bench:
    """a bench.sh RUN's rows, per step, set, query and variant"""
    def __init__(self, path):
        self.path = path
        self.rows = summary.load(path) if path and os.path.isdir(os.path.join(path, "res")) else []
        cells = collections.defaultdict(list)
        for r in self.rows:
            if r["rep"] != "0":
                cells[r["step"], r["set"], r["query"], r["variant"]].append(r)
        self.cells = {k: summary.Cell(v) for k, v in cells.items()}
        self.queries = collections.defaultdict(list)
        for r in self.rows:
            k = (r["step"], r["set"])
            if r["query"] not in self.queries[k]:
                self.queries[k].append(r["query"])

    def has(self, step, st):
        return bool(self.queries.get((step, st)))

    def pairs(self, step, st, v, ref):
        """per query: (query, pac cell, reference cell), both measured"""
        out = []
        for g in self.queries.get((step, st), []):
            c, t = self.cells.get((step, st, g, v)), self.cells.get((step, st, g, ref))
            if c and t:
                out.append((g, c, t))
        return out

    def gm(self, step, st, v, ref):
        """summary.py's geometric mean and bootstrap interval, seeded as it
        seeds them, so the numbers are Table P's"""
        ps = self.pairs(step, st, v, ref)
        if not ps:
            return None
        tool = summary.TOOL[step.split("-")[0]]
        seed = f"{step}:{st}:{v}" + ("" if ref == tool else f":{ref}")
        g = summary.boot([c.med / t.med for _, c, t in ps], seed)
        return g + (sum(1 for _, c, t in ps if c.med < t.med), len(ps))


def timing(conf, prov, st):
    benches = {k: Bench(e["path"]) for k, e in conf.bench.items()}
    res = []
    for cid, label, bid, step, ref, lrun, tkey in COMPS:
        ent = conf.bench.get(bid)
        b = benches.get(bid)
        cell = {"id": cid, "label": label, "run": lrun, "totals": tkey, "modes": {}, "src": {}}
        for mk, suf, mname in MODES:
            s = step + suf
            if b is None or not b.has(s, st):
                if b is None or not b.rows:
                    why = "no bench run: " + (ent["note"] if ent else "no bench line")
                else:
                    why = "no %s rows for set %s" % (s, st)
                prov.miss("E/G", "%s %s (%s)" % (label, mname, st), why)
                continue
            cell["src"][mk] = bench_source(prov, ent, s)
            for o in ORDERS:
                g = b.gm(s, st, "pac-" + o, ref)
                if g and g[0] is not None:
                    ps = b.pairs(s, st, "pac-" + o, ref)
                    cell["modes"][mk, o] = {
                        "gm": g[0], "lo": g[1], "hi": g[2], "faster": g[3], "n": g[4],
                        "parse": q([c.parse for _, c, _ in ps], .5), "solve": q([c.solve for _, c, _ in ps], .5),
                        "wall": q([c.med for _, c, _ in ps], .5), "tool": q([t.med for _, _, t in ps], .5),
                        "pts": [(g_, c.med, t.med) for g_, c, t in ps]}
        # the outlier block, for the scatter
        if b is not None and b.has(step, "outliers"):
            for o in ORDERS:
                cell["modes"]["outliers", o] = {"pts": [(g_, c.med, t.med) for g_, c, t in
                                                        b.pairs(step, "outliers", "pac-" + o, ref)]}
            cell["src"]["outliers"] = bench_source(prov, ent, step)
        res.append(cell)
    return res


MODE_STYLE = {"warm": ("evwarm", "*", 0.24), "cold": ("evcold", "square*", 0.0), "first": ("evfirst", "triangle*", -0.24)}


def fig_e(out, prov, tm, suffix, st):
    n = len(tm)
    lo = min([m["lo"] for c in tm for k, m in c["modes"].items() if "lo" in m] + [0.5])
    hi = max([m["hi"] for c in tm for k, m in c["modes"].items() if "hi" in m] + [2])
    xmin, xmax = lo / 1.6, hi * 4
    ticks = [x for x in (0.001, 0.003, 0.01, 0.03, 0.1, 0.3, 1, 3, 10, 30, 100, 300) if xmin <= x <= xmax]
    t = ["% Figure E: pac's time over the tool's, geometric mean over the " + esc(st) + " set with its 95% bootstrap",
         "% interval, warm, cold start and first run; tool order filled, PubGrub order hollow.",
         "% Generated by eval/paper/figures.py.",
         "\\begin{tikzpicture}",
         "\\begin{axis}[evdots, scale only axis, width=\\linewidth-120pt, height=%dpt, xmode=log, xmin=%g, xmax=%g, ymin=0.4, ymax=%.1f," %
         (n * 20, xmin, xmax, n + 0.6),
         "  xtick={%s}, xticklabels={%s}, xlabel={pac $\\div$ tool, wall time (log scale)}," % (
             ",".join("%g" % x for x in ticks), ",".join("%g$\\times$" % x for x in ticks)),
         "  ytick={%s}, yticklabels={%s}]" % (
             ",".join(str(n - i) for i in range(n)),
             ",".join("{%s%s}" % (esc(c["label"]), "".join(prov.mark(s) for s in dict.fromkeys(c["src"].values())))
                      for c in tm)),
         "\\draw[evink2, dashed] (axis cs:1,0.4) -- (axis cs:1,%.1f);" % (n + 0.6)]
    for mk, _, mname in MODES:
        col, mark, _ = MODE_STYLE[mk]
        t.append("\\addlegendimage{only marks, mark=%s, color=%s, mark size=2pt}\\addlegendentry{%s}" % (mark, col, mname))
    t.append("\\addlegendimage{only marks, mark=*, color=evink2, mark size=2pt}\\addlegendentry{tool order}")
    t.append("\\addlegendimage{only marks, mark=*, color=evink2, fill=white, mark size=2pt}\\addlegendentry{PubGrub order}")
    data = []
    for i, c in enumerate(tm):
        y = n - i
        absent = []
        for mk, _, mname in MODES:
            col, mark, dy = MODE_STYLE[mk]
            if not any((mk, o) in c["modes"] for o in ORDERS):
                absent.append(mname)
                continue
            for o, oy in (("tool", 0.05), ("pubgrub", -0.05)):
                m = c["modes"].get((mk, o))
                if not m:
                    continue
                yy = y + dy + oy
                t.append("\\draw[%s, line width=0.6pt] (axis cs:%.5g,%.3f) -- (axis cs:%.5g,%.3f);" % (
                    col, m["lo"], yy, m["hi"], yy))
                t.append("\\addplot[only marks, mark=%s, color=%s, mark size=1.8pt%s, forget plot] "
                         "coordinates {(%.5g,%.3f)};" % (mark, col, ", fill=white" if o == "pubgrub" else "", m["gm"], yy))
                data.append([c["id"], mname, o, "%.4f" % m["gm"], "%.4f" % m["lo"], "%.4f" % m["hi"],
                             "%d/%d" % (m["faster"], m["n"])])
        if absent:
            txt = "\\evmissing" if len(absent) == 3 else "%s: \\evmissing" % ", ".join(absent)
            t.append("\\node[anchor=east, font=\\tiny, inner sep=1pt] at (axis cs:%g,%.2f) {%s};" % (
                xmax, y, txt))
    t += ["\\end{axis}", "\\end{tikzpicture}", ""]
    out.tsv("fig-E-timing%s.tsv" % suffix, ["comparison", "mode", "order", "gm", "ci lo", "ci hi", "pac faster"], data)
    out.write("fig-E-timing%s.tex" % suffix, "\n".join(t))


def outlying(pts, names):
    """the points to label: the outlier block's, and the three whose ratio
    lies furthest from the median ratio, if more than 3x from it"""
    lr = [math.log10(p / tl) for _, p, tl in pts if p > 0 and tl > 0]
    lab = [x for x in pts if x[0] in names]
    if lr:
        md = q(lr, .5)
        far = [x for x in pts if x[0] not in names and abs(math.log10(x[1] / x[2]) - md) > math.log10(3)]
        far.sort(key=lambda x: -abs(math.log10(x[1] / x[2]) - md))
        lab += far[:3]
    return lab


def fig_f(out, prov, tm, suffix, st):
    t = ["% Figure F: per query, the tool's median wall time against pac's (" + esc(st) + " set, warm; the",
         "% outlier block too), log-log, with y = x.  Generated by eval/paper/figures.py.",
         "\\begin{tikzpicture}",
         "\\begin{groupplot}[evscatter, group style={group size=3 by %d, horizontal sep=34pt, vertical sep=40pt},"
         % math.ceil(len(tm) / 3),
         "  scale only axis, width=0.25\\linewidth, height=0.25\\linewidth]"]
    data = []
    legend = False
    for i, c in enumerate(tm):
        pts = {o: c["modes"].get(("warm", o), {}).get("pts", []) for o in ORDERS}
        opts = {o: c["modes"].get(("outliers", o), {}).get("pts", []) for o in ORDERS}
        allp = [p for o in ORDERS for p in pts[o] + opts[o]]
        srcs = "".join(prov.mark(s) for s in dict.fromkeys(v for k, v in c["src"].items() if k in ("warm", "outliers")))
        title = "title={%s%s}" % (esc(c["label"]), srcs)
        xl = "xlabel={tool (s)}," if i >= len(tm) - 3 else ""
        yl = "ylabel={pac (s)}," if i % 3 == 0 else ""
        if not allp:
            t.append("\\nextgroupplot[%s, %s %s xmin=0.01, xmax=10, ymin=0.01, ymax=10]" % (title, xl, yl))
            t.append("\\node[font=\\scriptsize] at (rel axis cs:0.5,0.5) {\\evmissing};")
            continue
        vals = [v for _, a, b in allp for v in (a, b) if v > 0]
        lo, hi = 10 ** math.floor(math.log10(min(vals))), 10 ** math.ceil(math.log10(max(vals)))
        leg = "" if legend else "legend to name=evF%s, legend columns=3, " % suffix.strip("-")
        t.append("\\nextgroupplot[%s, %s %s %sxmin=%g, xmax=%g, ymin=%g, ymax=%g]" % (title, xl, yl, leg, lo, hi,
                                                                                     lo, hi))
        t.append("\\addplot[evink2, dashed, domain=%g:%g, samples=2, forget plot] {x};" % (lo, hi))
        for o in ORDERS:
            both = pts[o] + opts[o]
            if not legend:
                legend = True
                t.append("\\addlegendimage{only marks, mark=*, mark size=1.6pt, color=evwarm}\\addlegendentry{tool order}")
                t.append("\\addlegendimage{only marks, mark=*, mark size=1.6pt, color=evwarm, fill=white}"
                         "\\addlegendentry{PubGrub order}")
                t.append("\\addlegendimage{evink2, dashed}\\addlegendentry{$y = x$}")
            if both:
                t.append("\\addplot[only marks, mark=*, mark size=1.1pt, color=evwarm%s, forget plot] "
                         "coordinates {%s};" % (", fill=white" if o == "pubgrub" else "",
                                                " ".join("(%.5g,%.5g)" % (tl, p) for _, p, tl in both)))
            for g, p, tl in both:
                data.append([c["id"], o, g, "%.5f" % tl, "%.5f" % p, "outlier block" if (g, p, tl) in opts[o] else st])
        names = {g for o in ORDERS for g, _, _ in opts[o]}
        seen, placed = set(), []
        for o in ORDERS:
            for g, p, tl in outlying(pts[o] + opts[o], names):
                # one label per query, and none on top of another
                if g in seen or any(abs(math.log10(tl / a)) < 0.3 and abs(math.log10(p / b)) < 0.12
                                    for a, b in placed):
                    continue
                seen.add(g)
                placed.append((tl, p))
                # beside the point, on the side of the panel with room
                right = math.log10(tl / lo) < 0.55 * math.log10(hi / lo)
                t.append("\\node[font=\\tiny, anchor=%s, inner sep=1.5pt, text=evink] at (axis cs:%.5g,%.5g) {%s};" % (
                    "west" if right else "east", tl, p, esc(g)))
    t += ["\\end{groupplot}",
          "\\node[anchor=south] at ($(group c2r1.north)+(0,14pt)$) {\\pgfplotslegendfromname{evF%s}};" % suffix.strip("-"),
          "\\end{tikzpicture}", ""]
    out.tsv("fig-F-scatter%s.tsv" % suffix, ["comparison", "order", "query", "tool s", "pac s", "set"], data)
    out.write("fig-F-scatter%s.tex" % suffix, "\n".join(t))


def tab_g(out, prov, conf, tm, suffix, st):
    tot = {}
    for l in lines(conf.totals) if conf.totals else []:
        k, *v = l.split()
        tot[k] = [int(x) for x in v]
    hdr = ["comparison", "order", "pac parse", "pac solve", "pac wall", "tool wall", "pac $\\div$ tool (95\\% CI)",
           "pac faster", "cold start", "first run", "names loaded / index"]
    t = ["% Table G: time (median seconds over the " + esc(st) + " set, warm) and laziness (median over the",
         "% scale run's answers).  Generated by eval/paper/figures.py.",
         "\\begin{tabular}{@{}ll" + "r" * (len(hdr) - 2) + "@{}}", "\\toprule",
         header(hdr, 2), "\\midrule"]
    data = []
    for c in tm:
        label, lrun, tkey = c["label"], c["run"], c["totals"]
        ent = conf.runs.get(lrun)
        lz_src = run_source(prov, ent, "run " + lrun) if have(ent) else None
        # the names of a run's own Packages, an index index-totals.txt does
        # not list
        if tkey not in tot and have(ent) and os.path.exists(os.path.join(ent["path"], "Packages")):
            tot[tkey] = [len({f["Package"] for f in stanzas(os.path.join(ent["path"], "Packages"))})]
        lrows = results(ent["path"]) if have(ent) else []
        for i, o in enumerate(ORDERS):
            w = c["modes"].get(("warm", o))
            first = (esc(label) + "".join(prov.mark(s) for s in dict.fromkeys(c["src"].values()))) if i == 0 else ""
            if w:
                cells = ["%.3f" % w["parse"] if w["parse"] is not None else "--",
                         "%.3f" % w["solve"] if w["solve"] is not None else "--",
                         "%.3f" % w["wall"], "%.3f" % w["tool"],
                         "%.2f$\\times$ (%.2f--%.2f)" % (w["gm"], w["lo"], w["hi"]), "%d/%d" % (w["faster"], w["n"])]
            else:
                cells = ["\\evmissing"] + [""] * 5
            for mk in ("cold", "first"):
                m = c["modes"].get((mk, o))
                cells.append("%.2f$\\times$" % m["gm"] if m else ("\\evmissing" if w else ""))
            ns = [num(r.get("names")) for r in lrows if r["mode"] == o and r["pac"] == "ok"]
            ns = [x for x in ns if x is not None]
            tn = tot.get(tkey, [None])[0]
            if ns and tn:
                med = q(ns, .5)
                cells.append("%s / %s (%s\\,\\%%)%s" % (cnt(int(med)), cnt(tn), ("%.3g" % (100 * med / tn)),
                                                       prov.mark(lz_src)))
            else:
                cells.append(prov.miss("G", "%s names loaded (%s)" % (label, o), "no scale run or index total"))
            t.append(" & ".join([first, ORDER_NAME[o]] + cells) + " \\\\")
            data.append([c["id"], o] + ([w["parse"], w["solve"], w["wall"], w["tool"], w["gm"], w["lo"], w["hi"],
                                         w["faster"], w["n"]] if w else [""] * 9) +
                        [c["modes"].get((mk, o), {}).get("gm", "") for mk in ("cold", "first")] +
                        [q(ns, .5) if ns else "", tn or ""])
    t += ["\\bottomrule", "\\end{tabular}", ""]
    out.tsv("tab-G-time%s.tsv" % suffix, ["comparison", "order", "parse", "solve", "pac wall", "tool wall", "gm",
                                          "ci lo", "ci hi", "faster", "n", "cold gm", "first gm",
                                          "names loaded median", "index names"], data)
    out.write("tab-G-time%s.tex" % suffix, "\n".join(t))


# ---------------------------------------------------------------- provenance, preamble, previews

PREAMBLE = r"""% What eval/paper/figures.py's figures and tables need in the preamble.
\usepackage{booktabs}
\usepackage{xcolor}
\usepackage{pgfplots}
\pgfplotsset{compat=1.18}
\usepgfplotslibrary{groupplots}
\usetikzlibrary{patterns, calc}
% categorical roles, validated for adjacency and colour-vision deficiency;
% the two greys and the light blue are deliberately recessive
\definecolor{evexact}{HTML}{184F95}
\definecolor{evrel}{HTML}{3987E5}
\definecolor{evgap}{HTML}{86B6EF}
\definecolor{evrefuse}{HTML}{8A8883}
\definecolor{evinvalid}{HTML}{E34948}
\definecolor{evplatform}{HTML}{EDA100}
\definecolor{evtimeout}{HTML}{4A3AA7}
\definecolor{evother}{HTML}{D6D4CF}
\definecolor{evwarm}{HTML}{2A78D6}
\definecolor{evcold}{HTML}{EB6834}
\definecolor{evfirst}{HTML}{1BAF7A}
\definecolor{evink}{HTML}{0B0B0B}
\definecolor{evink2}{HTML}{6B6A66}
\definecolor{evmiss}{HTML}{D0021B}
% a cell with no data yet; a zero; a source (red: its binary is not the current one)
\newcommand{\evmissing}{\textcolor{evmiss}{\textbf{missing}}}
\newcommand{\evnocause}{\textcolor{evmiss}{\textbf{cause not recorded}}}
\newcommand{\evzero}{\textcolor{evink2}{0}}
\newcommand{\evsrc}[1]{\textsuperscript{\textcolor{evink2}{\sffamily #1}}}
\newcommand{\evstale}[1]{\textsuperscript{\textcolor{evmiss}{\sffamily #1\textdagger}}}
\newcommand{\evprov}{\textsuperscript{\textcolor{evmiss}{\S}}}
\pgfplotsset{
  evbase/.style={axis line style={evink2}, tick style={evink2}, tick label style={font=\footnotesize},
    label style={font=\footnotesize}, legend style={font=\scriptsize, draw=none, fill=none},
    legend cell align=left},
  evbars/.style={evbase, bar width=7pt, axis y line*=left, axis x line*=bottom, ytick style={draw=none},
    xmajorgrids, grid style={evink2!25}, enlarge y limits=false, clip=false,
    legend style={at={(0.5,1.01)}, anchor=south, legend columns=4}, reverse legend=false},
  evdots/.style={evbase, axis y line*=left, axis x line*=bottom, ytick style={draw=none},
    xmajorgrids, grid style={evink2!25}, clip=false,
    legend style={at={(0.5,1.01)}, anchor=south, legend columns=5}},
  evscatter/.style={evbase, xmode=log, ymode=log, title style={font=\footnotesize, yshift=-3pt},
    xmajorgrids, ymajorgrids, grid style={evink2!20}, clip=false,
    tick label style={font=\scriptsize}, label style={font=\scriptsize}},
}
"""


def provenance(out, prov, conf):
    md = ["# Provenance of the evaluation figures and tables", "",
          "Current commit: %s.  A source is stale (red, with a dagger) when its pac binary is not that commit's."
          % conf.current, "",
          "| key | what | run directory | pac sha256 | commit | measured (UTC) | stale | note |",
          "|---|---|---|---|---|---|---|---|"]
    tx = ["% Provenance: the source each superscript names.  Generated by eval/paper/figures.py.",
          "\\begin{tabular}{@{}lp{0.3\\linewidth}lllp{0.33\\linewidth}@{}}", "\\toprule",
          "key & what & pac & commit & measured & run directory \\\\", "\\midrule"]
    for e in prov.ents.values():
        md.append("| %s | %s | %s | %s | %s | %s | %s | %s |" % (
            e["key"], e["what"], e["path"], e["sha"], e["commit"], e["date"], "stale" if e["stale"] else "",
            e["note"]))
        tx.append("%s & %s & \\texttt{%s} & %s & %s & {\\scriptsize\\texttt{%s}} \\\\" % (
            prov.mark(e["key"]), esc(e["what"]), e["sha"], esc(e["commit"]), esc(e["date"]),
            esc(e["path"]).replace("/", "/\\allowbreak{}")))
    tx += ["\\bottomrule", "\\end{tabular}", ""]
    out.write("provenance.md", "\n".join(md) + "\n")
    out.write("provenance.tex", "\n".join(tx))
    mm = ["# Cells printed as missing", "", "| where | what | why |", "|---|---|---|"]
    for w, what, why in prov.missing:
        mm.append("| %s | %s | %s |" % (w, what, why))
    out.write("missing.md", "\n".join(mm) + "\n")


def preview(out, sets, conf):
    doc = [r"\documentclass[9pt]{extarticle}",
           r"\usepackage[paperwidth=8.5in, paperheight=11in, textwidth=505.89pt, textheight=9.25in]{geometry}",
           r"\usepackage[T1]{fontenc}",
           r"\usepackage[tt=false, type1=true]{libertine}",
           r"\usepackage[varqu]{zi4}",
           r"\usepackage[libertine]{newtxmath}",
           r"\usepackage{graphicx}",
           r"\input{preamble.tex}",
           r"\usepackage{caption}",
           r"\captionsetup{font=small, labelformat=empty}",
           r"\setlength{\parindent}{0pt}",
           r"\begin{document}",
           r"\section*{Evaluation figures and tables (provisional)}",
           "Generated by \\texttt{eval/paper/figures.py}; current commit %s.  Superscripts name a source in the "
           "provenance table at the end; a red one with a dagger is stale, from another binary.  "
           "\\evmissing{} marks data not yet measured.  \\evprov{} marks an order whose correspondence is "
           "provisional." % esc(conf.current), ""]

    def fig(name, cap, wide=True):
        doc.extend([r"\begin{figure}[!ht]", r"\centering",
                    r"\begin{minipage}{%s}" % (r"\textwidth" if wide else "241.02pt"),
                    r"\input{%s.tex}" % name, r"\end{minipage}",
                    r"\caption{%s: %s}" % (name, cap), r"\end{figure}", r"\clearpage"])

    def tab(name, cap, size=r"\footnotesize", after=""):
        doc.extend([r"\begin{table}[!ht]", r"\centering", r"\caption{%s: %s}" % (name, cap), size,
                    r"\setlength{\tabcolsep}{3pt}", r"\resizebox{\ifdim\width>\textwidth\textwidth\else\width\fi}{!}{%",
                    r"\input{%s.tex}}" % name, after, r"\end{table}", r"\clearpage"])
    fig("fig-A-outcomes", "Correspondence and validity: every query of each set, by outcome, tool order above "
        "PubGrub order.  The npm and placement readings are judged against npm, the shared reading against "
        "Berry (its check, then its own answer); the placement reading's exact splits into layout-exact and "
        "exact by relation only; \\evprov{} marks an order whose correspondence is provisional.  Both refuse includes pac refusing the query itself where the tool refuses it too.  "
        "At the right, exact as a share of the set, and the classes too small to see.")
    tab("tab-B-correspondence", "Correspondence per set and order.  Exact \\% is of the queries the tool answered "
        "(Wilson 95\\% interval); the class columns are triage\\_lib's and sum to the queries.  The shared reading "
        "is shown judged by npm, then against Berry's own answer.  Re-ask: pac's 900\\,s timeouts asked again at "
        "3600\\,s, answered / exact / still timing out.")
    tab("tab-C-validity", "Validity by each tool's own check, per set and order.  Minimal and reproduced are "
        "reported beside validity and not counted in it.")
    tab("tab-C-fuzz", "Validity under random decision orders (seeds as \\texttt{--order=random --seed N}).  "
        "Valid-invalid split: queries valid under one seed and invalid under another; sat-unsat split: "
        "split.txt, queries answered under one seed and refused under another.  A check that timed out was "
        "checked again at 3600\\,s where a recheck run exists.",
        after=r"\par\medskip\begin{minipage}{\textwidth}\input{tab-C-fuzz-notes.tex}\end{minipage}")
    tab("tab-D-npm", "npm's three readings on one query set.  Exact against npm's own lock: by relation "
        "(nodes and edges) for the npm and shared readings and for placement, and layout path for path for "
        "placement.  Berry-valid and Berry's own answer for the shared reading only.")
    for st, suf in sets:
        fig("fig-E-timing" + suf, "pac's wall time over the tool's, geometric mean over the %s set's queries, with "
            "its 95\\%% bootstrap interval; tool order filled, PubGrub order hollow." % esc(st))
        fig("fig-F-scatter" + suf, "Per query, the tool's median wall time against pac's, %s set and the outlier "
            "block, warm; the dashed line is $y = x$, points below it pac is faster." % esc(st))
        tab("tab-G-time" + suf, "Time: medians over the %s set's queries, warm, in seconds, and pac $\\div$ tool "
            "as in Figure E; cold start and first run their geometric means.  Laziness: the median of the names "
            "pac loads over the scale run's answers, against the index's names (packuments for npm)." % esc(st))
    doc += [r"\begin{table}[p]", r"\centering", r"\caption{Provenance}", r"\footnotesize",
            r"\input{provenance.tex}", r"\end{table}", r"\end{document}", ""]
    out.write("eval-figures.tex", "\n".join(doc))
    for name in ["fig-A-outcomes"] + ["fig-E-timing" + s for _, s in sets] + ["fig-F-scatter" + s for _, s in sets]:
        out.write("standalone-%s.tex" % name, "\n".join([
            r"\documentclass[9pt, border=2pt]{standalone}",
            r"\usepackage[T1]{fontenc}", r"\usepackage[tt=false, type1=true]{libertine}",
            r"\usepackage[varqu]{zi4}", r"\usepackage[libertine]{newtxmath}", r"\input{preamble.tex}",
            r"\begin{document}", r"\begin{minipage}{505.89pt}", r"\input{%s.tex}" % name, r"\end{minipage}",
            r"\end{document}", ""]))


def pdf(d, sets):
    if not shutil.which("pdflatex"):
        print("no pdflatex on PATH: no PDFs", file=sys.stderr)
        return
    names = ["eval-figures"] + ["standalone-" + n for n in
                                ["fig-A-outcomes"] + ["fig-E-timing" + s for _, s in sets] +
                                ["fig-F-scatter" + s for _, s in sets]]
    for n in names:
        for _ in range(2 if n == "eval-figures" else 1):
            p = subprocess.run(["pdflatex", "-interaction=nonstopmode", "-halt-on-error", n + ".tex"], cwd=d,
                               stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        if p.returncode:
            sys.stderr.write(p.stdout.decode(errors="replace")[-3000:])
            raise SystemExit("pdflatex failed on %s.tex" % n)
        if n.startswith("standalone-"):
            os.replace(os.path.join(d, n + ".pdf"), os.path.join(d, n[len("standalone-"):] + ".pdf"))
    for f in glob.glob(os.path.join(d, "*.aux")) + glob.glob(os.path.join(d, "*.log")):
        os.remove(f)


def main():
    args = [a for a in sys.argv[1:] if a != "--pdf"]
    if len(args) < 2:
        raise SystemExit(__doc__)
    conf = Conf(args[:-1])
    # a set not yet measured has a row with path -; a set with no row at
    # all is a conf read alone that should have been read over another
    lack = [k for k, v in (("current", conf.current), ("totals", conf.totals), ("causes", conf.causes)) if not v]
    lack += ["%s %s" % (k, i) for k, have_, ids in (("run", conf.runs, [r for r, _ in ROWS_BC]),
                                                    ("fuzz", conf.fuzz, [f for f, _ in FUZZ_ROWS]),
                                                    ("bench", conf.bench, sorted({c[2] for c in COMPS})))
             for i in ids if i not in have_]
    if lack:
        raise SystemExit("figures.py: no conf line for %s (is sources.conf first?)" % ", ".join(lack))
    out = Out(args[-1])
    prov = Prov(conf)
    oc = outcome_counts(conf, prov)
    fig_a(out, prov, oc)
    tab_b(out, prov, oc, conf)
    tab_c(out, prov, oc, conf)
    tab_fuzz(out, prov, conf)
    tab_d(out, prov, conf)
    bsets = next((e["set"].split() for e in conf.bench.values() if e["set"]), ["strat"])
    sets = [(st, "" if i == 0 else "-" + st) for i, st in enumerate(bsets)]
    for st, suf in sets:
        tm = timing(conf, prov, st)
        fig_e(out, prov, tm, suf, st)
        fig_f(out, prov, tm, suf, st)
        tab_g(out, prov, conf, tm, suf, st)
    out.write("preamble.tex", PREAMBLE)
    provenance(out, prov, conf)
    preview(out, sets, conf)
    if "--pdf" in sys.argv:
        pdf(out.d, sets)
    print("%d sources, %d of them stale; %d missing cells (missing.md)" % (
        len(prov.ents), sum(1 for e in prov.ents.values() if e["stale"]), len(prov.missing)))


if __name__ == "__main__":
    main()
