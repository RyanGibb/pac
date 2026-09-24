#!/usr/bin/env python3
"""scale.sh's queries and its per-query worker.

  scale.py sample SEED N          N index files drawn uniformly, as crate
                                  names; one with no release left unyanked
                                  is dropped, since there is no root to ask
  scale.py targets SEED K [EXCL]  K crates per pool, as pool<TAB>crate, each
                                  pool exercising one modelling decision in
                                  the crate's newest release
  scale.py one CRATE PREFIX       the query's result line; run_query.py's and
                                  verify.py's files at PREFIX.*
"""
import contextlib, functools, json, multiprocessing, operator, os, random, re
import shutil, subprocess, sys, types

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
INDEX = os.path.normpath(HERE + "/../../repos/crates.io-index")
TOOLCHAIN = "1.97.1"


def num(s):
    # more than 9 digits saturates, as in Cargo_version
    x = int(re.match(r"[0-9]*", s).group() or 0)
    return x if x < 10 ** 9 else (1 << 62) - 1


@functools.lru_cache(maxsize=1 << 20)
def vkey(v):
    core, _, pre = v.split("+")[0].partition("-")
    m, n, p = ([num(x) for x in core.split(".")] + [0, 0])[:3]
    ids = tuple((0, int(i), b"") if re.fullmatch(r"[0-9]+", i) else (1, 0, i.encode())
                for i in pre.split(".")) if pre else ()
    return m, n, p, not pre, ids


def compat_class(v):
    m, n, p = vkey(v)[:3]
    return f"{m}.0.0" if m else f"0.{n}.0" if n else f"0.0.{p}"


def bounds(req):
    """Cargo_version's reading of a requirement, as (op, version) pairs."""
    out = []
    for c in req.split(","):
        op, spec = re.match(r"\s*(>=|<=|>|<|==|=|\^|~|)\s*(.*?)\s*$", c).groups()
        core, _, pre = spec.split("+")[0].partition("-")
        ma, mi, pa = ([None if not s else "*" if s in "*xX" or s[0] not in "0123456789" else num(s)
                       for s in core.split(".")] + [None, None])[:3]
        if not spec or not isinstance(ma, int):
            continue
        n, p = (mi if isinstance(mi, int) else 0), (pa if isinstance(pa, int) else 0)
        v = lambda a, b, c, pr="": f"{a}.{b}.{c}" + ("-" + pr if pr else "")
        lo = v(ma, n, p, pre)
        up = v(ma, mi + 1, 0) if isinstance(mi, int) else v(ma + 1, 0, 0)
        wild = [(">=", v(ma, n, 0)), ("<", up)]
        if op == "^" or op == "" and mi != "*" and not (isinstance(mi, int) and pa == "*"):
            cup = (v(ma + 1, 0, 0) if ma or not isinstance(mi, int) else
                   v(0, mi + 1, 0) if mi or not isinstance(pa, int) else v(0, 0, pa + 1))
            out += [(">=", lo), ("<", cup)]
        elif op == "":
            out += wild
        elif op == "~":
            out += [(">=", lo), ("<", up)]
        elif op in ("=", "=="):
            out += [("=", lo)] if isinstance(mi, int) and isinstance(pa, int) else wild
        elif op in (">=", "<") or isinstance(pa, int):
            out.append((op, lo))
        else:
            out.append((">=" if op == ">" else "<",
                        v(ma, n + 1, 0) if isinstance(mi, int) else v(ma + 1, 0, 0)))
    return out


OPS = {">=": operator.ge, ">": operator.gt, "<=": operator.le, "<": operator.lt, "=": operator.eq}


def holds(v, req):
    k = vkey(v)
    return all(OPS[op](k, vkey(c)) for op, c in req) and (
        k[3] or any(not vkey(c)[3] and vkey(c)[:3] == k[:3] for _, c in req))


@functools.lru_cache(maxsize=None)
def msrv_ok(msrv, rustc=TOOLCHAIN):
    return msrv is None or holds(".".join(map(str, vkey(rustc)[:3])), bounds("^" + msrv))


def read_rows(path):
    rows = []
    for line in open(os.path.join(INDEX, path), encoding="utf-8"):
        try:
            j = json.loads(line)
        except json.JSONDecodeError:
            continue
        if isinstance(j.get("name"), str) and isinstance(j.get("vers"), str):
            rows.append(j)
    return rows


def newest(rows):
    """The root pac picks: the greatest version not yanked, first of equals."""
    return max((j for j in rows if not j.get("yanked")), key=lambda j: vkey(j["vers"]), default=None)


def index_files():
    out = []
    for d, subs, files in os.walk(INDEX):
        subs[:] = [s for s in subs if not s.startswith(".")]
        if d != INDEX:
            out += [os.path.relpath(os.path.join(d, f), INDEX) for f in files]
    return sorted(out, key=str.encode)


def sample(seed, n):
    for rel in random.Random(int(seed)).sample(index_files(), int(n)):
        rows = read_rows(rel)
        if newest(rows):
            print(rows[0]["name"])


def summary(rel):
    rows = read_rows(rel)
    top = newest(rows)
    if top is None:
        return None
    feats = [e for t in ("features", "features2") for es in (top.get(t) or {}).values() for e in es]
    return {"name": top["name"], "msrv": top.get("rust_version"), "links": top.get("links"),
            "weak": any("?/" in e for e in feats),
            "vers": [(j["vers"], j.get("rust_version")) for j in rows if not j.get("yanked")],
            "deps": [{"alias": d["name"], "target": (d.get("package") or d["name"]).lower(),
                      "renamed": d["name"] != (d.get("package") or d["name"]),
                      "req": d.get("req", "*"), "kind": d.get("kind") or "normal",
                      "cfg": d.get("target"), "optional": bool(d.get("optional"))}
                     for d in top.get("deps") or []]}


def targets(seed, k, exclude=None):
    with multiprocessing.Pool() as pool:
        tops = [s for s in pool.imap(summary, index_files(), chunksize=256) if s]
    by = {s["name"].lower(): s for s in tops}

    @functools.lru_cache(maxsize=None)
    def moves(target, req, tc):
        """Whether the best version req admits is past toolchain tc while an
        older one of its class is not: where the MSRV preference acts."""
        r = bounds(req)
        adm = [(v, m) for v, m in by[target]["vers"] if holds(v, r)] if target in by else []
        if not adm:
            return False
        best = max(adm, key=lambda x: vkey(x[0]))
        return not msrv_ok(best[1], tc) and any(
            msrv_ok(m, tc) for v, m in adm if compat_class(v) == compat_class(best[0]) and v != best[0])

    def msrv_move(s):
        return any(moves(d["target"], d["req"], s["msrv"] or TOOLCHAIN) for d in s["deps"])

    def several(s, key, val):
        seen = {}
        for d in s["deps"]:
            seen.setdefault(key(d), set()).add(val(d))
        return any(len(v) > 1 for v in seen.values())

    def reached(s, pred):
        return any(d["target"] in by and pred(d, by[d["target"]]) for d in s["deps"])

    pools = {
        "msrv-fallback": lambda s: not s["msrv"] and msrv_move(s),
        "msrv-declared": lambda s: bool(s["msrv"]) and msrv_move(s),
        "weak-features": lambda s: s["weak"],
        "optional": lambda s: any(d["optional"] for d in s["deps"]),
        "renamed": lambda s: any(d["renamed"] for d in s["deps"]),
        "multisite": lambda s: several(s, lambda d: d["target"], lambda d: (d["alias"], d["kind"], d["cfg"])),
        "cfg": lambda s: any(d["cfg"] for d in s["deps"]),
        "cfg-split": lambda s: several(s, lambda d: (d["target"], d["kind"]), lambda d: d["cfg"]),
        "build": lambda s: any(d["kind"] == "build" for d in s["deps"]),
        "dev": lambda s: any(d["kind"] == "dev" for d in s["deps"]),
        "dev-cycle": lambda s: reached(s, lambda d, t: d["kind"] == "dev" and any(
            e["target"] == s["name"].lower() and e["kind"] != "dev" for e in t["deps"])),
        "links": lambda s: bool(s["links"]),
        "links-user": lambda s: reached(s, lambda d, t: d["kind"] != "dev" and bool(t["links"])),
    }
    skip = {l.strip() for l in open(exclude)} if exclude else set()
    for name, pred in pools.items():
        cand = sorted((s["name"] for s in tops if pred(s) and s["name"] not in skip), key=str.encode)
        for c in random.Random(f"{seed}:{name}").sample(cand, min(int(k), len(cand))):
            print(f"{name}\t{c}")


def one(crate, o):
    """run_query.py's and verify.py's answers, in-process so that every
    timeout they set is TIMEOUT, and pac, which verify.py runs again exactly
    as run_query.py did, runs once."""
    import run_query, verify
    timeout = float(os.environ["TIMEOUT"])
    sub = types.ModuleType("subprocess")
    sub.__dict__.update(vars(subprocess))
    sub.run = lambda *a, **kw: subprocess.run(*a, **(dict(kw, timeout=timeout) if "timeout" in kw else kw))
    run_query.subprocess = verify.subprocess = sub
    run_query.run_pac = functools.lru_cache(maxsize=None)(run_query.run_pac)
    with open(o + ".log", "w") as log, contextlib.redirect_stdout(log):
        sys.argv = ["run_query.py", crate, "--out", o + ".json"]
        run_query.main()
        res = json.load(open(o + ".json"))
        pac, cargo = res["pac"], res["cargo"]
        # run_query.py asks cargo only once pac has answered its first run
        root = re.search(r"^root (\S+) (\S+)", pac.get("stdout") or "", re.M)
        if cargo is None and root:
            try:
                cargo = run_query.run_cargo(root[1], root[2], False)
            except Exception as e:
                cargo = {"ok": False, "error": str(e)}
            res["cargo"] = cargo
            json.dump(res, open(o + ".json", "w"), indent=1)
        if pac["ok"]:
            sys.argv = ["verify.py", crate, "--out", o + ".valid.json"]
            verify.main()
    shutil.rmtree(run_query.CARGO_HOME, ignore_errors=True)
    open(o + ".out", "w").write(pac.get("stdout") or "")
    st = lambda r, fail: "-" if r is None else "ok" if r["ok"] else "timeout" if r.get("timeout") else fail
    f = {"pac": st(pac, "unsat" if "unsatisfiable:" in (pac.get("stdout") or "") else "crash"),
         "tool": st(cargo, "refuse"), "corr": "-", "valid": "-", "oo": "-", "to": "-",
         "wall": "%.2f" % pac["wall"] if pac.get("wall") is not None else "-", "kept": "-", "identical": "-"}
    if f["pac"] == "ok" == f["tool"]:
        pn, cn = ({tuple(x) for x in s["crates"]} for s in (pac, cargo))
        pe = {(dn, dv, tn, tv) for dn, dv, _alias, tn, tv in pac["edges"]}
        ce = {tuple(e) for e in cargo["edges"]}
        f["oo"], f["to"] = len(pn - cn), len(cn - pn)
        f["corr"] = "exact" if pn == cn and pe == ce else "diff"
    if f["pac"] == "ok":
        v = json.load(open(o + ".valid.json")) if os.path.exists(o + ".valid.json") else {}
        f["valid"] = v.get("verdict", "ERR")
        yn = {True: "yes", False: "no"}
        f["kept"], f["identical"] = yn.get(v.get("kept"), "-"), yn.get(v.get("identical"), "-")
    print(f"query={os.path.basename(o)} mode=default " + " ".join(f"{k}={v}" for k, v in f.items()))


if __name__ == "__main__":
    {"sample": sample, "targets": targets, "one": one}[sys.argv[1]](*sys.argv[2:])
