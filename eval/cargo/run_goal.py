#!/usr/bin/env python3
"""Correspondence harness: run one Cargo goal through pac and through real
cargo (against the same crates.io-index checkout) and dump both sides'
raw facts as JSON for later comparison.  Does not itself judge anything --
see compare.py.
"""
import argparse, json, os, re, shutil, subprocess, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.normpath(HERE + "/../..")
PAC = os.environ.get("PAC", ROOT + "/_build/default/src/main.exe")
INDEX = ROOT + "/repos/crates.io-index"
OUT = os.environ.get("CARGO_CMP_OUT", "/tmp/cargo-cmp")
CARGO_HOME = OUT + "/cargo-home"
WORK = OUT + "/work"
MANIFEST_JQ = HERE + "/manifest.jq"


def crate_path(name):
    n = name.lower()
    l = len(n)
    if l == 1:
        return f"{INDEX}/1/{n}"
    if l == 2:
        return f"{INDEX}/2/{n}"
    if l == 3:
        return f"{INDEX}/3/{n[0]}/{n}"
    return f"{INDEX}/{n[0:2]}/{n[2:4]}/{n}"


def index_line(name, version):
    path = crate_path(name)
    if not os.path.exists(path):
        return None
    with open(path) as f:
        for l in f:
            l = l.strip()
            if not l:
                continue
            try:
                j = json.loads(l)
            except json.JSONDecodeError:
                continue
            if j.get("vers") == version:
                return j
    return None


def run_pac(crate, feats, rustv=None):
    cmd = [PAC, "cargo", INDEX, crate]
    if feats:
        cmd += ["--features", ",".join(feats)]
    if rustv:
        cmd += ["--rust-version", rustv]
    cmd += ["--print-parents"]
    t0 = time.time()
    try:
        p = subprocess.run(cmd, capture_output=True, text=True, timeout=240)
    except subprocess.TimeoutExpired:
        return {"ok": False, "returncode": None, "stdout": "", "stderr": "timed out",
                "wall": time.time() - t0, "timeout": True}
    dt = time.time() - t0
    out = p.stdout
    err = p.stderr
    if p.returncode != 0:
        return {"ok": False, "returncode": p.returncode, "stdout": out, "stderr": err, "wall": dt}

    m = re.search(r"^root (\S+) (\S+)", out, re.M)
    root_name, root_version = (m.group(1), m.group(2)) if m else (None, None)

    crates = []
    in_crates = False
    feat_map = {}
    for line in out.splitlines():
        if line.startswith("crates ("):
            in_crates = True
            continue
        if line.startswith("encoded solution:"):
            in_crates = False
            continue
        if in_crates:
            mm = re.match(r"^  (\S+) (\S+)(?: \[(.*)\])?$", line)
            if mm:
                name, ver, fs = mm.group(1), mm.group(2), mm.group(3)
                crates.append([name, ver])
                feat_map[f"{name}@{ver}"] = fs.split(",") if fs else []

    edges = []
    in_edges = False
    for line in out.splitlines():
        if line.strip() == "parent-edges:":
            in_edges = True
            continue
        if line.startswith("loaded:"):
            in_edges = False
            continue
        if in_edges:
            mm = re.match(r"^  (\S+) (\S+) -> (\S+)\((\S+)\) (\S+)$", line)
            if mm:
                dn, dv, alias, tgt, tv = mm.groups()
                edges.append([dn, dv, alias, tgt, tv])

    mparse = re.search(r"^parse ([\d.]+)s", out, re.M)
    msolve = re.search(r"^solve ([\d.]+)s", out, re.M)

    return {
        "ok": True,
        "root": [root_name, root_version],
        "crates": crates,
        "feats": feat_map,
        "edges": edges,
        "wall": dt,
        "parse_s": float(mparse.group(1)) if mparse else None,
        "solve_s": float(msolve.group(1)) if msolve else None,
        "stdout": out,
        "stderr": err,
    }


def build_manifest(crate, version, workdir):
    j = index_line(crate, version)
    if j is None:
        raise RuntimeError(f"no index entry {crate}@{version}")
    os.makedirs(workdir + "/src", exist_ok=True)
    p = subprocess.run(["jq", "-r", "-f", MANIFEST_JQ], input=json.dumps(j),
                        capture_output=True, text=True)
    if p.returncode != 0:
        raise RuntimeError("jq failed: " + p.stderr)
    with open(workdir + "/Cargo.toml", "w") as f:
        f.write(p.stdout)
    libpath = workdir + "/src/lib.rs"
    if not os.path.exists(libpath):
        with open(libpath, "w") as f:
            f.write("")
    for stale in (workdir + "/Cargo.lock",):
        if os.path.exists(stale):
            os.remove(stale)


def run_cargo(crate, version, feats):
    workdir = f"{WORK}/{crate}"
    build_manifest(crate, version, workdir)
    # Not --offline: dependency *resolution* is already pinned by the
    # [source] replacement in CARGO_HOME/config.toml to the same
    # repos/crates.io-index checkout pac reads, so which versions get
    # picked cannot be affected by the network.  `cargo metadata` also
    # downloads each resolved package's real .crate to report its full
    # manifest (targets, authors, ...), which --offline blocks outright;
    # letting that go to the real (reachable) static.crates.io is safe --
    # crates.io versions are immutable and the body played no part in
    # picking which version this is.
    cmd = ["cargo", "metadata", "--format-version=1",
           "--manifest-path", workdir + "/Cargo.toml"]
    if feats is not None:
        cmd += ["--no-default-features"]
        if feats:
            cmd += ["--features", ",".join(feats)]
    os.makedirs(CARGO_HOME, exist_ok=True)
    cfg = CARGO_HOME + "/config.toml"
    if not os.path.exists(cfg):
        with open(cfg, "w") as f:
            f.write('[source.crates-io]\nreplace-with = "pinned-index"\n\n'
                    '[source.pinned-index]\n'
                    'registry = "sparse+http://127.0.0.1:8991/"\n\n'
                    '[registries.pinned-index]\n'
                    'index = "sparse+http://127.0.0.1:8991/"\n')
    env = dict(os.environ)
    env["CARGO_HOME"] = CARGO_HOME
    t0 = time.time()
    try:
        p = subprocess.run(cmd, capture_output=True, text=True, timeout=240, env=env)
    except subprocess.TimeoutExpired:
        return {"ok": False, "returncode": None, "stdout": "", "stderr": "timed out",
                "wall": time.time() - t0, "timeout": True}
    dt = time.time() - t0
    if p.returncode != 0:
        return {"ok": False, "returncode": p.returncode, "stdout": p.stdout[-4000:],
                "stderr": p.stderr[-4000:], "wall": dt}
    md = json.loads(p.stdout)
    pkgs = {pk["id"]: pk for pk in md["packages"]}
    resolve = md.get("resolve")
    if resolve is None:
        return {"ok": False, "returncode": 0, "stdout": "no resolve section",
                "stderr": "", "wall": dt}
    nodes = resolve["nodes"]
    root_id = resolve.get("root")
    crates = []
    edges = []
    for nd in nodes:
        pk = pkgs[nd["id"]]
        crates.append([pk["name"], pk["version"]])
        for dep_id in nd.get("dependencies", []):
            tp = pkgs[dep_id]
            edges.append([pk["name"], pk["version"], tp["name"], tp["version"]])
    root_pk = pkgs[root_id] if root_id else None
    return {
        "ok": True,
        "root": [root_pk["name"], root_pk["version"]] if root_pk else [None, None],
        "crates": crates,
        "edges": edges,
        "wall": dt,
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("crate")
    ap.add_argument("--features", default=None,
                     help="comma-separated features; if omitted, no features "
                          "(matches pac's empty root_feats and cargo's "
                          "--no-default-features with none named)")
    ap.add_argument("--out", default=None)
    args = ap.parse_args()
    feats = args.features.split(",") if args.features else ([] if args.features is not None else [])
    # pac's default (no --features flag at all) already means root_feats=[];
    # passing --features "" to this script also means [].  Both cases give
    # the identical instruction to cargo: --no-default-features, no --features.

    # Pass 1: let pac pick the root version (max, independent of any MSRV
    # setting -- main.ml's default-version fold does not consult msrv_ok).
    probe = run_pac(args.crate, feats)
    if not probe["ok"]:
        result = {"crate": args.crate, "features": feats, "pac": probe,
                  "cargo": None, "dropped": "pac failed on the probe run"}
        pac_res = probe
    else:
        root_name, root_version = probe["root"]
        root_entry = index_line(root_name, root_version)
        rustv = root_entry.get("rust_version") if root_entry else None

        # Pass 2 (only when the root crate itself declares an MSRV): real
        # cargo's resolver v3 reads that field straight off the manifest it
        # is resolving and applies the MSRV-preferring sort unconditionally
        # -- there is no cargo flag that targets a toolchain other than the
        # one named in rust-version, so pac's --rust-version is only a
        # correct stand-in for "the toolchain cargo resolves for" when set
        # to exactly this value.  Left unset (rustv is None), pac's
        # preference is off, matching a root with no declared rust-version,
        # where cargo has nothing to prefer by either.
        if rustv:
            pac_res = run_pac(args.crate, feats, rustv=rustv)
        else:
            pac_res = probe

        try:
            cargo_res = run_cargo(root_name, root_version, feats)
        except Exception as e:
            cargo_res = {"ok": False, "error": str(e)}
        result = {"crate": args.crate, "features": feats, "root_rust_version": rustv,
                  "pac": pac_res, "cargo": cargo_res}

    out_path = args.out or f"{OUT}/results/{args.crate}.json"
    os.makedirs(os.path.dirname(out_path), exist_ok=True)
    with open(out_path, "w") as f:
        json.dump(result, f, indent=1)
    print(f"wrote {out_path}")
    print(f"  pac ok={pac_res.get('ok')} wall={pac_res.get('wall'):.2f}s"
          if pac_res.get("wall") is not None else f"  pac ok={pac_res.get('ok')}")
    if result["cargo"]:
        c = result["cargo"]
        print(f"  cargo ok={c.get('ok')} wall={c.get('wall', 0):.2f}s")


if __name__ == "__main__":
    main()
