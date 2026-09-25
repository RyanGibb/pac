#!/usr/bin/env python3
"""Correspondence harness: run one Cargo query through pac and through real
cargo (against the same crates.io-index checkout) and dump both sides'
raw facts as JSON for later comparison.  Does not itself judge anything --
scale.py does.

A query names a crate, and the question is the lock of its newest
release's own published manifest as the one workspace member.  That
manifest is written out from the index entry (manifest.jq), and both sides
are handed the same file: pac as its root Cargo.toml, cargo as the
workspace it is run in.

Both sides are asked the lockfile question, and asked it the same way.
Pac's rootFeats defaults to every feature the root declares;
`cargo generate-lockfile` resolves the one workspace member under
CliFeatures::new_all(true) with HasDevUnits::Yes, which is that same
instantiation.  Neither side is given a feature selection, because a
lock is the resolve that has to serve every selection.

The answer is read out of Cargo.lock rather than out of `cargo
metadata`: metadata reports the second, feature-filtered resolve cargo
builds from the lock, and to report it at all it must download each
resolved package's body for the full manifest.  generate-lockfile writes
the artifact being compared and downloads nothing.
"""
import argparse, json, os, re, shutil, subprocess, sys, time, tomllib

# The toolchain the recorded results were taken with, pinned by nix/flake.lock.
# A query declaring no rust-version resolves for the installed rustc, so
# under any other the sweep measures a different question.
RUSTC_VERSION = "1.97.1"
CARGO_VERSION = "1.97.0"
# write_cargo_config hands cargo this rustc explicitly, so a build.rustc in
# some config file cannot pick another than the one checked here.
RUSTC = os.environ.get("RUSTC") or shutil.which("rustc") or "rustc"

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


def tool_version(exe):
    try:
        out = subprocess.run([exe, "--version"], capture_output=True,
                             text=True).stdout
        return out.split()[1]
    except (OSError, IndexError):
        return None


def installed_rustc():
    """What cargo falls back to when no member declares rust-version."""
    return tool_version(RUSTC)


def check_toolchain():
    have = (installed_rustc(), tool_version("cargo"))
    if have != (RUSTC_VERSION, CARGO_VERSION):
        sys.exit(f"rustc {have[0]} ({RUSTC}) and cargo {have[1]} here, but the"
                 f" recorded results were taken with rustc {RUSTC_VERSION} and"
                 f" cargo {CARGO_VERSION}; run inside nix develop ./nix, where"
                 f" nix/flake.lock pins them")


def run_pac(manifest):
    # the installed rustc, which cargo falls back to when the root declares
    # no rust-version and which pac cannot read off the toolchain; a
    # declared one pac reads off the manifest, as cargo does
    cmd = [PAC, "cargo", INDEX, manifest, "--rust-version", installed_rustc(),
           "--print-parents"]
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


def newest(crate):
    """The release the query names: the greatest version not yanked, first
    of equals, under cargo's order."""
    from scale import vkey
    path = crate_path(crate)
    rows = []
    if os.path.exists(path):
        for l in open(path, encoding="utf-8"):
            try:
                j = json.loads(l)
            except json.JSONDecodeError:
                continue
            if isinstance(j.get("vers"), str) and not j.get("yanked"):
                rows.append(j)
    return max(rows, key=lambda j: vkey(j["vers"]), default=None)


def ask_pac(crate):
    """pac's answer for the crate's published manifest, with the root it
    names and whether the manifest needed the self-patch.  Four regression
    queries (serde_json, tokio, actix-web and itoa) dev-depend on a crate
    that depends on them.  Cargo identifies a package by source as well as
    by name and version, so for it the path root and the registry copy are
    two packages; our model has one node per (name, version), and pac
    refuses such a manifest unless a [patch] says the two are one.  So the
    manifest is patched exactly when pac's answer merges them, and cargo is
    handed the same manifest."""
    top = newest(crate)
    if top is None:
        return {"ok": False, "returncode": None, "stdout": "",
                "stderr": "no release left unyanked", "wall": 0}, None, None, False
    root = (top["name"], top["vers"])
    manifest = f"{WORK}/{crate}/Cargo.toml"
    patched = False
    build_manifest(*root, os.path.dirname(manifest), patched)
    pac = run_pac(manifest)
    if pac.get("returncode") == 2 and "through the registry" in pac["stderr"]:
        patched = True
        build_manifest(*root, os.path.dirname(manifest), patched)
        pac = run_pac(manifest)
    return pac, root, top.get("rust_version") or installed_rustc(), patched


def build_manifest(crate, version, workdir, patch_self=False):
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
        if patch_self:
            # The queried crate reached as a dependency is the same package
            # as the root, which is what our node identity says: a [patch]
            # is exactly how cargo is told that a registry name resolves to
            # a path package it already has.  Nothing is relaxed by it --
            # every requirement on that name is still checked against this
            # package, and its own dependency rows are still resolved --
            # and it is written only for the queries where our answer
            # actually merges the two.
            f.write(f'\n[patch.crates-io]\n{crate} = {{ path = "." }}\n')
    libpath = workdir + "/src/lib.rs"
    if not os.path.exists(libpath):
        with open(libpath, "w") as f:
            f.write("")
    if j.get("links") and not os.path.exists(workdir + "/build.rs"):
        with open(workdir + "/build.rs", "w") as f:
            f.write("fn main() {}\n")
    for stale in (workdir + "/Cargo.lock",):
        if os.path.exists(stale):
            os.remove(stale)


def write_cargo_config():
    """Pin cargo to the snapshot pac reads.  Without this replacement
    cargo resolves against the live crates.io index and answers about a
    universe that has moved on since; sparse_proxy.py serves the
    checkout on PORT, and valid.sh and scale.sh start it there.  The file
    is rewritten whenever it differs, as a CARGO_HOME kept from a run on
    another port would otherwise point cargo at that one."""
    port = os.environ.get("PORT", "8991")
    url = f"sparse+http://127.0.0.1:{port}/"
    want = ('[source.crates-io]\nreplace-with = "pinned-index"\n\n'
            f'[source.pinned-index]\nregistry = "{url}"\n\n'
            f'[registries.pinned-index]\nindex = "{url}"\n')
    os.makedirs(CARGO_HOME, exist_ok=True)
    cfg = CARGO_HOME + "/config.toml"
    try:
        with open(cfg) as f:
            have = f.read()
    except FileNotFoundError:
        have = None
    if have != want:
        with open(cfg, "w") as f:
            f.write(want)
    env = dict(os.environ)
    env["CARGO_HOME"] = CARGO_HOME
    env["RUSTC"] = RUSTC
    return env


def read_lock(path):
    """A Cargo.lock as (packages, edges).  A `dependencies` entry is
    written "crate", "crate version" or "crate version (source)", the
    bare form only while one package carries that name."""
    with open(path, "rb") as f:
        doc = tomllib.load(f)
    pkgs = [(p["name"], p["version"]) for p in doc.get("package", [])]
    by_name = {}
    for n, v in pkgs:
        by_name.setdefault(n, set()).add(v)
    edges = []
    for p in doc.get("package", []):
        for d in p.get("dependencies", []):
            parts = d.split()
            name = parts[0]
            if len(parts) > 1:
                ver = parts[1]
            else:
                cands = by_name.get(name, ())
                if len(cands) != 1:
                    raise RuntimeError(f"ambiguous lock dependency {d!r}")
                ver = next(iter(cands))
            edges.append(((p["name"], p["version"]), (name, ver)))
    return pkgs, edges


def run_cargo(crate, version, patch_self):
    workdir = f"{WORK}/{crate}"
    build_manifest(crate, version, workdir, patch_self)
    # Not --offline: the index rows come over HTTP from the proxy, and
    # generate-lockfile wants nothing else -- it resolves and writes the
    # lock without downloading a single crate body.
    cmd = ["cargo", "generate-lockfile", "--manifest-path", workdir + "/Cargo.toml"]
    env = write_cargo_config()
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
    pkgs, edges = read_lock(workdir + "/Cargo.lock")
    return {
        "ok": True,
        "root": [crate, version],
        "crates": [[n, v] for n, v in pkgs],
        "edges": [[dn, dv, tn, tv] for (dn, dv), (tn, tv) in edges],
        "wall": dt,
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("crate")
    ap.add_argument("--out", default=None)
    args = ap.parse_args()
    check_toolchain()

    pac_res, root, rustv, patched = ask_pac(args.crate)
    if root is None:
        result = {"crate": args.crate, "pac": pac_res,
                  "cargo": None, "dropped": "no release left unyanked"}
    else:
        try:
            cargo_res = run_cargo(*root, patched)
        except Exception as e:
            cargo_res = {"ok": False, "error": str(e)}
        result = {"crate": args.crate, "root_rust_version": rustv,
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
