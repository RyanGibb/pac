#!/usr/bin/env python3
"""Correspondence harness: run one Cargo goal through pac and through real
cargo (against the same crates.io-index checkout) and dump both sides'
raw facts as JSON for later comparison.  Does not itself judge anything --
scale.py does.

Both sides are asked the lockfile question, and asked it the same way.
Pac's rootFeats defaults to every feature the goal crate declares;
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
# A goal declaring no rust-version resolves for the installed rustc, so
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


def run_pac(crate, rustv=None):
    cmd = [PAC, "cargo", INDEX, crate]
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


def self_depended(pac, root):
    """Whether our answer has the goal crate as a dependency of something
    other than itself, at the root's own version.  Four goals do:
    serde_json, tokio, actix-web and itoa each dev-depend on a crate that
    depends on them.  Cargo identifies a package by source as well as by
    name and version, so for it the path root and the registry copy are
    two packages; our model has one node per (name, version) and says
    they are one.  build_manifest passes that difference to cargo as a
    [patch], below."""
    return any((tn, tv) == root and (dn, dv) != root
               for dn, dv, _alias, tn, tv in pac["edges"])


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
            # The goal crate reached as a dependency is the same package
            # as the root, which is what our node identity says and what
            # cargo would otherwise deny: a [patch] is exactly how cargo
            # is told that a registry name resolves to a path package it
            # already has.  Nothing is relaxed by it -- every requirement
            # on that name is still checked against this package, and its
            # own dependency rows are still resolved -- and it is written
            # only for the goals where our answer actually merges the
            # two, because an unused patch would land in the lock as a
            # [[patch.unused]] section of its own.
            f.write(f'\n[patch.crates-io]\n{crate} = {{ path = "." }}\n')
    libpath = workdir + "/src/lib.rs"
    if not os.path.exists(libpath):
        with open(libpath, "w") as f:
            f.write("")
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

    # Pass 1: let pac pick the root version (max, independent of any MSRV
    # setting -- main.ml's default-version fold does not consult msrv_ok).
    probe = run_pac(args.crate)
    if not probe["ok"]:
        result = {"crate": args.crate, "pac": probe,
                  "cargo": None, "dropped": "pac failed on the probe run"}
        pac_res = probe
    else:
        root_name, root_version = probe["root"]
        root_entry = index_line(root_name, root_version)
        rustv = root_entry.get("rust_version") if root_entry else None

        # Pass 2: the toolchain cargo resolves for.  Resolver v3 reads
        # rust-version off the manifest, and when no workspace member
        # declares one it falls back to the rustc it finds installed
        # (ops/resolve.rs, `if rust_versions.is_empty()`).  Leaving pac's
        # preference off in that case would hand the two sides different
        # settings and show up as a divergence that is the harness's, so
        # the fallback is reproduced here rather than assumed away.
        if rustv is None:
            rustv = installed_rustc()
        pac_res = run_pac(args.crate, rustv=rustv)

        try:
            cargo_res = run_cargo(root_name, root_version,
                                  self_depended(pac_res, (root_name, root_version)))
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
