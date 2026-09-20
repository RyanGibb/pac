#!/usr/bin/env python3
"""Ask cargo whether OUR Cargo resolution is a resolution by cargo's own
rules, rather than whether it is the one cargo would have picked.
compare.py asks the second question over run_goal.py's dumps; this asks
the first, and a goal can fail that and pass this.

The check writes our answer out as the goal's Cargo.lock (mklock.py) and
runs `cargo metadata --frozen` over the same synthetic root manifest and
the same pinned index snapshot the correspondence run uses.

`--frozen` is `--locked --offline` together.  `--offline` is what makes a
measured run reproducible rather than merely disciplined: with no network
reachable, cargo cannot consult the live crates.io index even if the
[source] replacement were ever to go missing again, so the universe it
answers about is structurally the snapshot's.  It needs the bodies
already in CARGO_HOME, which is what warm.sh puts there in one online
pass; a run whose cache is short of one is reported NOCACHE, never
INVALID.

`--locked` verifies rather than re-resolves because cargo's resolver
takes the versions already in the lock as locked preferences: it keeps
each one wherever the constraints still admit it, and reaches for a
different version only where they do not.  `--locked` then fails if the
resolve it arrives at differs from the lock at all.  So a lock holding
some valid resolution is kept and passes even when cargo's own
unconstrained pick would have been another one -- which is the whole
distinction being measured -- while a lock that is not a resolution
(a version violating some req, a missing edge, a node nothing needs)
forces a change and fails.  Confirmed by controls in notes/validity.md,
including the one that matters: an older-but-satisfying version
substituted into an otherwise valid lock is accepted, so cargo really is
checking the lock rather than reproducing its own answer.

The one thing a Cargo.lock cannot carry, and this check therefore does
not verify: the feature selection, since the lock records versions and
edges, not features.  The cfg-gated rows it does carry -- cargo's
version resolver is platform-blind, so they bind here exactly as they
bind in pac.

The root's own version and any --rust-version are settled exactly as
run_goal.py settles them, by importing it, so the pac invocation being
verified is the one the correspondence sweep measured.

usage: verify.py <crate> [--features a,b] [--out <json>]
env: PAC, CARGO_CMP_OUT, and a sparse_proxy.py listening on 8991
"""
import argparse
import json
import os
import re
import subprocess
import sys
import time

# How --frozen distinguishes a cache that is short of something from a
# lock that is not a resolution.  Cargo appends "note: offline mode (via
# `--frozen`) can sometimes cause surprising resolution failures" exactly
# when being offline may be the cause, and says plainly "cannot update
# the lock file ... because --frozen was passed" when it is not.  Do NOT
# widen this to "--offline": that string is in the *help* line of the
# genuine-invalid message, and matching it scores every real failure
# NOCACHE.
COLD = re.compile(r"offline mode|failed to download|not yet downloaded", re.I)

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import run_goal  # noqa: E402


def cargo_check(workdir, feats, warm=False):
    if warm:
        # the one online pass: populate CARGO_HOME with every body the
        # verification pass will need, resolution still pinned by the
        # lock and the proxy
        cmd = ["cargo", "fetch", "--locked",
               "--manifest-path", workdir + "/Cargo.toml"]
    else:
        cmd = ["cargo", "metadata", "--frozen", "--format-version=1",
               "--manifest-path", workdir + "/Cargo.toml"]
    if not warm and feats is not None:
        cmd += ["--no-default-features"]
        if feats:
            cmd += ["--features", ",".join(feats)]
    # the same [source] replacement run_cargo writes, and for the same
    # reason: without it cargo resolves against the live crates.io index
    # rather than the snapshot pac read, and answers about a universe
    # that has moved on.
    os.makedirs(run_goal.CARGO_HOME, exist_ok=True)
    cfg = run_goal.CARGO_HOME + "/config.toml"
    if not os.path.exists(cfg):
        with open(cfg, "w") as f:
            f.write('[source.crates-io]\nreplace-with = "pinned-index"\n\n'
                    '[source.pinned-index]\n'
                    'registry = "sparse+http://127.0.0.1:8991/"\n\n'
                    '[registries.pinned-index]\n'
                    'index = "sparse+http://127.0.0.1:8991/"\n')
    env = dict(os.environ)
    env["CARGO_HOME"] = run_goal.CARGO_HOME
    t0 = time.time()
    try:
        p = subprocess.run(cmd, capture_output=True, text=True, timeout=600, env=env)
    except subprocess.TimeoutExpired:
        return None, "timed out", time.time() - t0
    return p.returncode, (p.stderr or p.stdout)[-4000:], time.time() - t0


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("crate")
    ap.add_argument("--features", default=None)
    ap.add_argument("--out", default=None)
    ap.add_argument("--warm", action="store_true",
                    help="online pass: fetch every body the verification "
                         "pass will need, instead of verifying")
    args = ap.parse_args()
    feats = args.features.split(",") if args.features else []

    probe = run_goal.run_pac(args.crate, feats)
    if not probe["ok"]:
        print("%-24s PAC FAILED" % args.crate)
        return 1
    root_name, root_version = probe["root"]
    entry = run_goal.index_line(root_name, root_version)
    rustv = entry.get("rust_version") if entry else None
    pac = run_goal.run_pac(args.crate, feats, rustv=rustv) if rustv else probe
    if not pac["ok"]:
        print("%-24s PAC FAILED (msrv pass)" % args.crate)
        return 1

    workdir = f"{run_goal.WORK}/{args.crate}"
    run_goal.build_manifest(root_name, root_version, workdir)
    lock = workdir + "/Cargo.lock"
    raw = workdir + "/pac.out"
    with open(raw, "w") as f:
        f.write(pac["stdout"])
    r = subprocess.run([sys.executable, HERE + "/mklock.py", raw, lock],
                       capture_output=True, text=True)
    if r.returncode != 0:
        print("%-24s LOCKGEN FAILED %s" % (args.crate, r.stderr.strip()[:200]))
        return 1

    rc, msg, wall = cargo_check(workdir, feats, warm=args.warm)
    if args.warm:
        v = "WARMED" if rc == 0 else "WARM-FAILED"
    elif rc == 0:
        v = "VALID"
    elif COLD.search(msg or ""):
        # a body missing from CARGO_HOME is the cache being incomplete,
        # not our answer being wrong; scoring it INVALID would be a lie
        v = "NOCACHE"
    else:
        v = "INVALID"
    print("%-24s n=%-4d rc=%-4s %-11s %.1fs" % (args.crate, len(pac["crates"]),
                                                rc, v, wall))
    if rc != 0:
        for line in msg.strip().splitlines()[:12]:
            print("    | " + line)
    if args.out:
        os.makedirs(os.path.dirname(args.out), exist_ok=True)
        with open(args.out, "w") as f:
            json.dump({"crate": args.crate, "features": feats, "rc": rc,
                       "verdict": v, "valid": rc == 0, "n": len(pac["crates"]),
                       "root_rust_version": rustv, "cargo": msg}, f, indent=1)
    return 0


if __name__ == "__main__":
    sys.exit(main())
