#!/usr/bin/env python3
"""Ask cargo whether OUR Cargo resolution is a resolution by cargo's own
rules, rather than whether it is the one cargo would have picked.
compare.py asks the second question over run_goal.py's dumps; this asks
the first, and a goal can fail that and pass this.

The check writes our answer out as the goal's Cargo.lock (mklock.py) and
runs `cargo update --workspace --locked`: cargo re-resolves with our lock
as the previous resolve and, naming no package, avoids none, so it keeps
every locked version a requirement still admits and changes only what its
rules force; --locked makes any change a refusal.  Accepted means our
answer is a fixed point of cargo's own resolver over cargo's own manifest
-- every version admitted by the requirement that reached it, nothing
present that nothing needs, nothing absent that something does -- whether
or not cargo would have picked it.

`cargo generate-lockfile --locked` cannot ask this: it resolves with no
previous resolve (ops/cargo_update.rs), so it accepts only a lock equal to
cargo's own fresh answer, which is correspondence again.  It is still run
when the keep check refuses, because cargo's own lock can fail that
check: a crate declaring one package at two sites has both rows re-locked
to the first previous version matching either (kreuzberg's zip), so a lock
identical to cargo's fresh one is valid whatever the keep check says.

--locked is the right question only because our answer is meant to BE a
Cargo.lock.  A lock is the feature-independent resolve: cargo writes it
with every feature of the workspace member enabled, so that one lock
serves every later --features selection.  That is what pac's default
rootFeats now is, so the two artifacts are the same artifact and can be
compared as one.  (While pac modelled the feature-filtered build view
instead, --locked scored 5/28 and every failure was cargo's lock being a
strict superset of ours -- unactivated optionals, down to single nodes
like rustc-std-workspace-core under cfg-if.  The gap was the model's,
not the check's.)

Nothing is downloaded: both commands want index rows, which
sparse_proxy.py serves byte-for-byte from the snapshot pac read, and no
crate bodies at all.  So there is no cache to warm and no offline pass
to distinguish from an online one -- a non-zero exit is cargo's verdict
and nothing else.

When cargo refuses, `cargo update --workspace` is run once more without
--locked over a pristine copy of our lock -- the repair -- and the lock it
writes is diffed against ours.  That names the packages and edges it
changed, which is the diagnostic worth printing; it is never the verdict.

The root's own version and any --rust-version are settled exactly as
run_goal.py settles them, by importing it, so the pac invocation being
verified is the one the correspondence sweep measured.

usage: verify.py <crate> [--out <json>]
env: PAC, CARGO_CMP_OUT, and PORT (default 8991), where a sparse_proxy.py
listens
"""
import argparse
import json
import os
import shutil
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import run_goal  # noqa: E402

KEEP = ["update", "--workspace"]
FRESH = ["generate-lockfile"]


def cargo_lock(workdir, sub, locked):
    cmd = ["cargo"] + sub + ["--manifest-path", workdir + "/Cargo.toml"]
    if locked:
        cmd += ["--locked"]
    env = run_goal.write_cargo_config()
    t0 = time.time()
    try:
        p = subprocess.run(cmd, capture_output=True, text=True, timeout=600, env=env)
    except subprocess.TimeoutExpired:
        return None, "timed out", time.time() - t0
    return p.returncode, (p.stderr or p.stdout)[-4000:], time.time() - t0


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("crate")
    ap.add_argument("--out", default=None)
    args = ap.parse_args()
    run_goal.check_toolchain()

    probe = run_goal.run_pac(args.crate)
    if not probe["ok"]:
        print("%-24s PAC FAILED" % args.crate)
        return 1
    root_name, root_version = probe["root"]
    entry = run_goal.index_line(root_name, root_version)
    rustv = entry.get("rust_version") if entry else None
    # The same fallback run_goal.py reproduces: with no member declaring a
    # rust-version, resolver v3 ranks against the installed rustc rather
    # than against nothing, so the lock being verified has to be the one
    # pac writes for that toolchain.  Verified red-then-green on
    # rustradio-ui, whose rustradio dependency moves under it.
    if rustv is None:
        rustv = run_goal.installed_rustc()
    pac = run_goal.run_pac(args.crate, rustv=rustv)
    if not pac["ok"]:
        print("%-24s PAC FAILED (msrv pass)" % args.crate)
        return 1

    root = (root_name, root_version)
    workdir = f"{run_goal.WORK}/{args.crate}"
    run_goal.build_manifest(root_name, root_version, workdir,
                            run_goal.self_depended(pac, root))
    lock = workdir + "/Cargo.lock"
    raw = workdir + "/pac.out"
    with open(raw, "w") as f:
        f.write(pac["stdout"])
    r = subprocess.run([sys.executable, HERE + "/mklock.py", raw, lock],
                       capture_output=True, text=True)
    if r.returncode != 0:
        print("%-24s LOCKGEN FAILED %s" % (args.crate, r.stderr.strip()[:200]))
        return 1
    ours = lock + ".ours"
    shutil.copy(lock, ours)

    rc, msg, wall = cargo_lock(workdir, KEEP, locked=True)
    kept = rc == 0
    identical = None
    if not kept:
        shutil.copy(ours, lock)
        irc, _imsg, _iwall = cargo_lock(workdir, FRESH, locked=True)
        identical = irc == 0
    v = "VALID" if kept or identical else "INVALID"

    lost, added, lost_edges, added_edges = [], [], [], []
    if v == "INVALID":
        # the repair: what cargo does to our lock when allowed to
        shutil.copy(ours, lock)
        rrc, _rmsg, _rwall = cargo_lock(workdir, KEEP, locked=False)
        if rrc == 0:
            op, oe = run_goal.read_lock(ours)
            tp, te = run_goal.read_lock(lock)
            op, tp, oe, te = set(op), set(tp), set(oe), set(te)
            lost, added = sorted(op - tp), sorted(tp - op)
            lost_edges, added_edges = sorted(oe - te), sorted(te - oe)

    detail = ""
    if v == "INVALID":
        detail = " lost=%d added=%d lost-edges=%d added-edges=%d" % (
            len(lost), len(added), len(lost_edges), len(added_edges))
    elif not kept:
        detail = " (identical to cargo's; not kept)"
    print("%-24s n=%-4d rc=%-4s %-8s%s %.1fs" % (
        args.crate, len(pac["crates"]), rc, v, detail, wall))
    for label, items in (("lost", lost), ("added", added),
                         ("lost-edge", lost_edges), ("added-edge", added_edges)):
        for it in items[:12]:
            print("    | %s %s" % (label, it))
    if v == "INVALID":
        for line in msg.strip().splitlines()[:12]:
            print("    | " + line)
    if args.out:
        os.makedirs(os.path.dirname(args.out), exist_ok=True)
        with open(args.out, "w") as f:
            json.dump({"crate": args.crate, "rc": rc, "verdict": v,
                       "valid": v == "VALID", "kept": kept,
                       "identical": identical, "n": len(pac["crates"]),
                       "root_rust_version": rustv, "lost": lost,
                       "added": added, "lost_edges": lost_edges,
                       "added_edges": added_edges, "cargo": msg}, f, indent=1)
    return 0


if __name__ == "__main__":
    sys.exit(main())
