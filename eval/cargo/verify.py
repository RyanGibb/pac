#!/usr/bin/env python3
"""Ask cargo whether OUR Cargo resolution is a resolution by cargo's own
rules, rather than whether it is the one cargo would have picked.
compare.py asks the second question over run_goal.py's dumps; this asks
the first, and a goal can fail that and pass this.

The check writes our answer out as the goal's Cargo.lock (mklock.py) and
runs `cargo generate-lockfile --locked`: cargo re-resolves and, because
--locked forbids it to write, either accepts the lock unchanged or
reports that it needs updating.  Accepted means our answer is a fixed
point of cargo's own resolver over cargo's own manifest -- every version
admitted by the requirement that reached it, nothing present that
nothing needs, nothing absent that something does.

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

Nothing is downloaded: generate-lockfile wants index rows, which
sparse_proxy.py serves byte-for-byte from the snapshot pac read, and no
crate bodies at all.  So there is no cache to warm and no offline pass
to distinguish from an online one -- a non-zero exit is cargo's verdict
and nothing else.

When cargo refuses, it is run once more without --locked over a pristine
copy of our lock -- the repair -- and the lock it writes is diffed
against ours.  That names the packages and edges it changed, which is
the diagnostic worth printing; it is never the verdict.

The root's own version and any --rust-version are settled exactly as
run_goal.py settles them, by importing it, so the pac invocation being
verified is the one the correspondence sweep measured.

usage: verify.py <crate> [--out <json>]
env: PAC, CARGO_CMP_OUT, and a sparse_proxy.py listening on 8991
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


def cargo_lockfile(workdir, locked):
    cmd = ["cargo", "generate-lockfile", "--manifest-path", workdir + "/Cargo.toml"]
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

    probe = run_goal.run_pac(args.crate)
    if not probe["ok"]:
        print("%-24s PAC FAILED" % args.crate)
        return 1
    root_name, root_version = probe["root"]
    entry = run_goal.index_line(root_name, root_version)
    rustv = entry.get("rust_version") if entry else None
    pac = run_goal.run_pac(args.crate, rustv=rustv) if rustv else probe
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

    rc, msg, wall = cargo_lockfile(workdir, locked=True)
    v = "VALID" if rc == 0 else "INVALID"

    lost, added, lost_edges, added_edges = [], [], [], []
    if rc != 0:
        # the repair: what cargo does to our lock when allowed to
        shutil.copy(ours, lock)
        rrc, _rmsg, _rwall = cargo_lockfile(workdir, locked=False)
        if rrc == 0:
            op, oe = run_goal.read_lock(ours)
            tp, te = run_goal.read_lock(lock)
            op, tp, oe, te = set(op), set(tp), set(oe), set(te)
            lost, added = sorted(op - tp), sorted(tp - op)
            lost_edges, added_edges = sorted(oe - te), sorted(te - oe)

    detail = ""
    if rc != 0:
        detail = " lost=%d added=%d lost-edges=%d added-edges=%d" % (
            len(lost), len(added), len(lost_edges), len(added_edges))
    print("%-24s n=%-4d rc=%-4s %-8s%s %.1fs" % (
        args.crate, len(pac["crates"]), rc, v, detail, wall))
    for label, items in (("lost", lost), ("added", added),
                         ("lost-edge", lost_edges), ("added-edge", added_edges)):
        for it in items[:12]:
            print("    | %s %s" % (label, it))
    if rc != 0:
        for line in msg.strip().splitlines()[:12]:
            print("    | " + line)
    if args.out:
        os.makedirs(os.path.dirname(args.out), exist_ok=True)
        with open(args.out, "w") as f:
            json.dump({"crate": args.crate, "rc": rc, "verdict": v,
                       "valid": v == "VALID", "n": len(pac["crates"]),
                       "root_rust_version": rustv, "lost": lost,
                       "added": added, "lost_edges": lost_edges,
                       "added_edges": added_edges, "cargo": msg}, f, indent=1)
    return 0


if __name__ == "__main__":
    sys.exit(main())
