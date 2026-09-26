#!/usr/bin/env python3
"""The check writes our answer out as the query's Cargo.lock (mklock.py),
beside a copy of the manifest pac was asked about, and runs `cargo update
--workspace --locked`: cargo re-resolves with our lock as the previous
resolve and, naming no package, avoids none, so it keeps every locked
version a requirement still admits and changes only what its rules force;
--locked makes any change a refusal.  Kept means our answer is a fixed
point of cargo's own resolver over cargo's own manifest -- every version
admitted by the requirement that reached it, nothing present that nothing
needs, nothing absent that something does -- whether or not cargo would
have picked it.

That fixed point is minimal and valid at once, and valid asks only the
second.  So where cargo refuses, `cargo update --workspace` is run once
more without --locked over a pristine copy of our lock, and the lock it
writes is diffed against ours.  If all it did was drop packages, with the
edges out of them, and add nothing, the answer is valid and not minimal:
cargo keeps nothing the root does not reach, and asks nothing of what it
drops, so each dropped package's requirements are checked here against
the answer, by the index's rows (normal and build, optional ones aside, as
cargo resolves a lock whatever the target).  Anything else it changed
makes the answer invalid.  An edge lost out of a package cargo keeps is
such a change, even where the package the edge reached is dropped with
it: the dependency was re-pointed, and whether another crate still holds
the old version is no part of the answer's validity.

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
serves every later --features selection, and pac resolves the root the
same way by default.

cargo fails with 101 for a lock it would change, for a requirement it
cannot meet, and for a registry it cannot reach alike; only the first two
are read as a verdict, and anything else leaves the answer unchecked, as
does a proxy that is not answering.

usage: check.py <answer> <out-dir> <Cargo.toml pac was asked>, through
       eval/check.sh
env: PORT (default 8991), where a sparse_proxy.py serves the index, and
     CARGO_INDEX, that index when not repos/crates.io-index
"""
import json
import os
import shutil
import subprocess
import sys
import urllib.request

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import run_query  # noqa: E402
from scale import REFUSED, bounds, holds  # noqa: E402

KEEP = ["update", "--workspace"]
FRESH = ["generate-lockfile"]
# cargo changing the lock, or refusing the question as scale.py reads a
# refusal
VERDICTS = ("because --locked was passed to prevent this",
            "needs to be updated but --locked was passed") + REFUSED


class Unchecked(Exception):
    pass


def proxy_up():
    try:
        urllib.request.urlopen("http://127.0.0.1:%s/config.json" % os.environ.get("PORT", "8991"),
                               timeout=10).read()
        return True
    except OSError:
        return False


def cargo_lock(workdir, home, sub, locked):
    cmd = ["cargo"] + sub + ["--manifest-path", workdir + "/Cargo.toml"]
    if locked:
        cmd += ["--locked"]
    p = subprocess.run(cmd, capture_output=True, text=True,
                       env=run_query.write_cargo_config(home))
    msg = (p.stderr or p.stdout)[-4000:]
    if p.returncode != 0 and not any(v in msg for v in VERDICTS):
        raise Unchecked("cargo %s: rc %d: %s" % (" ".join(sub), p.returncode, msg.strip()[-300:]))
    return p.returncode, msg


def unmet(dropped, crates):
    """the requirements of each dropped package that nothing in crates meets"""
    have = {}
    for n, v in crates:
        have.setdefault(n, []).append(v)
    out = []
    for n, v in dropped:
        j = run_query.index_line(n, v)
        if j is None:
            out.append("%s %s: not in the index" % (n, v))
            continue
        for d in j.get("deps") or []:
            if d.get("optional") or (d.get("kind") or "normal") == "dev":
                continue
            target = d.get("package") or d["name"]
            req = bounds(d.get("req", "*"))
            if not any(holds(u, req) for u in have.get(target, [])):
                out.append("%s %s needs %s %s" % (n, v, target, d.get("req", "*")))
    return out


def check(ans, out, manifest):
    if not proxy_up():
        raise Unchecked("no proxy on PORT")
    workdir, home = out + "/work", out + "/cargo-home"
    shutil.rmtree(workdir, ignore_errors=True)
    shutil.copytree(os.path.dirname(os.path.abspath(manifest)), workdir,
                    ignore=shutil.ignore_patterns("Cargo.lock", "target"))
    lock = workdir + "/Cargo.lock"
    r = subprocess.run([sys.executable, HERE + "/mklock.py", ans, lock],
                       capture_output=True, text=True)
    if r.returncode != 0:
        raise Unchecked("mklock: " + r.stderr.strip()[-300:])
    ours = lock + ".ours"
    shutil.copy(lock, ours)
    op, oe = run_query.read_lock(ours)

    rc, msg = cargo_lock(workdir, home, KEEP, locked=True)
    res = {"rc": rc, "kept": rc == 0, "identical": None, "cargo": msg, "lost": [], "added": [],
           "lost_edges": [], "added_edges": [], "unmet": []}
    if res["kept"]:
        return "VALID", "yes", res
    shutil.copy(ours, lock)
    irc, _ = cargo_lock(workdir, home, FRESH, locked=True)
    res["identical"] = irc == 0
    if res["identical"]:
        return "VALID", "yes", res
    # the repair: what cargo does to our lock when allowed to
    shutil.copy(ours, lock)
    rrc, rmsg = cargo_lock(workdir, home, KEEP, locked=False)
    if rrc != 0:
        res["cargo"] = rmsg
        return "INVALID", "-", res
    tp, te = run_query.read_lock(lock)
    op, tp, oe, te = set(op), set(tp), set(oe), set(te)
    lost = sorted(op - tp)
    res.update(lost=lost, added=sorted(tp - op), lost_edges=sorted(oe - te),
               added_edges=sorted(te - oe))
    dropped_only = not res["added"] and not res["added_edges"] and all(
        s in lost for s, _ in res["lost_edges"])
    if not dropped_only:
        return "INVALID", "-", res
    res["unmet"] = unmet(lost, op)
    return ("INVALID", "-", res) if res["unmet"] else ("VALID", "no", res)


def main():
    ans, out, manifest = sys.argv[1], sys.argv[2], sys.argv[3]
    try:
        v, m, res = check(ans, out, manifest)
    except (Unchecked, OSError, RuntimeError, ValueError) as e:
        v, m, res = "ERR", "-", {"error": str(e)}
    res.update(verdict=v, minimal=m)
    with open(out + "/valid.json", "w") as f:
        json.dump(res, f, indent=1)
    for label in ("lost", "added", "lost_edges", "added_edges", "unmet"):
        for it in res.get(label, [])[:12]:
            print("    | %s %s" % (label, it))
    if v == "ERR":
        print("    | " + res["error"])
    elif v == "INVALID":
        for line in res["cargo"].strip().splitlines()[:12]:
            print("    | " + line)
    print("%s kept=%s identical=%s lost=%d added=%d valid=%s minimal=%s" % (
        os.path.basename(os.path.dirname(os.path.abspath(manifest))), res.get("kept"),
        res.get("identical"), len(res.get("lost", [])), len(res.get("added", [])), v, m))


if __name__ == "__main__":
    main()
