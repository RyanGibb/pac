#!/usr/bin/env python3
"""Two questions of pac's Cargo answer, apart.

Valid: whether the answer is consistent, as consistent.py judges it from
the index rows and the query's manifest alone: every active declaration
met by the version the answer gives it, features existing and unified as
cargo unifies them, one version per semver compatibility class, one
package per `links`.

Reproduced: whether cargo keeps the answer as its lock.  The answer is
written out as the query's Cargo.lock (mklock.py), beside a copy of the
manifest pac was asked about, and `cargo update --workspace --locked` is
run: cargo re-resolves with our lock as the previous resolve and, naming
no package, avoids none, so it keeps every locked version a requirement
still admits and changes only what its rules force; --locked makes any
change a refusal.  A consistent answer cargo does not keep is one it
would repair by its own rules, and no less valid for that: a crate
declaring one package at two sites with different ranges gets two
versions in cargo's own fresh lock, which the re-resolve then re-locks to
the first previous version matching either (kreuzberg's zip), so cargo
does not keep even its own lock.  Where cargo refuses, `cargo
generate-lockfile --locked` says whether the lock is cargo's own fresh
answer (`identical`), which is correspondence rather than validity.

Minimal: whether every package and edge of the answer is one an active
declaration reaches from the root.

--locked is the right question for reproduced only because our answer is
meant to BE a Cargo.lock.  A lock is the feature-independent resolve:
cargo writes it with every feature of the workspace member enabled, so
that one lock serves every later --features selection, and pac resolves
the root the same way by default.

cargo fails with 101 for a lock it would change, for a requirement it
cannot meet, and for a registry it cannot reach alike; only the first two
are read as an answer, and anything else leaves reproduced unknown (-), as
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
from scale import REFUSED  # noqa: E402

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


def reproduce(ans, out, manifest):
    """whether cargo --locked keeps our lock, and whether it is cargo's own"""
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
    shutil.copy(lock, lock + ".ours")
    rc, msg = cargo_lock(workdir, home, KEEP, locked=True)
    if rc == 0:
        return True, None, msg
    shutil.copy(lock + ".ours", lock)
    irc, _ = cargo_lock(workdir, home, FRESH, locked=True)
    return False, irc == 0, msg


def main():
    ans, out, manifest = sys.argv[1], sys.argv[2], sys.argv[3]
    p = subprocess.run([sys.executable, HERE + "/consistent.py", ans, manifest],
                       capture_output=True, text=True)
    try:
        res = json.loads(p.stdout)
    except ValueError:
        res = {"valid": None, "minimal": None, "miss": ["consistent.py: " + p.stderr.strip()[-300:]]}
    try:
        res["kept"], res["identical"], res["cargo"] = reproduce(ans, out, manifest)
    except (Unchecked, OSError, RuntimeError, ValueError) as e:
        res["kept"], res["identical"], res["cargo"] = None, None, str(e)
    yn = {True: "yes", False: "no", None: "-"}
    v = {True: "VALID", False: "INVALID", None: "ERR"}[res["valid"]]
    m, r = (yn[res["minimal"]], yn[res["kept"]]) if v == "VALID" else ("-", "-")
    res.update(verdict=v, reproduced=r)
    with open(out + "/valid.json", "w") as f:
        json.dump(res, f, indent=1)
    for it in res["miss"][:12]:
        print("    | " + it)
    if res["kept"] is None:
        print("    | reproduced unknown: " + res["cargo"].strip()[-300:])
    print("%s kept=%s identical=%s valid=%s minimal=%s reproduced=%s" % (
        os.path.basename(os.path.dirname(os.path.abspath(manifest))), yn[res["kept"]],
        yn[res["identical"]], v, m, r))


if __name__ == "__main__":
    main()
