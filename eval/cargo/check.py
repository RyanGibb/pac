#!/usr/bin/env python3
"""Whether pac's Cargo answer is valid and minimal, as consistent.py
judges them from the index rows and the query's manifest alone, and,
apart, whether it is reproduced: whether `cargo update --workspace
--locked` keeps it as the query's Cargo.lock (mklock.py), a lock being
what the answer is meant to be.  An answer cargo would repair by its own
rules is no less valid.  Where cargo refuses, `cargo generate-lockfile
--locked` says whether the lock is cargo's own fresh answer (identical).
cargo's exit 101 is read as an answer only for a lock it would change or
a requirement it cannot meet; anything else leaves reproduced unknown (-).

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
    # the home is only cargo's copy of the index rows it fetched, ~13 MB a
    # check, which nothing reads afterwards
    try:
        rc, msg = cargo_lock(workdir, home, KEEP, locked=True)
        if rc == 0:
            return True, None, msg
        shutil.copy(lock + ".ours", lock)
        irc, _ = cargo_lock(workdir, home, FRESH, locked=True)
        return False, irc == 0, msg
    finally:
        shutil.rmtree(home, ignore_errors=True)


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
