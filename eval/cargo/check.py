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
drops, so each dropped package is checked here against the answer, by the
index's rows: every declaration cargo resolves whatever the features and
the target (normal and build, optional ones aside) met by one of its
edges, every edge a declaration it meets, and no second semver-compatible
version or second `links` owner beside another package of the answer.
Anything else cargo changed makes the answer invalid.  An edge lost out of
a package cargo keeps is such a change where the package still has an
edge of that name: the dependency was re-pointed, and whether another
crate still holds the old version is no part of the answer's validity.
Where it has none, cargo left the declaration inactive (an optional one
whose feature is off, a dependency's dev one), and the edge goes as a
dropped package does, asked only to be declared.

`cargo generate-lockfile --locked` cannot ask this: it resolves with no
previous resolve (ops/cargo_update.rs), so it accepts only a lock equal to
cargo's own fresh answer, which is correspondence again.  It is run when
the keep check refuses, for `identical` alone.  cargo's own fresh lock can
fail the keep check: a crate declaring one package at two sites with
different ranges can get two versions, and a re-resolve re-locks both
rows to the first previous version matching either (kreuzberg's zip).
Such a lock is still invalid: cargo --locked, as any locked build runs
it, refuses it whoever wrote it, and taking it where it happens to be
cargo's own would make the verdict on the split turn on every unrelated
choice elsewhere in the answer.

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
import tomllib
import urllib.request

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import run_query  # noqa: E402
from scale import REFUSED, bounds, compat_class, holds  # noqa: E402

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


def declared(crate, root, manifest):
    """crate's declarations, every target's, as (package, req, needed):
    needed where cargo resolves it for a lock whatever the features, which
    is neither an optional one nor, below the root, a dev one.  The root's
    are the manifest pac read rather than an index row."""
    if crate == root:
        with open(manifest, "rb") as f:
            doc = tomllib.load(f)
        out = []
        for t in [doc] + list((doc.get("target") or {}).values()):
            for kind in ("dependencies", "build-dependencies", "dev-dependencies"):
                for name, d in (t.get(kind) or {}).items():
                    d = {"version": d} if isinstance(d, str) else d
                    out.append((d.get("package") or name, d.get("version", "*"),
                                not d.get("optional")))
        return out
    j = run_query.index_line(*crate)
    if j is None:
        return None
    return [(d.get("package") or d["name"], d.get("req", "*"),
             not d.get("optional") and (d.get("kind") or "normal") != "dev")
            for d in j.get("deps") or []]


def undeclared(crate, children, ds):
    return ["%s %s -> %s %s is not declared" % (crate + c) for c in children
            if not any(t == c[0] and holds(c[1], bounds(req)) for t, req, _ in ds or [])]


def unmet(dropped, crates, edges, root, manifest):
    """what is wrong with the packages cargo drops, since cargo asks nothing
    of them: each needs an edge of the answer meeting every declaration that
    is not optional, each of its edges a declaration it meets, and none may
    be a second semver-compatible version, or a second owner of a `links`,
    beside another package of the answer"""
    out, kids = [], {}
    for p, c in edges:
        kids.setdefault(p, []).append(c)
    rows = {c: run_query.index_line(*c) for c in crates if c != root}
    for n, v in dropped:
        ds = declared((n, v), root, manifest)
        if ds is None:
            out.append("%s %s: not in the index" % (n, v))
            continue
        for target, req, needed in ds:
            if needed and not any(cn == target and holds(cv, bounds(req))
                                  for cn, cv in kids.get((n, v), [])):
                out.append("%s %s needs %s %s" % (n, v, target, req))
        out += undeclared((n, v), kids.get((n, v), []), ds)
        for m, w in crates:
            if m == n and w != v and compat_class(w) == compat_class(v):
                out.append("%s %s beside %s %s" % (n, v, m, w))
        links = (rows.get((n, v)) or {}).get("links")
        for c, j in rows.items():
            if links and c != (n, v) and (j or {}).get("links") == links:
                out.append("%s %s and %s %s both link %s" % (n, v, c[0], c[1], links))
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
    with open(manifest, "rb") as f:
        pkg = tomllib.load(f)["package"]
    root = (pkg["name"], pkg["version"])
    # an edge lost out of a package cargo keeps re-points a dependency where
    # the package still has one of that name; where it has none, cargo left
    # the declaration inactive, and the edge goes as a dropped package does
    repointed = [(s, c) for s, c in res["lost_edges"]
                 if s not in lost and any(p == s and d[0] == c[0] for p, d in te)]
    if res["added"] or res["added_edges"] or repointed:
        return "INVALID", "-", res
    res["unmet"] = unmet(lost, sorted(op), sorted(oe), root, manifest)
    for s, c in res["lost_edges"]:
        if s not in lost:
            res["unmet"] += undeclared(s, [c], declared(s, root, manifest))
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
