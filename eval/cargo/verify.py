#!/usr/bin/env python3
"""Ask cargo whether OUR Cargo resolution is a resolution by cargo's own
rules, rather than whether it is the one cargo would have picked.
compare.py asks the second question over run_goal.py's dumps; this asks
the first, and a goal can fail that and pass this.

The check writes our answer out as the goal's Cargo.lock (mklock.py),
hands that to cargo, and lets cargo re-resolve *freely* from it -- the
lock as a starting point rather than as a verdict -- then asks two things
of what comes back:

  1. nothing lost: every (name, version) we picked is still there.  This
     is the validity condition proper.  Cargo's resolver takes the
     versions already in the lock as locked preferences: it keeps each
     one wherever the constraints still admit it and reaches for a
     different version only where they do not.  So a pick that survives
     survived a resolver that was free to overrule it, and one that is
     not a resolution -- a version violating some req, a node nothing
     needs -- is changed or dropped and shows up as a loss.

  2. every addition is explicable: each package cargo adds must be one
     our feature resolution legitimately excluded rather than one we
     missed.  See explain() below; the test is run over the index, not
     over cargo's report.

Why not `--locked`, which asks cargo to accept the lock unchanged: a
Cargo.lock is the feature-INDEPENDENT resolve.  Cargo builds it with
every optional dependency treated as activatable, because one lock has to
serve every future feature selection, so it must list optionals that no
feature in play turns on.  Our answer is feature-resolved and legitimately
omits exactly those.  `--locked` therefore reports "the lock needs to be
updated" about that modelling difference, not about an error: it scored
5/28, and on all 23 failures cargo's own lock was a strict superset of
ours -- never a changed version, only added optionals, down to single
nodes like `rustc-std-workspace-core` under `cfg-if`.  Three of them
(bitflags, log, serde_json) had a package set identical to cargo's and
failed on a missing *edge* alone.  Asking the superset question instead
puts the modelling difference where it belongs, in condition 2, and
leaves condition 1 asking about validity.

`cargo fetch` is the repair: it resolves, writes the repaired lock, and
downloads the bodies of what it resolved, which is all three things this
check needs from cargo and nothing else.  `cargo metadata` would also
re-resolve, but it reports the feature-resolved view and insists on full
manifests to do it, while the artifact being compared here is a lock --
so the lock cargo writes is read back directly, and the comparison is
lock against lock.  `cargo fetch` also takes no `--features`, which is
the honest signature for a question the lock answers feature-
independently.

`--offline` keeps the measured pass reproducible rather than merely
disciplined: with no network reachable cargo cannot consult the live
crates.io index even if the [source] replacement were ever to go missing
again, so the universe it answers about is structurally the snapshot's.
It costs the bodies having to be in CARGO_HOME already, which is what
warm.sh puts there in one online pass -- the same repair, unrestricted --
and a run whose cache is short of one is reported NOCACHE, never INVALID.

Offline also narrows what the resolver may pick to what is cached, which
would matter if it could hide a loss.  It cannot, given a warm pass over
the same goal: the warm pass ran this identical resolution online and
downloaded whatever it chose, overrules included, so every version the
offline pass would choose is present, and dropping candidates it would
have rejected anyway cannot change the outcome.  A goal whose warm pass
failed is not scored.

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
import tomllib

# How the offline repair distinguishes a cache that is short of something
# from an answer that is wrong.  Under repair a wrong answer does not
# error at all -- cargo fixes it and the fix shows up as a loss -- so a
# non-zero exit is a cargo that could not run: most often a body or index
# row it may not fetch, which it reports with "note: offline mode (via
# `--offline`) can sometimes cause surprising resolution failures".  Do
# NOT widen this to "--offline": that string is in the *help* line of
# every offline message, genuine failures included.
COLD = re.compile(r"offline mode|failed to download|not yet downloaded", re.I)

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import run_goal  # noqa: E402


def cargo_repair(workdir, offline):
    # `cargo fetch` with no --locked: resolve from the lock we wrote,
    # keeping its versions wherever they are still admissible, and leave
    # the repaired lock behind.
    cmd = ["cargo", "fetch", "--manifest-path", workdir + "/Cargo.toml"]
    if offline:
        cmd += ["--offline"]
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


def cargo_strict(workdir, offline):
    """The question this check used to ask, kept as a second gate: does
    cargo accept our lock unchanged?  It is the right question exactly
    when our answer is meant to BE a Cargo.lock -- the all-features
    resolve -- and it fails today because we model the feature-resolved
    view instead.  It is reported, never scored, so the disagreement
    stays visible rather than being explained away: when the model
    changes it should go green on its own, and if it does not, that is a
    finding.  Kept because removing it once already hid a real modelling
    gap for a day."""
    cmd = ["cargo", "metadata", "--format-version=1", "--locked",
           "--manifest-path", workdir + "/Cargo.toml"]
    if offline:
        cmd += ["--offline"]
    env = dict(os.environ)
    env["CARGO_HOME"] = run_goal.CARGO_HOME
    try:
        p = subprocess.run(cmd, capture_output=True, text=True,
                           timeout=600, env=env)
    except subprocess.TimeoutExpired:
        return None
    return p.returncode


def read_lock(path):
    """The repaired lock as (packages, edges).  Its `dependencies` lists
    are the feature-independent edge set -- the thing our answer cannot
    carry and the reason the old check failed -- named either "crate" or
    "crate version", the bare form being used while one version of a name
    is in the lock."""
    with open(path, "rb") as f:
        doc = tomllib.load(f)
    pkgs = [(p["name"], p["version"]) for p in doc.get("package", [])]
    by_name = {}
    for n, v in pkgs:
        by_name.setdefault(n, []).append(v)
    edges = []
    for p in doc.get("package", []):
        for d in p.get("dependencies", []):
            parts = d.split()
            name = parts[0]
            if len(parts) > 1:
                ver = parts[1]
            else:
                cands = by_name.get(name, [])
                if len(cands) != 1:
                    raise RuntimeError(f"ambiguous lock dependency {d!r}")
                ver = cands[0]
            edges.append(((p["name"], p["version"]), (name, ver)))
    return pkgs, edges


def parse_version(s):
    core, pre = s.split("+", 1)[0], ""
    if "-" in core:
        core, pre = core.split("-", 1)
    nums = [int(x) for x in core.split(".")]
    return nums, tuple(pre.split(".")) if pre else ()


def vkey(nums, pre):
    # a pre-release sorts below the release it belongs to, and its dotted
    # identifiers compare numerically where both are numeric
    ids = tuple((0, int(i), "") if i.isdigit() else (1, 0, i) for i in pre)
    return (tuple(nums + [0] * (3 - len(nums)))[:3], 0 if pre else 1, ids)


def req_matches(req, version):
    """Whether a crates.io dependency requirement admits a version, by
    cargo's rules.

    Needed because a crate may declare the same crate several times under
    different aliases -- actix-tls carries tokio-rustls at ^0.23, ^0.24,
    ^0.25 and ^0.26 at once -- so a lock edge cannot be attributed to a
    declaration by name: only the requirement says which of them it came
    from, and with it the optionality and the features that would
    activate it.
    """
    cand = parse_version(version)
    bounds = []
    for raw in req.split(","):
        c = raw.strip()
        if not c or c == "*":
            continue
        op = "^"
        for prefix in (">=", "<=", "^", "~", "=", ">", "<"):
            if c.startswith(prefix):
                op, c = prefix, c[len(prefix):].strip()
                break
        if c.endswith("*"):
            # 1.* admits every 1.x and 1.2.* every 1.2.x, which is what ~
            # says of the part given
            c, op = c.rstrip("*").rstrip("."), "~"
            if not c:
                continue
        nums, pre = parse_version(c)
        bounds.append((op, nums, pre))
        n = len(nums)
        lo = vkey(nums, pre)
        if op in ("^", "~") or (op == "=" and n < 3):
            if op == "~" and n >= 2:
                hi = [nums[0], nums[1] + 1, 0]
            elif op == "=" and n == 2:
                hi = [nums[0], nums[1] + 1, 0]
            elif n == 1 or nums[0] > 0:
                hi = [nums[0] + 1, 0, 0]
            elif len(nums) == 2 or nums[1] > 0:
                hi = [0, nums[1] + 1, 0]
            else:
                hi = [0, 0, nums[2] + 1]
            ok = lo <= vkey(*cand) < vkey(hi, ())
        elif op == "=":
            ok = vkey(*cand) == lo
        elif op == ">":
            ok = (vkey(*cand) > lo if n == 3
                  else vkey(*cand) >= vkey(nums[:-1] + [nums[-1] + 1], ()))
        elif op == ">=":
            ok = vkey(*cand) >= lo
        elif op == "<":
            ok = vkey(*cand) < lo
        else:
            ok = (vkey(*cand) <= lo if n == 3
                  else vkey(*cand) < vkey(nums[:-1] + [nums[-1] + 1], ()))
        if not ok:
            return False
    if cand[1]:
        # a pre-release is only admitted by a bound naming that same
        # major.minor.patch with a pre-release of its own
        return any(len(nums) == 3 and pre and nums == cand[0]
                   for _op, nums, pre in bounds)
    return True


def merged_features(row):
    # features2 carries the v2-schema dep:/dep?/ entries the index moved
    # out of features for old-cargo compatibility; a key in both is one
    # feature, as manifest.jq and cargo_parse.ml's feature_table agree.
    out = {}
    for table in (row.get("features") or {}, row.get("features2") or {}):
        for k, v in table.items():
            out.setdefault(k, []).extend(v)
    return out


def declarations(row, is_root):
    """The dependency rows of one index entry that can put an edge in a
    lock.  A non-root package's dev-dependencies cannot: cargo resolves
    those only for workspace members, which is also slotActive's rule, so
    counting them here would call an edge mandatory on the strength of a
    row that never applies."""
    for d in row.get("deps") or []:
        if d.get("kind") == "dev" and not is_root:
            continue
        yield d


def activating_features(row, alias):
    """The features of `row` whose being enabled would pull in the
    optional dependency declared under `alias`: the implicit feature of
    the same name, any feature listing it bare (the pre-`dep:` spelling,
    still what most crates write -- serde's `derive = ["serde_derive"]`),
    any listing `dep:alias`, and any listing `alias/f` -- but not
    `alias?/f`, which is cargo's weak form and activates the dependency
    only if something else already has."""
    acc = {alias}
    for fname, entries in merged_features(row).items():
        for e in entries:
            if e in (alias, "dep:" + alias):
                acc.add(fname)
            elif "/" in e and not e.split("/")[0].endswith("?"):
                if e.split("/")[0].removeprefix("dep:") == alias:
                    acc.add(fname)
    return acc


def explain(ours, our_feats, root, pkgs, edges):
    """Condition 2, decided over the index rather than over what cargo
    reported: is every package cargo added one our feature resolution
    legitimately excluded?

    A dependency row that is not `optional` is required under every
    feature selection there is, so the packages reachable from the root
    through such rows alone are in every resolution of this goal, ours
    included.  Compute that mandatory closure over the repaired lock's
    edges and require it to add nothing: an addition inside it is a
    dependency we simply missed, which is exactly what the apt check
    catches for debian, and an addition outside it sits behind at least
    one optional row, which is the lock's feature-independence and not an
    error.

    That much is independent of our feature model.  The second half is
    not: for an addition sitting behind an optional row declared by a
    package in OUR answer, check that none of the features that would
    activate that row is one our answer reports enabled on that package.
    (That set need not be closed under the feature table: what our answer
    reports is already the closure, so a feature reached only through
    another feature is in it by name.)
    It catches an answer inconsistent with the features it claims -- a
    feature enabled whose `dep:` we left out -- but it takes our feature
    selection as given, so it cannot tell a correctly unactivated
    optional from one our feature resolution wrongly failed to activate.
    Deciding that independently would mean re-implementing the feature
    resolution under test.
    """
    rows = {}

    def row_of(nv):
        if nv not in rows:
            rows[nv] = run_goal.index_line(*nv) or {}
        return rows[nv]

    added = {p for p in pkgs if p not in ours}
    kids = {}
    for q, p in edges:
        kids.setdefault(q, []).append(p)

    def decls_for(q, p):
        # by requirement as well as by name: the same crate under two
        # aliases is two declarations with two optionalities and two sets
        # of activating features, and only the requirement says which one
        # this edge came from
        named = [d for d in declarations(row_of(q), q == root)
                 if (d.get("package") or d["name"]) == p[0]]
        matched = [d for d in named if req_matches(d["req"], p[1])]
        return matched or named

    ambiguous = []
    mandatory = set()
    stack = [root]
    seen = {root}
    while stack:
        q = stack.pop()
        for p in kids.get(q, ()):
            ds = decls_for(q, p)
            opts = {bool(d.get("optional")) for d in ds}
            if len(opts) > 1:
                # two rows for this crate that both admit this version,
                # optional in one and not in the other -- usually an
                # optional feature dependency the crate also dev-depends
                # on, or serde's cfg(any()) weld.  The requirement cannot
                # separate them, so take the stricter reading and call the
                # edge mandatory: that can only make an addition harder to
                # explain, never easier.  Counted so it can be looked at.
                ambiguous.append((q, p))
            if not ds or False in opts:
                mandatory.add(p)
                if p not in seen:
                    seen.add(p)
                    stack.append(p)

    missed = sorted(mandatory & added)
    activated = []
    for q, p in edges:
        if q not in ours or p not in added:
            continue
        on = set(our_feats.get("%s@%s" % q, ()))
        for d in decls_for(q, p):
            if d.get("optional") and activating_features(row_of(q), d["name"]) & on:
                activated.append((q, p, d["name"]))
    return missed, sorted(set(activated)), sorted(set(ambiguous))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("crate")
    ap.add_argument("--features", default=None)
    ap.add_argument("--out", default=None)
    ap.add_argument("--warm", action="store_true",
                    help="online pass: run the same repair with the "
                         "network reachable, so the measured pass can run "
                         "--offline, instead of scoring")
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
    import shutil as _sh
    _sh.copy(lock, lock + ".ours")

    rc, msg, wall = cargo_repair(workdir, offline=not args.warm)
    ours = {(n, v) for n, v in pac["crates"]}
    lost, missed, activated, ambiguous, added = [], [], [], [], []
    if args.warm:
        v = "WARMED" if rc == 0 else "WARM-FAILED"
    elif rc != 0:
        # under repair a wrong answer is repaired rather than refused, so
        # a non-zero exit is cargo unable to run at all; only then can an
        # incomplete cache be the reason
        v = "NOCACHE" if COLD.search(msg or "") else "INVALID"
    else:
        pkgs, edges = read_lock(lock)
        theirs = set(pkgs)
        lost = sorted(ours - theirs)
        added = sorted(theirs - ours)
        missed, activated, ambiguous = explain(
            ours, pac["feats"], (root_name, root_version), pkgs, edges)
        v = "VALID" if not (lost or missed or activated) else "INVALID"
    strict = None
    if not args.warm:
        # the lock rewrites itself under repair, so ask the strict
        # question against a pristine copy of what we wrote
        import shutil
        keep = lock + ".ours"
        if os.path.exists(keep):
            shutil.copy(keep, lock)
        strict = cargo_strict(workdir, offline=True)
    detail = ""
    if not args.warm and rc == 0:
        detail = " lost=%d added=%d unexplained=%d" % (
            len(lost), len(added), len(missed) + len(activated))
        if ambiguous:
            detail += " ambig=%d" % len(ambiguous)
    if strict is not None:
        detail += " strict=%s" % ("ok" if strict == 0 else "no")
    print("%-24s n=%-4d rc=%-4s %-11s%s %.1fs" % (
        args.crate, len(pac["crates"]), rc, v, detail, wall))
    for label, items in (("lost", lost), ("missed", missed),
                         ("activated", activated), ("ambiguous", ambiguous)):
        for it in items[:12]:
            print("    | %s %s" % (label, it))
    if rc != 0:
        for line in msg.strip().splitlines()[:12]:
            print("    | " + line)
    if args.out:
        os.makedirs(os.path.dirname(args.out), exist_ok=True)
        with open(args.out, "w") as f:
            json.dump({"crate": args.crate, "features": feats, "rc": rc,
                       "verdict": v, "valid": v == "VALID",
                       "n": len(pac["crates"]), "root_rust_version": rustv,
                       "lost": lost, "added": added, "missed": missed,
                       "activated": activated, "ambiguous": ambiguous,
                       "cargo": msg}, f, indent=1)
    return 0


if __name__ == "__main__":
    sys.exit(main())
