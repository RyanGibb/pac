#!/usr/bin/env python3
"""Classify each divergent edge as a preference gap or an instance gap.

The question a divergence poses is whether npm's answer was one our
instance already admitted -- in which case only our preference ordering
ranked it second -- or one our instance forbids outright.  For an npm-only
edge (R wants directory d, npm resolved it to V) that is two tests:

  range   does V satisfy the range R's manifest declares for d?  npm chose
          V so it satisfies under npm's semver, and the check runs against
          npm's own bundled semver, so a failure here means our reading of
          the requirer's row differs from npm's -- an alias or an override
          read differently, or the edge attributed to the wrong requirer --
          and is not a preference at all.
  gate    does V's manifest pass the gates our frontend applies at its
          hardcoded host (node 22.0.0, npm 10.0.0, linux/x64/glibc)?
          A failure here would be our instance being strictly smaller
          than npm's.

range and gate both pass  ->  preference gap
gate fails                ->  instance gap (gate)
range fails               ->  instance gap (row read differently)

The gate test is now a tripwire rather than a classification: our
frontend applies no engines gate (dropped in 68d24de) and no
os/cpu/libc gate (dropped when npm's resolution became
platform-independent), so it reads the manifests and not our instance.
A "gate" verdict today means either a regression or a version the
snapshot simply lacks.

usage: verdict.py <run-dir> <goal> <out-prefix>
"""
import json
import os
import shutil
import subprocess
import sys


def resolve_semver():
    """npm's *bundled* semver, wherever this machine keeps it.

    It has to be npm's own copy rather than any semver on the module path:
    the whole point of the range test is to ask npm's reading of the range,
    so a differently versioned semver would answer a question we are not
    asking.  $SEMVER overrides for a layout none of the probes find; the
    bare name is the last resort, correct when npm's copy is reachable by
    node's ordinary resolution (NODE_PATH) and wrong-but-visible otherwise.
    """
    env = os.environ.get("SEMVER")
    if env:
        return env
    cands = []
    npm = shutil.which("npm")
    if npm:
        # the CLI is a symlink into npm's own lib/node_modules on Nix and on
        # nvm alike, where `npm root -g` may name a node without npm beside it
        real = os.path.realpath(npm)
        here = os.path.dirname(real)
        while here != "/":
            if os.path.basename(here) == "npm":
                cands.append(os.path.join(here, "node_modules", "semver"))
                break
            here = os.path.dirname(here)
        for arg in (["root", "-g"], ["prefix", "-g"]):
            try:
                out = subprocess.run(["npm"] + arg, capture_output=True,
                                     text=True, timeout=30)
            except (OSError, subprocess.SubprocessError):
                continue
            root = out.stdout.strip()
            if out.returncode != 0 or not root:
                continue
            if arg[0] == "prefix":
                root = os.path.join(root, "lib", "node_modules")
            cands.append(os.path.join(root, "npm", "node_modules", "semver"))
    cands.append("/run/current-system/sw/lib/node_modules/npm/node_modules/semver")
    for c in cands:
        if os.path.isdir(c):
            return c
    return "semver"


SEMVER = resolve_semver()
HOST = {"node": "22.0.0", "npm": "10.0.0", "os": "linux", "cpu": "x64",
        "libc": "glibc"}


def escape(name):
    return name.replace("/", "%2F")


class Snapshot:
    def __init__(self, cache):
        self.cache, self.cached = cache, {}

    def manifest(self, name, ver):
        if name not in self.cached:
            try:
                with open(os.path.join(self.cache, escape(name) + ".json")) as f:
                    self.cached[name] = json.load(f)["versions"]
            except (OSError, KeyError, ValueError):
                self.cached[name] = {}
        return self.cached[name].get(ver)


def listed(m, field, host):
    l = m.get(field)
    if isinstance(l, str):
        l = [l]
    if not l or l == ["any"]:
        return True
    if any(x[1:] == host for x in l if x.startswith("!")):
        return False
    pos = [x for x in l if not x.startswith("!")]
    return not pos or host in pos


def declared(m, d):
    """the range the manifest declares for directory d"""
    for field in ("optionalDependencies", "dependencies", "peerDependencies"):
        spec = m.get(field, {}).get(d)
        if isinstance(spec, str):
            if spec.startswith("npm:"):
                body = spec[4:]
                i = max((j for j in range(1, len(body)) if body[j] == "@"),
                        default=-1)
                return body[i + 1:] if i >= 0 else "*"
            return spec
    return None


def satisfies(pairs):
    """npm's own semver, asked in one batch"""
    if not pairs:
        return {}
    js = (
        "const s=require(%s);"
        "console.log(JSON.stringify(JSON.parse(process.argv[1])"
        ".map(([v,r])=>{try{return s.satisfies(v,r)}catch(e){return null}})))"
        % json.dumps(SEMVER)
    )
    out = subprocess.run(
        ["node", "-e", js, json.dumps(pairs)],
        capture_output=True, text=True, check=True,
    )
    return dict(zip(map(tuple, pairs), json.loads(out.stdout)))


def main():
    run, goal, prefix = sys.argv[1], sys.argv[2], sys.argv[3]
    snap = Snapshot(os.path.join(run, "cache"))

    rows, pairs = [], []
    with open(prefix + ".edges.npmonly") as f:
        for line in f:
            rn, rv, d, vn, vv = line.rstrip("\n").split("\t")
            rm, vm = snap.manifest(rn, rv), snap.manifest(vn, vv)
            rg = declared(rm, d) if rm else None
            eng = (vm or {}).get("engines", {})
            eng = {k: v for k, v in eng.items()
                   if k in ("node", "npm") and isinstance(v, str)}
            rows.append((rn, rv, d, vn, vv, rg, vm, eng))
            if rg is not None:
                pairs.append([vv, rg])
            pairs += [[HOST[k], v] for k, v in eng.items()]
    sat = satisfies(pairs)

    counts, lines = {}, []
    for rn, rv, d, vn, vv, rg, vm, eng in rows:
        if vm is None:
            why = "instance gap (gate): version absent from snapshot"
        elif not all(listed(vm, f, HOST[f]) for f in ("os", "cpu", "libc")):
            why = "instance gap (gate): os/cpu/libc"
        elif not all(sat[(HOST[k], v)] for k, v in eng.items()):
            why = "instance gap (gate): engines"
        elif rg is None:
            why = "unclassified: requirer's row not found"
        elif sat[(vv, rg)] is not True:
            why = "instance gap: row read differently"
        else:
            why = "preference gap"
        counts[why] = counts.get(why, 0) + 1
        lines.append("%s\t%s %s -> %s = %s@%s\tdeclared %s" %
                     (why, rn, rv, d, vn, vv, rg))

    with open(prefix + ".verdict", "w") as f:
        f.write("\n".join(sorted(lines)) + ("\n" if lines else ""))
    print("%-24s %s" % (goal, json.dumps(counts, sort_keys=True)))


if __name__ == "__main__":
    main()
