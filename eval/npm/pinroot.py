#!/usr/bin/env python3
"""Force npm's own answer on our side, one edge at a time.

This is the preference-vs-instance test.  npm may hold two versions of one
name, so a pin keyed by name alone -- a flat root `overrides` entry -- would
force one of them on every edge and ask a different question from the one
npm answered.  The pin is instead the edge itself: each (requirer name,
requirer version, directory) npm resolved has its spec rewritten, in the
requirer's own manifest, to the exact version npm put there.  The requirer
is a packument version in a copy of the cache, or the root package.json.

Each rewritten spec admits a subset of what the original one did and
still admits npm's pick, so the pins only narrow our instance and npm's
answer satisfies all of them: npm need not be re-asked, and our pinned
answer is compared with its original lock.  If they coincide, npm's
resolution was one our instance already admitted and only our preference
ordering ranked it second; otherwise the instance itself differs.

A slot npm filled with two versions (one requirer version placed twice
and resolved differently) is pinned to the union of the two, which our
side, holding one node per version, can satisfy with only one of them.

usage: pinroot.py <npm lock> <cache> <pinned cache> <package.json>
"""
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from edges import ROOT, lock_sets  # noqa: E402
from tree import escape  # noqa: E402

# every manifest field an edge can come from; devDependencies only at the
# root, where npm installs them
FIELDS = ["dependencies", "optionalDependencies", "peerDependencies"]


def spec(dirname, name, versions):
    exact = " || ".join(sorted(versions))
    return exact if name == dirname else "npm:%s@%s" % (name, exact)


def rewrite(manifest, slots, fields):
    n = 0
    for d, (name, versions) in slots.items():
        for f in fields:
            if d in manifest.get(f, {}):
                manifest[f][d] = spec(d, name, versions)
                n += 1
    return n


def main():
    lockp, cache, pinned, rootp = sys.argv[1:5]
    with open(lockp) as f:
        lock = json.load(f)
    # raw edges, not --peer-parent's: a peer's pin belongs in the declarer's
    # manifest, which is where the raw edge leaves from
    _, edges, _, bundled = lock_sets(lock, False)

    pins = {}
    for rn, rv, d, pn, pv in edges - bundled:
        slot = pins.setdefault((rn, rv), {}).setdefault(d, (pn, set()))
        slot[1].add(pv)
    split = sum(len(s[1]) > 1 for r in pins.values() for s in r.values())

    with open(rootp) as f:
        root = json.load(f)
    n = rewrite(root, pins.pop(ROOT, {}), FIELDS + ["devDependencies"])
    with open(rootp, "w") as f:
        json.dump(root, f, indent=2)

    byname = {}
    for (rn, rv), slots in pins.items():
        byname.setdefault(escape(rn), {})[rv] = slots
    os.makedirs(pinned, exist_ok=True)
    for e in os.listdir(cache):
        if e[:-5] not in byname:
            os.symlink(os.path.abspath(os.path.join(cache, e)), os.path.join(pinned, e))
    for rn, byver in byname.items():
        with open(os.path.join(cache, rn + ".json")) as f:
            pk = json.load(f)
        for rv, slots in byver.items():
            n += rewrite(pk["versions"][rv], slots, FIELDS)
        with open(os.path.join(pinned, rn + ".json"), "w") as f:
            json.dump(pk, f)

    print("pinned %d specs, %d slots npm filled twice" % (n, split))


if __name__ == "__main__":
    main()
