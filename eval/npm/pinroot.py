#!/usr/bin/env python3
"""Re-ask a query with npm's own picks forced, on both sides at once.

This is the preference-vs-instance test.  The forcing is a root
`overrides` block naming each version npm chose and we did not, which is
the one knob both sides read the same way: npm applies a flat override to
every edge in the tree, and our parser's overrides_of hands the same flat
table to the calculus, where it replaces the range of every row naming
that package.  A root dependency would not do -- our solver resolves each
slot independently, so pinning the root's slot leaves every other slot
free.

Because the block goes into the one manifest both the wrapper packument
and the package.json are written from, the two sides are still asked the
same question.  If the answers then coincide, npm's resolution was one our
instance already admitted and only our preference ordering ranked it
second.  If our side is unsatisfiable or still differs, the instance
itself differs.

usage: pinroot.py <cache-dir> <work-dir> <name@version>...
prints: the pinned root's package name
"""
import json
import os
import sys


def main():
    cache, work = sys.argv[1], sys.argv[2]
    with open(os.path.join(work, "package.json")) as f:
        manifest = json.load(f)
    ovr = manifest.setdefault("overrides", {})
    for spec in sys.argv[3:]:
        name, _, ver = spec.rpartition("@")
        ovr[name] = ver
    # a distinct root name so the unpinned baseline packument survives
    manifest["name"] += "-pin"
    packument = {
        "name": manifest["name"],
        "dist-tags": {"latest": "1.0.0"},
        "versions": {"1.0.0": manifest},
    }
    p = os.path.join(cache, manifest["name"] + ".json")
    if os.path.islink(p) or os.path.exists(p):
        os.unlink(p)
    with open(p, "w") as f:
        json.dump(packument, f)
    with open(os.path.join(work, "package.json"), "w") as f:
        json.dump(manifest, f, indent=2)
    print(manifest["name"])


if __name__ == "__main__":
    main()
