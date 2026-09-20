#!/usr/bin/env python3
"""Mint the per-goal root both sides are asked about.

The root is a wrapper package depending on nothing but the goal, pinned
to one exact version.  Pinning is what makes the two sides answer the
same question at the root: a range would hand npm's pickManifest its
dist-tag preference and hand our solver its newest-satisfying rule, and
any disagreement there would be a root-only artefact rather than
something the sweep is measuring.

Two files come out of one manifest so they cannot drift:

  <cache>/pac-root-<goal>.json   a one-version packument, which is what
                                 `pac npm` reads as its root package
  <work>/package.json            the same manifest, which is what npm
                                 reads as the project being installed

With no version given the pin is the snapshot's dist-tags.latest;
--nth k pins the k'th newest published release instead, which is how
seed.sh walks back from a latest neither side can answer.

usage: mkroot.py <cache-dir> <goal> <work-dir> [version | --nth K]
prints: <root-name> <root-version> <goal-version>
"""
import json
import os
import re
import sys


def escape(name):
    return name.replace("/", "%2F")


def key(v):
    m = re.match(r"^(\d+)\.(\d+)\.(\d+)", v)
    return tuple(int(x) for x in m.groups()) if m else (-1, -1, -1)


def main():
    cache, goal, work = sys.argv[1], sys.argv[2], sys.argv[3]
    arg = sys.argv[4] if len(sys.argv) > 4 else None
    with open(os.path.join(cache, escape(goal) + ".json")) as f:
        pk = json.load(f)

    if arg == "--nth":
        # newest first, prereleases left out: a prerelease root would ask
        # both sides a question about prerelease admission rather than
        # about resolution
        rel = sorted(
            (v for v in pk["versions"] if "-" not in v), key=key, reverse=True
        )
        n = int(sys.argv[5])
        if n >= len(rel):
            sys.exit(f"{goal}: only {len(rel)} releases")
        pin = rel[n]
    elif arg:
        pin = arg
    else:
        pin = pk["dist-tags"]["latest"]
    if pin not in pk["versions"]:
        sys.exit(f"{goal}: {pin} is not published")

    name = "pac-root-" + re.sub(r"[@/]", lambda m: "-" if m.group() == "/" else "",
                                goal)
    manifest = {
        "name": name,
        "version": "1.0.0",
        "private": True,
        "dependencies": {goal: pin},
    }
    packument = {
        "name": name,
        "dist-tags": {"latest": "1.0.0"},
        "versions": {"1.0.0": manifest},
    }
    os.makedirs(work, exist_ok=True)
    # a symlink farm is the cache, so a stale real file must go first
    p = os.path.join(cache, name + ".json")
    if os.path.islink(p) or os.path.exists(p):
        os.unlink(p)
    with open(p, "w") as f:
        json.dump(packument, f)
    with open(os.path.join(work, "package.json"), "w") as f:
        json.dump(manifest, f, indent=2)
    print(name, "1.0.0", pin)


if __name__ == "__main__":
    main()
