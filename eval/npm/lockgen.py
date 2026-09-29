#!/usr/bin/env python3
"""Write pac's npm answer, which is a node_modules layout, out as a
lockfileVersion 3 package-lock.json, so npm can be asked to verify it.

Nothing is placed or searched for here: each "packages (N):" row of the
answer, "<lock path> <name>@<version>", becomes the lock entry at that
path.  Every other field is copied, not decided: version, resolved and
integrity come from the snapshot packument's own dist block, and the
dependency maps from that version's manifest, so the lock describes the
same packages our solver read.  An aliased entry (the key differs from the
registry name) carries "name", the way npm records one.

usage: lockgen.py <cache-dir> <pac output> <out package-lock.json>
       <root package.json>
Prints the paths of any entry whose manifest bundles dependencies, which
npm installs from the tarball whatever the lock says.
"""
import json
import re
import sys

from tree import entry, manifest, write_lock

ROW = re.compile(r"^  (node_modules/\S+) (\S+)$")


def main():
    cache, ans, dst, rootp = sys.argv[1:5]
    with open(rootp) as f:
        rm = json.load(f)
    head = {k: rm[k] for k in ("name", "version", "license", "dependencies",
                               "devDependencies", "optionalDependencies",
                               "peerDependencies") if rm.get(k)}
    pk = {"": head}
    section = False
    for line in open(ans):
        if line.startswith("packages ("):
            section = True
            continue
        if not line.startswith("  "):
            section = False
        m = ROW.match(line) if section else None
        if m:
            path, nv = m.group(1), m.group(2)
            name, version = nv.rsplit("@", 1)
            man = manifest(cache, name, version)
            pk[path] = entry(cache, name, version, path.rsplit("node_modules/", 1)[-1])
            if man.get("bundleDependencies") or man.get("bundledDependencies"):
                print(f"bundled {path}")
    write_lock(dst, pk)


if __name__ == "__main__":
    main()
