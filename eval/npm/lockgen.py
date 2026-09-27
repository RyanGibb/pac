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
import base64
import json
import os
import re
import sys

ROW = re.compile(r"^  (node_modules/\S+) (\S+)$")
COPY = ["dependencies", "optionalDependencies", "peerDependencies",
        "peerDependenciesMeta", "bin", "engines", "os", "cpu", "libc",
        "funding", "deprecated", "hasInstallScript"]
packuments = {}


def manifest(cache, name, version):
    if name not in packuments:
        with open(os.path.join(cache, name.replace("/", "%2F") + ".json")) as f:
            packuments[name] = json.load(f)
    v = packuments[name]["versions"].get(version)
    if v is None:
        raise RuntimeError(f"{name}@{version} not in the snapshot packument")
    return v


def entry(m, name, version, key):
    e = {"version": version}
    dist = m.get("dist") or {}
    if dist.get("tarball"):
        e["resolved"] = dist["tarball"]
    if dist.get("integrity"):
        e["integrity"] = dist["integrity"]
    elif dist.get("shasum"):
        # npm's own rendering of a pre-integrity dist for the lockfile
        e["integrity"] = "sha1-" + base64.b64encode(bytes.fromhex(dist["shasum"])).decode()
    if key != name:
        e["name"] = name
    if m.get("license"):
        e["license"] = m["license"]
    for k in COPY:
        if m.get(k):
            e[k] = m[k]
    return e


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
            pk[path] = entry(man, name, version, path.rsplit("node_modules/", 1)[-1])
            if man.get("bundleDependencies") or man.get("bundledDependencies"):
                print(f"bundled {path}")
    lock = {
        # npm names a nameless project by its directory
        "name": head.get("name", os.path.basename(os.path.dirname(os.path.abspath(dst)))),
        "version": head.get("version", "1.0.0"),
        "lockfileVersion": 3,
        "requires": True,
        "packages": pk,
    }
    with open(dst, "w") as f:
        json.dump(lock, f, indent=2)
        f.write("\n")


if __name__ == "__main__":
    main()
