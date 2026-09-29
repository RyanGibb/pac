"""The shared reading of a manifest, where npm and Yarn Berry must both
accept an answer (READING=shared, as pac's --reading=shared reads it).

normalize() is Berry's normalizePackage (Configuration.ts:1915-2011): the
built-in packageExtensions matching the version add the dependencies and
peers the manifest lacks and set peer meta (lib/npm/berry-extensions.json,
the list @yarnpkg/extensions 2.0.6 ships, which pac reads too); and a
peerDependenciesMeta name with no peer is a peer on *.
The optional peer on its @types package Berry gives every other peer is
left out, as pac leaves it out: optional and on *, it never makes Berry
reject an answer.

split() is Berry's peer with default: a package depending and peering on
one name holds its own copy there only when its depender offers nothing,
so the name is a dependency where the answer gives the package a copy and
a peer where it does not.
"""
import json
import os
import sys

from tree import satisfies

READING = os.environ.get("READING") or "npm"
if READING not in ("npm", "shared"):
    sys.exit(f"READING={READING} is neither npm nor shared")
SHARED = READING == "shared"

with open(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                       "..", "..", "lib", "npm", "berry-extensions.json")) as f:
    EXT = [(d[:d.rindex("@")], d[d.rindex("@") + 1:], x) for d, x in json.load(f)]


def normalize(m, name, version, npm=False):
    """the manifest m of name@version as Berry reads it; for npm's check
    (npm), the dependencies the extensions add, and of the peers they add
    only those on a name the package depends on: npm asks nothing of a peer
    Berry adds, but where the package also depends on the name the answer
    reads it as a peer with default, and places the package in sight of
    what its depender offers"""
    m = dict(m)
    deps = dict(m.get("dependencies") or {})
    own = dict(m.get("peerDependencies") or {})
    peers = dict(own)
    meta = {k: dict(v) for k, v in (m.get("peerDependenciesMeta") or {}).items()
            if isinstance(v, dict)}
    for n, rg, x in EXT:
        if n != name or not satisfies(version, rg, "berry"):
            continue
        for k, v in (x.get("dependencies") or {}).items():
            deps.setdefault(k, v)
        for k, v in (x.get("peerDependencies") or {}).items():
            peers.setdefault(k, v)
        for k, v in (x.get("peerDependenciesMeta") or {}).items():
            meta.setdefault(k, {}).update(v)
    for k in meta:
        peers.setdefault(k, "*")
    if npm:
        named = set(deps) | set(m.get("optionalDependencies") or {})
        peers = {k: v for k, v in peers.items() if k in own or k in named}
        meta = {k: v for k, v in meta.items() if k in peers}
    m["dependencies"], m["peerDependencies"], m["peerDependenciesMeta"] = deps, peers, meta
    return m


def split(m, holds):
    """(dependencies, {peer: optional}, needed dependencies) of the
    normalized manifest m, given the names the answer gives its package a
    copy of"""
    opt = set(m.get("optionalDependencies") or {})
    deps = set(m.get("dependencies") or {}) | opt
    meta = m.get("peerDependenciesMeta") or {}
    peers = {p: bool((meta.get(p) or {}).get("optional")) for p in m.get("peerDependencies") or {}}
    both = deps & set(peers)
    for p in both:
        if p in holds:
            del peers[p]
        else:
            deps.discard(p)
    bundled = m.get("bundleDependencies") or m.get("bundledDependencies") or []
    needed = (set(m.get("dependencies") or {}) - opt - both
              - set(deps if bundled is True else bundled))
    needed |= {p for p in both if p in holds} - opt
    return deps, peers, needed
