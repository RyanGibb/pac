"""The common core's reading of a manifest, where npm and Yarn Berry must
both accept an answer (PAC_NPM_CORE=1, as pac reads it).

normalize() is Berry's normalizePackage (Configuration.ts:1915-2011): the
built-in packageExtensions matching the version add the dependencies and
peers the manifest lacks and set peer meta (berry-extensions.json, the
list @yarnpkg/extensions 2.0.6 ships, from which lib/npm/berry_ext.ml is
generated); and a peerDependenciesMeta name with no peer is a peer on *.
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
import re

CORE = os.environ.get("PAC_NPM_CORE") == "1"

with open(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                       "berry-extensions.json")) as f:
    EXT = [(d[:d.rindex("@")], d[d.rindex("@") + 1:], x) for d, x in json.load(f)]


def _ver(s):
    m = re.match(r"^\s*v?(\d+)(?:\.(\d+|[xX*]))?(?:\.(\d+|[xX*]))?(?:-([0-9A-Za-z.-]+))?", s)
    if not m:
        return None
    parts = [m.group(1), m.group(2), m.group(3)]
    return parts, m.group(4)


def _key(parts, pre):
    return tuple(int(p) if p and p.isdigit() else 0 for p in parts) + ((0, pre) if pre else (1, ""),)


def _cmp_one(v, op, c):
    parts, pre = c
    vk = _key(*v)
    wild = [p is None or not p.isdigit() for p in parts]
    lo = _key(parts, pre)
    if op in ("", "="):
        if any(wild):
            n = wild.index(True)
            return vk[:n] == lo[:n]
        return vk == lo
    if op == ">=":
        return vk >= lo
    if op == ">":
        return vk > lo
    if op == "<=":
        return vk <= lo
    if op == "<":
        return vk < _key(parts, pre) if not any(wild) else vk[:wild.index(True)] < lo[:wild.index(True)]
    if op in ("^", "~"):
        if vk < lo:
            return False
        n = [int(p) if p and p.isdigit() else 0 for p in parts]
        if op == "~" or (n[0] == 0 and n[1] != 0 and op == "^"):
            hi = (n[0], n[1] + 1, 0) if op == "~" or n[0] == 0 else (n[0] + 1, 0, 0)
        elif op == "^" and n[0] == 0 and n[1] == 0:
            hi = (0, 0, n[2] + 1)
        else:
            hi = (n[0] + 1, 0, 0)
        return vk[:3] < hi
    return False


def satisfies(version, rng):
    """semver's satisfies with prereleases admitted, as Berry's
    satisfiesWithPrereleases reads a packageExtensions key; enough for the
    shapes that list uses"""
    v = _ver(version)
    if v is None:
        return False
    for alt in rng.split("||"):
        alt = alt.strip()
        if alt in ("", "*", "x"):
            return True
        ok = True
        for tok in re.findall(r"(<=|>=|<|>|=|\^|~)?\s*([0-9vxX*][^\s]*)", alt):
            c = _ver(tok[1])
            if c is None or not _cmp_one(v, tok[0], c):
                ok = False
                break
        if ok:
            return True
    return False


def normalize(m, name, version, npm=False):
    """the manifest m of name@version as Berry reads it; for npm's check
    (npm) only the dependencies the extensions add, since npm itself asks
    nothing of a peer Berry adds, and our answer gives such a dependency a
    copy that npm then finds"""
    m = dict(m)
    deps = dict(m.get("dependencies") or {})
    peers = dict(m.get("peerDependencies") or {})
    meta = {k: dict(v) for k, v in (m.get("peerDependenciesMeta") or {}).items()
            if isinstance(v, dict)}
    for n, rg, x in EXT:
        if n != name or not satisfies(version, rg):
            continue
        for k, v in (x.get("dependencies") or {}).items():
            deps.setdefault(k, v)
        if npm:
            continue
        for k, v in (x.get("peerDependencies") or {}).items():
            peers.setdefault(k, v)
        for k, v in (x.get("peerDependenciesMeta") or {}).items():
            meta.setdefault(k, {}).update(v)
    if npm:
        m["dependencies"] = deps
        return m
    for k in meta:
        peers.setdefault(k, "*")
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
