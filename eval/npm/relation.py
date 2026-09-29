#!/usr/bin/env python3
"""Whether a package-lock.json holds pac's answer: every edge of the answer,
looked up from where its requirer sits, links followed as require()
resolves from a realpath, lands on the copy the answer chose; a peer of a
declarer the requirer requires is looked up from the declarer, as npm
resolves one (arborist edge.js), and a requirer other than the root that
peers on the name holds none of it (PEER LOCAL).  An optional peer the
answer leaves open may find a copy only in its range (dep-valid.js), a
dist-tag read from the snapshot.  Every dependency and every peer that is
not optional has a provider.  Only the lock and the answer are read, so a
placement that misses is caught whatever wrote it.

usage: relation.py <package-lock.json> <our --tree output> [<cache-dir>]
Prints each miss and exits 3 when there is one, so that a crash, which
exits 1, is not read as one.
"""
import json
import sys

from shared import SHARED, normalize, split
from tree import is_link, packument, parse_tree, resolve, satisfies


def tagged(cache, name, spec):
    """the version the packument's dist-tags give spec, or spec itself
    where it names no tag: npm refuses a tag that is a valid range, so a
    spec that is a key of dist-tags is a tag"""
    if cache is None:
        return spec
    try:
        tags = packument(cache, name).get("dist-tags") or {}
    except (OSError, ValueError):
        return spec
    v = tags.get(spec.strip()) if isinstance(tags, dict) else None
    return v if isinstance(v, str) else spec


def identity(pk, path):
    key = path.rsplit("node_modules/", 1)[-1]
    return (pk[path].get("name") or key, pk[path].get("version", ""), key)


def fields(e, node=None, holds=frozenset(), npm=False):
    """(dependencies, {peer: optional}, needed dependencies) of the
    package e at node, the answer giving it copies of holds; under the
    shared reading, as it reads the manifest, unless npm asks for npm's
    own reading"""
    if SHARED and not npm:
        if node is None or node[0] == "":
            opt = set(e.get("optionalDependencies") or {})
            return set(e.get("dependencies") or {}) | opt, {}, set(e.get("dependencies") or {}) - opt
        return split(normalize(e, node[0], node[1], npm=True), holds)
    opt = set(e.get("optionalDependencies") or {})
    deps = set(e.get("dependencies") or {}) | opt
    meta = e.get("peerDependenciesMeta")
    meta = meta if isinstance(meta, dict) else {}
    # a dependency of the same name replaces the peer
    peers = {p: bool((meta.get(p) or {}).get("optional"))
             for p in e.get("peerDependencies") or {} if p not in deps}
    bundled = e.get("bundleDependencies") or e.get("bundledDependencies") or []
    needed = set(e.get("dependencies") or {}) - opt - set(deps if bundled is True else bundled)
    return deps, peers, needed


def name(n):
    return f"{n[0]} {n[1]}" + (f" at {n[2]}" if n[2] != n[0] else "")


def open_misses(pk, at, open_, through, cache=None):
    """the misses of the peers the answer leaves open, open_ holding each
    (lock path, peer) left open, and through each peer read through its
    depender's own as (lock path, depender's lock path, peer, optional,
    depender)"""
    miss = []
    # a peer read through a depender whose own optional peer the answer
    # leaves open is open too, which a peer that is not optional may not be
    grew = True
    while grew:
        grew = False
        for q, rp, p, optional, r in through:
            if (rp, p) in open_ and (q, p) not in open_:
                open_.add((q, p))
                grew = True
    miss += [(q, f"{name(at(q))} at {q}, as {name(r)} requires it, peers on {p}, which the "
                 f"answer leaves open for {name(r)}'s own optional peer")
             for q, rp, p, optional, r in through if not optional and (rp, p) in open_]
    # the answer's word is open, so a copy found anyway is a miss only
    # where npm finds it out of range; it is asked from that copy, which
    # mklock.py's search then nests out of sight
    hit = {(q, p): resolve(pk, q, p) for q, p in open_}
    spec = {(q, p): (pk[q].get("peerDependencies") or {}).get(p) or ""
            for (q, p), s in hit.items() if s is not None and s in pk}
    asks = {(q, p): (pk[hit[q, p]].get("version", ""), tagged(cache, p, r))
            for (q, p), r in spec.items()}
    # "" and * take anything; a range semver cannot read (None) is not ours
    # to judge
    ok = {a: a[1].strip() in ("", "*") or satisfies(*a, "loose") for a in asks.values()}
    miss += [(hit[q, p], f"{name(at(q))} at {q} peers on {p}, which the answer leaves open, yet it "
                 f"finds {name(at(hit[q, p]))} outside {spec[q, p]}"
                 + (f" ({asks[q, p][1]})" if asks[q, p][1] != spec[q, p] else ""))
             for (q, p) in sorted(asks) if ok[asks[q, p]] is False]
    return miss


def misses(pk, root, nodes, edges, cache=None):
    """each miss as (the lock path it was asked from, or None, and why),
    cache the snapshot's packuments where a dist-tag is to be read"""
    out = {}
    for r, key, c in edges:
        out.setdefault(r, {})[key] = c
    copies = {root: [""]}
    for path in pk:
        if path and not is_link(pk[path]):
            copies.setdefault(identity(pk, path), []).append(path)

    def at(path):
        return root if path == "" else identity(pk, path) if path in pk else None

    miss = [(None, f"{name(n)} is nowhere in the tree") for n in nodes if n not in copies]
    open_, through = set(), []
    for r in sorted(copies):
        given = out.get(r, {})
        for rp in copies[r]:
            deps, own_peers, needed = fields(pk[rp], None if r == root else r, set(given))
            miss += [(rp, f"{name(r)} requires {k}, and the answer gives it nothing")
                     for k in sorted(needed - set(given))]
            found, todo, peered = set(), [], set()
            for k in sorted(set(given) & deps):
                q = resolve(pk, rp, k)
                if at(q) != given[k]:
                    miss.append((rp, f"{name(r)} at {rp or '(root)'} requires {k}: we chose "
                                     f"{name(given[k])}, the tree gives {at(q) and name(at(q))}"))
                elif q not in found:
                    found.add(q)
                    todo.append(q)
            while todo:
                q = todo.pop()
                for p, optional in sorted(fields(pk[q], at(q), set(out.get(at(q), {})))[1].items()):
                    if p not in given and r != root and p in own_peers:
                        s, t = resolve(pk, q, p), resolve(pk, rp, p)
                        if s != t or (s is None and not optional):
                            miss.append((q, f"{name(at(q))} at {q}, as {name(r)} requires it, "
                                            f"peers on {p}: {name(r)}'s own peer finds "
                                            f"{at(t) and name(at(t))}, the tree gives "
                                            f"{at(s) and name(at(s))}"))
                        through.append((q, rp, p, optional, r))
                        continue
                    if p not in given and r != root and p == r[2]:
                        s = resolve(pk, q, p)
                        if s != rp:
                            miss.append((q, f"{name(at(q))} at {q}, as {name(r)} requires it, "
                                            f"peers on {p}: {name(r)} offers itself, the tree "
                                            f"gives {at(s) and name(at(s))}"))
                        continue
                    if p not in given:
                        # the answer leaves q's optional peer open here
                        open_.add((q, p))
                        if not optional:
                            miss.append((rp, f"{name(r)} gives {name(at(q))} no {p} for its peer"))
                        continue
                    peered.add(p)
                    s = resolve(pk, q, p)
                    if at(s) != given[p]:
                        miss.append((q, f"{name(at(q))} at {q}, as {name(r)} requires it, peers on "
                                        f"{p}: we chose {name(given[p])}, the tree gives "
                                        f"{at(s) and name(at(s))}"))
                    elif s not in found:
                        found.add(s)
                        todo.append(s)
            miss += [(rp, f"{name(r)} gives {k} to nothing that requires or peers on it")
                     for k in sorted(set(given) - deps - peered)]
    return miss + open_misses(pk, at, open_, through, cache)


def main():
    with open(sys.argv[1]) as f:
        pk = json.load(f)["packages"]
    with open(sys.argv[2]) as f:
        root, nodes, edges = parse_tree(f.read())
    miss = misses(pk, root, nodes, edges, sys.argv[3] if len(sys.argv) > 3 else None)
    for line in sorted({why for _, why in miss}):
        print(line)
    return 3 if miss else 0


if __name__ == "__main__":
    sys.exit(main())
