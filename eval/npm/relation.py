#!/usr/bin/env python3
"""Whether a package-lock.json holds our answer: for every edge of the
answer, node_modules lookup from where the requirer sits lands on the copy
the answer chose, links followed, as require() resolves from a realpath.

An edge the requirer's manifest names as a dependency is resolved from the
requirer.  Our answer hangs a declarer's peers on the package that required
the declarer, so an edge naming a peer of a declarer the requirer requires
is resolved as npm resolves a peer: from where that declarer sits, its own
node_modules first (arborist edge.js).  A provider the answer gives a peer
may declare peers of its own, which hang on the same requirer, and is asked
from where it was found.  Every copy of a requirer in the lock is asked,
since each resolves for itself.

The answer must also give a provider to every dependency a manifest names
(bundled and optional ones aside) and to every peer that is not optional of
a declarer required: npm might find a package there by lookup, but it would
not be ours.

This reads only the lock and the answer, not how mklock.py placed it, so a
placement that does not hold the answer is caught whatever wrote it.

usage: relation.py <package-lock.json> <our --tree output>
Prints each miss and exits 3 when there is one, so that a crash, which
exits 1, is not read as one.
"""
import json
import sys

from tree import is_link, parse_tree, resolve


def identity(pk, path):
    key = path.rsplit("node_modules/", 1)[-1]
    return (pk[path].get("name") or key, pk[path].get("version", ""), key)


def fields(e):
    opt = set(e.get("optionalDependencies") or {})
    deps = set(e.get("dependencies") or {}) | opt
    meta = e.get("peerDependenciesMeta") or {}
    # a dependency of the same name replaces the peer
    peers = {p: bool((meta.get(p) or {}).get("optional"))
             for p in e.get("peerDependencies") or {} if p not in deps}
    bundled = e.get("bundleDependencies") or e.get("bundledDependencies") or []
    needed = set(e.get("dependencies") or {}) - opt - set(deps if bundled is True else bundled)
    return deps, peers, needed


def misses(pk, root, nodes, edges):
    """each miss as (the lock path it was asked from, or None, and why)"""
    out = {}
    for r, key, c in edges:
        out.setdefault(r, {})[key] = c
    copies = {root: [""]}
    for path in pk:
        if path and not is_link(pk[path]):
            copies.setdefault(identity(pk, path), []).append(path)

    def at(path):
        return root if path == "" else identity(pk, path) if path in pk else None

    def name(n):
        return f"{n[0]} {n[1]}" + (f" at {n[2]}" if n[2] != n[0] else "")

    miss = [(None, f"{name(n)} is nowhere in the tree") for n in nodes if n not in copies]
    for r in sorted(copies):
        given = out.get(r, {})
        for rp in copies[r]:
            deps, _, needed = fields(pk[rp])
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
                for p, optional in sorted(fields(pk[q])[1].items()):
                    if p not in given:
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
    return miss


def main():
    with open(sys.argv[1]) as f:
        pk = json.load(f)["packages"]
    with open(sys.argv[2]) as f:
        root, nodes, edges = parse_tree(f.read())
    miss = misses(pk, root, nodes, edges)
    for line in sorted({why for _, why in miss}):
        print(line)
    return 3 if miss else 0


if __name__ == "__main__":
    sys.exit(main())
