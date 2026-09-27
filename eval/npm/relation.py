#!/usr/bin/env python3
"""Whether a package-lock.json holds our answer: for every edge of the
answer, node_modules lookup from where the requirer sits lands on the copy
the answer chose, links followed, as require() resolves from a realpath.

An edge the requirer's manifest names as a dependency is resolved from the
requirer.  Our answer hangs a declarer's peers on the package that required
the declarer, so an edge naming a peer of a declarer the requirer requires
is resolved as npm resolves a peer: from where that declarer sits, its own
node_modules first (arborist edge.js).  A requirer other than the root that
peers on the name itself holds none of it (arborist's PEER LOCAL), so there
the declarer's peer must find what the requirer's own peer finds, and a
requirer other than the root that neither gives nor peers on the name but
sits at a directory of that name offers itself, which the declarer's
lookup reaches from inside the requirer's node_modules.  A peer read
through a requirer whose own optional peer the answer leaves open is open
too.  An optional peer the answer leaves open that finds a copy anyway
must find one in its range, as npm judges it (arborist dep-valid.js).  A
provider the answer gives a peer
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
import subprocess
import sys

from tree import is_link, parse_tree, resolve

SATISFIES = {}


def satisfies(pairs):
    """{(version, range): whether npm's semver takes it}, as arborist's
    dep-valid.js asks it (loose, "" and * taking anything); None for a
    range semver cannot read, which is not ours to judge"""
    todo = sorted({p for p in pairs if p not in SATISFIES and p[1].strip() not in ("", "*")})
    if todo:
        # npm's own semver, looked for only when some range needs it
        from verdict import resolve_semver
        js = ("const s=require(%s);console.log(JSON.stringify(JSON.parse(process.argv[1])"
              ".map(([v,r])=>{try{return s.satisfies(v,r,true)}catch(e){return null}})))"
              % json.dumps(resolve_semver()))
        out = subprocess.run(["node", "-e", js, json.dumps(todo)],
                             capture_output=True, text=True, check=True)
        SATISFIES.update(zip(todo, json.loads(out.stdout)))
    return {p: True if p[1].strip() in ("", "*") else SATISFIES[p] for p in pairs}


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
    open_, through = set(), []
    for r in sorted(copies):
        given = out.get(r, {})
        for rp in copies[r]:
            deps, own_peers, needed = fields(pk[rp])
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
    asks = {(q, p): (pk[s].get("version", ""), (pk[q].get("peerDependencies") or {}).get(p) or "")
            for (q, p), s in hit.items() if s is not None and s in pk}
    ok = satisfies(list(asks.values()))
    miss += [(hit[q, p], f"{name(at(q))} at {q} peers on {p}, which the answer leaves open, yet it "
                 f"finds {name(at(hit[q, p]))} outside {asks[q, p][1]}")
             for (q, p) in sorted(asks) if ok[asks[q, p]] is False]
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
