#!/usr/bin/env python3
"""Write OUR npm resolution out as a lockfileVersion 3 package-lock.json,
so npm can be asked to verify it.

The inverse of edges.py, and not a symmetric one.  edges.py reads a
lockfile and recovers the resolution relation from it by walking
node_modules chains upward; going the other way means inventing a
placement, because our answer is the relation and carries no directory
layout at all.  A placement is only a faithful encoding of our answer if
resolving each requirer's key from that requirer's directory lands on
exactly the provider we chose, so that is what is computed here and then
checked, rather than npm's hoisting heuristic being guessed at:

  place   for each placed requirer and each of its edges, put the
          provider in the shallowest node_modules on the path from the
          root to that requirer that is *safe*, not merely the
          shallowest that is empty.  A slot is safe when taking it
          leaves every lookup already answered still answering the same
          way.  Two things can go wrong, and both are checked:

          A free slot is not automatically harmless.  The directory it
          sits in is itself a package, and every package already placed
          at or below that directory sees the new slot; if one of them
          requires the same key at a different provider it is now
          shadowed.  So a free
          slot is rejected when some lookup for this key that is
          already answered comes from a package at or below that
          directory and is answered from higher up.

          Symmetrically, the requirer's own chain may already carry a
          slot for this key deeper than the candidate, and that deeper
          slot is what the requirer would find.  So nothing shallower
          than the deepest existing slot on the chain is a candidate at
          all: either that slot already holds our provider, in which
          case it is shared, or the provider goes strictly below it.

          A slot therefore always exists: the requirer's own
          node_modules is reached only once, at which point nothing
          below the requirer has been asked anything yet.

          A package with a mandatory peer is the exception to
          shallowest: it goes in its requirer's own node_modules.  npm
          resolves a peer from the declarer, and a copy in the declarer's
          own node_modules is PEER LOCAL, an invalid edge (arborist
          edge.js); our answer puts the peer beside the
          declarer, among its requirer's edges.  Hoisted any higher, the
          declarer would look its peer up from a directory that may hold
          another version, which `npm ci` then rejects although the answer
          is one npm accepts.  For the same reason, a name the requirer
          itself peers on goes beside the requirer where it can; inside
          is the last resort, and verify does not catch it there.

          npm's arborist decides the same question with a third move we
          deliberately do not make: an occupied slot may be taken over,
          evicting an incumbent that could still be pushed deeper
          (can-place-dep.js REPLACE).  Adding that would make this
          writer a small reimplementation of arborist, and `npm ci`
          accepting the result would then be testing the clone rather
          than our solver.  Refusing to evict costs nesting, and where a
          peer's only slot beside its declarer is held by an incumbent
          that could move deeper, it puts the peer in the declarer's own
          node_modules, which npm rejects.

  verify  re-resolve every edge against the finished tree and fail if
          any of them does not come out right: an assertion, not a
          repair, since a lockfile must never quietly describe a
          different answer from ours.  It re-resolves
          our edges only: a peer edge as npm reads it, from the
          declarer, is left to check.sh.

Every other field is copied, not decided: version, resolved and
integrity come from the snapshot packument's own dist block, and the
dependency maps come from that version's manifest, so the lockfile
describes the same packages our solver read.  An aliased slot (the key
differs from the registry name) carries "name", the way npm records one.

usage: mklock.py <cache-dir> <our --tree output> <out package-lock.json>
       [--root-manifest <package.json>]
Exits 4 when no finite tree realises the answer, so that a crash, which
exits 1, is not read as one.
"""
import itertools
import json
import os
import sys

from tree import ancestors, escape, parse_tree, resolve, slot


def self_cycle(root, edges):
    """A copy sitting at key k that resolves k to another copy must hold
    that copy in its own node_modules, since the first k its lookup meets
    above is itself.  So a chain of such holds that comes back round nests
    without end, and no finite node_modules tree realises the answer.  The
    chain, or None."""
    held = {r: c for r, key, c in edges if r != root and key == r[2] and c != r}
    for start in sorted(held):
        chain, n = [], start
        while n in held and n not in chain:
            chain.append(n)
            n = held[n]
        if n in chain:
            return chain[chain.index(n):] + [n]
    return None


def components(succ):
    """succ's strongly connected components, by Tarjan's algorithm without
    recursion, which an answer's depth would exhaust"""
    index, low, on, stack, out = {}, {}, set(), [], []
    for v0 in succ:
        if v0 in index:
            continue
        index[v0] = low[v0] = len(index)
        stack.append(v0)
        on.add(v0)
        work = [(v0, iter(succ.get(v0, ())))]
        while work:
            v, it = work[-1]
            for w in it:
                if w not in index:
                    index[w] = low[w] = len(index)
                    stack.append(w)
                    on.add(w)
                    work.append((w, iter(succ.get(w, ()))))
                    break
                if w in on:
                    low[v] = min(low[v], index[w])
            else:
                work.pop()
                if work:
                    low[work[-1][0]] = min(low[work[-1][0]], low[v])
                if low[v] == index[v]:
                    comp = []
                    while not comp or comp[-1] != v:
                        comp.append(stack.pop())
                        on.discard(comp[-1])
                    out.append(comp)
    return out


def unclosed(root, edges, limit=50000):
    """A strongly connected part of the answer that no finite tree holds,
    or None.  A copy's lookups see its own node_modules, then what is
    visible where it sits, its own slot included; so a copy is determined
    by its node and that environment, a key to the copy it would find or
    to none.  A copy can be finished, in finitely many levels below it,
    when some contents of its own node_modules meet its edges over the
    environment and each copy they hold can be finished in turn.  The
    least such set is computed over the part's own edges, which only drops
    constraints.  The topmost copies of the part on any path see none of
    it above them, so some set of siblings, finishable beside one another
    over nothing, must start it; where none can, no copy of the part sits
    in a finite tree, and every node is placed.  A key the part holds one
    copy of is taken to be visible as that copy, which again only drops
    constraints, so only keys with several are tracked.  A part too large
    to track is tried two such keys at a time, the nodes of any other key
    dropped with their edges, which is sound for the same reason."""
    succ = {}
    for r, key, c in edges:
        if r != root:
            succ.setdefault(r, {})[key] = c

    def parts(nodes):
        return components({n: {c for c in succ.get(n, {}).values() if c in nodes}
                           for n in nodes})

    for comp in parts(set(succ)):
        keys = sorted({n[2] for n in comp if sum(m[2] == n[2] for m in comp) > 1})
        found = stuck(comp, succ, limit)
        if found is None and len(keys) > 2:
            for i, k1 in enumerate(keys):
                for k2 in keys[i + 1:]:
                    for sub in parts({n for n in comp if n[2] in (k1, k2)}):
                        found = found or stuck(sub, succ, limit)
        if found:
            return found
    return None


def stuck(comp, succ, limit):
    """unclosed's question of one part: its keys and versions, or None
    where the part can start or is too large to ask"""
    inside = set(comp)
    bykey = {}
    for n in comp:
        bykey.setdefault(n[2], []).append(n)
    multi = sorted(k for k, ns in bykey.items() if len(ns) > 1)
    if not multi:
        return None
    size = 1
    for k in multi:
        size *= len(bykey[k]) + 1
    if len(comp) * size * size > limit:
        return None
    ix = {k: i for i, k in enumerate(multi)}
    need = {n: {k: c for k, c in succ.get(n, {}).items() if c in inside and k in ix}
            for n in comp}
    views = lambda n: itertools.product(
        *[(n,) if k == n[2] else [None] + bykey[k] for k in multi])

    def finishes(n, env, good):
        forced = {k: m for k, m in need[n].items() if env[ix[k]] != m}
        free = [k for k in multi if k not in need[n]]
        for shape in itertools.product(*[[None] + bykey[k] for k in free]):
            inner = dict(forced)
            inner.update((k, z) for k, z in zip(free, shape) if z is not None)
            below = tuple(inner.get(k, env[i]) for i, k in enumerate(multi))
            if all((z, below) in good for z in inner.values()):
                return True
        return False

    good = set()
    grew = True
    while grew:
        grew = False
        for n in comp:
            for env in views(n):
                if (n, env) not in good and finishes(n, env, good):
                    good.add((n, env))
                    grew = True
    single = [n for n in comp if n[2] not in ix]
    starts = any(
        all((z, top) in good for z in top if z is not None)
        and (any(z is not None for z in top) or any((n, top) in good for n in single))
        for top in itertools.product(*[[None] + bykey[k] for k in multi]))
    return None if starts else [(k, sorted(v for _, v, _ in bykey[k])) for k in multi]


def place(root, nodes, edges, declarers=frozenset(), peers={}):
    out_edges = {}
    for r, key, c in edges:
        out_edges.setdefault(r, []).append((key, c))

    # a node is (name, version, key): one version under two keys, an alias
    # beside its own name, is two copies, and each resolves its own edges
    at = {"": root}                 # path -> node
    paths = {root: [""]}            # node -> its paths
    answered = {}                   # key -> [(requirer path, answering dir)]

    def sees(anc, path):
        """whether a lookup from path walks through anc's node_modules"""
        return anc == "" or path == anc or path.startswith(anc + "/node_modules/")

    def shadows(anc, key):
        """whether a new slot for key in anc's node_modules would capture a
        lookup that is answered today from further up.  Both halves matter:
        deeper is where the lookup would now stop, and inside anc's subtree
        is where it can reach at all."""
        for rp, held in answered.get(key, ()):
            if len(anc) > len(held) and sees(anc, rp):
                return True
        return False

    def put(dst, node):
        at[dst] = node
        paths.setdefault(node, []).append(dst)
        # a guard, not a verdict: a placement this deep or this large is
        # taken never to end, and leaves the answer unchecked rather than
        # the check running on to its timeout
        if dst.count("node_modules/") > len(nodes) + 8 or len(at) > 64 * len(nodes) + 1024:
            raise RuntimeError(f"no placement within {len(nodes) + 8} levels and "
                               f"{64 * len(nodes) + 1024} copies ({dst!r})")

    seen = set()

    def grow(frontier):
        while frontier:
            path, node = frontier.pop(0)
            for key, child in out_edges.get(node, ()):
                ancs = ancestors(path)
                # a slot deeper on this chain is what the requirer would find,
                # so the search starts there rather than at the root
                lo = 0
                for i, anc in enumerate(ancs):
                    if slot(anc, key) in at:
                        lo = i if at[slot(anc, key)] == child else i + 1
                # npm refuses a peer found in its declarer's own node_modules
                # (PEER LOCAL), so for a name the requirer peers on that slot is
                # only the last resort
                hi = len(ancs) - 1 if path and key in peers.get(node, ()) else len(ancs)
                # a declarer already on the requirer's own path is a cycle, and
                # nesting it again would not end
                if child in declarers and all(at[anc] != child for anc in ancs):
                    lo = max(lo, hi - 1)
                target = None
                for anc in ancs[lo:hi] + ancs[max(lo, hi):]:
                    if slot(anc, key) in at:
                        target = anc          # shared: already holds our provider
                        break
                    if not shadows(anc, key):
                        target = anc
                        break
                if target is None:
                    raise RuntimeError(f"no slot for {key} under {path!r}")
                dst = slot(target, key)
                if dst not in at:
                    put(dst, child)
                answered.setdefault(key, []).append((path, target))
                if (dst, child) not in seen:
                    seen.add((dst, child))
                    frontier.append((dst, child))

    grow([("", root)])
    # a package nothing reaches is placed too, where it shadows no lookup
    # already answered, so that npm judges it as any unreached entry of a
    # lock: prunes it, and asks nothing of it but what reach.py asks
    for node in sorted(nodes - set(paths)):
        if node in paths:
            continue
        dirs = sorted(at, key=lambda p: (p.count("node_modules/"), p))
        target = next((d for d in dirs if slot(d, node[2]) not in at
                       and not shadows(d, node[2])), None)
        if target is None:
            raise RuntimeError(f"no slot for {node[2]}, which nothing reaches")
        put(slot(target, node[2]), node)
        grow([(slot(target, node[2]), node)])

    for node, ps in paths.items():
        for path in ps:
            for key, child in out_edges.get(node, ()):
                q = resolve(at, path, key)
                if q is None or at[q] != child:
                    got = at[q] if q else None
                    raise RuntimeError(
                        f"placement is not our answer: {node} at {path!r} "
                        f"requires {key}, we chose {child}, the tree says {got}")
    return at


def manifest(cache, name, version):
    p = os.path.join(cache, escape(name) + ".json")
    with open(p) as f:
        pk = json.load(f)
    v = pk["versions"].get(version)
    if v is None:
        raise RuntimeError(f"{name}@{version} not in the snapshot packument")
    return v


COPY = ["dependencies", "optionalDependencies", "peerDependencies",
        "peerDependenciesMeta", "bin", "engines", "os", "cpu", "libc",
        "funding", "deprecated", "hasInstallScript"]


def entry(cache, name, version, key):
    m = manifest(cache, name, version)
    e = {"version": version}
    dist = m.get("dist") or {}
    if dist.get("tarball"):
        e["resolved"] = dist["tarball"]
    if dist.get("integrity"):
        e["integrity"] = dist["integrity"]
    elif dist.get("shasum"):
        # npm's own rendering of a pre-integrity dist for the lockfile
        import base64
        e["integrity"] = "sha1-" + base64.b64encode(
            bytes.fromhex(dist["shasum"])).decode()
    if key != name:
        e["name"] = name
    if m.get("license"):
        e["license"] = m["license"]
    for k in COPY:
        if m.get(k):
            e[k] = m[k]
    return e


def main():
    cache, oursp, dst = sys.argv[1], sys.argv[2], sys.argv[3]
    rootman = None
    if "--root-manifest" in sys.argv:
        with open(sys.argv[sys.argv.index("--root-manifest") + 1]) as f:
            rootman = json.load(f)
    with open(oursp) as f:
        root, nodes, edges = parse_tree(f.read())
    if root is None:
        raise RuntimeError("no root line")

    declarers, peers = set(), {}
    for n in nodes:
        # the query is published nowhere; its manifest is the project's
        m = (rootman or {}) if n == root else manifest(cache, n[0], n[1])
        meta = m.get("peerDependenciesMeta")
        meta = meta if isinstance(meta, dict) else {}
        # a dependency of the same name replaces the peer
        deps = set(m.get("dependencies") or {}) | set(m.get("optionalDependencies") or {})
        peers[n] = set(m.get("peerDependencies") or {}) - deps
        if any(not (meta.get(p) or {}).get("optional") for p in peers[n]):
            declarers.add(n)
    cycle = self_cycle(root, edges)
    if cycle:
        print("no finite node_modules tree: each of "
              + " -> ".join(f"{n} {v}" for n, v, _ in cycle)
              + f" holds the next in its own node_modules/{cycle[0][2]}")
        return 4
    part = unclosed(root, edges)
    if part:
        print("no finite node_modules tree: "
              + "; ".join(f"{k} {', '.join(vs)}" for k, vs in part)
              + " need one another round cycles that no nesting closes")
        return 4
    at = place(root, nodes, edges, declarers, peers)

    packages = {}
    rm = rootman or {}
    packages[""] = {k: v for k, v in (
        ("name", rm.get("name", None if root[0] == "." else root[0])),
        ("version", rm.get("version", root[1])),
        ("license", rm.get("license")),
        ("dependencies", rm.get("dependencies")),
        ("devDependencies", rm.get("devDependencies")),
        ("optionalDependencies", rm.get("optionalDependencies")),
    ) if v}
    for path in sorted(at):
        if path == "":
            continue
        name, version, _ = at[path]
        key = path.rsplit("node_modules/", 1)[-1]
        packages[path] = entry(cache, name, version, key)

    lock = {
        # npm names a nameless project by its directory
        "name": packages[""].get(
            "name", os.path.basename(os.path.dirname(os.path.abspath(dst)))),
        "version": packages[""].get("version", "1.0.0"),
        "lockfileVersion": 3,
        "requires": True,
        "packages": packages,
    }
    with open(dst, "w") as f:
        json.dump(lock, f, indent=2)
        f.write("\n")
    depth = max((p.count("/node_modules/") for p in at), default=0)
    print(f"{dst}: {len(at)} placements for {len(nodes)} packages, "
          f"{len(edges)} edges, max nesting {depth}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
