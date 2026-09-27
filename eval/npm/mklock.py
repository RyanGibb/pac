#!/usr/bin/env python3
"""Write OUR npm resolution out as a lockfileVersion 3 package-lock.json,
so npm can be asked to verify it.

The inverse of edges.py, and not a symmetric one.  edges.py reads a
lockfile and recovers the resolution relation from it by walking
node_modules chains upward; going the other way means inventing a
placement, because our answer is the relation and carries no directory
layout at all.  A placement is only a faithful encoding of our answer if
resolving each requirer's key from that requirer's directory lands on
exactly the provider we chose, so that is what is computed here, rather
than npm's hoisting heuristic being guessed at; relation.py then asks it
of the lock, apart from how it was placed:

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

          Where the slot would hold a copy that a directory above it
          already is, it holds a link to that copy instead, as arborist
          writes one to close a cycle (place-dep.js), since nesting the
          copy again would repeat the chain forever.  So placement always
          ends, and every answer has a tree.

          A package whose peers our answer gives is the exception to
          shallowest: it goes in its requirer's own node_modules.  npm
          resolves a peer from the declarer, and a copy in the declarer's
          own node_modules is PEER LOCAL, an invalid edge (arborist
          edge.js); our answer puts the peer beside the declarer, among
          its requirer's edges.  Hoisted any higher, the declarer would
          look its peer up from a directory that may hold another
          version.  So a copy is the package and the providers its
          requirer gives its peers, and two requirers giving different
          ones get two copies.  A requirer other than the root that peers
          on a name gives its declarers none of it, which is PEER LOCAL
          again, and their peer finds what the requirer's own does: they
          too go in the requirer's own node_modules, and are told apart by
          that provider.  So too a requirer of the peer's own name that
          neither gives nor peers on it, whose declarers find the requirer
          itself.  For the same reason, a name some package
          on the requirer's chain peers on goes in that package's own
          node_modules only as the last resort.

          A declarer whose own declarers need another provider of a name
          it peers on cannot hold them in its node_modules, where they
          would see its peer, nor the provider they need, which it would
          then see itself.  So they go above the directory holding the
          declarer's peer, with their provider beside them, and to leave
          that room the declarer's peer goes in its requirer's own
          node_modules.  Where the root holds the declarer's peer, there
          is no room above it, and no tree holds the answer.

  search  where no directory above the peer takes them, or relation.py
          finds a miss in the placement, another tree might, and search()
          looks for one: it nests the copies in the way, and places each
          copy no shallower than the torn peers below it need (levels()).
          It returns only a tree relation.py holds, and where impossible()
          shows that none does, or none is found, the first placement
          instead, for relation.py to name what it misses.  What neither
          settles is left unchecked.  A miss is typically a copy hoisted
          into sight of an optional peer our answer leaves open, which
          finds it out of range; nested in its requirer, it is not seen.

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

Every other field is copied, not decided: version, resolved and
integrity come from the snapshot packument's own dist block, and the
dependency maps come from that version's manifest, so the lockfile
describes the same packages our solver read.  An aliased slot (the key
differs from the registry name) carries "name", the way npm records one.

usage: mklock.py <cache-dir> <our --tree output> <out package-lock.json>
       [--root-manifest <package.json>]
"""
import functools
import json
import os
import sys
import time

from shared import SHARED, normalize, split
from relation import fields, misses
from tree import ancestors, escape, is_link, lookup, parse_tree, slot


class Unplaced(Exception):
    """a placement that found no slot, with the lock path it was placing
    from, whose chain the search may deepen"""
    def __init__(self, path, why, blockers=()):
        super().__init__(why)
        self.path = path
        self.blockers = list(blockers)


def place(root, nodes, edges, claims, peers, deep, hints=frozenset(), floor=None):
    out_edges = {}
    for r, key, c in edges:
        out_edges.setdefault(r, []).append((key, c))

    # a node is (name, version, key): one version under two keys, an alias
    # beside its own name, is two copies, and each resolves its own edges.
    # A copy of a package with peers is told apart by the providers its
    # requirer gives those peers too, since npm resolves them from the copy.
    at = {"": root}                 # path -> node, a link's included
    ident = {"": (root, ())}        # path -> (node, claims)
    links = {}                      # path -> the ancestor copy it links to
    stuck = []                      # declarers above() found no directory for
    blocked = []                    # what kept above()'s last declarer out
    origin = {}                     # path -> the declarer above() put it there for,
                                    # and what kept it out of the directories it passed
    nest = {c for how, c in hints if how == "nest"}
    up = {c for how, c in hints if how == "up"}
    paths = {root: [""]}            # node -> the paths of its copies
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

    def holders(anc, key, cid):
        """what would let cid into anc's node_modules: the copy in its slot
        nested where it is required, or where above() put it there, its
        declarer put higher; and those answering a lookup there would
        capture nested where they are required"""
        def moved(s, how):
            return [("up", origin[s][0]), *origin[s][1]] if s in origin else [(how, ident[s])]
        s = slot(anc, key)
        return (moved(s, "nest") if s in at and ident[s] != cid else []) + [
            h for rp, held in answered.get(key, ()) if len(anc) > len(held) and sees(anc, rp)
            for h in (moved(rp, None) if rp in origin else [("nest", ident[slot(held, key)])])]

    def put(dst, cid):
        """a copy at dst, or a link where a directory above dst already is
        this copy: arborist's own way out of a nesting loop (place-dep.js),
        and the reason placement ends, since no chain of copies repeats"""
        at[dst] = cid[0]
        ident[dst] = cid
        for anc in reversed(ancestors(dst)[1:-1]):
            if ident[anc] == cid:
                links[dst] = anc
                return False
        paths.setdefault(cid[0], []).append(dst)
        # a guard, not a verdict: no chain is longer than the copies there are
        # to tell apart, so a placement past this is a bug here
        if dst.count("node_modules/") > len(edges) + 8:
            raise Unplaced(dst, f"no placement within {len(edges) + 8} levels ({dst!r})")
        return True

    def low(anc, cid):
        """whether anc's node_modules is shallower than the level cid needs"""
        return floor is not None and len(ancestors(anc)) - 1 < floor.get(cid, 0)

    def peer_local(anc, key, node, path):
        """whether the package at anc peers on key, so that a copy in its own
        node_modules is PEER LOCAL to it, an invalid edge (arborist edge.js)"""
        return anc != "" and key in peers.get(node if anc == path else at[anc], ())

    def found(path, key):
        s = lookup(at, path, key)
        return None if s is None else links.get(s, s)

    def above(path, node, key, cid, frontier):
        """Place a declarer whose peers the requirer at path gives other
        providers than the requirer's own peers of those names: in its
        requirer's node_modules it would see the requirer's peers, so it
        goes in a directory above the one holding them, with the providers
        it needs beside it where it does not see them already.  Whether
        that placed it; None where the root holds them, above which there is
        no directory, so that no tree holds the answer."""
        ancs = ancestors(path)
        own = dict(ident[path][1])
        top = min(max((i for i, a in enumerate(ancs[:-1]) if slot(a, p) in at), default=0)
                  for p, x in cid[1] if own.get(p, x) != x)
        if top == 0:
            return None
        lo = max((i + (ident[slot(a, key)] != cid) for i, a in enumerate(ancs)
                  if slot(a, key) in at), default=0)
        blocked.clear()
        passed = []
        blocked.extend(("nest", ident[slot(a, key)]) for a in ancs[:-1]
                       if slot(a, key) in at and ident[slot(a, key)] != cid)
        # nearest first, which leaves the levels above to others; or, where
        # that took a slot another declarer needed, furthest first
        for a in (ancs[lo:top] if cid in up else reversed(ancs[lo:top])):
            s = slot(a, key)
            if s in at and ident[s] == cid:
                answered.setdefault(key, []).append((path, a))
                return True
            if low(a, cid):
                continue
            if s in at or shadows(a, key) or peer_local(a, key, node, path):
                passed.extend(holders(a, key, cid))
                blocked.extend(holders(a, key, cid))
                continue
            need = [(p, x) for p, x in cid[1] if at.get(found(a, p)) != x]
            if any(slot(a, p) in at or shadows(a, p) for p, _ in need):
                passed.extend(b for p, x in need for b in holders(a, p, (x, claims(node, x))))
                blocked.extend(b for p, x in need for b in holders(a, p, (x, claims(node, x))))
                continue
            if put(s, cid):
                frontier.append((s, cid[0]))
            origin[s] = cid, passed
            answered.setdefault(key, []).append((path, a))
            if floor is not None:
                # the peers it finds where it is, which nothing placed later
                # may shadow
                for p, x in cid[1]:
                    if (p, x) not in need:
                        f = lookup(at, a, p)
                        answered.setdefault(p, []).append((s, f[:-len("node_modules/" + p)].rstrip("/")))
            for p, x in need:
                if put(slot(a, p), (x, claims(node, x))):
                    frontier.append((slot(a, p), x))
                origin[slot(a, p)] = cid, passed
                answered.setdefault(p, []).append((s, a))
            return True
        return False

    def grow(frontier):
        while frontier:
            path, node = frontier.pop(0)
            own = dict(ident[path][1])
            kids = out_edges.get(node, ())

            def copy_of(child):
                """the child, the providers its requirer gives its peers, and
                those its peers find through a requirer that is not the root
                and peers on the name itself: such a requirer holds none of
                it (PEER LOCAL), so the child's peer must find what the
                requirer's own finds, which it does from the requirer's own
                node_modules"""
                gives = {k for k, _ in kids}
                through = tuple((p, at[found(path, p)]) for p in sorted(peers.get(child, ()))
                                if path != "" and p in peers.get(node, ())
                                and p not in gives and found(path, p) is not None)
                # a requirer at a directory of the peer's name that neither
                # gives nor peers on it offers itself, which the child's
                # lookup reaches from the requirer's own node_modules
                itself = tuple((p, node) for p in sorted(peers.get(child, ()))
                               if path != "" and p == node[2] and p not in gives
                               and p not in peers.get(node, ()))
                return (child, tuple(sorted(claims(node, child) + through + itself)))

            # a name this package peers on, which it gives its declarers
            # another provider of, is theirs to place
            placed = set()
            for key, child in kids:
                if any(own.get(p, x) != x for p, x in claims(node, child)):
                    done = above(path, node, key, copy_of(child), frontier)
                    if done:
                        placed.add((key, child))
                    elif done is False:
                        stuck.append((path, child, list(blocked)))
            aside = {p for key, child in placed for p, x in claims(node, child) if own.get(p, x) != x}
            for key, child in kids:
                if (key, child) in placed or key in aside and own.get(key) != child:
                    continue
                cid = copy_of(child)
                ancs = ancestors(path)
                # a slot deeper on this chain is what the requirer would find,
                # so the search starts there rather than at the root
                lo = 0
                for i, anc in enumerate(ancs):
                    if slot(anc, key) in at:
                        lo = i if ident[slot(anc, key)] == cid else i + 1
                # into the requirer's own node_modules, unless a directory on
                # its path is this copy already, which the lookup finds or a
                # link reaches; and so too a provider of a name one of the
                # requirer's declarers peers on and gives its own declarers
                # another of, which leaves them room above it
                if ((cid[1] or (node, key) in deep or cid in nest)
                        and all(ident[anc] != cid for anc in ancs)):
                    lo = max(lo, len(ancs) - 1 - (path != "" and key in peers.get(node, ())))
                cands = [a for a in ancs[lo:] if not low(a, cid)]
                cands = ([a for a in cands if not peer_local(a, key, node, path)]
                         + [a for a in cands if peer_local(a, key, node, path)])
                target = None
                for anc in cands:
                    if slot(anc, key) in at:
                        target = anc          # shared: already holds our provider
                        break
                    if not shadows(anc, key):
                        target = anc
                        break
                if target is None:
                    raise Unplaced(path, f"no slot for {key} under {path!r}",
                                   [b for a in cands for b in holders(a, key, cid)])
                dst = slot(target, key)
                if dst not in at and put(dst, cid):
                    frontier.append((dst, child))
                answered.setdefault(key, []).append((path, target))

    try:
        grow([("", root)])
    except Unplaced as e:
        return at, ident, links, stuck, e
    # a package nothing reaches is placed too, where it shadows no lookup
    # already answered, so that npm judges it as any unreached entry of a
    # lock: prunes it, and asks nothing of it but what reach.py asks
    for node in sorted(nodes - set(paths)):
        if node in paths:
            continue
        dirs = sorted((p for p in at if p not in links),
                      key=lambda p: (p.count("node_modules/"), p))
        target = next((d for d in dirs if slot(d, node[2]) not in at
                       and not shadows(d, node[2])), None)
        if target is None:
            return at, ident, links, stuck, Unplaced(None, f"no slot for {node[2]}, which nothing reaches")
        try:
            put(slot(target, node[2]), (node, ()))
            grow([(slot(target, node[2]), node)])
        except Unplaced as e:
            return at, ident, links, stuck, e
    return at, ident, links, stuck, None


def peer_locals(pk):
    """a peer its declarer finds in its own node_modules, an edge npm calls
    PEER LOCAL and invalid (arborist edge.js), though relation.py, which
    reads lookup alone, lets it through"""
    return [(q, f"{q} peers on {p}, which its own node_modules holds")
            for q, e in pk.items() if q and not is_link(e)
            for p in fields(e, npm=True)[1] if slot(q, p) in pk]


def levels(root, edges, claims, peers):
    """The least level of the node_modules each copy can sit in, the
    root's own being level 0, with the copy below it that sets it, as
    {cid: (level, cid or None)}; None where a cycle of copies each needs to
    sit above the next, which no tree does.  These hold of every tree, the
    links in it included, since a link's copy sits higher still.

    A copy's dependency may sit in its own node_modules, a level below it.
    A provider it gives its declarers of a name it peers on, and gets
    itself, sits at its level or above, where it finds its own.  A declarer
    it gives another provider of a name they both peer on than its own
    sits a level above it at least: at its level or in its node_modules the
    declarer would find the copy's own, since its node_modules may not
    hold its peer (PEER LOCAL, arborist edge.js); and so too the provider
    it gives that declarer.  So a chain of such tears costs a level each."""
    out = {}
    for r, key, c in edges:
        out.setdefault(r, []).append((key, c))
    kids, todo, seen = {}, [(root, ())], {(root, ())}
    while todo:
        cid = todo.pop()
        node, own = cid[0], dict(cid[1])
        kids[cid] = []
        for key, c in out.get(node, ()):
            kc = (c, claims(node, c))
            if any(own.get(p, x) != x for p, x in kc[1]):
                w = 1
            elif key in peers.get(node, ()):
                w = int(own.get(key, c) != c)
            else:
                w = -1
            kids[cid].append((kc, w))
            if kc not in seen:
                seen.add(kc)
                todo.append(kc)
    parents = {}
    for cid, ks in kids.items():
        for kc, _ in ks:
            parents.setdefault(kc, set()).add(cid)
    need = {cid: (0, None) for cid in kids}
    todo, cap = list(kids), len(kids) + 1
    while todo:
        cid = todo.pop()
        best = max(((need[kc][0] + w, kc) for kc, w in kids[cid] if need[kc][0] + w > 0),
                   default=(0, None), key=lambda t: t[0])
        if best[0] > need[cid][0]:
            if best[0] > cap:
                return None
            need[cid] = best
            todo.extend(parents.get(cid, ()))
    return need


def impossible(root, edges, claims, peers, deps):
    """Why no tree holds the answer, or None where these two counts find
    no reason.

    Depth: the root finds its dependencies in its own node_modules, at
    level 0, so none may need a lower level (levels()).

    Breadth: a copy Q the root reaches along d dependencies sits at level
    d - 1 at most, since each lookup lands at its requirer's level or
    above; every copy in a tree is held to its edges.  Say Q gives its
    dependencies R_1..R_k a peer p = x, and each R_i gives a declarer of
    its own p = y_i != x.  R_i sits at or above Q's own node_modules, and
    its node_modules may not hold p, so it and its declarer find p where a
    lookup from one of the d + 1 levels from the root to Q's own does; and
    the declarer's is found at a level above the one R_i's is.  So the
    y_i are found at d levels, and more than d different ones cannot all
    be."""
    need = levels(root, edges, claims, peers)
    if need is None:
        return "a cycle of copies each needs to sit below the next"
    for cid in sorted({(c, claims(root, c)) for r, _, c in edges if r == root}):
        if need[cid][0] > 0:
            chain, at = [], cid
            while at is not None:
                chain.append(f"{at[0][0]} {at[0][1]} (level {need[at][0]})")
                at = need[at][1]
            return ("the root's dependency " + " -> ".join(chain) + " needs a level below the "
                    "root's own node_modules, where the root finds it")
    out, dist, todo = {}, {root: 0}, [root]
    for r, key, c in edges:
        out.setdefault(r, {})[key] = c
    while todo:
        r = todo.pop(0)
        for key, c in sorted(out.get(r, {}).items()):
            if key in deps.get(r, ()) and c not in dist:
                dist[c] = dist[r] + 1
                todo.append(c)
    for q in sorted(dist, key=lambda n: (dist[n], n)):
        given = out.get(q, {})
        for p, x in sorted(given.items()):
            ys = {}
            for key, r in sorted(given.items()):
                y = out.get(r, {}).get(p)
                if (key in deps.get(q, ()) and p in peers.get(r, ()) and y not in (None, x)
                        and any(k in deps.get(r, ()) and p in peers.get(d, ())
                                for k, d in out.get(r, {}).items())):
                    ys.setdefault(y, r)
            if len(ys) > dist[q]:
                name = "the root" if q == root else f"{q[0]} {q[1]}"
                return (f"{name}, {dist[q]} requirements from the root, gives {p} {x[1]} to "
                        + ", ".join(f"{r[0]} {r[1]}" for r in ys.values())
                        + f", which give their own declarers {len(ys)} others ("
                        + ", ".join(sorted(y[1] for y in ys)) + f"), more than its {dist[q]} "
                        "levels above can hold")
    return None


def search(root, nodes, edges, claims, peers, deep, deps, verify):
    """place() as it stands where it places everything.  Otherwise, where
    impossible() shows no tree holds the answer, that placement is kept
    for relation.py to name what it misses; and failing both, a search.

    The search places each copy no shallower than levels() needs, and
    makes room above a stuck declarer's peer with hints to place() and
    starts again: nest a copy in its requirer's own node_modules where it
    was shared from further up (one on the declarer's chain, which puts a
    directory above the peer, or one holding a slot the declarer or its
    peer needs), or place a declarer above() put in the way from the top
    down.  Each round takes every failure's first hint not yet taken; where
    a round has none left, the search backs up to try the others one at a
    time.  Only a placement verify() finds no miss in is returned, so the
    search can widen what is placed, never what is accepted.  MKLOCK_TRIES
    placements or MKLOCK_SECONDS bound it; what it does not settle is left
    unchecked."""
    tries = int(os.environ.get("MKLOCK_TRIES", "64"))
    budget = float(os.environ.get("MKLOCK_SECONDS", "300"))
    start = time.monotonic()

    def fails(at, ident, stuck, unplaced):
        """(path, deepest ancestor worth nesting, blockers, why) for each failure"""
        out = []
        for path, child, blockers in stuck:
            ancs = ancestors(path)
            own = dict(ident[path][1])
            hi = min(max((i for i, a in enumerate(ancs[:-1]) if slot(a, p) in at), default=0)
                     for p, x in claims(ident[path][0], child) if own.get(p, x) != x)
            out.append((path, hi, blockers, f"no directory above their declarer's peer took "
                                            f"{child[0]} {child[1]} under {path}"))
        if unplaced is not None:
            p = unplaced.path or ""
            out.append((p, len(ancestors(p)) - 1, unplaced.blockers, str(unplaced)))
        return out

    first = place(root, nodes, edges, claims, peers, deep)
    whole = not first[3] and first[4] is None
    if whole and not verify(first[0], first[2]):
        return first[0], first[2]
    why = impossible(root, edges, claims, peers, deps)
    if why is not None:
        print(f"no tree holds the answer: {why}")
        return first[0], first[2]
    floor = {cid: n for cid, (n, _) in levels(root, edges, claims, peers).items()}
    # each entry: the hints of a placement yet to run, and those of its
    # parent's other children, tried if it leads nowhere
    stack, seen, rounds, whys = [(frozenset(), [])], set(), 1, []
    while stack:
        hints, alts = stack.pop()
        if hints in seen:
            continue
        seen.add(hints)
        if rounds >= tries or time.monotonic() - start > budget:
            break
        at, ident, links, stuck, unplaced = place(root, nodes, edges, claims, peers, deep,
                                                  hints, floor)
        rounds += 1
        if not stuck and unplaced is None:
            miss = verify(at, links)
            if not miss:
                print(f"placed in {rounds} rounds, with {len(hints)} hints")
                return at, links
            failed = [(p or "", len(ancestors(p or "")) - 1, [], why) for p, why in miss]
        else:
            failed = fails(at, ident, stuck, unplaced)
        whys = sorted({why for _, _, _, why in failed})
        cands = []
        for path, hi, blockers, _ in failed:
            ancs = ancestors(path)
            cands.append([h for h in [("nest", ident[a]) for a in reversed(ancs[1:hi + 1])]
                          + blockers if h not in hints and h[1][0] != root])
        more = {c[0] for c in cands if c}
        others = [hints | {h} for h in dict.fromkeys(h for c in cands for h in c[1:])
                  if h not in more]
        if alts:
            stack.append((alts[0], alts[1:]))
        if more:
            stack.append((hints | more, others))
        elif others:
            stack.append((others[0], others[1:]))
    if whole:
        print(f"no tree in {rounds} placements; the first kept: " + "; ".join(whys[:5]))
        return first[0], first[2]
    raise RuntimeError(f"no tree in {rounds} placements: " + "; ".join(whys[:5]))


@functools.lru_cache(maxsize=None)
def packument(cache, name):
    with open(os.path.join(cache, escape(name) + ".json")) as f:
        return json.load(f)


def manifest(cache, name, version):
    v = packument(cache, name)["versions"].get(version)
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

    out = {}
    for r, key, c in edges:
        out.setdefault(r, {})[key] = c
    peers, needed, deps = {}, {}, {}
    for n in sorted(nodes):
        # the query is published nowhere; its manifest is the project's
        m = (rootman or {}) if n == root else manifest(cache, n[0], n[1])
        if SHARED:
            # the shared reading, the root asking no peer of anyone
            if n == root:
                deps[n] = set(m.get("dependencies") or {}) | set(m.get("optionalDependencies") or {})
                peers[n], needed[n] = set(), set()
            else:
                d, pr, _ = split(normalize(m, n[0], n[1], npm=True), set(out.get(n, {})))
                deps[n], peers[n] = d, set(pr)
                needed[n] = {p for p, o in pr.items() if not o}
            continue
        meta = m.get("peerDependenciesMeta")
        meta = meta if isinstance(meta, dict) else {}
        # a dependency of the same name replaces the peer
        deps[n] = set(m.get("dependencies") or {}) | set(m.get("optionalDependencies") or {})
        peers[n] = set(m.get("peerDependencies") or {}) - deps[n]
        needed[n] = {p for p in peers[n] if not (meta.get(p) or {}).get("optional")}

    def claims(r, c):
        """the providers our answer gives c's peers where r requires it.  An
        optional peer c requires the name of itself resolves by c's own
        lookup, whatever r gives, and npm judges that it is in range."""
        return tuple(sorted((p, out[r][p]) for p in peers.get(c, ()) if p in out.get(r, {})
                            and (p in needed.get(c, ()) or p not in out.get(c, {}))))

    # r's provider of a name its declarer c peers on, where c gives its own
    # declarers another provider of that name
    deep = {(r, p) for r, _, c in edges for p, x in claims(r, c) if out.get(c, {}).get(p, x) != x}

    rm = rootman or {}
    head = {k: v for k, v in (
        ("name", rm.get("name", None if root[0] == "." else root[0])),
        ("version", rm.get("version", root[1])),
        ("license", rm.get("license")),
        ("dependencies", rm.get("dependencies")),
        ("devDependencies", rm.get("devDependencies")),
        ("optionalDependencies", rm.get("optionalDependencies")),
    ) if v}

    def packages(at, links):
        pk = {"": head}
        for path in sorted(at):
            if path == "":
                continue
            if path in links:
                pk[path] = {"resolved": links[path], "link": True}
                continue
            name, version, _ = at[path]
            pk[path] = entry(cache, name, version, path.rsplit("node_modules/", 1)[-1])
        return pk

    def verify(at, links):
        pk = packages(at, links)
        return misses(pk, root, nodes, edges) + peer_locals(pk)

    at, links = search(root, nodes, edges, claims, peers, deep, deps, verify)
    packages = packages(at, links)

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
    print(f"{dst}: {len(at) - len(links)} placements and {len(links)} links for "
          f"{len(nodes)} packages, {len(edges)} edges, max nesting {depth}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
