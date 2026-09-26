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
          ones get two copies.  For the same reason, a name some package
          on the requirer's chain peers on goes in that package's own
          node_modules only as the last resort.

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

  verify  re-resolve every edge against the finished tree, following
          links, and every peer as npm does, from its declarer, and fail
          if any of them does not come out as our answer says: an
          assertion, not a repair, since a lockfile must never quietly
          describe a different answer from ours.  Whether npm takes what
          comes out, PEER LOCAL included, is check.sh's question.

Before any of this, an answer that gives a declarer's peer, from the root,
one provider and the declarer's own edge of that name another is refused,
since no tree holds it; given from below the root, the answer is left
unchecked.

Every other field is copied, not decided: version, resolved and
integrity come from the snapshot packument's own dist block, and the
dependency maps come from that version's manifest, so the lockfile
describes the same packages our solver read.  An aliased slot (the key
differs from the registry name) carries "name", the way npm records one.

usage: mklock.py <cache-dir> <our --tree output> <out package-lock.json>
       [--root-manifest <package.json>]
Exits 4 when the answer resolves a peer two ways from the root, so that a
crash, which exits 1, is not read as one.
"""
import json
import os
import sys

from tree import ancestors, escape, lookup, parse_tree, slot


def place(root, nodes, edges, claims, peers):
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
            raise RuntimeError(f"no placement within {len(edges) + 8} levels ({dst!r})")
        return True

    def peer_local(anc, key, node, path):
        """whether the package at anc peers on key, so that a copy in its own
        node_modules is PEER LOCAL to it, an invalid edge (arborist edge.js)"""
        return anc != "" and key in peers.get(node if anc == path else at[anc], ())

    def grow(frontier):
        while frontier:
            path, node = frontier.pop(0)
            for key, child in out_edges.get(node, ()):
                cid = (child, claims(node, child))
                ancs = ancestors(path)
                # a slot deeper on this chain is what the requirer would find,
                # so the search starts there rather than at the root
                lo = 0
                for i, anc in enumerate(ancs):
                    if slot(anc, key) in at:
                        lo = i if ident[slot(anc, key)] == cid else i + 1
                # into the requirer's own node_modules, unless a directory on
                # its path is this copy already, which the lookup finds or a
                # link reaches
                if cid[1] and all(ident[anc] != cid for anc in ancs):
                    lo = max(lo, len(ancs) - 1 - (path != "" and key in peers.get(node, ())))
                cands = ancs[lo:]
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
                    raise RuntimeError(f"no slot for {key} under {path!r}")
                dst = slot(target, key)
                if dst not in at and put(dst, cid):
                    frontier.append((dst, child))
                answered.setdefault(key, []).append((path, target))

    grow([("", root)])
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
            raise RuntimeError(f"no slot for {node[2]}, which nothing reaches")
        put(slot(target, node[2]), (node, ()))
        grow([(slot(target, node[2]), node)])

    def found(path, key):
        s = lookup(at, path, key)
        return None if s is None else links.get(s, s)

    for node, ps in paths.items():
        for path in ps:
            for key, child in out_edges.get(node, ()):
                q = found(path, key)
                if q is None or ident[q] != (child, claims(node, child)):
                    raise RuntimeError(
                        f"placement is not our answer: {node} at {path!r} requires "
                        f"{key}, we chose {child}, the tree says {ident[q] if q else None}")
            # npm resolves a peer from its declarer, its own node_modules first
            for p, prov in ident[path][1]:
                q = found(path, p)
                if q is None or at[q] != prov:
                    raise RuntimeError(
                        f"placement is not our answer: {node} at {path!r} peers on "
                        f"{p}, we chose {prov}, the tree says {at[q] if q else None}")
    return at, links


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

    out = {}
    for r, key, c in edges:
        out.setdefault(r, {})[key] = c
    peers, needed = {}, {}
    for n in sorted(nodes):
        # the query is published nowhere; its manifest is the project's
        m = (rootman or {}) if n == root else manifest(cache, n[0], n[1])
        meta = m.get("peerDependenciesMeta")
        meta = meta if isinstance(meta, dict) else {}
        # a dependency of the same name replaces the peer
        deps = set(m.get("dependencies") or {}) | set(m.get("optionalDependencies") or {})
        peers[n] = set(m.get("peerDependencies") or {}) - deps
        needed[n] = {p for p in peers[n] if not (meta.get(p) or {}).get("optional")}
    torn = {True: [], False: []}
    for r, key, c in edges:
        # a declarer c whose own declarers need another provider of a name c
        # peers on: they cannot sit in c's node_modules, which would hold
        # c's peer too (PEER LOCAL), so they sit above the provider c sees.
        # Where the root gives c its peer, that provider is in the root's
        # own node_modules and nothing is above it, nor does a link as npm
        # writes one lead anywhere else; below the root they could be, but
        # that is a tree this placement does not build
        torn[r == root] += [
            f"{c[0]} {c[1]} peers on {p}, {out[r][p][1]} from "
            f"{'the root' if r == root else r[0] + ' ' + r[1]}, "
            f"and gives its own {p} {out[c][p][1]}"
            for p in sorted(needed.get(c, set()) & set(out.get(r, {})) & set(out.get(c, {})))
            if out[r][p] != out[c][p]]
    if torn[True]:
        print("peers no tree holds: " + "; ".join(sorted(set(torn[True]))[:5]))
        return 4
    if torn[False]:
        raise RuntimeError("peers this placement does not hold: "
                           + "; ".join(sorted(set(torn[False]))[:5]))

    def claims(r, c):
        """the providers our answer gives c's peers where r requires it.  An
        optional peer c requires the name of itself resolves by c's own
        lookup, whatever r gives, and npm judges that it is in range."""
        return tuple(sorted((p, out[r][p]) for p in peers.get(c, ()) if p in out.get(r, {})
                            and (p in needed.get(c, ()) or p not in out.get(c, {}))))

    at, links = place(root, nodes, edges, claims, peers)

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
        if path in links:
            packages[path] = {"resolved": links[path], "link": True}
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
    print(f"{dst}: {len(at) - len(links)} placements and {len(links)} links for "
          f"{len(nodes)} packages, {len(edges)} edges, max nesting {depth}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
