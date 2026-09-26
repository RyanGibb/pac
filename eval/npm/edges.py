#!/usr/bin/env python3
"""Score one query: our resolution against npm's, on nodes and on edges.

Both sides are reduced to the same two sets.

  nodes   (registry-name, version) pairs, the root included.  npm's tree
          nests duplicate versions at different depths and our solution
          carries one granular node per (key, version), so a name may
          legitimately appear twice on either side; the pair is the unit
          on both, and a duplicate placed twice on npm's side collapses
          to the one pair it is.

  edges   (requirer-name, requirer-version, directory, provider-name,
          provider-version).  This is the resolution relation, not the
          directory layout: npm hoists to dedupe on disk, which is a
          separate question, and lockfileVersion 3 records enough to
          reconstruct resolution independently of placement -- each
          node's own dependency ranges, resolved by walking the
          node_modules chain upwards from that node's path, which is
          exactly what require() would do.

  The directory component is the manifest key rather than the registry
  name so that an alias (npm:pkg@range) is compared as the alias it is.

One optional normalisation names a difference between the two answers
that is not a difference of resolution, applied to npm's side alone so
the delta it accounts for can be read off:

  --peer-parent   re-attribute an auto-installed peer's edge from the
                  package that declared the peer to each package that
                  selected the declarer, by a dependency or by a peer
                  edge itself re-attributed.  Where both sides put the
                  peer in the same place, they disagree only about which
                  node the edge leaves.  npm's lockfile resolves a peer
                  the way require() would, from the declarer; pac hangs
                  the declarer's peer edges on the package that selected
                  it.

usage: edges.py <package> <lockfile> <our --tree output> <out-prefix>
                [--peer-parent]
"""
import json
import sys

from tree import parse_tree, resolve

def node_name(path, entry):
    # an aliased node carries the registry name in "name"; a plain one is
    # named by the directory it sits in
    if "name" in entry:
        return entry["name"]
    return path.rsplit("node_modules/", 1)[-1]


def lock_sets(lock, peer_parent):
    pkgs = lock["packages"]

    # (requirer path, directory, provider path), kept as paths so the peer
    # re-attribution can ask who required the declarer before identities
    # collapse distinct placements of one version
    plain, peer, unresolved = [], [], set()
    for path, e in pkgs.items():
        meta = e.get("peerDependenciesMeta", {})
        deps = set(e.get("dependencies", {})) | set(e.get("optionalDependencies", {}))
        for d in sorted(deps):
            q = resolve(pkgs, path, d)
            (plain.append((path, d, q)) if q else unresolved.add((path, d)))
        # npm >=7 installs a peer unless the declarer marks it optional, and
        # a dependency of the same name replaces the peer's edge
        for d in sorted(e.get("peerDependencies", {})):
            if meta.get(d, {}).get("optional", False) or d in deps:
                continue
            q = resolve(pkgs, path, d)
            (peer.append((path, d, q)) if q else unresolved.add((path, d)))

    live = set(pkgs)
    plain = [(r, d, q) for (r, d, q) in plain if r in live and q in live]
    peer = [(r, d, q) for (r, d, q) in peer if r in live and q in live]

    if peer_parent:
        # a declarer installed only as another declarer's peer was selected
        # by wherever that peer edge was moved, so selection is closed over
        # the moved edges too; otherwise the declarer's own peer edge has
        # nowhere to go and drops out
        requirers = {"": {""}}
        for r, _, q in plain:
            requirers.setdefault(q, set()).add(r)
        while True:
            moved = {
                (r2, d, q)
                for (r, d, q) in peer
                for r2 in requirers.get(r, ())
            }
            grown = False
            for r2, _, q in moved:
                if r2 not in requirers.setdefault(q, set()):
                    requirers[q].add(r2)
                    grown = True
            if not grown:
                break
        peer = sorted(moved)

    ident = {p: (node_name(p, pkgs[p]), pkgs[p].get("version", "")) for p in live}
    ident[""] = ROOT
    nodes = set(ident.values())
    edges = {
        (ident[r][0], ident[r][1], d, ident[q][0], ident[q][1])
        for (r, d, q) in plain + peer
    }
    # npm copied these out of the bundler's tarball rather than resolving
    # them, and a bundled version need not even be published, so verdict.py
    # has to tell them apart by path before identities collapse
    bundled = {
        (ident[r][0], ident[r][1], d, ident[q][0], ident[q][1])
        for (r, d, q) in plain + peer
        if pkgs[r].get("inBundle") or pkgs[q].get("inBundle")
    }
    unres = {(node_name(p, pkgs[p]), pkgs[p].get("version", ""), d)
             for (p, d) in unresolved if p in live}
    return nodes, edges, unres, bundled


# The root is the query, which both sides name as they please -- npm by its
# directory, pac as the manifest does or "." -- so it is compared as the
# root, the way npm's lock keys it.
ROOT = ("", "")


def our_sets(text):
    root, nodes, edges = parse_tree(text)
    ident = lambda n: ROOT if root and n[:2] == root[:2] else n[:2]
    return ({ident(n) for n in nodes},
            {ident(p) + (key,) + ident(c) for p, key, c in edges})


def dump(path, s):
    with open(path, "w") as f:
        for x in sorted(s):
            f.write("\t".join(x) + "\n")


def main():
    pkg, lockp, oursp, prefix = sys.argv[1:5]
    flags = sys.argv[5:]
    with open(lockp) as f:
        lock = json.load(f)
    nn, ne, nu, nb = lock_sets(lock, "--peer-parent" in flags)
    with open(oursp) as f:
        on, oe = our_sets(f.read())

    dump(prefix + ".nodes.ours", on)
    dump(prefix + ".nodes.npm", nn)
    dump(prefix + ".edges.ours", oe)
    dump(prefix + ".edges.npm", ne)
    dump(prefix + ".nodes.oursonly", on - nn)
    dump(prefix + ".nodes.npmonly", nn - on)
    dump(prefix + ".edges.oursonly", oe - ne)
    dump(prefix + ".edges.npmonly", ne - oe)
    dump(prefix + ".unresolved.npm", nu)
    dump(prefix + ".edges.bundled", nb)

    # the trailing #-field is what scale.sh totals; the rest is for reading
    print(
        "%-24s nodes ours=%-4d npm=%-4d agree=%-4d ours-only=%-3d npm-only=%-3d "
        "| edges ours=%-4d npm=%-4d agree=%-4d ours-only=%-3d npm-only=%-3d "
        "#%d,%d,%d,%d,%d,%d"
        % (
            pkg,
            len(on),
            len(nn),
            len(on & nn),
            len(on - nn),
            len(nn - on),
            len(oe),
            len(ne),
            len(oe & ne),
            len(oe - ne),
            len(ne - oe),
            len(on),
            len(nn),
            len(on & nn),
            len(oe),
            len(ne),
            len(oe & ne),
        )
    )


if __name__ == "__main__":
    main()
