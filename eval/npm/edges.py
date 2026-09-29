#!/usr/bin/env python3
"""Score one query, pac's resolution against npm's lock, on nodes,
(registry name, version) pairs with the root, and on edges, (requirer
name, requirer version, directory, provider name, provider version): the
resolution relation, read off the lock by walking node_modules up from
each requirer as require() does, and not its layout.  The directory is
the manifest key, so that an alias is compared as the alias it is.

--peer-parent hangs each auto-installed peer's edge in npm's lock on the
package that selected its declarer, as pac does, rather than on the
declarer, from which npm resolves it.

usage: edges.py <package> <lockfile> <our --tree output> <out-prefix>
                [--peer-parent]
"""
import json
import sys

from tree import is_link, parse_tree, resolve

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
        # a link is the package it points at, which resolve() follows
        if is_link(e):
            continue
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

    live = {p for p, e in pkgs.items() if not is_link(e)}
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
        # a peer resolving to the declarer's own requirer is that requirer
        # offering itself, which pac's answer holds no edge for
        peer = [(r, d, q) for (r, d, q) in peer if q not in requirers.get(r, ())]

        def peers_on(path, d):
            e = pkgs[path]
            deps = set(e.get("dependencies", {})) | set(e.get("optionalDependencies", {}))
            return d in e.get("peerDependencies", {}) and d not in deps

        # a requirer other than the root that peers on d holds none of it
        # (arborist's PEER LOCAL), so the edge goes on up to its requirers
        def hangs(r, d, seen):
            out = set()
            for r2 in requirers.get(r, ()):
                if r2 != "" and peers_on(r2, d):
                    if r2 not in seen:
                        out |= hangs(r2, d, seen | {r2})
                else:
                    out.add(r2)
            return out

        while True:
            moved = {
                (r2, d, q)
                for (r, d, q) in peer
                for r2 in hangs(r, d, {r})
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
