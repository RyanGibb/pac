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
          shadowed.  This is what makes the old rule's monotonicity
          argument false -- a lookup does stop at the first hit walking
          upward, but a new slot can *be* that first hit.  So a free
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
          resolves a peer from the declarer's parent -- a copy in the
          declarer's own node_modules is PEER LOCAL, an invalid edge
          (arborist edge.js) -- and our answer puts the peer beside the
          declarer, among its requirer's edges.  Hoisted any higher, the
          declarer would look its peer up from a directory that may hold
          another version, which `npm ci` then rejects although the answer
          is one npm accepts.  For the same reason, a name the requirer
          itself peers on goes beside the requirer rather than inside it.

          npm's arborist decides the same question with a third move we
          deliberately do not make: an occupied slot may be taken over,
          evicting an incumbent that could still be pushed deeper
          (can-place-dep.js REPLACE).  Adding that would make this
          writer a small reimplementation of arborist, and `npm ci`
          accepting the result would then be testing the clone rather
          than our solver.  Refusing to evict costs some nesting and
          nothing else, and is a rule that stands on its own.

  verify  re-resolve every edge against the finished tree and fail if
          any of them does not come out right.  Placement is correct by
          construction, so this is an assertion rather than a repair:
          the one thing that must never happen is a lockfile that
          quietly describes a different answer from ours, and stopping
          is the only response to that which does not.

Every other field is copied, not decided: version, resolved and
integrity come from the snapshot packument's own dist block, and the
dependency maps come from that version's manifest, so the lockfile
describes the same packages our solver read.  An aliased slot (the key
differs from the registry name) carries "name", the way npm records one.

usage: mklock.py <cache-dir> <our --tree output> <out package-lock.json>
       [--root-manifest <package.json>]
"""
import json
import os
import re
import sys

SIDE = re.compile(r"^(\S+) (\S+?)(?: at (\S+))?$")


def escape(name):
    return name.replace("/", "%2F")


def parse_side(s):
    m = SIDE.match(s)
    if not m:
        raise ValueError(s)
    name, ver, at = m.group(1), m.group(2), m.group(3)
    return name, ver, (at if at else name)


def parse_ours(text):
    m = re.search(r"^root (\S+) (\S+)", text, re.M)
    if not m:
        raise RuntimeError("no root line")
    root = (m.group(1), m.group(2))
    nodes, edges = set(), []
    section = None
    for line in text.splitlines():
        if line.startswith("packages ("):
            section = "p"
            continue
        if line.startswith("node_modules ("):
            section = "e"
            continue
        if not line.startswith("  "):
            section = None
            continue
        body = line[2:]
        if section == "p":
            n, v, _ = parse_side(body)
            nodes.add((n, v))
        elif section == "e":
            p, c = body.split(" <- ", 1)
            pn, pv, _ = parse_side(p)
            cn, cv, cd = parse_side(c)
            edges.append(((pn, pv), cd, (cn, cv)))
    return root, nodes, edges


def ancestors(path):
    """"" then each package directory on the way down to path, shallowest
    first: the directories whose node_modules a lookup from path can see.
    A scoped name spends two segments, so the walk consumes "node_modules"
    plus one or two, rather than splitting on the separator."""
    out = [""]
    if not path:
        return out
    segs = path.split("/")
    cur = []
    i = 0
    while i < len(segs):
        if segs[i] != "node_modules":
            raise ValueError(path)
        take = 3 if (i + 1 < len(segs) and segs[i + 1].startswith("@")) else 2
        cur += segs[i:i + take]
        out.append("/".join(cur))
        i += take
    return out


def place(root, edges, declarers=frozenset(), peers={}):
    out_edges = {}
    for r, key, c in edges:
        out_edges.setdefault(r, []).append((key, c))

    at = {"": root}                 # path -> (name, version)
    paths = {root: [""]}            # node -> its paths
    answered = {}                   # key -> [(requirer path, answering dir)]

    def slot(anc, key):
        return (anc + "/node_modules/" + key) if anc else "node_modules/" + key

    def resolve(path, key):
        for anc in reversed(ancestors(path)):
            if slot(anc, key) in at:
                return slot(anc, key)
        return None

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

    frontier = [("", root)]
    seen = {("", root)}
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
            # (PEER LOCAL), so a name the requirer peers on goes beside it
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
                at[dst] = child
                paths.setdefault(child, []).append(dst)
            answered.setdefault(key, []).append((path, target))
            if (dst, child) not in seen:
                seen.add((dst, child))
                frontier.append((dst, child))

    for node, ps in paths.items():
        for path in ps:
            for key, child in out_edges.get(node, ()):
                q = resolve(path, key)
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
        root, nodes, edges = parse_ours(f.read())

    declarers, peers = set(), {}
    for n in nodes:
        m = manifest(cache, n[0], n[1])
        meta = m.get("peerDependenciesMeta")
        meta = meta if isinstance(meta, dict) else {}
        # a dependency of the same name replaces the peer
        deps = set(m.get("dependencies") or {}) | set(m.get("optionalDependencies") or {})
        peers[n] = set(m.get("peerDependencies") or {}) - deps
        if any(not (meta.get(p) or {}).get("optional") for p in peers[n]):
            declarers.add(n)
    at = place(root, edges, declarers, peers)
    placed = {n for n in at.values()}
    orphans = sorted(nodes - placed)

    packages = {}
    rm = rootman or {}
    packages[""] = {k: v for k, v in (
        ("name", rm.get("name", root[0])),
        ("version", rm.get("version", root[1])),
        ("license", rm.get("license")),
        ("dependencies", rm.get("dependencies")),
        ("devDependencies", rm.get("devDependencies")),
        ("optionalDependencies", rm.get("optionalDependencies")),
    ) if v}
    for path in sorted(at):
        if path == "":
            continue
        name, version = at[path]
        key = path.rsplit("node_modules/", 1)[-1]
        packages[path] = entry(cache, name, version, key)

    lock = {
        "name": packages[""]["name"],
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
          f"{len(edges)} edges, max nesting {depth}"
          + (f", ORPHANS {orphans}" if orphans else ""))
    return 1 if orphans else 0


if __name__ == "__main__":
    sys.exit(main())
