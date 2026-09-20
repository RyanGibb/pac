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
          root to that requirer whose slot for the key is either free or
          already holds that same provider.  Adding a placement in a
          free slot can never change a resolution that already
          succeeded, since a lookup walks from the deepest directory
          upward and stops at the first hit -- so the rule is monotone
          and hoists as far as the relation allows.

  verify  re-resolve every edge against the finished tree and nest any
          provider that does not come out right, to a fixpoint.  This
          should never fire; it is here so that a placement bug shows up
          as a deeper tree rather than as a silently different answer
          handed to npm.

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
MAXDEPTH = 40


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


def place(root, edges):
    out_edges = {}
    for r, key, c in edges:
        out_edges.setdefault(r, []).append((key, c))

    at = {"": root}                 # path -> (name, version)
    paths = {root: [""]}            # node -> its paths

    def resolve(path, key):
        for anc in reversed(ancestors(path)):
            cand = (anc + "/node_modules/" + key) if anc else "node_modules/" + key
            if cand in at:
                return cand
        return None

    def slot(path, key):
        # shallowest visible node_modules whose key is free or already ours
        return [((anc + "/node_modules/" + key) if anc else "node_modules/" + key)
                for anc in ancestors(path)]

    frontier = [("", root)]
    seen = {("", root)}
    while frontier:
        path, node = frontier.pop(0)
        for key, child in out_edges.get(node, ()):
            target = None
            for cand in slot(path, key):
                if cand not in at:
                    target = cand
                    break
                if at[cand] == child:
                    target = cand
                    break
            if target is None:
                raise RuntimeError(f"no slot for {key} under {path}")
            if target not in at:
                at[target] = child
                paths.setdefault(child, []).append(target)
            if (target, child) not in seen:
                seen.add((target, child))
                frontier.append((target, child))

    # fixpoint check: every edge must resolve to the provider we chose
    for _ in range(MAXDEPTH):
        bad = 0
        for node, ps in list(paths.items()):
            for path in list(ps):
                for key, child in out_edges.get(node, ()):
                    q = resolve(path, key)
                    if q is None or at[q] != child:
                        forced = (path + "/node_modules/" + key) if path \
                            else "node_modules/" + key
                        at[forced] = child
                        paths.setdefault(child, []).append(forced)
                        bad += 1
        if bad == 0:
            break
    else:
        raise RuntimeError("placement did not converge")
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

    at = place(root, edges)
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
