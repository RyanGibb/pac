#!/usr/bin/env python3
"""Our answer as a Yarn Berry project, for berry.sh.

prepare  writes the project: package.json with the query's dependencies,
         the peers our answer installs at the root beside them (which a
         Berry user lists there), and one pin per package of the answer,
         an alias that makes Berry resolve and lock exactly that version;
         .yarnrc.yml pointing at berryreg.py; and expect.json, what the
         answer says each copy loads, for berryprobe.cjs.
patch    moves each descriptor our answer resolves to the lockfile entry
         of the version it chose, and drops the pins, from package.json
         and the lockfile alike.  Berry keeps a locked resolution, so the
         next install resolves our answer rather than its own picks.
compare  whether the lockfile Berry then wrote still resolves every
         descriptor of our answer as we did.

A descriptor is a directory and its spec as the manifest writes it, the
spec being Berry's own reading: npm: before a range or tag.  Manifests are
read as the common core reads them (core.py), packageExtensions included,
so a dependency Berry adds is a descriptor too.

usage: berrylock.py prepare <snapshot> <our --tree output> <dir> <port> <query...>
       berrylock.py patch <dir>
       berrylock.py compare <dir>
"""
import json
import os
import re
import sys

from core import normalize, split
from tree import escape, parse_tree

ROOT = "pac-berry-root"


def manifest(cache, name, version):
    with open(os.path.join(cache, escape(name) + ".json")) as f:
        return json.load(f)["versions"][version]


def berry_spec(raw):
    return raw if raw.startswith("npm:") else "npm:" + raw


def query_specs(args):
    """key -> spec as pac reads npm install's arguments, a package.json
    among them giving its own dependencies"""
    out = {}
    for a in args:
        if a.endswith("package.json") and os.path.isfile(a):
            with open(a) as f:
                pj = json.load(f)
            for field in ("dependencies", "optionalDependencies", "devDependencies"):
                out.update(pj.get(field) or {})
            continue
        i = a.find("@", 1)
        k, raw = (a, "*") if i < 0 else (a[:i], a[i + 1:] or "*")
        out[k] = raw
    return out


def descriptors(cache, root, edges, qspecs):
    """(berry descriptor, locator) for each edge of our answer, and the
    root's dependencies"""
    rootdeps, out = {}, []
    mans = {}
    for r, key, c in edges:
        if r == root:
            raw = qspecs.get(key, c[1] if key == c[0] else "npm:%s@%s" % (c[0], c[1]))
            rootdeps[key] = raw
        else:
            if r not in mans:
                mans[r] = normalize(manifest(cache, r[0], r[1]), r[0], r[1])
            m = mans[r]
            raw = (m.get("optionalDependencies") or {}).get(key) or (m.get("dependencies") or {}).get(key)
            if raw is None:
                continue
        out.append(("%s@%s" % (key, berry_spec(raw)), "%s@npm:%s" % (c[0], c[1])))
    return rootdeps, out


def prepare(cache, ours, d, port, args):
    with open(ours) as f:
        root, nodes, edges = parse_tree(f.read())
    rootdeps, descs = descriptors(cache, root, edges, query_specs(args))
    os.makedirs(d, exist_ok=True)
    pins = {"__pin%d" % i: "npm:%s@%s" % (n[0], n[1])
            for i, n in enumerate(sorted({(n[0], n[1]) for n in nodes if n != root}))}
    with open(os.path.join(d, "package.json"), "w") as f:
        json.dump({"name": ROOT, "version": "0.0.0", "private": True,
                   "dependencies": dict(rootdeps, **pins)}, f, indent=2)
    # one descriptor resolved two ways is an answer no lockfile holds
    seen = {}
    for k, loc in descs:
        seen.setdefault(k, set()).add(loc)
    split_ = sorted(k for k, locs in seen.items() if len(locs) > 1)
    with open(os.path.join(d, ".yarnrc.yml"), "w") as f:
        f.write('npmRegistryServer: "http://127.0.0.1:%s"\n'
                'unsafeHttpWhitelist: ["127.0.0.1"]\n'
                "nodeLinker: pnp\nenableTelemetry: false\nenableGlobalCache: false\n"
                "cacheFolder: ./.yarn/cache\nenableScripts: false\n"
                "enableImmutableInstalls: false\nenableProgressBars: false\n"
                "httpTimeout: 600000\n" % port)
    open(os.path.join(d, "yarn.lock"), "w").close()
    # what each copy loads: its rows, and the peers it declares as the core
    # reads them, whose provider its depender decides (berryprobe.cjs)
    rows = {}
    for r, key, c in edges:
        rows.setdefault(r, {})[key] = c
    ids = {n: "%s@%s@%s" % n for n in nodes}
    ids[root] = ""
    exp, extra = {}, []
    for n in nodes:
        if n == root:
            peers, deps, conds = {}, set(rows.get(n, {})), False
        else:
            m = manifest(cache, n[0], n[1])
            deps, peers, _ = split(normalize(m, n[0], n[1]), set(rows.get(n, {})))
            conds = any(m.get(k) for k in ("os", "cpu", "libc"))
        # a copy the answer puts where no manifest asks for one, which no
        # Berry project can hold
        extra += ["%s -> %s" % (ids[n], k) for k in rows.get(n, {}) if k not in deps]
        exp[ids[n]] = {"name": ROOT if n == root else n[0], "version": n[1],
                       "rows": {k: ids[c] for k, c in rows.get(n, {}).items() if k in deps},
                       "peers": peers, "conds": conds}
    with open(os.path.join(d, "pins.json"), "w") as f:
        json.dump({"pins": sorted(pins), "descriptors": dict(descs), "split": split_,
                   "extra": extra}, f, indent=1)
    with open(os.path.join(d, "expect.json"), "w") as f:
        json.dump(exp, f, indent=1)
    print("%d nodes, %d edges, %d descriptors, %d pins" % (len(nodes), len(edges), len(descs), len(pins)))
    print("split %d extra %d" % (len(split_), len(extra)))


def read_lock(path):
    """[(keys, resolution, body lines)], the header kept as keys None"""
    with open(path) as f:
        blocks = f.read().split("\n\n")
    out = []
    for b in blocks:
        lines = [l for l in b.split("\n") if l != ""]
        if not lines:
            continue
        if lines[0].startswith("#") or not lines[0].endswith(":") or lines[0].startswith("__metadata"):
            out.append((None, None, lines))
            continue
        head = lines[0][:-1].strip('"')
        keys = [k.strip() for k in head.split(",")]
        m = next((re.match(r'^  resolution: "?([^"]*)"?$', l) for l in lines[1:]
                  if l.startswith("  resolution:")), None)
        out.append((keys, m.group(1) if m else None, lines[1:]))
    return out


def write_lock(path, entries):
    parts = []
    for keys, res, body in entries:
        if keys is None:
            parts.append("\n".join(body))
        elif keys:
            parts.append("\n".join(['"%s":' % ", ".join(sorted(keys))] + body))
    with open(path, "w") as f:
        f.write("\n\n".join(parts) + "\n")


def patch(d):
    with open(os.path.join(d, "pins.json")) as f:
        p = json.load(f)
    pins, descs = set(p["pins"]), p["descriptors"]
    ents = read_lock(os.path.join(d, "yarn.lock"))
    by_res = {}
    for i, (keys, res, body) in enumerate(ents):
        if keys is not None and res is not None:
            by_res.setdefault(res, i)
    moved = {i: [] for i in range(len(ents))}
    missing = 0
    for i, (keys, res, body) in enumerate(ents):
        if keys is None:
            continue
        keep = []
        for k in keys:
            if k.split("@npm:", 1)[0] in pins or k.split("@", 2)[0] in pins:
                continue
            want = descs.get(k)
            if want is None or want == res:
                keep.append(k)
            elif want in by_res:
                moved[by_res[want]].append(k)
            else:
                missing += 1
                keep.append(k)
        ents[i] = (keep, res, body)
    out = []
    for i, (keys, res, body) in enumerate(ents):
        if keys is None:
            out.append((keys, res, body))
            continue
        keys = keys + moved[i]
        if res and res.endswith("@workspace:."):
            body = [l for l in body if not re.match(r"^    __pin\d+:", l)]
        out.append((keys, res, body))
    write_lock(os.path.join(d, "yarn.lock"), out)
    with open(os.path.join(d, "package.json")) as f:
        pk = json.load(f)
    pk["dependencies"] = {k: v for k, v in pk.get("dependencies", {}).items() if k not in pins}
    with open(os.path.join(d, "package.json"), "w") as f:
        json.dump(pk, f, indent=2)
    print("moved %d descriptors, %d with no entry for our version" % (sum(map(len, moved.values())), missing))


def compare(d):
    with open(os.path.join(d, "pins.json")) as f:
        descs = json.load(f)["descriptors"]
    got = {}
    for keys, res, _ in read_lock(os.path.join(d, "yarn.lock")):
        for k in keys or ():
            got[k] = res
    off = sorted(k for k, want in descs.items() if got.get(k) != want)
    for k in off[:10]:
        print("%s: ours %s, Berry's %s" % (k, descs[k], got.get(k)))
    print("descriptors %d, off %d" % (len(descs), len(off)))
    return 1 if off else 0


if __name__ == "__main__":
    cmd = sys.argv[1]
    if cmd == "prepare":
        prepare(sys.argv[2], sys.argv[3], sys.argv[4], sys.argv[5], sys.argv[6:])
    elif cmd == "patch":
        patch(sys.argv[2])
    elif cmd == "compare":
        sys.exit(compare(sys.argv[2]))
