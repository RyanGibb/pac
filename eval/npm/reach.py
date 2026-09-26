#!/usr/bin/env python3
"""Each package of a package-lock.json that nothing reaches from the root,
as "unreached <path>": the entries `npm install --package-lock-only`
prunes because nothing needs them, not because anything is wrong with
them.  npm judges none of their own dependencies either, so each one a
registry range names that lookup does not meet is "unmet <path> <key>
<spec>".

An edge is followed where node_modules lookup takes it from its
requirer, a peer's included: npm resolves a peer from its declarer too,
and a copy the declarer holds in its own node_modules is PEER LOCAL, an
invalid edge (arborist edge.js), so such a copy counts as reached and
its removal as a repair.  Ranges are read by ranges.js, with npm's own
npm-package-arg and semver.

usage: reach.py <package-lock.json>
"""
import json
import os
import subprocess
import sys

from tree import resolve

HERE = os.path.dirname(os.path.abspath(__file__))


def edges(pk, p):
    e = pk[p]
    fields = ["dependencies", "optionalDependencies", "peerDependencies"]
    if p == "":
        fields.append("devDependencies")
    meta = e.get("peerDependenciesMeta") or {}
    return [(key, spec, f == "optionalDependencies" or
             (f == "peerDependencies" and bool((meta.get(key) or {}).get("optional"))))
            for f in fields for key, spec in (e.get(f) or {}).items()]


def main():
    pk = json.load(open(sys.argv[1], encoding="utf-8"))["packages"]
    seen, todo = {""}, [""]
    while todo:
        p = todo.pop()
        for key, _, _ in edges(pk, p):
            q = resolve(pk, p, key)
            if q is not None and q not in seen:
                seen.add(q)
                todo.append(q)
    unreached = sorted(p for p in pk if p not in seen)
    asks = []
    for p in unreached:
        for key, spec, optional in edges(pk, p):
            q = resolve(pk, p, key)
            asks.append((p, key, spec, optional, q))
    out = subprocess.run(["node", os.path.join(HERE, "ranges.js")], check=True,
                         input=json.dumps([{"key": k, "spec": s,
                                            "version": pk[q].get("version") if q is not None else None}
                                           for _, k, s, _, q in asks]),
                         capture_output=True, text=True).stdout
    unmet = {}
    for (p, key, spec, optional, q), ok in zip(asks, json.loads(out)):
        if ok is not None and (not optional if q is None else not ok):
            unmet.setdefault(p, []).append(f"unmet {p} {key} {spec}")
    for p in unreached:
        print("unreached " + p)
        for line in unmet.get(p, []):
            print(line)


if __name__ == "__main__":
    main()
