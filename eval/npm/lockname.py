#!/usr/bin/env python3
"""Fail if some edge of a package-lock.json lands on a different registry
package from the one its depender's manifest names.

npm checks an edge against the entry its node_modules lookup finds by
version alone (arborist dep-valid.js); the only name it compares is the
directory key (edge.js satisfiedBy), since that is what lets an alias sit
at a key that is not its package's name.  So neither
`npm ci` nor a relock notices baz@1.0.0 at node_modules/bar answering
"bar": "^1".  An entry's registry package is its "name" when it has one
and its key otherwise, which is how npm records an alias and how
mklock.py writes our answer.  A link names the package it points at.  A
peer is the exception: it takes an alias sitting at its name, as npm and
Yarn Berry both offer a holder's alias to its dependencies' peers.

usage: lockname.py <package-lock.json>
Exits 3 on a mismatch, so that a crash, which exits 1, is not read as one.
"""
import json
import os
import sys

from tree import ancestors, resolve

CORE = os.environ.get("PAC_NPM_CORE") == "1"

FIELDS = ("dependencies", "optionalDependencies", "peerDependencies",
          "devDependencies")


def target(key, spec):
    """the registry package spec names at key, or None when it names
    something off the registry, whose identity npm does not take from a name"""
    if not isinstance(spec, str):
        return None
    if spec.startswith("npm:"):
        body = spec[4:]
        i = body.find("@", 1)
        return body[:i] if i >= 0 else body
    if ":" in spec or "/" in spec:
        return None
    return key


def main():
    with open(sys.argv[1]) as f:
        pk = json.load(f)["packages"]
    bad = 0
    for path, e in sorted(pk.items()):
        for field in FIELDS:
            if field == "devDependencies" and path:
                continue
            for key, spec in (e.get(field) or {}).items():
                want = target(key, spec)
                if want is None:
                    continue
                # a copy inside the declarer is PEER LOCAL (arborist
                # edge.js), which check.sh judges
                frm = path
                if field == "peerDependencies" and path:
                    frm = ancestors(path)[-2]
                q = resolve(pk, frm, key)
                if q not in pk:
                    continue
                got = pk[q].get("name") or q.rsplit("node_modules/", 1)[-1]
                # a peer takes whatever sits at its name, an alias a holder
                # installed there too, by version alone; relation.py asks
                # that it be the copy our answer offers
                if field == "peerDependencies" and got != key:
                    continue
                # under the common core a dependency beside a peer of its
                # name is a peer with default, which takes what the depender
                # offers under the peer's name: an aliased dependency then
                # finds the name's own package, as npm and Berry both load
                peer = (e.get("peerDependencies") or {}).get(key)
                if (CORE and field != "peerDependencies" and peer is not None
                        and got == target(key, peer)):
                    continue
                if got != want:
                    print(f"{path or '(root)'} {field} {key}: {spec} "
                          f"names {want}, {q} is {got}")
                    bad = 3
    return bad


if __name__ == "__main__":
    sys.exit(main())
