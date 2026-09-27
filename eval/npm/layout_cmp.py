#!/usr/bin/env python3
"""Score one answer lock against npm's own lock, both as layouts and as
resolution relations.

  layout    {lock path: (registry name, version)}, links and the root left
            out: whether npm's tree and ours put the same package at the
            same place.
  relation  edges.py's reading of each lock -- the nodes, and each edge
            resolved by walking node_modules up from its depender, a peer
            from its declarer -- the same reader on both sides.

usage: layout_cmp.py <our lock> <npm's lock>
Prints "layout=exact|diff <ours>,<npm>,<agree> relation=exact|diff
<nodes ours,npm,agree>,<edges ours,npm,agree>".
"""
import json
import sys

from edges import lock_sets


def layout(lock):
    return {(p, e.get("name", p.rsplit("node_modules/", 1)[-1]), e.get("version", ""))
            for p, e in lock["packages"].items() if p and not e.get("link")}


def main():
    with open(sys.argv[1]) as f:
        ours = json.load(f)
    with open(sys.argv[2]) as f:
        theirs = json.load(f)
    lo, lt = layout(ours), layout(theirs)
    on, oe, _, _ = lock_sets(ours, False)
    tn, te, _, _ = lock_sets(theirs, False)
    lx = "exact" if lo == lt else "diff"
    rx = "exact" if on == tn and oe == te else "diff"
    print(f"layout={lx} {len(lo)},{len(lt)},{len(lo & lt)} "
          f"relation={rx} {len(on)},{len(tn)},{len(on & tn)},{len(oe)},{len(te)},{len(oe & te)}")


if __name__ == "__main__":
    main()
