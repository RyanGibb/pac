"""The two trees the npm scripts read: pac's --tree output, and a
package-lock's node_modules paths, which a lookup walks as require()
does."""
import re

# "name 1.2.3" or "name 1.2.3 at dir", and the root may have no version
SIDE = re.compile(r"^(\S+)(?: (\S+?))?(?: at (\S+))?$")


def escape(name):
    return name.replace("/", "%2F")


def parse_side(s):
    """(name, version, key): a copy is named by the directory it sits in,
    which is its name unless an alias put it elsewhere"""
    m = SIDE.match(s)
    if not m:
        raise ValueError(s)
    name, ver, at = m.group(1), m.group(2) or "", m.group(3)
    return name, ver, (at if at else name)


def parse_tree(text):
    m = re.search(r"^root (.*)$", text, re.M)
    root = parse_side(m.group(1)) if m else None
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
            nodes.add(parse_side(body))
        elif section == "e":
            p, c = body.split(" <- ", 1)
            child = parse_side(c)
            edges.append((parse_side(p), child[2], child))
    return root, nodes, edges


def ancestors(path):
    """"" then each package directory on the way down to path, shallowest
    first: the directories whose node_modules a lookup from path can see.
    A scoped name spends two segments, so the walk consumes "node_modules"
    plus one or two, rather than splitting on the separator."""
    out = [""]
    segs = path.split("/") if path else []
    i = 0
    while i < len(segs):
        take = 3 if i + 1 < len(segs) and segs[i + 1].startswith("@") else 2
        out.append("/".join(segs[:i + take]))
        i += take
    return out


def slot(anc, key):
    return (anc + "/node_modules/" if anc else "node_modules/") + key


def resolve(pkgs, path, key):
    for anc in reversed(ancestors(path)):
        if slot(anc, key) in pkgs:
            return slot(anc, key)
    return None
