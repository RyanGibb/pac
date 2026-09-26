#!/usr/bin/env bash
# usage: controls.sh <scratch-dir>        PORT=<free port for the shim>
set -u
export LC_ALL=C
S="$(cd "$(dirname "$0")" && pwd)"
T=$(mkdir -p "$1" && cd "$1" && pwd)
PORT=${PORT:-8899}
bad=0

rm -rf "$T/cache" "$T/home" "$T/work"
mkdir -p "$T/cache" "$T/home" "$T/work"
: > "$T/home/.npmrc"; : > "$T/home/npmrc-global"

# a: optional peer b@^2.  p: peer b@^1.  q: peer r@^1.  c: b@^1.  y: r@^1.
python3 - "$T" <<'EOF'
import base64, hashlib, json, os, sys
T = sys.argv[1]
PKGS = {
    "a": {"1.0.0": {"peerDependencies": {"b": "^2.0.0"},
                    "peerDependenciesMeta": {"b": {"optional": True}}}},
    "p": {"1.0.0": {"peerDependencies": {"b": "^1.0.0"}}},
    "b": {"1.0.0": {}, "1.1.0": {}, "2.0.0": {}},
    "c": {"1.0.0": {"dependencies": {"b": "^1.0.0"}}},
    "z": {"1.0.0": {}},
    "q": {"1.0.0": {"peerDependencies": {"r": "^1.0.0"}}},
    "r": {"1.0.0": {}},
    "baz": {"1.0.0": {}},
    "d": {"1.0.0": {"dependencies": {"b": "npm:baz@^1.0.0"}}},
    "y": {"1.0.0": {"dependencies": {"r": "^1.0.0"}}},
    "w": {"1.0.0": {"dependencies": {"s": "^1.0.0"}}},
    "s": {"1.0.0": {}, "1.1.0": {}, "2.0.0": {}},
    "bl": {"1.0.0": {"dependencies": {"u": "^1.0.0"}}, "1.1.0": {"dependencies": {"u": "^1.0.0"}}},
    "u": {"1.0.0": {"peerDependencies": {"bl": "^1.0.0"}}},
    "at": {"1.0.0": {"dependencies": {"ot": "^1.0.0"}}, "2.0.0": {"dependencies": {"ot": "^2.0.0"}}},
    "ot": {"1.0.0": {"dependencies": {"at": "^2.0.0"}}, "2.0.0": {"dependencies": {"at": "^1.0.0"}}},
    "cy": {"1.0.0": {"dependencies": {"oz": "^1.0.0"}}, "2.0.0": {"dependencies": {"cy": "^1.0.0"}}},
    "oz": {"1.0.0": {"dependencies": {"cy": "^2.0.0"}}},
    "sx": {"1.0.0": {"dependencies": {"sx": "^2.0.0"}}, "2.0.0": {"dependencies": {"sx": "^1.0.0"}}},
    "k1": {"1.0.0": {"dependencies": {"d1": "^1.0.0"}}, "2.0.0": {"dependencies": {"k1": "^1.0.0"}}},
    "d1": {"1.0.0": {"peerDependencies": {"k1": "^2.0.0"}}},
    "yc": {"1.0.0": {"dependencies": {"yc": "npm:xc@^1.0.0"}}},
    "xc": {"1.0.0": {"dependencies": {"yc": "^1.0.0"}}},
    "dx": {"1.0.0": {"dependencies": {"rx": "^1.0.0"}, "peerDependencies": {"px": "^1.0.0"}}},
    "rx": {"1.0.0": {"dependencies": {"dx": "^1.0.0"}}, "2.0.0": {}},
    "px": {"1.0.0": {}, "2.0.0": {}},
    "de": {"1.0.0": {"dependencies": {"re": "^1.0.0", "qe": "^1.0.0"},
                     "peerDependencies": {"pe": "^1.0.0"}}},
    "re": {"1.0.0": {"dependencies": {"de": "^1.0.0"}}, "2.0.0": {}},
    "qe": {"1.0.0": {"dependencies": {"pe": "^1.0.0"}}, "2.0.0": {}},
    "pe": {"1.0.0": {}, "2.0.0": {}},
    "op": {"1.0.0": {"peerDependencies": {"oq": "^1.0.0"},
                     "peerDependenciesMeta": {"oq": {"optional": True}}}},
    "oq": {"1.0.0": {}, "1.1.0": {}, "2.0.0": {}},
    "or": {"1.0.0": {"dependencies": {"op": "^1.0.0"}}},
    "ut": {"1.0.0": {"dependencies": {"bu": "^1.0.0"}, "peerDependencies": {"tl": "^2.0.0"}}},
    "bu": {"1.0.0": {"peerDependencies": {"tl": "^2.0.0"}}},
    "tl": {"2.5.0": {}, "2.6.0": {}},
    "hx": {"1.0.0": {"dependencies": {"ut": "^1.0.0", "tl": "^2.0.0"}}},
    "ma": {"1.0.0": {"dependencies": {"mb": "^1.0.0"}}},
    "mb": {"1.0.0": {}},
    "gc": {"1.0.0": {}, "2.0.0": {}},
    "gp": {"1.0.0": {"peerDependencies": {"gc": "*"}}},
    "gj": {"1.0.0": {"dependencies": {"gp": "^1.0.0"}, "peerDependencies": {"gc": "*"}}},
    "gf": {"1.0.0": {"dependencies": {"gj": "^1.0.0", "gc": "^1.0.0"}}},
    "gr": {"1.0.0": {"dependencies": {"gf": "^1.0.0"}}},
    "tm": {"1.0.0": {}, "1.1.0": {}, "1.2.0": {}, "1.3.0": {}},
    "wq": {"1.0.0": {"dependencies": {"wr": "^1.0.0", "ws": "^1.0.0", "tm": "^1.0.0"}}},
    "wr": {"1.0.0": {"dependencies": {"wd": "^1.0.0"}, "peerDependencies": {"tm": "^1.0.0"}}},
    "ws": {"1.0.0": {"dependencies": {"we": "^1.0.0"}, "peerDependencies": {"tm": "^1.0.0"}}},
    "wd": {"1.0.0": {"peerDependencies": {"tm": "^1.0.0"}}},
    "we": {"1.0.0": {"peerDependencies": {"tm": "^1.0.0"}}},
    "dq": {"1.0.0": {"dependencies": {"dr": "^1.0.0", "tm": "^1.0.0"}}},
    "dr": {"1.0.0": {"dependencies": {"ds": "^1.0.0"}, "peerDependencies": {"tm": "^1.0.0"}}},
    "ds": {"1.0.0": {"dependencies": {"dt": "^1.0.0"}, "peerDependencies": {"tm": "^1.0.0"}}},
    "dt": {"1.0.0": {"peerDependencies": {"tm": "^1.0.0"}}},
    "up": {"1.0.0": {"dependencies": {"uq": "^1.0.0"}}},
    "uq": {"1.0.0": {"dependencies": {"ur": "^1.0.0", "us": "^1.0.0", "tm": "^1.0.0"}}},
    "ur": {"1.0.0": {"dependencies": {"ud": "^1.0.0"}, "peerDependencies": {"tm": "^1.0.0"}}},
    "ud": {"1.0.0": {"dependencies": {"ue": "^1.0.0"}, "peerDependencies": {"tm": "^1.0.0"}}},
    "ue": {"1.0.0": {"peerDependencies": {"tm": "^1.0.0"}}},
    "us": {"1.0.0": {"dependencies": {"uf": "^1.0.0"}, "peerDependencies": {"tm": "^1.0.0"}}},
    "uf": {"1.0.0": {"peerDependencies": {"tm": "^1.0.0"}}},
}
CASES = {
    "po-valid":   ("VALID/yes/yes", {"a": "^1.0.0", "c": "^1.0.0"},
                   {"a": "a@1.0.0", "c": "c@1.0.0", "c/node_modules/b": "b@1.0.0"}),
    "pl-valid":   ("VALID/yes/yes", {"p": "^1.0.0", "b": "^1.0.0"},
                   {"p": "p@1.0.0", "b": "b@1.0.0"}),
    "nest-valid": ("VALID/yes/yes", {"c": "^1.0.0"},
                   {"c": "c@1.0.0", "c/node_modules/b": "b@1.0.0"}),
    "old-valid":  ("VALID/yes/yes", {"c": "^1.0.0"},
                   {"c": "c@1.0.0", "b": "b@1.0.0"}),
    "missing":    ("INVALID/-/-", {"c": "^1.0.0"}, {"c": "c@1.0.0"}),
    "range":      ("INVALID/-/-", {"c": "^1.0.0"}, {"c": "c@1.0.0", "b": "b@2.0.0"}),
    # a's optional peer ^2 sees b@1 at the root
    "po-invalid": ("INVALID/-/-", {"a": "^1.0.0", "c": "^1.0.0"},
                   {"a": "a@1.0.0", "c": "c@1.0.0", "b": "b@1.0.0"}),
    # a peer resolved inside its requirer (PEER LOCAL)
    "pl-invalid": ("INVALID/-/-", {"p": "^1.0.0", "b": "^1.0.0"},
                   {"p": "p@1.0.0", "b": "b@1.0.0", "p/node_modules/b": "b@1.0.0"}),
    # the same where npm's repair keeps the copy, which ci lets through
    "pl-keep":    ("INVALID/-/-", {"q": "^1.0.0", "r": "^1.0.0"},
                   {"q": "q@1.0.0", "r": "r@1.0.0", "q/node_modules/r": "r@1.0.0"}),
    "pl-noroot":  ("INVALID/-/-", {"p": "^1.0.0"},
                   {"p": "p@1.0.0", "p/node_modules/b": "b@1.0.0"}),
    "alias-valid": ("VALID/yes/yes", {"d": "^1.0.0"}, {"d": "d@1.0.0", "b": "baz@1.0.0"}),
    # the wrong package at the right version, which npm checks by version only
    "swap":       ("INVALID/-/-", {"c": "^1.0.0"}, {"c": "c@1.0.0", "b": "baz@1.0.0"}),
    # reached by nothing
    "extra":      ("VALID/no/yes", {"b": "^1.0.0"}, {"b": "b@1.0.0", "z": "z@1.0.0"}),
    # reached by nothing, and its own dependency unmet
    "extra-broken": ("INVALID/-/-", {"b": "^1.0.0"}, {"b": "b@1.0.0", "y": "y@1.0.0"}),
    # npm's own lock for sx 2 -> sx 1 -> sx 2, the cycle closed by a link
    "link-valid": ("VALID/yes/yes", {"sx": "^2.0.0"},
                   {"sx": "sx@2.0.0", "sx/node_modules/sx": "sx@1.0.0",
                    "sx/node_modules/sx/node_modules/sx": {"link": "node_modules/sx"}}),
    # dx's peer px@^1 answered by a 2.0.0 in dx's own node_modules, which
    # npm keeps with only a warning
    "peer-override": ("INVALID/-/-", {"dx": "^1.0.0", "rx": "^2.0.0", "px": "^1.0.0"},
                      {"dx": "dx@1.0.0", "rx": "rx@2.0.0", "px": "px@1.0.0",
                       "dx/node_modules/rx": "rx@1.0.0", "dx/node_modules/px": "px@2.0.0"}),
    # npm's own lock: op's optional peer oq@^1 is the 1.1.0 beside it, which
    # npm's relock prunes, leaving op's peer invalid
    "opt-peer-lock": ("VALID/no/yes", {"or": "^1.0.0", "oq": "^2.0.0"},
                      {"or": "or@1.0.0", "oq": "oq@2.0.0", "or/node_modules/op": "op@1.0.0",
                       "or/node_modules/oq": "oq@1.1.0"}),
    # op's optional peer sees the root's oq 2.0.0
    "opt-peer-range": ("INVALID/-/-", {"or": "^1.0.0", "oq": "^2.0.0"},
                       {"or": "or@1.0.0", "oq": "oq@2.0.0", "op": "op@1.0.0"}),
    # ut sees hx's tl 2.6.0, and its bu, above hx, the root's 2.5.0
    "torn-lock":   ("VALID/yes/yes", {"hx": "^1.0.0"},
                    {"hx": "hx@1.0.0", "hx/node_modules/ut": "ut@1.0.0",
                     "hx/node_modules/tl": "tl@2.6.0", "bu": "bu@1.0.0", "tl": "tl@2.5.0"}),
}
# answers as pac prints them, which mklock.py has to place: the root's
# dependencies, then the node_modules rows
OURS = {
    # two copies of one version under two keys, each with its own string-width
    "alias-copies": ("VALID/yes/yes", {"w": "^1.0.0", "wc": "npm:w@^1.0.0"},
                     [". <- w 1.0.0", ". <- w 1.0.0 at wc",
                      "w 1.0.0 <- s 1.0.0", "w 1.0.0 at wc <- s 1.1.0"]),
    "alias-range":  ("INVALID/-/-", {"w": "^1.0.0", "wc": "npm:w@^1.0.0"},
                     [". <- w 1.0.0", ". <- w 1.0.0 at wc",
                      "w 1.0.0 <- s 1.0.0", "w 1.0.0 at wc <- s 2.0.0"]),
    # u's peer on bl beside u, in the bl that holds it: the copy under
    # 1.1.0 is 1.0.0, which sees itself
    "self-chain":   ("VALID/yes/yes", {"bl": "^1.0.0"},
                     [". <- bl 1.1.0", "bl 1.1.0 <- u 1.0.0", "bl 1.1.0 <- bl 1.0.0",
                      "bl 1.0.0 <- u 1.0.0", "bl 1.0.0 <- bl 1.0.0"]),
    # each bl holds the other, which nesting never closes and a link to the
    # ancestor copy does
    "self-cycle":   ("VALID/yes/yes", {"bl": "^1.0.0"},
                     [". <- bl 1.0.0", "bl 1.0.0 <- u 1.0.0", "bl 1.0.0 <- bl 1.1.0",
                      "bl 1.1.0 <- u 1.0.0", "bl 1.1.0 <- bl 1.0.0"]),
    # at 1 -> ot 1 -> at 2 -> ot 2 -> at 1: below ot 1, at resolves to at 2
    # at the latest, so the at 1 the cycle comes back to is a link
    "cycle-four":   ("VALID/yes/yes", {"at": "^1.0.0"},
                     [". <- at 1.0.0", "at 1.0.0 <- ot 1.0.0", "ot 1.0.0 <- at 2.0.0",
                      "at 2.0.0 <- ot 2.0.0", "ot 2.0.0 <- at 1.0.0"]),
    "selfdep-cycle": ("VALID/yes/yes", {"sx": "^2.0.0"},
                      [". <- sx 2.0.0", "sx 2.0.0 <- sx 1.0.0", "sx 1.0.0 <- sx 2.0.0"]),
    # d1's peer, hung on k1 1.0.0, is the k1 2.0.0 above it
    "selfpeer":     ("VALID/yes/yes", {"k1": "^2.0.0"},
                     [". <- k1 2.0.0", "k1 2.0.0 <- k1 1.0.0", "k1 1.0.0 <- d1 1.0.0",
                      "k1 1.0.0 <- k1 2.0.0"]),
    "alias-cycle":  ("VALID/yes/yes", {"yc": "^1.0.0"},
                     [". <- yc 1.0.0", "yc 1.0.0 <- xc 1.0.0 at yc", "xc 1.0.0 at yc <- yc 1.0.0"]),
    # the dx rx 1.0.0 selects has px 2.0.0 for its peer px@^1
    "peer-wrong":   ("INVALID/-/-", {"dx": "^1.0.0", "rx": "^2.0.0", "px": "^1.0.0"},
                     [". <- dx 1.0.0", ". <- rx 2.0.0", ". <- px 1.0.0",
                      "dx 1.0.0 <- rx 1.0.0", "rx 1.0.0 <- dx 1.0.0", "rx 1.0.0 <- px 2.0.0"]),
    # the same where de's own node_modules holds qe
    "peer-wrong-deep": ("INVALID/-/-", {"de": "^1.0.0", "re": "^2.0.0", "qe": "^2.0.0", "pe": "^1.0.0"},
                        [". <- de 1.0.0", ". <- re 2.0.0", ". <- qe 2.0.0", ". <- pe 1.0.0",
                         "de 1.0.0 <- qe 1.0.0", "de 1.0.0 <- re 1.0.0", "qe 1.0.0 <- pe 1.0.0",
                         "re 1.0.0 <- de 1.0.0", "re 1.0.0 <- pe 2.0.0"]),
    # ut and its bu both peer on tl, so ut's own lookup of tl, which is its
    # peer, is the one bu's peer needs too
    "peer-shared":  ("VALID/yes/yes", {"ut": "^1.0.0", "tl": "^2.0.0"},
                     [". <- ut 1.0.0", ". <- tl 2.6.0", "ut 1.0.0 <- bu 1.0.0", "ut 1.0.0 <- tl 2.6.0"]),
    # bu's peer another tl: nothing is above the root's, and in ut's own
    # node_modules ut itself would load it
    "peer-torn":    ("INVALID/-/-", {"ut": "^1.0.0", "tl": "^2.0.0"},
                     [". <- ut 1.0.0", ". <- tl 2.6.0", "ut 1.0.0 <- bu 1.0.0", "ut 1.0.0 <- tl 2.5.0"]),
    # the same below the root, which a tree holds with bu above hx's tl
    # (torn-lock)
    "peer-torn-deep": ("VALID/yes/yes", {"hx": "^1.0.0"},
                       [". <- hx 1.0.0", "hx 1.0.0 <- ut 1.0.0", "hx 1.0.0 <- tl 2.6.0",
                        "ut 1.0.0 <- bu 1.0.0", "ut 1.0.0 <- tl 2.5.0"]),
    # op's optional peer, hung on or: 1.1.0 in range, 2.0.0 not, and with no
    # edge op sees the root's 2.0.0
    "opt-peer":     ("VALID/no/yes", {"or": "^1.0.0", "oq": "^2.0.0"},
                     [". <- or 1.0.0", ". <- oq 2.0.0", "or 1.0.0 <- op 1.0.0", "or 1.0.0 <- oq 1.1.0"]),
    "opt-peer-bad": ("INVALID/-/-", {"or": "^1.0.0", "oq": "^2.0.0"},
                     [". <- or 1.0.0", ". <- oq 2.0.0", "or 1.0.0 <- op 1.0.0", "or 1.0.0 <- oq 2.0.0"]),
    "opt-peer-seen": ("INVALID/-/-", {"or": "^1.0.0", "oq": "^2.0.0"},
                      [". <- or 1.0.0", ". <- oq 2.0.0", "or 1.0.0 <- op 1.0.0"]),
    # ma's mb has no edge, though the lookup would land on the mb there is
    "no-edge":      ("INVALID/-/-", {"ma": "^1.0.0"}, [". <- ma 1.0.0"], ["mb 1.0.0"]),
    # cy 1 -> oz 1 -> cy 2 -> cy 1, which closes: the cy 1 inside cy 2 sees
    # the top oz 1
    "cycle-three":  ("VALID/yes/yes", {"cy": "^1.0.0"},
                     [". <- cy 1.0.0", "cy 1.0.0 <- oz 1.0.0", "oz 1.0.0 <- cy 2.0.0",
                      "cy 2.0.0 <- cy 1.0.0"]),
    "unreached":    ("VALID/no/yes", {"b": "^1.0.0"}, [". <- b 1.0.0"], ["z 1.0.0"]),
    # gj's gp needs gc 2 above gf's gc 1, where the root's gc 1 is: the
    # search nests gf in gr, and gp and gc 2 go in gr's node_modules
    "peer-torn-nest": ("VALID/yes/yes", {"gr": "^1.0.0", "gc": "^1.0.0"},
                       [". <- gr 1.0.0", ". <- gc 1.0.0", "gr 1.0.0 <- gf 1.0.0",
                        "gf 1.0.0 <- gj 1.0.0", "gf 1.0.0 <- gc 1.0.0", "gj 1.0.0 <- gp 1.0.0",
                        "gj 1.0.0 <- gc 2.0.0"]),
    # wd and we need tm 1.1 and 1.0 above wq's 1.2, and above wq, which the
    # root requires, there is one node_modules
    "peer-torn-wide": ("INVALID/-/-", {"wq": "^1.0.0"},
                       [". <- wq 1.0.0", "wq 1.0.0 <- wr 1.0.0", "wq 1.0.0 <- ws 1.0.0",
                        "wq 1.0.0 <- tm 1.2.0", "wr 1.0.0 <- wd 1.0.0", "wr 1.0.0 <- tm 1.1.0",
                        "ws 1.0.0 <- we 1.0.0", "ws 1.0.0 <- tm 1.0.0"]),
    # dt's tm above ds's, above dr's, above dq's own: two levels above dq,
    # which sits in the root's node_modules
    "peer-torn-depth": ("INVALID/-/-", {"dq": "^1.0.0", "tm": "^1.0.0"},
                        [". <- dq 1.0.0", ". <- tm 1.3.0", "dq 1.0.0 <- dr 1.0.0",
                         "dq 1.0.0 <- tm 1.2.0", "dr 1.0.0 <- ds 1.0.0", "dr 1.0.0 <- tm 1.1.0",
                         "ds 1.0.0 <- dt 1.0.0", "ds 1.0.0 <- tm 1.0.0"]),
    # no tree: ue, ud and ur need tm 1.1, 1.2 and 1.3 at the three levels
    # down to uq's own, and uf another above us's; but neither count shows
    # it, and the search gives up
    "peer-torn-open": ("ERR/-/-", {"up": "^1.0.0"},
                       [". <- up 1.0.0", "up 1.0.0 <- uq 1.0.0", "uq 1.0.0 <- ur 1.0.0",
                        "uq 1.0.0 <- us 1.0.0", "uq 1.0.0 <- tm 1.3.0", "ur 1.0.0 <- ud 1.0.0",
                        "ur 1.0.0 <- tm 1.2.0", "ud 1.0.0 <- ue 1.0.0", "ud 1.0.0 <- tm 1.1.0",
                        "us 1.0.0 <- uf 1.0.0", "us 1.0.0 <- tm 1.0.0"]),
    "unreached-broken": ("INVALID/-/-", {"b": "^1.0.0"}, [". <- b 1.0.0"], ["y 1.0.0"]),
}
# arborist's Node.matches takes two nodes of one name and one integrity for
# the same package, whatever their versions
def dist(n, v):
    return {"tarball": f"https://registry.npmjs.org/{n}/-/{n}-{v}.tgz",
            "integrity": "sha512-" + base64.b64encode(hashlib.sha512(f"{n}@{v}".encode()).digest()).decode()}
for n, vs in PKGS.items():
    doc = {"name": n, "dist-tags": {"latest": max(vs)},
           "versions": {v: {"name": n, "version": v, **m, "dist": dist(n, v)} for v, m in vs.items()}}
    json.dump(doc, open(f"{T}/cache/{n}.json", "w"))
with open(f"{T}/cases", "w") as out:
    for case, (want, deps, layout) in CASES.items():
        d = f"{T}/work/{case}"
        os.makedirs(d)
        root = {"name": "root", "version": "1.0.0", "private": True, "dependencies": deps}
        json.dump(root, open(f"{d}/package.json", "w"), indent=2)
        pk = {"": {"name": "root", "version": "1.0.0", "dependencies": deps}}
        for path, nv in layout.items():
            if isinstance(nv, dict):
                pk["node_modules/" + path] = {"resolved": nv["link"], "link": True}
                continue
            n, v = nv.split("@")
            e = {"version": v, "resolved": dist(n, v)["tarball"], "integrity": dist(n, v)["integrity"]}
            if n != path.rsplit("node_modules/", 1)[-1]:
                e["name"] = n
            e.update(PKGS[n][v])
            pk["node_modules/" + path] = e
        json.dump({"name": "root", "version": "1.0.0", "lockfileVersion": 3,
                   "requires": True, "packages": pk}, open(f"{d}/package-lock.json", "w"), indent=2)
        out.write(f"{case} {want} {d}/package-lock.json\n")
    for case, (want, deps, rows, *extra) in OURS.items():
        d = f"{T}/work/{case}"
        os.makedirs(d)
        root = {"name": "root", "version": "1.0.0", "private": True, "dependencies": deps}
        json.dump(root, open(f"{d}/package.json", "w"), indent=2)
        pkgs = sorted({s for r in rows for s in r.split(" <- ")} | set(sum(extra, [])))
        with open(f"{d}/ans.out", "w") as f:
            f.write("root .\n" + f"packages ({len(pkgs)}):\n" + "".join(f"  {p}\n" for p in pkgs)
                    + f"node_modules ({len(rows)}):\n" + "".join(f"  {r}\n" for r in rows))
        out.write(f"{case} {want} {d}/ans.out\n")
EOF

. "$S/../serve.sh"
serve "$PORT" "$T/cache" "$T/shim.log" python3 "$S/shim.py" "$PORT" "$T/cache" --frozen \
  --log "$T/miss.log" || exit 1

# a check that does not finish is one that reached no verdict
check() {  # <case> <answer>
  NPM_RUN=$T timeout 120 bash "$S/../check.sh" npm "$2" "$T/work/$1.check" \
    "$T/work/$1/package.json" | tail -n 1
}

verdicts() { sed -n 's/.* valid=\([A-Z]*\) minimal=\([a-z-]*\) reproduced=\([a-z-]*\)$/\1\/\2\/\3/p'; }
while read -r case want ans; do
  line=$(check "$case" "$ans")
  got=$(verdicts <<< "$line")
  printf '%-16s expect %-15s got %-15s %s\n' "$case" "$want" "${got:-ERR/-/-}" "${line% valid=*}"
  [ "$got" = "$want" ] || bad=1
done < "$T/cases"

# npm failing for want of a registry says nothing of the answer
kill $served; wait $served 2> /dev/null
got=$(check po-valid "$T/work/po-valid/package-lock.json" | verdicts)
printf '%-16s expect %-15s got %s\n' noshim ERR/-/- "$got"
[ "$got" = ERR/-/- ] || bad=1

exit $bad
