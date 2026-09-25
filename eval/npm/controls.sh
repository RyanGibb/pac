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
}
CASES = {
    "po-valid":   ("VALID/yes", {"a": "^1.0.0", "c": "^1.0.0"},
                   {"a": "a@1.0.0", "c": "c@1.0.0", "c/node_modules/b": "b@1.0.0"}),
    "pl-valid":   ("VALID/yes", {"p": "^1.0.0", "b": "^1.0.0"},
                   {"p": "p@1.0.0", "b": "b@1.0.0"}),
    "nest-valid": ("VALID/yes", {"c": "^1.0.0"},
                   {"c": "c@1.0.0", "c/node_modules/b": "b@1.0.0"}),
    "old-valid":  ("VALID/yes", {"c": "^1.0.0"},
                   {"c": "c@1.0.0", "b": "b@1.0.0"}),
    "missing":    ("INVALID/-", {"c": "^1.0.0"}, {"c": "c@1.0.0"}),
    "range":      ("INVALID/-", {"c": "^1.0.0"}, {"c": "c@1.0.0", "b": "b@2.0.0"}),
    # a's optional peer ^2 sees b@1 at the root
    "po-invalid": ("INVALID/-", {"a": "^1.0.0", "c": "^1.0.0"},
                   {"a": "a@1.0.0", "c": "c@1.0.0", "b": "b@1.0.0"}),
    # a peer resolved inside its requirer (PEER LOCAL)
    "pl-invalid": ("INVALID/-", {"p": "^1.0.0", "b": "^1.0.0"},
                   {"p": "p@1.0.0", "b": "b@1.0.0", "p/node_modules/b": "b@1.0.0"}),
    # the same where npm's repair keeps the copy, which ci lets through
    "pl-keep":    ("INVALID/-", {"q": "^1.0.0", "r": "^1.0.0"},
                   {"q": "q@1.0.0", "r": "r@1.0.0", "q/node_modules/r": "r@1.0.0"}),
    "pl-noroot":  ("INVALID/-", {"p": "^1.0.0"},
                   {"p": "p@1.0.0", "p/node_modules/b": "b@1.0.0"}),
    "alias-valid": ("VALID/yes", {"d": "^1.0.0"}, {"d": "d@1.0.0", "b": "baz@1.0.0"}),
    # the wrong package at the right version, which npm checks by version only
    "swap":       ("INVALID/-", {"c": "^1.0.0"}, {"c": "c@1.0.0", "b": "baz@1.0.0"}),
    # reached by nothing
    "extra":      ("VALID/no", {"b": "^1.0.0"}, {"b": "b@1.0.0", "z": "z@1.0.0"}),
    # reached by nothing, and its own dependency unmet
    "extra-broken": ("INVALID/-", {"b": "^1.0.0"}, {"b": "b@1.0.0", "y": "y@1.0.0"}),
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
            n, v = nv.split("@")
            e = {"version": v, "resolved": dist(n, v)["tarball"], "integrity": dist(n, v)["integrity"]}
            if n != path.rsplit("node_modules/", 1)[-1]:
                e["name"] = n
            e.update(PKGS[n][v])
            pk["node_modules/" + path] = e
        json.dump({"name": "root", "version": "1.0.0", "lockfileVersion": 3,
                   "requires": True, "packages": pk}, open(f"{d}/package-lock.json", "w"), indent=2)
        out.write(f"{case} {want}\n")
EOF

python3 "$S/shim.py" "$PORT" "$T/cache" --frozen --log "$T/miss.log" &
shim=$!
trap 'kill $shim 2> /dev/null' EXIT
sleep 1
kill -0 $shim 2> /dev/null || { echo "no shim on $PORT" >&2; exit 1; }

check() {  # <case>
  NPM_RUN=$T bash "$S/../check.sh" npm "$T/work/$1/package-lock.json" "$T/work/$1.check" \
    "$T/work/$1/package.json" | tail -n 1
}

while read -r case want; do
  line=$(check "$case")
  got=$(sed -n 's/.* valid=\([A-Z]*\) minimal=\(.*\)$/\1\/\2/p' <<< "$line")
  printf '%-11s expect %-11s got %-11s %s\n' "$case" "$want" "$got" "${line% valid=*}"
  [ "$got" = "$want" ] || bad=1
done < "$T/cases"

# npm failing for want of a registry says nothing of the answer
kill $shim; wait $shim 2> /dev/null
got=$(check po-valid | sed -n 's/.* valid=\([A-Z]*\) minimal=\(.*\)$/\1\/\2/p')
printf '%-11s expect %-11s got %s\n' noshim ERR/- "$got"
[ "$got" = ERR/- ] || bad=1

exit $bad
