#!/usr/bin/env bash
# accepts.sh's verdict on hand-written locks over a hand-written registry,
# beside the verdict each must get.  A check that passes every real answer
# says nothing until it is seen to fail these; the ones expected VALID keep
# it from failing everything, and two of them are valid layouts npm would
# not have chosen.  Exits non-zero if any verdict differs.
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

# a: optional peer b@^2.  p: peer b@^1.  q: peer r@^1.  c: b@^1.
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
}
CASES = {
    "po-valid":   ("VALID", {"a": "^1.0.0", "c": "^1.0.0"},
                   {"a": "a@1.0.0", "c": "c@1.0.0", "c/node_modules/b": "b@1.0.0"}),
    "pl-valid":   ("VALID", {"p": "^1.0.0", "b": "^1.0.0"},
                   {"p": "p@1.0.0", "b": "b@1.0.0"}),
    "nest-valid": ("VALID", {"c": "^1.0.0"},
                   {"c": "c@1.0.0", "c/node_modules/b": "b@1.0.0"}),
    "old-valid":  ("VALID", {"c": "^1.0.0"},
                   {"c": "c@1.0.0", "b": "b@1.0.0"}),
    "missing":    ("INVALID", {"c": "^1.0.0"}, {"c": "c@1.0.0"}),
    "range":      ("INVALID", {"c": "^1.0.0"}, {"c": "c@1.0.0", "b": "b@2.0.0"}),
    # a's optional peer ^2 sees b@1 at the root
    "po-invalid": ("INVALID", {"a": "^1.0.0", "c": "^1.0.0"},
                   {"a": "a@1.0.0", "c": "c@1.0.0", "b": "b@1.0.0"}),
    # a peer resolved inside its requirer (PEER LOCAL)
    "pl-invalid": ("INVALID", {"p": "^1.0.0", "b": "^1.0.0"},
                   {"p": "p@1.0.0", "b": "b@1.0.0", "p/node_modules/b": "b@1.0.0"}),
    # the same where npm's repair keeps the copy, which ci lets through
    "pl-keep":    ("INVALID", {"q": "^1.0.0", "r": "^1.0.0"},
                   {"q": "q@1.0.0", "r": "r@1.0.0", "q/node_modules/r": "r@1.0.0"}),
    "pl-noroot":  ("INVALID", {"p": "^1.0.0"},
                   {"p": "p@1.0.0", "p/node_modules/b": "b@1.0.0"}),
    # reached by nothing
    "extra":      ("INVALID", {"b": "^1.0.0"}, {"b": "b@1.0.0", "z": "z@1.0.0"}),
}
# npm takes two versions with one integrity for the same package
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

npmc() {  # <dir> <npm args...>
  (cd "$1" && shift && HOME="$T/home" npm_config_git=false npm "$@" \
    --registry "http://127.0.0.1:$PORT" --cache "$T/home/npmcache" \
    --userconfig "$T/home/.npmrc" --globalconfig "$T/home/npmrc-global" \
    --no-audit --no-fund --no-update-notifier)
}
. "$S/accepts.sh"

while read -r case want; do
  accepts "$T/work/$case" "$T/work/$case.log" && got=VALID || got=INVALID
  printf '%-11s expect %-7s got %-7s ci=%s relock=%s moved=%s\n' \
    "$case" "$want" "$got" "$ci_rc" "$relock_rc" "$moved"
  [ "$got" = "$want" ] || bad=1
done < "$T/cases"

exit $bad
