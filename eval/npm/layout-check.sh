#!/usr/bin/env bash
# The check for an answer that is itself a node_modules layout: lockgen.py
# writes it as the project's package-lock.json, copying each entry from the
# snapshot and placing nothing, and npm's own commands judge it.
#
# Valid: `npm ci --dry-run` builds the tree the lock describes and accepts
# it; `npm ls --all --package-lock-only` finds no edge invalid or missing;
# npm overrides no peer ("ERESOLVE overriding peer dependency"); every edge
# lands on the registry package its manifest names (lockname.py, since npm
# checks by version alone); and every edge of every entry, require.resolve'd
# on a skeleton of the tree, lands in range and no peer is PEER LOCAL
# (resolve.js).  An answer holding a package that bundles dependencies is
# ERR bundled: npm installs those from the tarball whatever the lock says.
#
# npm exits 1 for every error; one is read as a verdict only under a code
# npm gives an answer it will not take (refusals), and anything else leaves
# the answer unchecked.
#
# NPM_RUN holds the snapshot farm (cache/) and a scratch home/, as
# setup.sh builds them; PORT is where shim.py serves that farm.
# usage: layout-check.sh <answer> <out-dir> <query...>; the query as npm's
#        specs, or the path of a package.json
set -u
export LC_ALL=C
S="$(cd "$(dirname "$0")" && pwd)"
RUN=${NPM_RUN:?} PORT=${PORT:-8899}
ans=$1 out=$2; shift 2
mkdir -p "$out"
W=$out/ci
. "$S/npm.sh"
. "$S/refused.sh"
npmc() { GIT_MISS=$out/gitmiss NPM_TIMEOUT= npm_in "$@" --loglevel=http; }
shim() { curl -s -o /dev/null "http://127.0.0.1:$PORT/-/ping"; }
verdict() {  # <valid> <why>
  printf '%s valid=%s\n' "$2" "$1"
  exit 0
}
err=0
ran() { [ "$1" -eq 0 ] || refused "$1" "$2" || err=1; }

rm -rf "$W"; mkdir -p "$W"
shim || verdict ERR "no shim on $PORT"
if [ $# -eq 1 ] && [ "${1##*/}" = package.json ] && [ -f "$1" ]; then
  cp "$1" "$W/package.json"
else
  node "$S/root.js" "$RUN/cache" "$@" > "$W/package.json" 2> "$out/root.log" ||
    verdict ERR "root.js failed"
fi
python3 "$S/lockgen.py" "$RUN/cache" "$ans" "$W/package-lock.json" "$W/package.json" \
  > "$out/lockgen" 2>&1 || verdict ERR "lockgen failed: $(tail -n 1 "$out/lockgen" | cut -c 1-300)"
bundled=$(grep -c '^bundled ' "$out/lockgen")

npmc "$W" ci --dry-run > "$out/ci.log" 2>&1
ci_rc=$?; ran $ci_rc "$out/ci.log"
npmc "$W" ls --all --package-lock-only --json > "$out/ls.json" 2> "$out/ls.log" ||
  grep -q ELSPROBLEMS "$out/ls.log" || err=1
jq -r '.problems[]? | select(startswith("invalid:") or startswith("missing:"))' \
  "$out/ls.json" > "$out/ls.problems" 2>&1 || err=1
broken=$(wc -l < "$out/ls.problems")
override=$(grep -c 'ERESOLVE overriding peer dependency' "$out/ci.log")
shim || err=1
# the placement reading reads manifests as npm does
READING=npm python3 "$S/lockname.py" "$W/package-lock.json" "$W/package.json" > "$out/names" 2>&1
named=$?
node "$S/resolve.js" "$W/package-lock.json" "$W/package.json" "$out/skel" > "$out/resolve" 2>&1
resolved=$?

why="ci=$ci_rc ls=$broken override=$override named=$named resolve=$resolved bundled=$bundled"
[ "$err" -eq 0 ] || verdict ERR "$why"
case $named$resolved in [03][03]) ;; *) verdict ERR "$why" ;; esac
[ "$bundled" -eq 0 ] || verdict ERR "$why"
[ "$ci_rc" -eq 0 ] && [ "$broken" -eq 0 ] && [ "$override" -eq 0 ] && [ "$named" -eq 0 ] &&
  [ "$resolved" -eq 0 ] || verdict INVALID "$why"
verdict VALID "$why"
