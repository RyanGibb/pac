#!/usr/bin/env bash
# The check for an answer that is itself a node_modules layout: lockgen.py
# writes it as the project's package-lock.json, copying each entry from the
# snapshot and placing nothing, and npm's own commands judge it (`npm ci
# --dry-run`, `npm ls --all --package-lock-only`, no peer overridden,
# lockname.py, resolve.js).  A package that bundles dependencies is ERR
# bundled: npm installs those from the tarball whatever the lock says.
# npm exits 1 for every error; one is read as a verdict only under a code
# npm gives an answer it will not take (refusals), and anything else leaves
# the answer unchecked.
# usage: layout-check.sh <answer> <out-dir> <query...>; the query as npm's
#        specs, or the path of a package.json
S="$(cd "$(dirname "$0")" && pwd)"
verdict() {  # <valid> <why>
  printf '%s valid=%s\n' "$2" "$1"
  exit 0
}
. "$S/check-lib.sh"
python3 "$S/lockgen.py" "$RUN/cache" "$ans" "$W/package-lock.json" "$W/package.json" \
  > "$out/lockgen" 2>&1 || verdict ERR "lockgen failed: $(tail -n 1 "$out/lockgen" | cut -c 1-300)"
bundled=$(grep -c '^bundled ' "$out/lockgen")

npmc "$W" ci --dry-run > "$out/ci.log" 2>&1
ci_rc=$?; ran $ci_rc "$out/ci.log"
problems
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
if platform "$ci_rc" "$out/ci.log" && [ "$broken" -eq 0 ] && [ "$override" -eq 0 ] &&
   [ "$named" -eq 0 ] && [ "$resolved" -eq 0 ]; then
  why="$why $(forced "$W" "$out")"
  case $why in *" ci-force=0 "*) verdict PLATFORM "$why" ;; esac
fi
[ "$ci_rc" -eq 0 ] && [ "$broken" -eq 0 ] && [ "$override" -eq 0 ] && [ "$named" -eq 0 ] &&
  [ "$resolved" -eq 0 ] || verdict INVALID "$why"
verdict VALID "$why"
