#!/usr/bin/env bash
# The check writes our answer out as the project's package-lock.json
# (mklock.py) beside the query's package.json (root.js), and asks npm
# against a frozen shim.
#
# `npm ci --dry-run` builds the tree the lock describes and checks it
# against every manifest, but it repairs as it builds and fails only when
# the repair changes the inventory: an invalid peerOptional, or a peer
# resolving inside its requirer where npm's repair keeps that copy, passes
# it.  `npm install --package-lock-only` on a copy runs the same repair and
# writes it back, so the lock it leaves must name the same version at every
# path -- but for a package nothing reaches, which it prunes: that is the
# minimal verdict, not the valid one.  npm asks nothing of such a package,
# so reach.py asks that its own dependencies be met.  Neither asks whether
# an edge landed on the package its manifest names, so lockname.py does.
# Measured on express, not assumed: ci rejects a lock with a transitive
# package deleted and one whose version violates a requirer's range, and
# accepts both a valid-but-older version npm would not have picked and a
# package nested where npm would have hoisted it.
#
# What our answer does not carry is a directory layout -- it is the
# resolution relation, one provider per (requirer, key) -- so mklock.py
# has to synthesise a placement that reproduces exactly that relation
# under node_modules lookup, and controls.sh's nest-valid is what says npm
# judges the placement we chose rather than demanding its own.  An answer
# that is already a lock is taken as it stands, which is how controls.sh
# poses layouts pac would never write.
#
# npm exits 1 for every error; one is read as a verdict only under a code
# npm gives an answer it will not take (refusals, the codes scale.sh reads
# as npm refusing a query), and anything else, like a shim that stopped
# answering, leaves the answer unchecked.
#
# NPM_RUN holds the snapshot farm (cache/) and a scratch home/, as
# setup.sh builds them; PORT is where shim.py serves that farm; NPM_GIT
# names the git npm is to run (default: none).
# usage: check.sh <answer> <out-dir> <query...>, through eval/check.sh; the
#        query as npm's specs, or the path of a package.json
set -u
# byte order, so the output is the same whatever the host's locale
export LC_ALL=C
S="$(cd "$(dirname "$0")" && pwd)"
RUN=${NPM_RUN:?} PORT=${PORT:-8899}
ans=$1 out=$2; shift 2
W=$out/ci
. "$S/npm.sh"
npmc() { GIT_MISS=$out/gitmiss NPM_TIMEOUT= npm_in "$@" --loglevel=http; }  # <dir> <npm args...>
shim() { curl -s -o /dev/null "http://127.0.0.1:$PORT/-/ping"; }
paths() { jq -r '.packages | to_entries[] | select(.key != "") | "\(.key) \(.value.version)"' "$1" | sort; }
verdict() {  # <valid> <minimal> <why>
  printf '%s valid=%s minimal=%s\n' "$3" "$1" "$2"
  exit 0
}
err=0
ran() {  # <rc> <log>: whether npm ran to an answer, a refusal included
  [ "$1" -eq 0 ] || { [ "$1" -eq 1 ] && grep -qE -f "$S/refusals" "$2"; } || err=1
}

rm -rf "$W" "$W.plo"; mkdir -p "$W"
shim || verdict ERR - "no shim on $PORT"
if [ $# -eq 1 ] && [ "${1##*/}" = package.json ] && [ -f "$1" ]; then
  cp "$1" "$W/package.json"
else
  node "$S/root.js" "$RUN/cache" "$@" > "$W/package.json" 2> "$out/root.log" ||
    verdict ERR - "root.js failed"
fi
if jq -e .packages "$ans" > /dev/null 2>&1; then
  cp "$ans" "$W/package-lock.json"
else
  python3 "$S/mklock.py" "$RUN/cache" "$ans" "$W/package-lock.json" \
    --root-manifest "$W/package.json" > "$out/mklock" 2>&1
  case $? in
    0) ;;
    # no node_modules tree npm could be handed holds the answer
    4) verdict INVALID - "$(tail -n 1 "$out/mklock")" ;;
    *) verdict ERR - "mklock failed" ;;
  esac
fi

npmc "$W" ci --dry-run > "$out/ci.log" 2>&1
ci_rc=$?; ran $ci_rc "$out/ci.log"
cp -r "$W" "$W.plo"
npmc "$W.plo" install --package-lock-only --ignore-scripts > "$out/plo.log" 2>&1
relock_rc=$?; ran $relock_rc "$out/plo.log"
shim || err=1
diff <(paths "$W/package-lock.json") <(paths "$W.plo/package-lock.json") > "$out/moved"
moved=$(grep -c '^[<>]' "$out/moved")
python3 "$S/lockname.py" "$W/package-lock.json" > "$out/names" 2>&1
named=$?
python3 "$S/reach.py" "$W/package-lock.json" > "$out/reach" 2> "$out/reach.log" || err=1
unmet=$(grep -c '^unmet ' "$out/reach")
# every change the relock made is the pruning of a package nothing reaches
repaired=$(awk 'FILENAME == ARGV[1] {if ($1 == "unreached") u[$2]; next}
                /^>/ || /^</ && !($2 in u)' "$out/reach" "$out/moved" | wc -l)

why="ci=$ci_rc relock=$relock_rc moved=$moved repaired=$repaired unmet=$unmet named=$named"
[ "$err" -eq 0 ] || verdict ERR - "$why"
case $named in 0|3) ;; *) verdict ERR - "$why" ;; esac
[ "$ci_rc" -eq 0 ] && [ "$relock_rc" -eq 0 ] && [ "$named" -eq 0 ] && [ "$repaired" -eq 0 ] &&
  [ "$unmet" -eq 0 ] || verdict INVALID - "$why"
[ "$moved" -eq 0 ] && verdict VALID yes "$why"
verdict VALID no "$why"
