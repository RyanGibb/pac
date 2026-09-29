#!/usr/bin/env bash
# The check writes our answer out as the project's package-lock.json
# (mklock.py) beside the query's package.json (root.js), and asks npm
# against a frozen shim whether that tree is consistent.
#
# Valid: `npm ci --dry-run` builds the tree the lock describes and accepts
# it; `npm ls --all --package-lock-only` finds no edge invalid or missing
# (an extraneous package is minimality's business, not validity's); npm
# overrides no peer, which it does with only an "ERESOLVE overriding peer
# dependency" warning and exit 0; every edge lands on the package its
# manifest names, which npm checks by version alone (lockname.py); a
# package nothing reaches, which npm asks nothing of, has its own
# dependencies met (reach.py); and the tree holds our answer, every edge of
# it resolved from where its requirer sits, a peer from where its declarer
# sits (relation.py).
#
# Reproduced: `npm install --package-lock-only` on a copy, npm's relock,
# changes nothing but pruning packages nothing reaches.  Minimal: it
# changes nothing at all.  Neither counts against validity: npm's relock
# repairs by its own preferences, and is not even idempotent on its own
# locks (an optional peer's copy it pruned leaves the peer invalid).
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
# that is already a lock is taken as it stands, with no relation to hold,
# which is how controls.sh poses layouts pac would never write.
#
# npm exits 1 for every error; one is read as a verdict only under a code
# npm gives an answer it will not take (refusals, the codes scale.sh reads
# as npm refusing a query), and anything else, like a shim that stopped
# answering, leaves the answer unchecked.
# usage: check.sh <answer> <out-dir> <query...>, through eval/check.sh; the
#        query as npm's specs, or the path of a package.json
S="$(cd "$(dirname "$0")" && pwd)"
verdict() {  # <valid> <why> [<minimal> <reproduced>]
  printf '%s valid=%s minimal=%s reproduced=%s\n' "$2" "$1" "${3:--}" "${4:--}"
  exit 0
}
. "$S/check-lib.sh"
paths() { jq -r '.packages | to_entries[] | select(.key != "") | "\(.key) \(.value.version)"' "$1" | sort; }
yn() { if [ "$1" -eq 0 ]; then echo yes; else echo no; fi; }

ours=
if jq -e .packages "$ans" > /dev/null 2>&1; then
  cp "$ans" "$W/package-lock.json"
else
  ours=$ans
  python3 "$S/mklock.py" "$RUN/cache" "$ans" "$W/package-lock.json" \
    --root-manifest "$W/package.json" > "$out/mklock" 2>&1 ||
    verdict ERR "mklock failed: $(tail -n 1 "$out/mklock" | cut -c 1-300)"
fi

npmc "$W" ci --dry-run > "$out/ci.log" 2>&1
ci_rc=$?; ran $ci_rc "$out/ci.log"
cp -r "$W" "$W.plo"
npmc "$W.plo" install --package-lock-only --ignore-scripts > "$out/plo.log" 2>&1
relock_rc=$?; ran $relock_rc "$out/plo.log"
problems
override=$(cat "$out/ci.log" "$out/plo.log" | grep -c 'ERESOLVE overriding peer dependency')
shim || err=1
diff <(paths "$W/package-lock.json") <(paths "$W.plo/package-lock.json") > "$out/moved"
moved=$(grep -c '^[<>]' "$out/moved")
python3 "$S/lockname.py" "$W/package-lock.json" "$W/package.json" > "$out/names" 2>&1
named=$?
python3 "$S/reach.py" "$W/package-lock.json" > "$out/reach" 2> "$out/reach.log" || err=1
unmet=$(grep -c '^unmet ' "$out/reach")
related=0
if [ -n "$ours" ]; then
  python3 "$S/relation.py" "$W/package-lock.json" "$ours" "$RUN/cache" > "$out/relation" 2>&1
  related=$?
fi
# every change the relock made is the pruning of a package nothing reaches
repaired=$(awk 'FILENAME == ARGV[1] {if ($1 == "unreached") u[$2]; next}
                /^>/ || /^</ && !($2 in u)' "$out/reach" "$out/moved" | wc -l)

why="ci=$ci_rc ls=$broken override=$override named=$named unmet=$unmet relation=$related"
why="$why relock=$relock_rc moved=$moved repaired=$repaired"
[ "$err" -eq 0 ] || verdict ERR "$why"
case $named$related in [03][03]) ;; *) verdict ERR "$why" ;; esac
# the tree holds our answer and npm ls finds it whole, and `npm ci` refuses
# it only for a package whose os, cpu or libc excludes this host, taking it
# once that check alone is skipped: a resolution npm agrees with, which
# this host cannot install
if platform "$ci_rc" "$out/ci.log" && [ "$broken" -eq 0 ] && [ "$override" -eq 0 ] &&
   [ "$named" -eq 0 ] && [ "$unmet" -eq 0 ] && [ "$related" -eq 0 ]; then
  why="$why $(forced "$W" "$out")"
  case $why in *" ci-force=0 "*) verdict PLATFORM "$why" ;; esac
fi
[ "$ci_rc" -eq 0 ] && [ "$broken" -eq 0 ] && [ "$override" -eq 0 ] && [ "$named" -eq 0 ] &&
  [ "$unmet" -eq 0 ] && [ "$related" -eq 0 ] || verdict INVALID "$why"
[ "$relock_rc" -eq 0 ] && [ "$repaired" -eq 0 ]; reproduced=$(yn $?)
[ "$relock_rc" -eq 0 ] && [ "$moved" -eq 0 ]; minimal=$(yn $?)
verdict VALID "$why" "$minimal" "$reproduced"
