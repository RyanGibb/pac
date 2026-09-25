#!/usr/bin/env bash
# Re-ask pac every query of a scale.sh run whose edges diverged from npm's,
# with every edge npm resolved pinned to the version npm put there (see
# pinroot.py).  A query whose pinned answer then agrees exactly with npm's
# original lock was a preference gap: npm's answer was already a
# resolution of our instance and only our ordering ranked it second.
# usage: pin.sh <run-dir>      NORM as the run was given it
set -u
# byte order, so the output is the same whatever the host's locale
export LC_ALL=C
S="$(cd "$(dirname "$0")" && pwd)"
run=$1 NORM=${NORM---peer-parent}
npmv=$(sed -n 1p "$S/npm-version") nodev=$(sed -n 2p "$S/npm-version")

ok=0; bad=0
for f in "$run"/out/*.edges.npmonly; do
  [ -s "$f" ] || continue
  k=${f##*/}; k=${k%.edges.npmonly}
  g=${k//+/ }; g=${g//%2F//}; g=${g//%2B/+}; g=${g//%25/%}
  o=$run/out/$k.pin W=$run/work/$k.pin
  rm -rf "$W"; mkdir -p "$W"
  cp "$run/work/$k/lock/package.json" "$W/package.json"
  python3 "$S/pinroot.py" "$run/out/$k.theirs" "$run/cache" "$W/cache" "$W/package.json" > "$o.pins"
  "$run/pac.exe" npm --offline --cache "$W/cache" --tree --node-version "$nodev" \
    --npm-version "$npmv" "$(realpath "$W/package.json")" > "$o.out" 2>&1
  if ! grep -q '^node_modules' "$o.out"; then
    printf '%-24s NO ANSWER (see %s.out)\n' "$g" "$o"
    bad=$((bad+1)); continue
  fi
  line=$(python3 "$S/edges.py" "${g%@*}" "$run/out/$k.theirs" "$o.out" "$o" $NORM)
  echo "$line"
  case $line in
  *"ours-only=0 "*"npm-only=0 "*"ours-only=0 "*"npm-only=0 "*) ok=$((ok+1)) ;;
  *) bad=$((bad+1)) ;;
  esac
done
printf 'PINNED now-exact=%d still-divergent=%d\n' "$ok" "$bad"
