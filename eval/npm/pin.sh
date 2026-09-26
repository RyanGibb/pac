#!/usr/bin/env bash
# usage: pin.sh <run-dir>      NORM as the run was given it, MODE the mode
#        whose npm-only edges are re-asked (default tool)
set -u
# byte order, so the output is the same whatever the host's locale
export LC_ALL=C
S="$(cd "$(dirname "$0")" && pwd)"
run=$1 NORM=${NORM---peer-parent} MODE=${MODE:-tool} TIMEOUT=${TIMEOUT:-900}
npmv=$(sed -n 1p "$S/npm-version") nodev=$(sed -n 2p "$S/npm-version")

ok=0; bad=0
for f in "$run"/out/*."$MODE".edges.npmonly; do
  [ -s "$f" ] || continue
  k=${f##*/}; k=${k%."$MODE".edges.npmonly}
  g=$(python3 "$S/../triage_lib.py" unkey "$k")
  o=$run/out/$k.pin W=$run/work/$k.pin
  rm -rf "$W"; mkdir -p "$W"
  cp "$run/work/$k/lock/package.json" "$W/package.json"
  python3 "$S/pinroot.py" "$run/out/$k.theirs" "$run/cache" "$W/cache" "$W/package.json" > "$o.pins"
  if ! timeout "$TIMEOUT" "$run/pac.exe" npm --offline --cache "$W/cache" --tree \
       --node-version "$nodev" --npm-version "$npmv" "$(realpath "$W/package.json")" > "$o.out" 2>&1; then
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
