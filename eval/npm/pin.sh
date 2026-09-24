#!/usr/bin/env bash
# Re-ask every goal of a scale.sh run whose edges diverged from npm's, with
# the versions npm chose and we did not forced on both sides as root
# overrides.  A goal that then agrees exactly was a preference gap: npm's
# answer was already a resolution of our instance and only our ordering
# ranked it second.
# usage: pin.sh <run-dir> [port]      NORM as the run was given it
set -u
# byte order, so the output is the same whatever the host's locale
export LC_ALL=C
S="$(cd "$(dirname "$0")" && pwd)"
run=$1; PORT="${2:-8899}" NORM=${NORM---peer-parent}
npmv=$(sed -n 1p "$S/npm-version") nodev=$(sed -n 2p "$S/npm-version")

: > "$run/pin-miss.log"
python3 "$S/shim.py" "$PORT" "$run/cache" --frozen --log "$run/pin-miss.log" &
shim=$!
trap 'kill $shim 2>/dev/null' EXIT
sleep 1

ok=0; bad=0
for f in "$run"/out/*.edges.npmonly; do
  [ -s "$f" ] || continue
  k=${f##*/}; k=${k%.edges.npmonly}
  g=${k//+/ }; g=${g//%2F//}; g=${g//%2B/+}; g=${g//%25/%}
  o=$run/out/$k.pin W=$run/work/$k.pin
  mkdir -p "$W"
  cp "$run/work/$k/lock/package.json" "$W/package.json"
  # one pin per (name, version) npm resolved to and we did not
  root=$(python3 "$S/pinroot.py" "$run/cache" "$W" $(cut -f4,5 "$f" | sort -u | awk '{printf "%s@%s ", $1, $2}'))
  "$run/pac.exe" npm --offline --cache "$run/cache" --tree --node-version "$nodev" \
    --npm-version "$npmv" "$root" > "$o.out" 2>&1
  ( cd "$W" && rm -f package-lock.json && HOME="$run/home" npm install --package-lock-only \
      --registry "http://127.0.0.1:$PORT" --cache "$run/home/npmcache" \
      --userconfig "$run/home/.npmrc" --globalconfig "$run/home/npmrc-global" \
      --no-audit --no-fund --no-update-notifier --loglevel=error ) > "$o.npm" 2>&1
  if [ ! -s "$W/package-lock.json" ] || ! grep -q '^node_modules' "$o.out"; then
    printf '%-24s NO ANSWER (see %s.npm, %s.out)\n' "$g" "$o" "$o"
    bad=$((bad+1)); continue
  fi
  line=$(python3 "$S/edges.py" "${g%@*}" "$W/package-lock.json" "$o.out" "$o" $NORM)
  echo "$line"
  case $line in
  *"ours-only=0 "*"npm-only=0 "*"ours-only=0 "*"npm-only=0 "*) ok=$((ok+1)) ;;
  *) bad=$((bad+1)) ;;
  esac
done
printf 'PINNED now-exact=%d still-divergent=%d\n' "$ok" "$bad"
bash "$S/check-misses.sh" "$run/pin-miss.log"
