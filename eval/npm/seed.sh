#!/usr/bin/env bash
# One online pass that fixes what the measured sweep then answers offline:
# which root version each goal is asked about, and a snapshot closed over
# both sides' cones.
#
# Root choice.  The obvious pin is dist-tags.latest, and where both sides
# can answer it that is what this writes.  Where they cannot it walks back
# to the next-newest release, because a goal whose root no one can resolve
# yields no edges to score.  Two things make latest unanswerable, and both
# are findings rather than accidents: our engines-as-availability gate cuts
# a root whose engines exclude the host node our frontend hardcodes, and a
# packument in repos/npm can be old enough that a newer release's own
# dependency range matches nothing in it, which stops npm as well.  The
# version that comes out is written to baseline/roots.txt and used
# verbatim by both sides, so the question stays shared whatever the reason
# for walking back.
#
# Snapshot closure.  repos/npm is an on-demand cache accumulated by earlier
# `pac npm` runs, so it holds our cone and not necessarily npm's: npm asks
# for names our parser drops (git and tag specs), for optional targets we
# never look up, and for peers we place differently.  A frozen shim would
# answer those 404 and npm would be solving a different registry from ours.
# So our side runs online and fills the farm with what it needs, and npm
# runs against a --fill shim that fetches a miss once into the same farm.
# After this the farm is closed over both and scale.sh runs frozen.
#
# usage: seed.sh <exe> [run-dir] [port] [max-walkback]
set -eu
# byte order, so the output is the same whatever the host's locale
export LC_ALL=C
S="$(cd "$(dirname "$0")" && pwd)"
exe=$1; RUN="${2:-/tmp/npm-cmp}"; PORT="${3:-8899}"; BACK="${4:-40}"

: > "$RUN/miss.log"
python3 "$S/shim.py" "$PORT" "$RUN/cache" --fill --log "$RUN/miss.log" &
shim=$!
trap 'kill $shim 2>/dev/null' EXIT
sleep 1

: > "$S/baseline/roots.txt"
while read -r g; do
  [ -n "$g" ] || continue
  slug=${g//\//__}
  W="$RUN/work/$slug"
  pin=""; back=""
  for n in $(seq 0 "$BACK"); do
    line=$(python3 "$S/mkroot.py" "$RUN/cache" "$g" "$W" --nth "$n") || break
    root=${line%% *}; v=${line##* }
    if "$exe" npm --cache "$RUN/cache" "$root" > "$W/seed.ours" 2>&1; then
      pin=$v; back=$n; break
    fi
  done
  if [ -z "$pin" ]; then
    echo "$g DROP no root our side can resolve in $BACK releases"
    continue
  fi
  ( cd "$W" && rm -f package-lock.json && \
    HOME="$RUN/home" npm install --package-lock-only \
      --registry "http://127.0.0.1:$PORT" --cache "$RUN/home/npmcache" \
      --userconfig "$RUN/home/.npmrc" --globalconfig "$RUN/home/npmrc-global" \
      --no-audit --no-fund --no-update-notifier --loglevel=error \
      > seed.npm 2>&1 ) || { echo "$g DROP npm cannot resolve $pin"; tail -2 "$W/seed.npm"; continue; }
  latest=$(python3 -c 'import json,sys;print(json.load(open(sys.argv[1]))["dist-tags"]["latest"])' \
             "$RUN/cache/${g//\//%2F}.json")
  echo "$g $pin (walked back $back from $latest)"
  # goal, pin, releases walked back, dist-tags.latest
  printf '%s %s %s %s\n' "$g" "$pin" "$back" "$latest" >> "$S/baseline/roots.txt"
done < "$S/goals.txt"

echo "filled $(sort -u "$RUN/miss.log" | wc -l) names npm asked for and the farm lacked"
# npm's own http cache would otherwise answer a frozen run from what the
# fill pass fetched, which would hide a snapshot hole rather than show it
rm -rf "$RUN/home/npmcache"
