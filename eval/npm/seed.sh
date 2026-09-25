#!/usr/bin/env bash
# One online pass that fixes what the measured sweep then answers offline:
# which root version each query is asked about, and a snapshot closed over
# both sides' cones.
#
# Root choice.  It starts at the newest release, usually dist-tags.latest.
# Where our side cannot answer it it walks back to the next-newest,
# because a query whose root no one can resolve yields no edges to score;
# where npm cannot, the query is dropped.  A packument in repos/npm can be
# old enough that a newer release's own dependency range matches nothing
# in it, which stops npm as well.  The version that comes out is written
# to baseline/roots.txt and used verbatim by both sides, so the question stays shared whatever the reason
# for walking back.
#
# Snapshot closure.  repos/npm is an on-demand cache accumulated by earlier
# `pac npm` runs, so it holds our cone and not necessarily npm's: npm asks
# for names our parser drops (git and tag specs) and for peers we place
# differently.  A frozen shim would
# answer those 404 and npm would be solving a different registry from ours.
# So our side runs online and fills the farm with what it needs, and npm
# runs against a --fill shim that fetches a miss once into the same farm.
# After this the farm is closed over the seeded roots; a FILL=1 scale.sh
# pass closes it over the rest.
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
  mkdir -p "$W"
  for n in $(seq 0 "$BACK"); do
    # newest first, prereleases left out: a prerelease root would ask both
    # sides a question about prerelease admission rather than resolution
    v=$(python3 - "$RUN/cache/${g//\//%2F}.json" "$n" <<'EOF'
import json, re, sys
def key(v):
    m = re.match(r"^(\d+)\.(\d+)\.(\d+)", v)
    return tuple(int(x) for x in m.groups()) if m else (-1, -1, -1)
rel = sorted((v for v in json.load(open(sys.argv[1]))["versions"] if "-" not in v),
             key=key, reverse=True)
n = int(sys.argv[2])
sys.exit(1) if n >= len(rel) else print(rel[n])
EOF
    ) || break
    if "$exe" npm --cache "$RUN/cache" "$g@$v" > "$W/seed.ours" 2>&1; then
      pin=$v; back=$n; break
    fi
  done
  if [ -z "$pin" ]; then
    echo "$g DROP no root our side can resolve in $BACK releases"
    continue
  fi
  node "$S/root.js" "$RUN/cache" "$g@$pin" > "$W/package.json"
  # the shim fills from the registry alone, and npm clones a git dependency
  # itself, into no snapshot
  ( cd "$W" && rm -f package-lock.json && \
    HOME="$RUN/home" npm_config_git=false npm install --package-lock-only \
      --registry "http://127.0.0.1:$PORT" --cache "$RUN/home/npmcache" \
      --userconfig "$RUN/home/.npmrc" --globalconfig "$RUN/home/npmrc-global" \
      --no-audit --no-fund --no-update-notifier --loglevel=error \
      > seed.npm 2>&1 ) || { echo "$g DROP npm cannot resolve $pin"; tail -2 "$W/seed.npm"; continue; }
  latest=$(python3 -c 'import json,sys;print(json.load(open(sys.argv[1]))["dist-tags"]["latest"])' \
             "$RUN/cache/${g//\//%2F}.json")
  echo "$g $pin (walked back $back from $latest)"
  # query, pin, releases walked back, dist-tags.latest
  printf '%s %s %s %s\n' "$g" "$pin" "$back" "$latest" >> "$S/baseline/roots.txt"
done < "$S/queries.txt"

echo "filled $(sort -u "$RUN/miss.log" | wc -l) names npm asked for and the farm lacked"
# npm's own http cache would otherwise answer a frozen run from what the
# fill pass fetched, which would hide a snapshot hole rather than show it
rm -rf "$RUN/home/npmcache"
