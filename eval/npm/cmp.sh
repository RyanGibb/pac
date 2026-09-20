#!/usr/bin/env bash
# Compare one goal's resolution against npm's, on nodes and on edges.
#
# Both sides are asked the same question: a wrapper root depending on
# nothing but the goal, pinned to the exact version the snapshot's
# dist-tags.latest names (mkroot.py writes the packument our side reads
# and the package.json npm reads from that one manifest).  Our side runs
# --offline and npm runs against a frozen shim, so neither can reach past
# the snapshot.
#
# Baselines are kept in lock-<goal>.json and reused; they were taken with
# the npm in npm-version, whose arborist differs across majors, so
# regenerate them all or none.  EXTRA pins names on *both* sides at once
# -- "name@version ..." appended to the wrapper's dependencies -- so a
# divergence can be re-asked with npm's pick forced: if the two then
# coincide, npm's answer was one our instance already admitted and only
# our preference ordering differed.
#
# usage: cmp.sh <exe> <tag> <goal>
set -u
S="$(cd "$(dirname "$0")" && pwd)"
RUN="${RUN:-/tmp/npm-cmp}"
PORT="${PORT:-8899}"
exe=$1; tag=$2; goal=$3
slug=${goal//\//__}
out="$S/out/$tag"
mkdir -p "$out"

pin=$(awk -v g="$goal" '$1==g{print $2}' "$S/roots.txt")
[ -n "$pin" ] || { printf '%-24s NOT IN roots.txt (dropped by seed.sh)\n' "$goal"; exit 1; }

W="$RUN/work/$slug"
[ -n "${EXTRA:-}" ] && W="$RUN/work/$slug.pin"
mkdir -p "$W"
root=$(python3 "$S/mkroot.py" "$RUN/cache" "$goal" "$W" "$pin" | cut -d' ' -f1)

if [ -n "${EXTRA:-}" ]; then
  root=$(python3 "$S/pinroot.py" "$RUN/cache" "$W" ${EXTRA})
  # a pinned lockfile is derived, not a baseline: it is remade every run
  lock="$out/$slug.lock"; rm -f "$lock"
else
  lock="$S/lock-$slug.json"
fi

"$exe" npm --offline --cache "$RUN/cache" --tree "$root" > "$out/$slug.ours" 2>&1

if [ ! -s "$lock" ]; then
  ( cd "$W" && rm -f package-lock.json && \
    HOME="$RUN/home" npm install --package-lock-only \
      --registry "http://127.0.0.1:$PORT" --cache "$RUN/home/npmcache" \
      --userconfig "$RUN/home/.npmrc" --globalconfig "$RUN/home/npmrc-global" \
      --no-audit --no-fund --no-update-notifier --loglevel=error \
      > "$out/$slug.npmlog" 2>&1 )
  cp "$W/package-lock.json" "$lock" 2>/dev/null
fi

if [ ! -s "$lock" ]; then
  printf '%-24s NO LOCKFILE (see %s)\n' "$goal" "$out/$slug.npmlog"
  exit 1
fi
if ! grep -q '^node_modules' "$out/$slug.ours"; then
  printf '%-24s NO SOLUTION (see %s)\n' "$goal" "$out/$slug.ours"
  exit 1
fi
python3 "$S/edges.py" "$goal" "$lock" "$out/$slug.ours" "$out/$slug" ${NORM:-}
