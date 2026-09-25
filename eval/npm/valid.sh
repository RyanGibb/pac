#!/usr/bin/env bash
# The check writes our answer out as the project's package-lock.json
# (mklock.py) beside the query's package.json (root.js), and asks
# npm against a frozen shim, as accepts.sh does: `npm ci --dry-run`, then
# `npm install --package-lock-only` on a copy, which must leave the same
# version at every path of the lock.
#
# npm ci rebuilds the ideal tree from the lock, repairing any edge the
# lock leaves invalid, and fails with EUSAGE only when the repair changes
# a version in the inventory; accepts.sh says what that lets through.
# Measured on express,
# not assumed: it rejects a lock with a transitive package deleted and
# one whose version violates a requirer's range, and accepts both a
# valid-but-older version npm would not have picked and a package nested
# where npm would have hoisted it.
#
# What our answer does not carry is a directory layout -- it is the
# resolution relation, one provider per (requirer, key) -- so mklock.py
# has to synthesise a placement that reproduces exactly that relation
# under node_modules lookup, and controls.sh's nest-valid is what says npm
# judges the placement we chose rather than demanding its own.
#
# usage: valid.sh <exe> <tag> [query]
# With no query it starts the frozen shim, sweeps queries.txt and totals;
# with one it checks that query and expects a shim already listening.
set -u
# byte order, so the output is the same whatever the host's locale
export LC_ALL=C
S="$(cd "$(dirname "$0")" && pwd)"
RUN="${RUN:-/tmp/npm-cmp}"
PORT="${PORT:-8899}"
exe=$1; tag=$2

if [ $# -lt 3 ]; then
  mkdir -p "$S/out"
  : > "$RUN/valid-miss.log"
  python3 "$S/shim.py" "$PORT" "$RUN/cache" --frozen --log "$RUN/valid-miss.log" &
  shim=$!
  trap 'kill $shim 2>/dev/null' EXIT
  sleep 1
  export RUN PORT
  xargs -P 4 -I{} bash "$0" "$exe" "$tag" {} < "$S/queries.txt" \
    > "$S/out/$tag.valid" 2>&1
  sort "$S/out/$tag.valid" -o "$S/out/$tag.valid"
  awk '/ NO (SOLUTION|ROOT|LOCK)/ {bad++; next}
       {n++; if ($NF=="VALID") ok++; else print}
       END {printf "TOTAL valid=%d/%d dropped=%d\n", ok, n, bad}' \
    "$S/out/$tag.valid"
  bash "$S/check-misses.sh" "$RUN/valid-miss.log"
  exit $?
fi
query=$3
slug=${query//\//__}
out="$S/out/$tag"
mkdir -p "$out"

pin=$(awk -v g="$query" '$1==g{print $2}' "$S/baseline/roots.txt")
[ -n "$pin" ] || { printf '%-24s NO ROOT (dropped by seed.sh)\n' "$query"; exit 1; }

# the query scale.sh --regress measures, so validity and correspondence
# are answering about one question
W="$RUN/work/$slug.valid"
mkdir -p "$W"
node "$S/root.js" "$RUN/cache" "$query@$pin" > "$W/package.json"

cd "$S/../.."
# the host scale.sh gives, so the answer validated here is the answer
# compared there rather than a differently ranked sibling of it
npmv=$(sed -n 1p "$S/npm-version")
nodev=$(sed -n 2p "$S/npm-version")

"$exe" npm --offline --cache "$RUN/cache" --tree \
  ${nodev:+--node-version "$nodev"} ${npmv:+--npm-version "$npmv"} \
  "$query@$pin" > "$out/$slug.ours" 2>&1
if ! grep -q '^node_modules' "$out/$slug.ours"; then
  printf '%-24s NO SOLUTION (see %s)\n' "$query" "$out/$slug.ours"
  exit 1
fi

if ! python3 "$S/mklock.py" "$RUN/cache" "$out/$slug.ours" "$W/package-lock.json" \
     --root-manifest "$W/package.json" > "$out/$slug.mklock" 2>&1; then
  printf '%-24s NO LOCK (see %s)\n' "$query" "$out/$slug.mklock"
  exit 1
fi

# the shim fences the registry alone, and npm clones a git dependency itself
npmc() {  # <dir> <npm args...>
  (cd "$1" && shift && HOME="$RUN/home" npm_config_git=false npm "$@" \
    --registry "http://127.0.0.1:$PORT" --cache "$RUN/home/npmcache" \
    --userconfig "$RUN/home/.npmrc" --globalconfig "$RUN/home/npmrc-global" \
    --no-audit --no-fund --no-update-notifier)
}
. "$S/accepts.sh"
accepts "$W" "$out/$slug" && v=VALID || v=INVALID

n=$(sed -n 's/^packages (\([0-9]*\)).*/\1/p' "$out/$slug.ours")
plc=$(sed -n 's/.*: \([0-9]*\) placements.*/\1/p' "$out/$slug.mklock")
dep=$(sed -n 's/.*max nesting \([0-9]*\).*/\1/p' "$out/$slug.mklock")
bad=$(grep -cE 'npm error (Invalid|Missing):' "$out/$slug.ci")
printf '%-24s %-7s n=%-5s placed=%-5s depth=%-3s rc=%-3s bad=%-4s relock=%-3s moved=%-4s %s\n' \
  "$query" "$tag" "$n" "$plc" "$dep" "$ci_rc" "$bad" "$relock_rc" "$moved" "$v"
