#!/usr/bin/env bash
# Ask npm whether OUR resolution for a goal is a resolution by npm's own
# rules, rather than whether it is the one npm would have picked.
# cmp.sh asks the second question against a recorded lock-<goal>.json;
# this one can pass where that fails, because npm ranking another tree
# first is preference, not error.
#
# The check writes our answer out as the project's package-lock.json
# (mklock.py) beside the same wrapper package.json mkroot.py mints for
# cmp.sh, and runs `npm ci --dry-run` against the same frozen shim.
#
# npm ci verifies rather than re-resolves by design: it never consults
# the registry for a version, it builds the tree the lockfile describes
# and then checks that tree against every manifest in it, failing with
# EUSAGE if anything is missing or out of range.  Measured on express,
# not assumed: it rejects a lock with a transitive package deleted and
# one whose version violates a requirer's range, and accepts both a
# valid-but-older version npm would not have picked and a package nested
# where npm would have hoisted it.  See notes/validity.md.
#
# What our answer does not carry is a directory layout -- it is the
# resolution relation, one provider per (requirer, key) -- so mklock.py
# has to synthesise a placement that reproduces exactly that relation
# under node_modules lookup, and control 5 above is what says npm judges
# the placement we chose rather than demanding its own.
#
# usage: valid.sh <exe> <tag> [goal]
# With no goal it starts the frozen shim, sweeps goals.txt and totals;
# with one it checks that goal and expects a shim already listening.
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
  xargs -P 4 -I{} bash "$0" "$exe" "$tag" {} < "$S/goals.txt" \
    > "$S/out/$tag.valid" 2>&1
  sort "$S/out/$tag.valid" -o "$S/out/$tag.valid"
  awk '/ NO (SOLUTION|ROOT|LOCK)/ {bad++; next}
       {n++; if ($NF=="VALID") ok++; else print}
       END {printf "TOTAL valid=%d/%d dropped=%d\n", ok, n, bad}' \
    "$S/out/$tag.valid"
  bash "$S/check-misses.sh" "$RUN/valid-miss.log"
  exit $?
fi
goal=$3
slug=${goal//\//__}
out="$S/out/$tag"
mkdir -p "$out"

pin=$(awk -v g="$goal" '$1==g{print $2}' "$S/roots.txt")
[ -n "$pin" ] || { printf '%-24s NO ROOT (dropped by seed.sh)\n' "$goal"; exit 1; }

# the same wrapper root cmp.sh measures, so validity and correspondence
# are answering about one question
W="$RUN/work/$slug.valid"
mkdir -p "$W"
root=$(python3 "$S/mkroot.py" "$RUN/cache" "$goal" "$W" "$pin" | cut -d' ' -f1)

cd "$S/../.."
# the same host cmp.sh gives, so the answer validated here is the answer
# compared there rather than a differently ranked sibling of it
npmv=$(sed -n 1p "$S/npm-version")
nodev=$(sed -n 2p "$S/npm-version")

"$exe" npm --offline --cache "$RUN/cache" --tree \
  ${nodev:+--node-version "$nodev"} ${npmv:+--npm-version "$npmv"} \
  "$root" > "$out/$slug.ours" 2>&1
if ! grep -q '^node_modules' "$out/$slug.ours"; then
  printf '%-24s NO SOLUTION (see %s)\n' "$goal" "$out/$slug.ours"
  exit 1
fi

if ! python3 "$S/mklock.py" "$RUN/cache" "$out/$slug.ours" "$W/package-lock.json" \
     --root-manifest "$W/package.json" > "$out/$slug.mklock" 2>&1; then
  printf '%-24s NO LOCK (see %s)\n' "$goal" "$out/$slug.mklock"
  exit 1
fi

( cd "$W" && HOME="$RUN/home" npm ci --dry-run \
    --registry "http://127.0.0.1:$PORT" --cache "$RUN/home/npmcache" \
    --userconfig "$RUN/home/.npmrc" --globalconfig "$RUN/home/npmrc-global" \
    --no-audit --no-fund --no-update-notifier ) > "$out/$slug.npmlog" 2>&1
nrc=$?

n=$(sed -n 's/^packages (\([0-9]*\)).*/\1/p' "$out/$slug.ours")
plc=$(sed -n 's/.*: \([0-9]*\) placements.*/\1/p' "$out/$slug.mklock")
dep=$(sed -n 's/.*max nesting \([0-9]*\).*/\1/p' "$out/$slug.mklock")
bad=$(grep -cE 'npm error (Invalid|Missing):' "$out/$slug.npmlog")
[ "$nrc" -eq 0 ] && v=VALID || v=INVALID
printf '%-24s %-7s n=%-5s placed=%-5s depth=%-3s rc=%-3s bad=%-4s %s\n' \
  "$goal" "$tag" "$n" "$plc" "$dep" "$nrc" "$bad" "$v"
