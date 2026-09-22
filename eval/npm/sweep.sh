#!/usr/bin/env bash
# Run every goal against a frozen shim and total the two scores.
# usage: sweep.sh <exe> <tag> [run-dir] [port]
set -u
S="$(cd "$(dirname "$0")" && pwd)"
exe=$1; tag=$2
RUN="${3:-/tmp/npm-cmp}"; PORT="${4:-8899}"
export RUN PORT NORM
mkdir -p "$S/out"

: > "$RUN/frozen-miss.log"
python3 "$S/shim.py" "$PORT" "$RUN/cache" --frozen --log "$RUN/frozen-miss.log" &
shim=$!
trap 'kill $shim 2>/dev/null' EXIT
sleep 1

xargs -P 4 -I{} bash "$S/cmp.sh" "$exe" "$tag" {} < "$S/goals.txt" > "$S/out/$tag.sweep" 2>&1
sort "$S/out/$tag.sweep" -o "$S/out/$tag.sweep"
cat "$S/out/$tag.sweep"

awk -F'#' '/#/ { split($2,a,","); for (i=1;i<=6;i++) t[i]+=a[i]; g++ }
     END { printf "TOTAL %d goals | nodes ours=%d npm=%d agree=%d (%.1f%% of npm) | edges ours=%d npm=%d agree=%d (%.1f%% of npm)\n",
                  g, t[1], t[2], t[3], 100*t[3]/t[2], t[4], t[5], t[6], 100*t[6]/t[5] }' \
     "$S/out/$tag.sweep"

for g in $(cut -d' ' -f1 "$S/roots.txt"); do
  slug=${g//\//__}
  [ -s "$S/out/$tag/$slug.edges.npmonly" ] || continue
  python3 "$S/verdict.py" "$RUN" "$g" "$S/out/$tag/$slug"
done

bash "$S/check-misses.sh" "$RUN/frozen-miss.log"
