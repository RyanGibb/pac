#!/usr/bin/env bash
# Re-run every goal that diverged in <base-tag>, with the versions npm
# chose and we did not forced on both sides as root overrides.  A goal
# that then agrees exactly was a preference gap: npm's answer was already
# a resolution of our instance and only our ordering ranked it second.
# usage: pin.sh <exe> <base-tag> <tag> [run-dir] [port]
set -u
S="$(cd "$(dirname "$0")" && pwd)"
exe=$1; base=$2; tag=$3
RUN="${4:-/tmp/npm-cmp}"; PORT="${5:-8899}"
export RUN PORT NORM

: > "$RUN/pin-miss.log"
python3 "$S/shim.py" "$PORT" "$RUN/cache" --frozen --log "$RUN/pin-miss.log" &
shim=$!
trap 'kill $shim 2>/dev/null' EXIT
sleep 1

ok=0; bad=0
for g in $(cut -d' ' -f1 "$S/roots.txt"); do
  slug=${g//\//__}
  [ -s "$S/out/$base/$slug.edges.npmonly" ] || continue
  # one pin per (name, version) npm resolved to and we did not
  ex=$(cut -f4,5 "$S/out/$base/$slug.edges.npmonly" | sort -u \
       | awk '{printf "%s@%s ", $1, $2}')
  line=$(EXTRA="$ex" bash "$S/cmp.sh" "$exe" "$tag" "$g")
  echo "$line"
  case $line in
  *"ours-only=0 "*"npm-only=0 "*"ours-only=0 "*"npm-only=0 "*) ok=$((ok+1)) ;;
  *) bad=$((bad+1)) ;;
  esac
done
printf 'PINNED now-exact=%d still-divergent=%d\n' "$ok" "$bad"
