#!/usr/bin/env bash
# Ask cargo whether OUR answers are resolutions by cargo's own rules,
# rather than whether they are the ones cargo would have picked.  The
# per-goal work is verify.py; this is run_all.sh's shape around it, plus
# the sparse index both sides must read, which run_all.sh expects to be
# started by hand.
#
# The index proxy is not optional and not a speed trick: it serves the
# repos/crates.io-index snapshot pac reads, so the universe cargo answers
# about is the one pac answered about.  Against the live index cargo sees
# whatever has been published since, and a verdict stops being
# reproducible.
#
# Nothing else has to be in place.  verify.py asks cargo for a lockfile
# and nothing more, so no crate body is ever fetched and there is no
# cache to warm before a sweep.
#
# usage: valid.sh [goals-file | goal ...]      (default goals.txt)
# env: PAC, CARGO_CMP_OUT (run dir), PORT
set -uo pipefail
S="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
export CARGO_CMP_OUT="${CARGO_CMP_OUT:-/tmp/cargo-valid}"
# exported, since run_goal.py writes it into cargo's config
export PORT="${PORT:-8991}"

if [ $# -eq 0 ]; then
  GOALS="$S/goals.txt"
elif [ $# -eq 1 ] && [ -f "$1" ]; then
  GOALS="$1"
else
  GOALS="$CARGO_CMP_OUT/goals.ad-hoc"
  mkdir -p "$CARGO_CMP_OUT"
  printf '%s\n' "$@" > "$GOALS"
fi

mkdir -p "$CARGO_CMP_OUT"
if ! curl -sf "http://127.0.0.1:$PORT/config.json" > /dev/null; then
  python3 "$S/sparse_proxy.py" "$PORT" > "$CARGO_CMP_OUT/proxy.log" 2>&1 &
  proxy=$!
  trap 'kill $proxy 2>/dev/null' EXIT
  for _ in $(seq 20); do
    curl -sf "http://127.0.0.1:$PORT/config.json" > /dev/null && break
    sleep 0.5
  done
fi

ok=0; n=0
while IFS= read -r crate; do
  [ -z "$crate" ] && continue
  n=$((n+1))
  out=$(timeout 900 python3 "$S/verify.py" "$crate" \
          --out "$CARGO_CMP_OUT/valid/$crate.json" 2>&1)
  printf '%s\n' "$out"
  # INVALID contains the word it negates, so it has to be ruled out first
  case "$out" in
    *INVALID*) ;;
    *VALID*) ok=$((ok+1)) ;;
  esac
done < "$GOALS"
printf 'TOTAL valid=%d/%d\n' "$ok" "$n"
