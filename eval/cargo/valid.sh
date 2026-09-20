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
# Crate bodies come from CARGO_HOME, which warm.sh fills in one online
# pass: `cargo metadata` insists on full manifests and will not report
# without them, but the verification pass itself runs --frozen and so
# reaches no network at all.  Run warm.sh once per snapshot before
# sweeping; a goal whose bodies are missing is reported NOCACHE rather
# than scored.
#
# usage: valid.sh [goals-file | goal ...]      (default goals.txt)
#        WARM=1 valid.sh ...  -- the online warming pass (see warm.sh)
# env: PAC, CARGO_CMP_OUT (run dir), PORT
set -uo pipefail
S="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
export CARGO_CMP_OUT="${CARGO_CMP_OUT:-/tmp/cargo-valid}"
PORT="${PORT:-8991}"

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

warm=""; sub="valid"; word="valid"
if [ "${WARM:-}" = 1 ]; then warm="--warm"; sub="warm"; word="warmed"; fi

ok=0; n=0; cold=0
while IFS= read -r line; do
  [ -z "$line" ] && continue
  crate="$(echo "$line" | cut -d' ' -f1)"
  feats="$(echo "$line" | cut -s -d' ' -f2-)"
  n=$((n+1))
  args=("$crate" --out "$CARGO_CMP_OUT/$sub/$crate.json")
  [ -n "$warm" ] && args+=("$warm")
  [ -n "$feats" ] && args+=(--features "$feats")
  out=$(timeout 900 python3 "$S/verify.py" "${args[@]}" 2>&1)
  printf '%s\n' "$out"
  # INVALID and WARM-FAILED both contain the word they negate, so the
  # failing cases have to be ruled out first
  case "$out" in
    *INVALID*|*WARM-FAILED*) ;;
    *NOCACHE*) cold=$((cold+1)) ;;
    *VALID*|*WARMED*) ok=$((ok+1)) ;;
  esac
done < "$GOALS"
printf 'TOTAL %s=%d/%d' "$word" "$ok" "$n"
[ "$cold" -eq 0 ] && echo || printf ' nocache=%d (run warm.sh)\n' "$cold"
