#!/usr/bin/env bash
set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
export CARGO_CMP_OUT="${CARGO_CMP_OUT:-/tmp/cargo-cmp}"
GOALS="${1:-$HERE/goals.txt}"

while IFS= read -r line; do
  [ -z "$line" ] && continue
  crate="$(echo "$line" | cut -d' ' -f1)"
  feats="$(echo "$line" | cut -s -d' ' -f2-)"
  echo "=== $crate ${feats:+(features: $feats)} ==="
  if [ -n "$feats" ]; then
    timeout 280 python3 "$HERE/run_goal.py" "$crate" --features "$feats"
  else
    timeout 280 python3 "$HERE/run_goal.py" "$crate"
  fi
  rc=$?
  if [ $rc -ne 0 ]; then
    echo "  !! run_goal.py exited $rc for $crate"
  fi
done < "$GOALS"
