#!/usr/bin/env bash
set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
export CARGO_CMP_OUT="${CARGO_CMP_OUT:-/tmp/cargo-cmp}"
GOALS="${1:-$HERE/goals.txt}"

while IFS= read -r crate; do
  [ -z "$crate" ] && continue
  echo "=== $crate ==="
  timeout 280 python3 "$HERE/run_goal.py" "$crate"
  rc=$?
  if [ $rc -ne 0 ]; then
    echo "  !! run_goal.py exited $rc for $crate"
  fi
done < "$GOALS"
