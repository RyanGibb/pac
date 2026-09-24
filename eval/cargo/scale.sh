#!/usr/bin/env bash
# run_goal.py's and verify.py's questions over a seeded sample of crates.io
# (scale.py sample 20260923 3000), or over the crates a goals file lists
# (scale.py targets makes pools of them), answered into the run directory.
# usage: scale.sh <pac-exe> <run-dir> [goals-file]    P=<jobs> TIMEOUT=<s> PORT=<proxy>
S="$(cd "$(dirname "$0")" && pwd)"
. "$S/../scale-lib.sh"
export PORT=${PORT:-8991}

all_goals() { python3 "$S/scale.py" sample 20260923 3000; }

prepare() {
  snapshot crates.io-index
  python3 -c "import sys; sys.path[0] = '$S'; import run_goal; run_goal.check_toolchain()" || return 1
  # run_goal.py points cargo at this port, and the proxy serves the snapshot pac reads
  if ! curl -sf "http://127.0.0.1:$PORT/config.json" > /dev/null; then
    python3 "$S/sparse_proxy.py" "$PORT" &
    trap "kill $!" EXIT
    sleep 1
  fi
}

# each goal its own CARGO_HOME, since cargo locks it for a whole generate-lockfile
one() { CARGO_CMP_OUT=$run/w/$1 PAC=$run/pac.exe python3 "$S/scale.py" one "$2" "$run/out/$1"; }

main "$@"
