#!/usr/bin/env bash
# usage: scale.sh [--regress] <pac-exe> <run-dir> [queries-file]    P=<jobs> TIMEOUT=<s> PORT=<proxy>
#        MODES="tool pubgrub"
S="$(cd "$(dirname "$0")" && pwd)"
ECO=cargo
. "$S/../scale-lib.sh"
export PORT=${PORT:-8991}

all_queries() { python3 "$S/scale.py" sample 20260923 3000; }

prepare() {
  # cargo runs for validity anyway, against the pinned index, and the
  # question it is asked depends on pac's answer, through run_query.py's
  # [patch], so there is no answer per query to record
  if [ "$BASELINE" = record ]; then
    echo "$0: cargo keeps no baseline; --regress asks cargo afresh" >&2; return 1
  fi
  snapshot crates.io-index
  python3 -c "import sys; sys.path[0] = '$S'; import run_query; run_query.check_toolchain()" || return 1
  # run_query.py points cargo at this port, which must serve the snapshot
  # pac reads
  serve "$PORT" "$TOP/repos/crates.io-index" "$run/proxy.log" \
    python3 "$S/sparse_proxy.py" "$PORT" "$TOP/repos/crates.io-index"
}

# cargo is asked in run_pac, per mode
ask_tool() { tool=-; twall=-; }

# each query its own CARGO_HOME, since cargo locks it for a whole generate-lockfile
run_pac() {
  CARGO_CMP_OUT=$run/w/${2##*/} PAC=$run/pac.exe EXTRA=$(flag "$1") \
    python3 "$S/scale.py" one "$3" "$2"
  local rc=$?
  tool=$(cat "$2.tool" 2> /dev/null || echo error)
  rm -rf "$run/w/${2##*/}"
  return $rc
}

extract() { :; }

correspond() { read -r corr oo to < <(python3 "$S/scale.py" corr "$1"); }

# answers are compared in Python, crates and edges; every mode is checked
canon() { return 1; }

check_query() { printf '%s\n' "$1.manifest/Cargo.toml"; }

fields() {
  python3 - "$1.check/valid.json" <<'EOF'
import json, sys
try:
    v = json.load(open(sys.argv[1]))
except (OSError, ValueError):
    v = {}
yn = {True: "yes", False: "no"}
print(" kept=%s identical=%s" % (yn.get(v.get("kept"), "-"), yn.get(v.get("identical"), "-")), end="")
EOF
}

main "$@"
