#!/usr/bin/env bash
# usage: scale.sh [--regress] <pac-exe> <run-dir> [queries-file]    P=<jobs> TIMEOUT=<s> PORT=<proxy>
#        MODES="tool pubgrub"
S="$(cd "$(dirname "$0")" && pwd)"
ECO=cargo ANSWER='^crates ('
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
  # run_query.py points cargo at this port.  A proxy some other run left
  # there would serve its own index, so this run's must be the one that
  # answers, serving the snapshot pac reads
  python3 "$S/sparse_proxy.py" "$PORT" > "$run/proxy.log" 2>&1 &
  local proxy=$! i want have=
  trap "kill $proxy 2> /dev/null" EXIT
  want=$(realpath "$TOP/repos/crates.io-index")
  for i in $(seq 50); do
    have=$(curl -sf "http://127.0.0.1:$PORT/pac-index") && break
    sleep 0.2
  done
  if ! kill -0 "$proxy" 2> /dev/null || [ "$have" != "$want" ]; then
    echo "$0: the proxy on $PORT is not this run's (serving '${have:-nothing}')" >&2; return 1
  fi
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
