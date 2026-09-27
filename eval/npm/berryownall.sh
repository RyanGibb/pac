#!/usr/bin/env bash
# Yarn Berry's own answer to each query of a scale.sh run (berryown.py), and
# how each of our answers there compares with it, P at a time, against one
# berryreg.py over the run's snapshot.  Writes <run>/berryown.txt, a line
# per answer, and a summary.
# usage: berryownall.sh <run-dir> <port>   P=<jobs>; the run's READING=shared
set -u
export LC_ALL=C
S="$(cd "$(dirname "$0")" && pwd)"
run=$(cd "$1" && pwd) port=$2
grep -qx 'READING=shared' "$run/params" ||
  { echo "$0: $run was not run with READING=shared, whose answers alone compare with Berry's" >&2; exit 2; }
export NPM_RUN=$run BPORT=$port S
python3 "$S/berryreg.py" "$port" "$run/cache" > "$run/berryreg-own.log" 2>&1 &
reg=$!
trap 'kill $reg' EXIT
sleep 1
one() {  # <key> <query...>
  local key=$1; shift
  local w=$NPM_RUN/out/$key.berryown
  case "$w" in */out/*.berryown) rm -rf "$w" ;; esac
  mkdir -p "$w/.home"
  python3 "$S/berryown.py" prepare "$w" "$BPORT" "$@"
  (cd "$w" && HOME=$w/.home XDG_CACHE_HOME=$w/.home/.cache YARN_ENABLE_TELEMETRY=0 CI=1 \
     timeout 1800 yarn install --mode=update-lockfile) > "$w.log" 2>&1
  local rc=$?
  for m in $(sed -n 's/^MODES=//p' "$NPM_RUN/params"); do
    local o=$NPM_RUN/out/$key.$m.out
    grep -q '^node_modules' "$o" 2>/dev/null || continue
    if [ $rc -eq 0 ]; then
      printf 'query=%s mode=%s %s\n' "$key" "$m" "$(python3 "$S/berryown.py" compare "$NPM_RUN/cache" "$o" "$w" 2>&1 | tail -n 1)"
    else
      printf 'query=%s mode=%s berry-own install rc=%s\n' "$key" "$m" "$rc"
    fi
  done
}
export -f one
tr '\t' ' ' < "$run/keys" | xargs -P "${P:-16}" -L 1 bash -c 'one "$@"' _ > "$run/berryown.txt"
awk '{for (i = 1; i <= NF; i++) if ($i ~ /^exact=/) n[$i]++; if (/install rc=/) n["install-failed"]++}
     END {for (k in n) print k, n[k]}' "$run/berryown.txt"
