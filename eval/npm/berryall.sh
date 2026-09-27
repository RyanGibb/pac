#!/usr/bin/env bash
# The Berry check (berry.sh) of every answer a scale.sh run holds, P at a
# time, against one berryreg.py over the run's snapshot farm.  Writes
# <run>/berry.txt, a line per answer (query, mode, then berry.sh's), and a
# summary.
# usage: berryall.sh <run-dir> <port>   P=<jobs>; the run's READING=shared
set -u
S="$(cd "$(dirname "$0")" && pwd)"
run=$(cd "$1" && pwd) port=$2
grep -qx 'READING=shared' "$run/params" ||
  { echo "$0: $run was not run with READING=shared, whose answers alone Berry must take" >&2; exit 2; }
export NPM_RUN=$run BPORT=$port S
python3 "$S/berryreg.py" "$port" "$run/cache" > "$run/berryreg.log" 2>&1 &
reg=$!
trap 'kill $reg' EXIT
sleep 1
one() {  # <key> <mode> <query...>
  local key=$1 mode=$2; shift 2
  local o=$NPM_RUN/out/$key.$mode
  grep -q '^node_modules' "$o.out" 2>/dev/null || return 0
  mkdir -p "$o.bcheck"
  printf 'query=%s mode=%s %s\n' "$key" "$mode" "$(bash "$S/berry.sh" "$o.out" "$o.bcheck" "$@")"
}
export -f one
modes=$(sed -n 's/^MODES=//p' "$run/params")
while IFS=$'\t' read -r key query; do
  for m in $modes; do printf '%s\t%s\t%s\n' "$key" "$m" "$query"; done
done < "$run/keys" |
  xargs -P "${P:-16}" -d '\n' -n 1 bash -c 'IFS=$'"'"'\t'"'"' read -r k m q <<< "$1"; one "$k" "$m" $q' _ \
  > "$run/berry.txt"
awk '{for (i = 1; i <= NF; i++) if ($i ~ /^berry=/) n[$i]++} END {for (k in n) print k, n[k]}' "$run/berry.txt"
