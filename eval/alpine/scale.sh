#!/usr/bin/env bash
# Whether pac answers as apk add --simulate does, and valid.sh's question,
# over every package in the APKINDEX, or over the worlds a queries file lists,
# each answered into the run directory.
# usage: scale.sh [--regress | --record] <pac-exe> <run-dir> [queries-file]
#        P=<jobs> TIMEOUT=<s>
S="$(cd "$(dirname "$0")" && pwd)"
. "$S/../scale-lib.sh"
INDEX=$TOP/repos/alpine/APKINDEX

all_queries() { sed -n 's/^P://p' "$INDEX" | sort -u; }

prepare() {
  snapshot alpine/APKINDEX
  bash "$S/setup.sh" "$run/apkroot" > "$run/setup.log" 2>&1 || { cat "$run/setup.log" >&2; return 1; }
  export APKROOT=$run/apkroot APK=${APK:-apk}
}

ask() {
  timeout "$TIMEOUT" "$APK" add --root "$APKROOT/root" --usermode --allow-untrusted \
    --no-network --repository "$APKROOT/repo" --simulate $1 > "$o.apk" 2>&1
  local rc=$?
  sed -n 's/^( *[0-9]*\/[0-9]*) Installing \([^ ]*\) .*/\1/p' "$o.apk" | sort -u > "$o.theirs"
  return $rc
}

one() {
  local o=$run/out/$1 pac tool corr=- valid=- oo=- to=- t0=$EPOCHREALTIME
  set -f
  timeout "$TIMEOUT" "$run/pac.exe" alpine "$INDEX" $2 > "$o.out" 2>&1
  echo $? > "$o.rc"
  local wall; wall=$(since "$t0")
  pac=$(pac_status "$(cat "$o.rc")" "$o.out" '^packages (')
  sed -n '/^packages (/,/^encoded solution/s/^  \([^ ]*\) .*/\1/p' "$o.out" | sort -u > "$o.ours"
  answer "$S/baseline/apk-$1" names ask "$2"
  [ "$pac" = ok ] && [ "$tool" = ok ] && compare "$o.ours" "$o.theirs"
  [ "$pac" = ok ] && valid "$o" default "$2"
  echo "query=$1 mode=default pac=$pac tool=$tool corr=$corr valid=$valid oo=$oo to=$to wall=$wall"
}

main "$@"
