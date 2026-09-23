#!/usr/bin/env bash
# cmp.sh's and valid.sh's questions over every package in the APKINDEX, or
# over the worlds a goals file lists, each answered into the run directory.
# usage: scale.sh <pac-exe> <run-dir> [goals-file]    P=<jobs> TIMEOUT=<s>
S="$(cd "$(dirname "$0")" && pwd)"
. "$S/../scale-lib.sh"
INDEX=$TOP/repos/alpine/APKINDEX

all_goals() { sed -n 's/^P://p' "$INDEX" | sort -u; }

prepare() {
  snapshot alpine/APKINDEX
  bash "$S/setup.sh" "$run/apkroot" > "$run/setup.log" 2>&1 || { cat "$run/setup.log" >&2; return 1; }
  export APKROOT=$run/apkroot APK=${APK:-apk}
}

one() {
  local o=$run/out/$1 pac tool corr=- valid=- oo=- to=- t0=$EPOCHREALTIME
  set -f
  timeout "$TIMEOUT" "$run/pac.exe" alpine "$INDEX" $2 > "$o.out" 2>&1
  echo $? > "$o.rc"
  local wall; wall=$(since "$t0")
  pac=$(pac_status "$(cat "$o.rc")" "$o.out" '^packages (')
  sed -n '/^packages (/,/^encoded solution/s/^  \([^ ]*\) .*/\1/p' "$o.out" | sort -u > "$o.ours"
  timeout "$TIMEOUT" "$APK" add --root "$APKROOT/root" --usermode --allow-untrusted \
    --no-network --repository "$APKROOT/repo" --simulate $2 > "$o.apk" 2>&1
  tool=$?
  sed -n 's/^( *[0-9]*\/[0-9]*) Installing \([^ ]*\) .*/\1/p' "$o.apk" | sort -u > "$o.theirs"
  tool=$(tool_status "$tool" "$o.theirs")
  [ "$pac" = ok ] && [ "$tool" = ok ] && compare "$o.ours" "$o.theirs"
  [ "$pac" = ok ] && valid "$o" default "$2"
  echo "goal=$1 mode=default pac=$pac tool=$tool corr=$corr valid=$valid oo=$oo to=$to wall=$wall"
}

main "$@"
