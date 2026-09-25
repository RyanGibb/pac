#!/usr/bin/env bash
# usage: scale.sh [--regress | --record] <pac-exe> <run-dir> [queries-file]
#        MODES="tool pubgrub" P=<jobs> TIMEOUT=<s>
S="$(cd "$(dirname "$0")" && pwd)"
ECO=alpine ANSWER='^packages ('
. "$S/../scale-lib.sh"
INDEX=$TOP/repos/alpine/APKINDEX

all_queries() { sed -n 's/^P://p' "$INDEX" | sort -u; }

prepare() {
  snapshot alpine/APKINDEX
  bash "$S/setup.sh" "$run/apkroot" > "$run/setup.log" 2>&1 || { cat "$run/setup.log" >&2; return 1; }
  export APKROOT=$run/apkroot APK=${APK:-apk}
}

refused() { grep -q '^ERROR: unable to select packages' "$2"; }

ask() {
  timeout "$TIMEOUT" "$APK" add --root "$APKROOT/root" --usermode --allow-untrusted \
    --no-network --repository "$APKROOT/repo" --simulate $1 > "$o.apk" 2>&1
  local rc=$?
  sed -n 's/^( *[0-9]*\/[0-9]*) Installing \([^ ]*\) .*/\1/p' "$o.apk" | sort -u > "$o.theirs"
  return $rc
}

ask_tool() { answer "$S/baseline/apk-$1" names "$o.apk" ask "$2"; }

# the query with every package of apk's answer added to the world: unsat
# says apk's answer is no resolution of our instance.  A baseline records
# names only, and a name has one version in an APKINDEX
pin_tool() {
  timeout "$TIMEOUT" "$run/pac.exe" alpine "$INDEX" $2 $(cat "$o.theirs") > "$o.pin.out" 2>&1
  pin=$(pac_status $? "$o.pin.out" "$ANSWER")
  sed -n '/^packages (/,/^encoded solution/s/^  \([^ ]*\) .*/\1/p' "$o.pin.out" | sort -u > "$o.pin"
}

run_pac() { timeout "$TIMEOUT" "$run/pac.exe" alpine $(flag "$1") "$INDEX" $3 > "$2.out" 2>&1; }

extract() { sed -n '/^packages (/,/^encoded solution/s/^  \([^ ]*\) .*/\1/p' "$1.out" | sort -u > "$1.ours"; }

canon() { sed -n '/^packages (/,/^encoded solution/p' "$1.out"; }

main "$@"
