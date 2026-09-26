#!/usr/bin/env bash
# usage: scale.sh [--regress | --record] <pac-exe> <run-dir> [queries-file]
#        MODES="tool pubgrub" P=<jobs> TIMEOUT=<s>
S="$(cd "$(dirname "$0")" && pwd)"
ECO=debian
. "$S/../scale-lib.sh"

all_queries() { sed -n 's/^Package: //p' "$TOP/repos/debian/Packages" | sort -u; }

prepare() {
  snapshot debian/Packages
  bash "$S/setup.sh" "$run/aptroot" > "$run/setup.log" 2>&1 || { cat "$run/setup.log" >&2; return 1; }
  export APTROOT=$run/aptroot APT=${APT:-apt-get}
}

. "$S/refused.sh"

ask() {
  APT_CONFIG=$APTROOT/etc/apt/apt.conf timeout "$TIMEOUT" "$APT" -s install $1 > "$o.apt" 2>&1
  local rc=$?
  grep '^Inst ' "$o.apt" | awk '{print $2}' | sort -u > "$o.theirs"
  return $rc
}

ask_tool() { answer "$S/baseline/apt-$1" names "$o.apt" ask "$2"; }

run_pac() {
  (cd "$TOP" && timeout "$TIMEOUT" "$run/pac.exe" debian $(flag "$1") --native amd64 \
     repos/debian/Packages $3) > "$2.out" 2>&1
}

extract() { rows "$1.out" | sed -n 's/:amd64 .*//p' | sort -u > "$1.ours"; }

canon() { rows "$1.out"; }

main "$@"
