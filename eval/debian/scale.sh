#!/usr/bin/env bash
# usage: scale.sh [--regress | --record] <pac-exe> <run-dir> [queries-file]
#        MODES="tool pubgrub" P=<jobs> TIMEOUT=<s>
S="$(cd "$(dirname "$0")" && pwd)"
ECO=debian ANSWER=':amd64 '
. "$S/../scale-lib.sh"

all_queries() { sed -n 's/^Package: //p' "$TOP/repos/debian/Packages" | sort -u; }

prepare() {
  snapshot debian/Packages
  bash "$S/setup.sh" "$run/aptroot" > "$run/setup.log" 2>&1 || { cat "$run/setup.log" >&2; return 1; }
  export APTROOT=$run/aptroot APT=${APT:-apt-get}
}

# apt exits 100 for a broken root as for a query it cannot satisfy
refused() {
  [ "$1" -eq 100 ] && grep -qE '^E: (Unable to correct problems|Unmet dependencies|Unable to locate package|Package .* has no installation candidate|Version .* was not found)' "$2"
}

ask() {
  APT_CONFIG=$APTROOT/etc/apt/apt.conf timeout "$TIMEOUT" "$APT" -s install $1 > "$o.apt" 2>&1
  local rc=$?
  grep '^Inst ' "$o.apt" | awk '{print $2}' | sort -u > "$o.theirs"
  return $rc
}

ask_tool() { answer "$S/baseline/apt-$1" names "$o.apt" ask "$2"; }

run_pac() {
  (cd "$TOP" && timeout "$TIMEOUT" "$run/pac.exe" debian $(flag "$1") --native amd64 \
     $3 repos/debian/Packages) > "$2.out" 2>&1
}

extract() { grep ':amd64 ' "$1.out" | sed 's/:amd64 .*//' | sort -u > "$1.ours"; }

# check.sh reads nothing of pac's output but its name:arch rows
canon() { awk 'NF == 2 && $1 ~ /:/' "$1.out"; }

main "$@"
