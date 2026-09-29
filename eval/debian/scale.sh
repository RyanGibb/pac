#!/usr/bin/env bash
# usage: scale.sh [--regress | --record] <pac-exe> <run-dir> [queries-file]
#        MODES="tool pubgrub" P=<jobs> TIMEOUT=<s>
#        PAC_CACHE=<pac's --cache, by default <run-dir>/pac-cache; empty for none>
#        FOREIGN=<dir>/Packages.<arch>, a foreign architecture's index, which
#          eval/SNAPSHOTS must record as foreign/debian/Packages.<arch>
S="$(cd "$(dirname "$0")" && pwd)"
ECO=debian
. "$S/../scale-lib.sh"
export FOREIGN=${FOREIGN:-}

all_queries() { sed -n 's/^Package: //p' "$TOP/repos/debian/Packages" | sort -u; }

# With a foreign architecture, apt's root holds each index as a repository
# of its own, and pac and the check read the two as one file, the native
# one first: what pac reads of several Packages files is their stanzas in
# turn, and the Architecture: all stanzas both repeat count once
prepare() {
  snapshot debian/Packages
  export PAC_INDEX=repos/debian/Packages
  if [ -n "$FOREIGN" ]; then
    snapshot "debian/${FOREIGN##*/}" "$FOREIGN"
    cat "$TOP/repos/debian/Packages" "$FOREIGN" > "$run/Packages" || return 1
    PAC_INDEX=$run/Packages
  fi
  bash "$S/setup.sh" "$run/aptroot" > "$run/setup.log" 2>&1 || { cat "$run/setup.log" >&2; return 1; }
  [ -z "$FOREIGN" ] || export INDEX=$run/Packages
  export APTROOT=$run/aptroot APT=${APT:-apt-get} PAC_CACHE=${PAC_CACHE-$run/pac-cache}
}

params() { [ -z "$FOREIGN" ] || echo "FOREIGN=$FOREIGN"; }

. "$S/refused.sh"

ask() {
  APT_CONFIG=$APTROOT/etc/apt/apt.conf timeout "$TIMEOUT" "$APT" -s install $1 > "$o.apt" 2>&1
  local rc=$?
  grep '^Inst ' "$o.apt" | awk '{print $2}' | sort -u > "$o.theirs"
  return $rc
}

ask_tool() { answer "$S/baseline/apt-$1" names "$o.apt" ask "$2"; }

run_pac() {
  local c=(--no-cache)
  [ -z "$PAC_CACHE" ] || c=(--cache "$PAC_CACHE")
  (cd "$TOP" && timeout "$TIMEOUT" "$run/pac.exe" debian $(flag "$1") --native amd64 \
     "${c[@]}" "$PAC_INDEX" $3) > "$2.out" 2>&1
}

# apt names a native package bare and a foreign one name:arch
extract() { rows "$1.out" | awk '{sub(/:amd64$/, "", $1); print $1}' | sort -u > "$1.ours"; }

canon() { rows "$1.out"; }

main "$@"
