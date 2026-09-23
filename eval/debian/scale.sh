#!/usr/bin/env bash
# cmp.sh's and valid.sh's questions over every package in the Packages index,
# or over the goals a file lists, in each of pac's search modes, answered
# into the run directory.
# usage: scale.sh <pac-exe> <run-dir> [goals-file]
#        MODES="default apt-heap" P=<jobs> TIMEOUT=<s>
S="$(cd "$(dirname "$0")" && pwd)"
MODES=${MODES:-default apt-heap}
. "$S/../scale-lib.sh"

all_goals() { sed -n 's/^Package: //p' "$TOP/repos/debian/Packages" | sort -u; }

prepare() {
  snapshot debian/Packages
  bash "$S/setup.sh" "$run/aptroot" > "$run/setup.log" 2>&1 || { cat "$run/setup.log" >&2; return 1; }
  export APTROOT=$run/aptroot APT=${APT:-apt-get}
}

one() {
  local o=$run/out/$1 m p pac tool corr valid oo to t0 wall last= lastvalid
  APT_CONFIG=$APTROOT/etc/apt/apt.conf timeout "$TIMEOUT" "$APT" -s install "$2" > "$o.apt" 2>&1
  tool=$?
  grep '^Inst ' "$o.apt" | awk '{print $2}' | sort -u > "$o.theirs"
  tool=$(tool_status "$tool" "$o.theirs")
  for m in $MODES; do
    p=$o.$m corr=- valid=- oo=- to=- t0=$EPOCHREALTIME
    (cd "$TOP" && timeout "$TIMEOUT" "$run/pac.exe" debian $(flag "$m") --native amd64 \
       "$2" repos/debian/Packages) > "$p.out" 2>&1
    echo $? > "$p.rc"
    wall=$(since "$t0")
    pac=$(pac_status "$(cat "$p.rc")" "$p.out" ':amd64 ')
    grep ':amd64 ' "$p.out" | sed 's/:amd64 .*//' | sort -u > "$p.ours"
    [ "$pac" = ok ] && [ "$tool" = ok ] && compare "$p.ours" "$o.theirs"
    if [ "$pac" = ok ]; then
      # valid.sh reads nothing of pac's output but its :amd64 rows, so a
      # mode answering the same rows gets the same verdict
      if [ -n "$last" ] && cmp -s <(grep ':amd64 ' "$p.out") <(grep ':amd64 ' "$last.out"); then
        valid=$lastvalid
      else valid "$p" "$m" "$2"; fi
      last=$p lastvalid=$valid
    fi
    echo "goal=$1 mode=$m pac=$pac tool=$tool corr=$corr valid=$valid oo=$oo to=$to wall=$wall"
  done
}

main "$@"
