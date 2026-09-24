#!/usr/bin/env bash
# Whether pac's selection is builtin-0install's, and valid.sh's question,
# over every package name in the repository, or over the queries a goals
# file lists (flags included, as in "--with-test fmt"), in each of pac's
# search modes, answered into the run directory.  Not builtin-mccs, opam's
# default: that one optimises over whole resolutions and is out of reach by
# construction.  Two more per goal: pin, whether 0install's answer is a
# resolution of our instance at all, which is what separates a preference
# gap from an instance gap; and where 0install refuses, mccs, since 0install
# gives up where a solution may still exist.
# usage: scale.sh [--regress | --record] <pac-exe> <run-dir> [goals-file]
#        MODES="default 0install-order" P=<jobs> TIMEOUT=<s>
S="$(cd "$(dirname "$0")" && pwd)"
MODES=${MODES:-default 0install-order}
. "$S/../scale-lib.sh"
REPO=$TOP/repos/opam-repository

all_goals() { ls "$REPO/packages"; }

prepare() {
  # opam runs ocamlc to set sys-ocaml-version, which would make ocaml-system
  # available to opam and to nothing on our side
  if command -v ocamlc > /dev/null; then echo "$0: ocamlc is on PATH" >&2; return 1; fi
  snapshot opam-repository
  bash "$S/setup.sh" "$run/opamroot" > "$run/setup.log" 2>&1 || { cat "$run/setup.log" >&2; return 1; }
  mkdir -p "$run/ovl/packages"
  ln -sfn -t "$run/ovl/packages" "$REPO"/packages/*
  export OPAMROOT=$run/opamroot OV=$(opam --version)
}

ask() {
  # opam holds the switch's lock for a whole dry run, so each goal asks its own copy
  rm -rf "$o.root"; cp -r "$OPAMROOT" "$o.root"
  OPAMROOT=$o.root timeout "$TIMEOUT" opam install $1 --dry-run --solver=builtin-0install \
    --switch cmp --no-depexts -y > "$o.0i" 2>&1
  local rc=$?
  sed -n 's/^.*installed \([^ ]*\)$/\1/p' "$o.0i" | sort -u > "$o.theirs"
  return $rc
}

one() {
  local o=$run/out/$1 m p pac tool corr valid oo to t0 wall pin=- mccs=- last= lastvalid
  local pn=pac-pin-${1//[^A-Za-z0-9_+-]/_}
  set -f
  answer "$S/baseline/opam-$1" sel ask "$2"
  if [ "$tool" = refuse ] && [ "$BASELINE" != regress ]; then
    OPAMROOT=$o.root timeout "$TIMEOUT" opam install $2 --dry-run --switch cmp --no-depexts -y \
      > "$o.mccs" 2>&1
    mccs=$?
    sed -n 's/^.*installed \([^ ]*\)$/\1/p' "$o.mccs" > "$o.mccs.sel"
    mccs=$(tool_status "$mccs" "$o.mccs.sel")
  fi
  rm -rf "$o.root"
  if [ "$tool" = ok ]; then
    mkdir -p "$run/ovl/packages/$pn/$pn.0"
    { echo 'opam-version: "2.0"'; echo 'depends: ['
      sed 's/^\([^.]*\)\.\(.*\)$/  "\1" {= "\2"}/' "$o.theirs"; echo ']'
    } > "$run/ovl/packages/$pn/$pn.0/opam"
    timeout "$TIMEOUT" "$run/pac.exe" opam --opam-version "$OV" "$run/ovl" $2 "$pn" > "$o.pin" 2>&1
    pin=$(pac_status $? "$o.pin" '^opam packages (')
  fi
  for m in $MODES; do
    p=$o.$m corr=- valid=- oo=- to=- t0=$EPOCHREALTIME
    (cd "$TOP" && timeout "$TIMEOUT" "$run/pac.exe" opam --opam-version "$OV" $(flag "$m") \
       repos/opam-repository $2) > "$p.out" 2>&1
    echo $? > "$p.rc"
    wall=$(since "$t0")
    pac=$(pac_status "$(cat "$p.rc")" "$p.out" '^opam packages (')
    sed -n '/^opam packages (/,/^\(system packages\|loaded\)/s/^  \([^ ]*\)$/\1/p' "$p.out" |
      sort -u > "$p.ours"
    [ "$pac" = ok ] && [ "$tool" = ok ] && compare "$p.ours" "$o.theirs"
    if [ "$pac" = ok ]; then
      # valid.sh reads nothing of pac's output but the selection
      if [ -n "$last" ] && cmp -s "$p.ours" "$last.ours"; then valid=$lastvalid
      else valid "$p" "$m" "$2"; fi
      last=$p lastvalid=$valid
    fi
    echo "goal=$1 mode=$m pac=$pac tool=$tool corr=$corr valid=$valid oo=$oo to=$to wall=$wall pin=$pin mccs=$mccs"
  done
}

main "$@"
