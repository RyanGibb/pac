#!/usr/bin/env bash
# The baseline is builtin-0install, not builtin-mccs, opam's default: that
# one optimises over whole resolutions and is out of reach by
# construction.  Two more per query: pin, whether 0install's answer is a
# resolution of our instance at all, which is what separates a preference
# gap from an instance gap; and where 0install refuses, mccs, since 0install
# gives up where a solution may still exist.
# usage: scale.sh [--regress | --record] <pac-exe> <run-dir> [queries-file]
#        MODES="tool pubgrub" P=<jobs> TIMEOUT=<s>
S="$(cd "$(dirname "$0")" && pwd)"
ECO=opam
. "$S/../scale-lib.sh"
REPO=$TOP/repos/opam-repository

all_queries() { ls "$REPO/packages"; }

prepare() {
  # opam runs ocamlc to set sys-ocaml-version, which would make ocaml-system
  # available to opam and to nothing on our side
  if command -v ocamlc > /dev/null; then echo "$0: ocamlc is on PATH" >&2; return 1; fi
  snapshot opam-repository
  bash "$S/setup.sh" "$run/opamroot" > "$run/setup.log" 2>&1 || { cat "$run/setup.log" >&2; return 1; }
  mkdir -p "$run/ovl/packages" "$run/ovl.tmp"
  ln -sfn -t "$run/ovl/packages" "$REPO"/packages/*
  export OPAMROOT=$run/opamroot OV=$(opam --version)
}

# opam's exit 5, not found, is not the query's alone, so it counts only
# beside an error saying the query names nothing opam could install
refused() {
  [ "$1" -eq 20 ] || { [ "$1" -eq 5 ] &&
    grep -qE '^\[ERROR\] (Package .* has no version|No package named|.*: unmet availability conditions)' "$2"; }
}

ask() {
  # opam holds the switch's lock for a whole dry run, so each query asks its own copy
  rm -rf "$o.root"; cp -r "$OPAMROOT" "$o.root"
  OPAMROOT=$o.root timeout "$TIMEOUT" opam install $1 --dry-run --solver=builtin-0install \
    --switch cmp --no-depexts -y > "$o.0i" 2>&1
  local rc=$?
  sed -n 's/^.*installed \([^ ]*\)$/\1/p' "$o.0i" | sort -u > "$o.theirs"
  return $rc
}

ask_tool() {
  local rc
  mccs=-
  answer "$S/baseline/opam-$1" sel "$o.0i" ask "$2"
  if [ "$tool" = refuse ] && [ "$BASELINE" != regress ]; then
    OPAMROOT=$o.root timeout "$TIMEOUT" opam install $2 --dry-run --switch cmp --no-depexts -y \
      > "$o.mccs" 2>&1
    rc=$?
    sed -n 's/^.*installed \([^ ]*\)$/\1/p' "$o.mccs" > "$o.mccs.sel"
    mccs=$(tool_status "$rc" "$o.mccs.sel" "$o.mccs")
  fi
  rm -rf "$o.root"
}

# every run of pac loads the whole overlay, so a query's package is named
# for a hash of its key, which no other key shares, and appears whole or
# not at all
pin_tool() {
  local pn t=$run/ovl.tmp/$1
  pn=pac-pin-$(printf '%s' "$1" | sha256sum | cut -c1-16)
  rm -rf "$t"; mkdir -p "$t/$pn.0"
  { echo 'opam-version: "2.0"'; echo 'depends: ['
    sed 's/^\([^.]*\)\.\(.*\)$/  "\1" {= "\2"}/' "$o.theirs"; echo ']'
  } > "$t/$pn.0/opam"
  if [ -d "$run/ovl/packages/$pn" ]; then mv "$t/$pn.0/opam" "$run/ovl/packages/$pn/$pn.0/opam"
  else mv -T "$t" "$run/ovl/packages/$pn"; fi
  rm -rf "$t"
  timeout "$TIMEOUT" "$run/pac.exe" opam --opam-version "$OV" "$run/ovl" $2 "$pn" > "$o.pin" 2>&1
  pin=$(pac_status $? "$o.pin")
}

run_pac() {
  (cd "$TOP" && timeout "$TIMEOUT" "$run/pac.exe" opam --opam-version "$OV" $(flag "$1") \
     repos/opam-repository $3) > "$2.out" 2>&1
}

extract() { rows "$1.out" | sed -n 's/^\([^ ]*\) \([^ ]*\)$/\1.\2/p' | sort -u > "$1.ours"; }

# a fuzz run skips ask_tool, the one setter of mccs
fields() { printf ' mccs=%s' "${mccs:--}"; }

main "$@"
