#!/usr/bin/env bash
# Re-ask our solver the divergent goals with 0install's answer pinned, to
# separate a preference gap from an instance gap.  There is no --pin flag
# on the opam frontend and the snapshot must not be touched, so the pin
# is a synthetic root: an overlay repository that symlinks every package
# directory of repos/opam-repository and adds one package pac-pin.0 whose
# depends are exactly 0install's selection at exact versions.  If our
# solver satisfies pac-pin, 0install's answer was already a resolution of
# our instance and only our preference ordering ranked it second; if it
# reports unsatisfiable, our instance does not contain that resolution.
# usage: pin.sh <exe> <base-tag>
set -u
S="$(cd "$(dirname "$0")" && pwd)"
R="$(cd "$S/../../repos/opam-repository" && pwd)"
OVL="${OVL:-/tmp/claude-1000/opam-ovl}"
exe=$1; base=$2

if [ ! -d "$OVL/packages" ]; then
  mkdir -p "$OVL/packages"
  cp "$R/repo" "$R/version" "$OVL/" 2>/dev/null || true
  for d in "$R"/packages/*; do ln -sfn "$d" "$OVL/packages/$(basename "$d")"; done
fi

pref=0; inst=0
for g in $(cat "$S/goals.txt"); do
  [ -s "$S/out/$base/$g.oursonly" ] || [ -s "$S/out/$base/$g.themonly" ] || continue
  rm -rf "$OVL/packages/pac-pin"
  mkdir -p "$OVL/packages/pac-pin/pac-pin.0"
  {
    echo 'opam-version: "2.0"'
    echo 'depends: ['
    sed 's/^\([^.]*\)\.\(.*\)$/  "\1" {= "\2"}/' "$S/opam-$g.sel"
    echo ']'
  } > "$OVL/packages/pac-pin/pac-pin.0/opam"
  "$exe" opam "$OVL" pac-pin > "$S/out/$g.pin" 2>&1
  if grep -q '^unsatisfiable' "$S/out/$g.pin"; then
    inst=$((inst+1)); echo "INSTANCE GAP $g"
  else
    pref=$((pref+1)); echo "preference  $g"
  fi
done
printf 'PINNED preference=%d instance=%d\n' "$pref" "$inst"
