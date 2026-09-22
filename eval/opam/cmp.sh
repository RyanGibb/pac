#!/usr/bin/env bash
# Compare a pac binary's opam selection against opam's builtin-0install
# backend on the same repos/opam-repository checkout.  Not builtin-mccs:
# that one optimises over whole resolutions and is out of reach by
# construction.  Both sides solve from a bare universe with no pins, no
# preinstalled packages and no pinned compiler, so each picks its own
# ocaml.
# Baselines under opam-<goal>.sel were taken with opam 2.5.2; regenerate
# them all or none.
# usage: cmp.sh <exe> <tag> <goal>
set -u
# comm expects its inputs in its own collation, and the baselines are in byte order
export LC_ALL=C
S="$(cd "$(dirname "$0")" && pwd)"
export OPAMROOT="${OPAMROOT:-/tmp/claude-1000/opam-cmp-root}"
exe=$1; tag=$2; goal=$3
mkdir -p "$S/out/$tag"
cd "$S/../.."

read -r -a extra <<< "${EXTRA:-}"
"$exe" opam ${extra[@]+"${extra[@]}"} repos/opam-repository "$goal" \
  > "$S/out/$tag/$goal.out" 2>&1
sed -n '/^opam packages (/,/^\(system packages\|loaded\)/p' "$S/out/$tag/$goal.out" \
  | sed -n 's/^  \([^ ]*\)$/\1/p' | sort -u > "$S/out/$tag/$goal.ours"

if [ ! -f "$S/opam-$goal.sel" ]; then
  opam install "$goal" --dry-run --solver=builtin-0install --switch cmp \
    --no-depexts -y > "$S/out/$goal.0i" 2>&1
  sed -n 's/^.*installed \([^ ]*\)$/\1/p' "$S/out/$goal.0i" \
    | sort -u > "$S/opam-$goal.sel"
fi

ours=$(wc -l < "$S/out/$tag/$goal.ours")
them=$(wc -l < "$S/opam-$goal.sel")
agree=$(comm -12 "$S/out/$tag/$goal.ours" "$S/opam-$goal.sel" | wc -l)
comm -23 "$S/out/$tag/$goal.ours" "$S/opam-$goal.sel" > "$S/out/$tag/$goal.oursonly"
comm -13 "$S/out/$tag/$goal.ours" "$S/opam-$goal.sel" > "$S/out/$tag/$goal.themonly"
oo=$(wc -l < "$S/out/$tag/$goal.oursonly")
to=$(wc -l < "$S/out/$tag/$goal.themonly")
printf '%-20s %-7s ours=%-5s 0i=%-5s agree=%-5s ours-only=%-5s 0i-only=%-5s\n' \
  "$goal" "$tag" "$ours" "$them" "$agree" "$oo" "$to"
