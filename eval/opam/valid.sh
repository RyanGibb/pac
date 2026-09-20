#!/usr/bin/env bash
# Ask opam whether OUR opam selection is a resolution by opam's own
# rules, rather than whether it is the one opam would have picked.
# cmp.sh asks the second question against builtin-0install; this one can
# pass where that fails, because 0install ranking another selection first
# is preference, not error.
#
# The check asks for our whole selection at exact versions --
# `opam install --dry-run pkg.ver ...` into the empty switch setup.sh
# built -- and demands that opam succeed and report installing exactly
# our selection.  opam is verifying, not re-resolving: every atom is
# `name.version`, so no version is left for the solver to pick, and an
# atom named in the request must appear in the solution or there is no
# solution.  The only freedom left is to add a package, which opam takes
# when some depends of a requested package is unsatisfied by the rest.
# So an extra installed line means our selection is not closed, and a
# failed solve means it is inconsistent -- a conflicts, an unsatisfiable
# constraint, or a version that does not exist.  Verified by three
# negative controls, see notes/validity.md.
#
# The solver is opam's own default (builtin-mccs), not the
# builtin-0install cmp.sh takes its baseline from: the question here is
# whether opam as shipped accepts the selection, and with every version
# pinned the choice of backend cannot change the answer, only the
# explanation printed when there is none.
#
# Requires the OPAMROOT setup.sh builds -- in particular the global
# variables pinned there, without which opam reads a different universe
# from our loader and the two are no longer answering about one instance.
# usage: valid.sh <exe> <tag> [goal]        EXTRA=<flags> passes flags to <exe>
# With no goal it sweeps goals.txt and totals; with one it checks that one.
set -u
S="$(cd "$(dirname "$0")" && pwd)"
export OPAMROOT="${OPAMROOT:-/tmp/claude-1000/opam-cmp-root}"
exe=$1; tag=$2

if [ $# -lt 3 ]; then
  mkdir -p "$S/out"
  xargs -P 4 -I{} bash "$0" "$exe" "$tag" {} < "$S/goals.txt" \
    > "$S/out/$tag.valid" 2>&1
  sort "$S/out/$tag.valid" -o "$S/out/$tag.valid"
  awk '/ NO SOLUTION/ {bad++; next}
       {n++; if ($NF=="VALID") ok++; else print}
       END {printf "TOTAL valid=%d/%d nosol=%d\n", ok, n, bad}' "$S/out/$tag.valid"
  exit 0
fi
goal=$3
out="$S/out/$tag"
mkdir -p "$out"
cd "$S/../.."

read -r -a extra <<< "${EXTRA:-}"
"$exe" opam ${extra[@]+"${extra[@]}"} repos/opam-repository "$goal" \
  > "$out/$goal.vout" 2>&1
sed -n '/^opam packages (/,/^\(system packages\|loaded\)/p' "$out/$goal.vout" \
  | sed -n 's/^  \([^ ]*\)$/\1/p' | sort -u > "$out/$goal.req"
if [ ! -s "$out/$goal.req" ]; then
  printf '%-20s %-7s NO SOLUTION (see %s)\n' "$goal" "$tag" "$out/$goal.vout"
  exit 1
fi
mapfile -t req < "$out/$goal.req"

opam install --dry-run --switch cmp --no-depexts -y "${req[@]}" \
  > "$out/$goal.opam" 2>&1
orc=$?
sed -n 's/^.*installed \([^ ]*\)$/\1/p' "$out/$goal.opam" | sort -u \
  > "$out/$goal.inst"

n=$(wc -l < "$out/$goal.req")
comm -13 "$out/$goal.req" "$out/$goal.inst" > "$out/$goal.opamextra"
comm -23 "$out/$goal.req" "$out/$goal.inst" > "$out/$goal.notinst"
ex=$(wc -l < "$out/$goal.opamextra")
mi=$(wc -l < "$out/$goal.notinst")

if [ "$orc" -eq 0 ] && [ "$ex" -eq 0 ] && [ "$mi" -eq 0 ]; then
  v=VALID
else
  v=INVALID
fi
printf '%-20s %-7s n=%-5s extra=%-4s missing=%-4s rc=%-3s %s\n' \
  "$goal" "$tag" "$n" "$ex" "$mi" "$orc" "$v"
