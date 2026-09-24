#!/usr/bin/env bash
# Ask opam whether OUR opam selection is a resolution by opam's own
# rules, rather than whether it is the one opam would have picked.
# scale.sh asks the second question against builtin-0install; this one can
# pass where that fails, because 0install ranking another selection first
# is preference, not error.
#
# Our selection becomes the switch's installed state, written straight
# into switch-state with only the packages the query names as roots, and
# three questions must then have nothing to do.  `opam install` of the
# query as given: every atom is satisfied by what is installed.  `opam
# upgrade --fixup`, which resolves for the roots at their installed
# versions with the fewest changes, so it acts only on an inconsistent
# state -- a dependency missing, a conflicts, a package no longer
# available -- and any action at all is that inconsistency.  The same
# fixup again, every package pinned at its version and the solver told to
# remove what it can: the roots need everything installed.  Asking instead
# for the whole selection at exact versions makes every package
# requested, so none could be found unneeded, and --with-test, --with-doc
# and --with-dev-setup, which enable dependencies of requested packages
# only, would be enabled for every package: a different query.
#
# `opam remove --auto-remove` would ask a weaker "needed": it keeps the
# depopts of whatever it keeps and every arm of an `|`, and decides with
# --with-test and the like off.  fixup takes those flags through its roots.
#
# The solver is opam's own default (builtin-mccs), not the
# builtin-0install scale.sh takes its baseline from: the question here is
# whether opam as shipped accepts the selection.  Each query gets its own
# copy of the OPAMROOT setup.sh built, whose pinned global variables are
# load-bearing -- without them opam reads a different universe from our
# loader and the two are no longer answering about one instance.
# usage: valid.sh <exe> <tag> [query]        EXTRA=<flags> passes flags to <exe>
# A query is a query as opam's command line takes it, flags included, e.g.
# "--with-test uri yojson".  With no query it sweeps queries.txt and totals;
# with one it checks that one.
set -u
# byte order, so the output is the same whatever the host's locale
export LC_ALL=C
S="$(cd "$(dirname "$0")" && pwd)"
BASE="${OPAMROOT:-/tmp/claude-1000/opam-cmp-root}"
exe=$1; tag=$2

if [ $# -lt 3 ]; then
  mkdir -p "$S/out"
  xargs -P 4 -I{} bash "$0" "$exe" "$tag" {} < "$S/queries.txt" \
    > "$S/out/$tag.valid" 2>&1
  sort "$S/out/$tag.valid" -o "$S/out/$tag.valid"
  awk '/ NO SOLUTION/ {bad++; next}
       {n++; if ($NF=="VALID") ok++; else print}
       END {printf "TOTAL valid=%d/%d nosol=%d\n", ok, n, bad}' "$S/out/$tag.valid"
  exit 0
fi
query=$3
key=${query//--/}; key=${key// /+}
out="$S/out/$tag"
mkdir -p "$out"
cd "$S/../.."

read -r -a extra <<< "${EXTRA:-}"
read -r -a query <<< "$query"
# opam-version is the one global setup.sh cannot pin opam to, so our side
# is pinned to opam's
"$exe" opam --opam-version "$(opam --version)" ${extra[@]+"${extra[@]}"} \
  repos/opam-repository "${query[@]}" > "$out/$key.vout" 2>&1
sed -n '/^opam packages (/,/^\(system packages\|loaded\)/p' "$out/$key.vout" \
  | sed -n 's/^  \([^ ]*\)$/\1/p' | sort -u > "$out/$key.req"
if [ ! -s "$out/$key.req" ]; then
  printf '%-26s %-7s NO SOLUTION (see %s)\n' "$query" "$tag" "$out/$key.vout"
  exit 1
fi
mapfile -t req < "$out/$key.req"

flags=(); atoms=()
for a in ${extra[@]+"${extra[@]}"} "${query[@]}"; do
  case $a in -t|--with-test|--with-doc|--with-dev-setup) flags+=("$a") ;; esac
done
for a in "${query[@]}"; do
  case $a in -*) ;; *) atoms+=("$a") ;; esac
done
roots=()
for a in "${atoms[@]}"; do
  nv=$(awk -v n="${a%%[.<>=!]*}." 'index($0, n) == 1' "$out/$key.req")
  [ -n "$nv" ] && roots+=("$nv")
done

list() { local s=; for x; do s+=" \"$x\""; done; printf '[%s ]' "$s"; }
r="$out/$key.root"
state() {
  printf 'opam-version: "2.0"\nroots: %s\ninstalled: %s\n' \
    "$(list "$@")" "$(list "${req[@]}")" > "$r/cmp/.opam-switch/switch-state"
}
rm -rf "$r"
cp -r "$BASE" "$r"
export OPAMROOT="$r" OPAMNODEPEXTS=1
o=(--switch cmp -y)

state ${roots[@]+"${roots[@]}"}
opam install --dry-run "${o[@]}" ${flags[@]+"${flags[@]}"} "${atoms[@]}" \
  > "$out/$key.install" 2>&1
irc=$?
opam upgrade --fixup --dry-run "${o[@]}" ${flags[@]+"${flags[@]}"} \
  > "$out/$key.fixup" 2>&1
frc=$?
# every version pinned leaves the solver nothing to change but whether a
# package stays, and with new packages minimised first it removes what it
# can: any removal is a set the roots do not need, jointly unneeded
# cycles included
state ${roots[@]+"${roots[@]}"}
printf "pinned: %s\n" "$(list "${req[@]}")" >> "$r/cmp/.opam-switch/switch-state"
OPAMFIXUPCRITERIA=-new,+removed opam upgrade --fixup --dry-run "${o[@]}" \
  ${flags[@]+"${flags[@]}"} > "$out/$key.prune" 2>&1
arc=$?
state ${roots[@]+"${roots[@]}"}
# opam orders actions, and refuses a cyclic order, only once it has actions
# to take, and on the installed state the questions above have none.
# Marking every package for reinstall and reinstalling the roots hands it
# the whole selection to order, requested as the query requests it, so the
# flags reach the roots alone, and its ordering drops {post} edges as it
# does at install time.  A cycle is a verdict of its own: the selection is
# still a resolution, one opam cannot then install.
printf '%s\n' "${req[@]/./ }" > "$r/cmp/.opam-switch/reinstall"
opam reinstall --dry-run "${o[@]}" ${flags[@]+"${flags[@]}"} \
  ${roots[@]+"${roots[@]}"} > "$out/$key.reinstall" 2>&1
rrc=$?
rm -rf "$r"

acts() { grep -c '^  - [a-z]* ' "$@" | awk -F: '{s+=$NF} END {print s+0}'; }
n=${#req[@]}
ch=$(acts "$out/$key.install" "$out/$key.fixup")
un=$(acts "$out/$key.prune")
re=$(grep -c '^  - recompile ' "$out/$key.reinstall")
rc=$((irc ? irc : frc ? frc : arc))

# both fixups print this only for an empty solution, and install
# of atoms already satisfied never reaches the solver.  The reinstall must
# reach all n packages, or a cycle among the rest would go unseen.
if [ "$rc" -eq 0 ] && [ "$ch" -eq 0 ] && [ "$un" -eq 0 ] &&
   grep -qx 'Nothing to do.' "$out/$key.fixup" &&
   grep -qx 'Nothing to do.' "$out/$key.prune" &&
   ! grep -q 'actions will be simulated' "$out/$key.install"; then
  if grep -q '^The actions to process have cyclic dependencies:' "$out/$key.reinstall"; then
    v=CYCLIC
  elif [ "$rrc" -eq 0 ] && [ "$re" -eq "$n" ] && [ "$(acts "$out/$key.reinstall")" -eq "$n" ]; then
    v=VALID
  else
    v=INVALID
  fi
else
  v=INVALID
fi
printf '%-26s %-7s n=%-5s changes=%-4s unneeded=%-4s rc=%-3s %s\n' \
  "$query" "$tag" "$n" "$ch" "$un" "$rc" "$v"
