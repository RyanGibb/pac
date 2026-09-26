#!/usr/bin/env bash
# Our selection becomes the switch's installed state, written straight
# into switch-state with only the packages the query names as roots.
#
# Valid asks two questions that must have nothing to do.  `opam install`
# of the query as given: every atom is satisfied by what is installed.
# `opam upgrade --fixup`, which resolves for the roots at their installed
# versions with the fewest changes, so it acts only on an inconsistent
# state -- a dependency missing, a conflicts, a package no longer
# available -- and any action at all is that inconsistency.  Asking
# instead for the whole selection at exact versions makes every package
# requested, and --with-test, --with-doc and --with-dev-setup, which
# enable dependencies of requested packages only, would be enabled for
# every package: a different query.  A switch-state holds one version of
# a name, and opam cannot load one holding a version the repository lacks,
# so both fail before opam is asked.
#
# Minimal asks a third: the same fixup, every package pinned at its
# version and the solver told to remove what it can, must also have
# nothing to do, or the roots do not need everything installed.
# `opam remove --auto-remove` would ask a weaker "needed": it keeps the
# depopts of whatever it keeps and every arm of an `|`, and decides with
# --with-test and the like off.  fixup takes those flags through its roots.
#
# opam exits 20 where the solver finds nothing, and 5 for a package it
# cannot install at all; any other failure, a switch it cannot find among
# them, leaves the answer unchecked.
#
# The solver is opam's own default (builtin-mccs), not the
# builtin-0install scale.sh takes its baseline from: the question here is
# whether opam as shipped accepts the selection.  Each answer gets its own
# copy of OPAMROOT, the root setup.sh built, whose pinned global variables
# are load-bearing -- without them opam reads a different universe from
# our loader and the two are no longer answering about one instance.
# usage: check.sh <answer> <out-dir> <query...>, through eval/check.sh
set -u
# byte order, so the output is the same whatever the host's locale
export LC_ALL=C
S="$(cd "$(dirname "$0")" && pwd)"
. "$S/refused.sh"
BASE=${OPAMROOT:?}
REPO="${REPO:-$(dirname "$0")/../../repos/opam-repository}"
ans=$1 out=$2; shift 2
[ -d "$REPO/packages" ] || { echo "no repository $REPO valid=ERR minimal=-"; exit 0; }

# name.version, the form opam names a package by
rows "$ans" | sed -n 's/^\([^ ]*\) \([^ ]*\)$/\1.\2/p' | sort -u > "$out/req"
mapfile -t req < "$out/req"
# the extraction above skips any line that is not a row, so such a line
# would leave opam judging fewer packages than the answer names
malformed=$(rows "$ans" | awk '!/^[^[:space:].]+ [^[:space:]]+$/' | wc -l)
whole "$ans" || malformed=$((malformed + 1))
dups=$(sed 's/\..*//' "$out/req" | sort | uniq -d | wc -l)
# opam cannot even load a switch holding a version the repository lacks
absent=0
for nv in ${req[@]+"${req[@]}"}; do
  [ -f "$REPO/packages/${nv%%.*}/$nv/opam" ] || absent=$((absent + 1))
done

flags=(); atoms=()
for a; do
  case $a in
    -t|--with-test|--with-doc|--with-dev-setup) flags+=("$a") ;;
    -*) ;;
    *) atoms+=("$a") ;;
  esac
done
roots=()
for a in ${atoms[@]+"${atoms[@]}"}; do
  nv=$(awk -v n="${a%%[.<>=!]*}." 'index($0, n) == 1' "$out/req")
  [ -n "$nv" ] && roots+=("$nv")
done

err=0
ran() {  # <rc> <log>: whether opam ran to an answer, a refusal included
  [ "$1" -eq 0 ] || refused "$1" "$2" || err=1
}
list() { local s=; for x; do s+=" \"$x\""; done; printf '[%s ]' "$s"; }
r="$out/root"
state() {
  printf 'opam-version: "2.0"\nroots: %s\ninstalled: %s\n' \
    "$(list "$@")" "$(list ${req[@]+"${req[@]}"})" > "$r/cmp/.opam-switch/switch-state"
}
rm -rf "$r"
cp -r "$BASE" "$r" || err=1
export OPAMROOT="$r" OPAMNODEPEXTS=1
o=(--switch cmp -y)

state ${roots[@]+"${roots[@]}"}
opam install --dry-run "${o[@]}" ${flags[@]+"${flags[@]}"} ${atoms[@]+"${atoms[@]}"} \
  > "$out/install" 2>&1
irc=$?; ran $irc "$out/install"
opam upgrade --fixup --dry-run "${o[@]}" ${flags[@]+"${flags[@]}"} > "$out/fixup" 2>&1
frc=$?; ran $frc "$out/fixup"
# every version pinned leaves the solver nothing to change but whether a
# package stays, and with new packages minimised first it removes what it
# can: any removal is a set the roots do not need, jointly unneeded
# cycles included
state ${roots[@]+"${roots[@]}"}
printf "pinned: %s\n" "$(list ${req[@]+"${req[@]}"})" >> "$r/cmp/.opam-switch/switch-state"
OPAMFIXUPCRITERIA=-new,+removed opam upgrade --fixup --dry-run "${o[@]}" \
  ${flags[@]+"${flags[@]}"} > "$out/prune" 2>&1
arc=$?
# opam orders actions, and refuses a cyclic order, only once it has actions
# to take, and on the installed state the questions above have none.
# Marking every package for reinstall and reinstalling the roots hands it
# the whole selection to order, requested as the query requests it, so the
# flags reach the roots alone, and its ordering drops {post} edges as it
# does at install time.  A cycle is a verdict of its own: the selection is
# still a resolution, one opam cannot then install.
#
# The roots do not reach a package they do not need, so where they leave
# some out, every package is reinstalled as requested, and without the
# flags, which would otherwise reach every package.
cyclic() {
  grep -qE '^(The actions to process have cyclic dependencies:|\[ERROR\] Cycles found during dependency resolution)' "$@"
}
acts() { grep -c '^  - [a-z]* ' "$@" | awk -F: '{s+=$NF} END {print s+0}'; }
n=${#req[@]}
reinstall() {  # <log> <opam args...>: sets rlog, rrc and re
  rlog=$1; shift
  state ${roots[@]+"${roots[@]}"}
  printf '%s\n' "${req[@]/./ }" > "$r/cmp/.opam-switch/reinstall"
  opam reinstall --dry-run "${o[@]}" "$@" > "$rlog" 2>&1
  rrc=$?
  cyclic "$rlog" || ran $rrc "$rlog"
  re=$(grep -c '^  - recompile ' "$rlog")
}
reinstall "$out/reinstall" ${flags[@]+"${flags[@]}"} ${roots[@]+"${roots[@]}"}
: > "$out/reinstall-all"
if [ "$rrc" -eq 0 ] && [ "$re" -lt "$n" ]; then
  reinstall "$out/reinstall-all" ${req[@]+"${req[@]%%.*}"}
fi
rm -rf "$r"

ch=$(acts "$out/install" "$out/fixup")
un=$(acts "$out/prune")
rc=$((irc ? irc : frc))

# An answer that is no selection fails whatever opam made of it.  fixup
# prints "Nothing to do." only for an empty solution, and install of atoms
# already satisfied never reaches the solver.  The reinstall must reach
# all n packages, or a cycle among the rest would go unseen.
m=-
if [ "$n" -eq 0 ] || [ "$malformed" -ne 0 ] || [ "$dups" -ne 0 ] || [ "$absent" -ne 0 ]; then
  v=INVALID
elif [ "$err" -ne 0 ]; then
  v=ERR
elif [ "$rc" -eq 0 ] && [ "$ch" -eq 0 ] && grep -qx 'Nothing to do.' "$out/fixup" &&
   ! grep -q 'actions will be simulated' "$out/install"; then
  if cyclic "$out/reinstall" "$out/reinstall-all"; then
    v=CYCLIC
  elif [ "$rrc" -eq 0 ] && [ "$re" -eq "$n" ] && [ "$(acts "$rlog")" -eq "$n" ]; then
    v=VALID
    if [ "$arc" -eq 0 ] && [ "$un" -eq 0 ] && grep -qx 'Nothing to do.' "$out/prune"; then m=yes
    else case $arc in 0|20) m=no ;; *) v=ERR ;; esac; fi
  else
    v=INVALID
  fi
else
  v=INVALID
fi
printf '%-26s n=%-5s changes=%-4s unneeded=%-4s malformed=%-3s dups=%-3s absent=%-3s rc=%-3s valid=%s minimal=%s\n' \
  "$*" "$n" "$ch" "$un" "$malformed" "$dups" "$absent" "$rc" "$v" "$m"
