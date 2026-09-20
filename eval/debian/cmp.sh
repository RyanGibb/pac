#!/usr/bin/env bash
# Compare a pac binary's Debian install set against apt-get -s install.
# Baselines were taken with apt 3.3.0 (nixpkgs); heap tie-breaking is
# version-sensitive, so regenerate them all or none.
# A goal apt has no candidate for is recorded as apt-<goal>.absent, so the
# empty baseline is not mistaken for one that was never taken; such a goal
# agrees when we call it unsatisfiable, and counts in neither install set.
# usage: cmp.sh <exe> <tag> <goal>          EXTRA=<flags> passes flags to <exe>
set -u
S="$(cd "$(dirname "$0")" && pwd)"
ROOT="${APTROOT:-/tmp/apt-cmp-root}"
APT="${APT:-apt-get}"
exe=$1; tag=$2; goal=$3
read -r -a extra <<< "${EXTRA:-}"
mkdir -p "$S/out/$tag"
cd "$S/../.."

"$exe" debian ${extra[@]+"${extra[@]}"} --native amd64 "$goal" repos/debian/Packages \
  > "$S/out/$tag/$goal.out" 2>&1
rc=$?
if [ "$rc" -ne 0 ] && head -n 1 "$S/out/$tag/$goal.out" | grep -q '^unsatisfiable:'; then
  unsat=1; : > "$S/out/$tag/$goal.ours"
else
  unsat=0
  grep ':amd64 ' "$S/out/$tag/$goal.out" | sed -e 's/:amd64 .*//' | sort -u \
    > "$S/out/$tag/$goal.ours"
fi

if [ ! -s "$S/apt-$goal.names" ] && [ ! -e "$S/apt-$goal.absent" ]; then
  aptout=$(APT_CONFIG="$ROOT/etc/apt/apt.conf" "$APT" -s install "$goal" 2>&1)
  printf '%s\n' "$aptout" | grep '^Inst ' | awk '{print $2}' | sort -u \
    > "$S/apt-$goal.names"
  if [ ! -s "$S/apt-$goal.names" ] && printf '%s\n' "$aptout" \
       | grep -q "^E: \(Unable to locate package\|Package '.*' has no installation candidate\)"; then
    : > "$S/apt-$goal.absent"
  fi
fi

if [ -e "$S/apt-$goal.absent" ] && [ "$unsat" -eq 1 ]; then
  printf '%-18s %-7s absent (apt: no candidate, ours: unsatisfiable)\n' "$goal" "$tag"
  exit 0
fi

ours=$(wc -l < "$S/out/$tag/$goal.ours")
apt=$(wc -l < "$S/apt-$goal.names")
agree=$(comm -12 "$S/out/$tag/$goal.ours" "$S/apt-$goal.names" | wc -l)
comm -23 "$S/out/$tag/$goal.ours" "$S/apt-$goal.names" > "$S/out/$tag/$goal.oursonly"
comm -13 "$S/out/$tag/$goal.ours" "$S/apt-$goal.names" > "$S/out/$tag/$goal.aptonly"
oo=$(wc -l < "$S/out/$tag/$goal.oursonly")
ao=$(wc -l < "$S/out/$tag/$goal.aptonly")
printf '%-18s %-7s ours=%-5s apt=%-5s agree=%-5s ours-only=%-5s apt-only=%-5s\n' \
  "$goal" "$tag" "$ours" "$apt" "$agree" "$oo" "$ao"
