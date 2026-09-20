#!/usr/bin/env bash
# Ask apk whether OUR Alpine answer is a resolution by apk's own rules,
# rather than whether it is the one apk would have picked.  cmp.sh asks
# the second question; this one can pass where that fails, because apk
# preferring a different provider is preference, not error.
#
# The check makes our whole set the world, at exact versions --
# `apk add --simulate name=version ...` against the empty root setup.sh
# built -- and demands that apk succeed and report installing exactly our
# set.  apk is verifying, not re-resolving: each `name=version` is an
# equality constraint in world, so the solver has no version left to
# choose; it can only add a package whose absence leaves some dependency
# of the world unsatisfied, or refuse.  An extra Installing line is
# therefore a closure failure and a non-zero exit is an inconsistency
# (a conflicts:/breaks: pair, or a version no row provides).  Verified by
# three negative controls, see notes/validity.md.
#
# The one soft rule is install_if: apk installs such a package on its own
# once its triggers are present, the way apt pulls a Recommends, so an
# extra that is install_if-triggered is reported in its own column and
# does not fail the set.
#
# APK names the binary when apk is not on PATH (setup.sh prints the
# invocation it resolved).  Requires the root setup.sh builds.
# usage: valid.sh <exe> <tag> [goal]        EXTRA=<flags> passes flags to <exe>
# With no goal it sweeps goals.txt and totals; with one it checks that one.
set -u
S="$(cd "$(dirname "$0")" && pwd)"
ROOT="${APKROOT:-/tmp/apk-cmp-root}"
APK="${APK:-apk}"
exe=$1; tag=$2

if [ $# -lt 3 ]; then
  mkdir -p "$S/out"
  xargs -P 8 -I{} bash "$0" "$exe" "$tag" {} < "$S/goals.txt" \
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

"$exe" alpine repos/alpine/APKINDEX "$goal" ${EXTRA:-} > "$out/$goal.vout" 2>&1
sed -n '/^packages (/,/^encoded solution/p' "$out/$goal.vout" \
  | sed -n 's/^  \([^ ]*\) \([^ ]*\)$/\1=\2/p' | sort -u > "$out/$goal.req"
if [ ! -s "$out/$goal.req" ]; then
  printf '%-18s %-7s NO SOLUTION (see %s)\n' "$goal" "$tag" "$out/$goal.vout"
  exit 1
fi
mapfile -t req < "$out/$goal.req"

"$APK" add --root "$ROOT/root" --usermode --allow-untrusted --no-network \
  --repository "$ROOT/repo" --simulate "${req[@]}" > "$out/$goal.apk" 2>&1
arc=$?
sed -n 's/^( *[0-9]*\/[0-9]*) Installing \([^ ]*\) (\([^)]*\))$/\1=\2/p' \
  "$out/$goal.apk" | sort -u > "$out/$goal.inst"

n=$(wc -l < "$out/$goal.req")
comm -13 "$out/$goal.req" "$out/$goal.inst" > "$out/$goal.apkextra"
comm -23 "$out/$goal.req" "$out/$goal.inst" > "$out/$goal.notinst"
mi=$(wc -l < "$out/$goal.notinst")

# an extra apk brought in on its own initiative rather than to close a
# dependency: i: in the index is the install_if trigger list
ii=0; hard=0
while IFS= read -r e; do
  [ -n "$e" ] || continue
  if awk -F: -v p="${e%%=*}" '$1=="P"&&$2==p{f=1;next} $1=="P"{f=0}
       f&&$1=="i"{found=1} END{exit !found}' repos/alpine/APKINDEX; then
    ii=$((ii+1))
  else
    hard=$((hard+1))
  fi
done < "$out/$goal.apkextra"

if [ "$arc" -eq 0 ] && [ "$hard" -eq 0 ] && [ "$mi" -eq 0 ]; then
  v=VALID
else
  v=INVALID
fi
printf '%-18s %-7s n=%-5s extra=%-4s missing=%-4s rc=%-3s install-if=%-4s %s\n' \
  "$goal" "$tag" "$n" "$hard" "$mi" "$arc" "$ii" "$v"
