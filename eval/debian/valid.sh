#!/usr/bin/env bash
# Ask apt whether OUR Debian answer is a resolution by apt's own rules,
# rather than whether it is the one apt would have picked.  cmp.sh asks
# the second question; a goal can fail that and still pass this, which is
# the whole point: apt prefers one resolution among many, and preferring
# another is not an error.
#
# The check hands apt our whole set at exact versions --
# `apt-get -s install name=ver ...` -- and demands that the simulation
# succeed and its Inst lines be exactly our set.  apt is verifying, not
# re-resolving, because every member is pinned: the only freedom left is
# to add a package, which it takes only when some Depends of a requested
# package is unsatisfied by the rest of the request.  So an extra Inst
# means our set is not closed, a non-zero exit means it is inconsistent
# (a Conflicts/Breaks pair, or a version that does not exist), and no
# outcome can report success by quietly resolving to something else.
# Verified by three negative controls, see notes/validity.md.
#
# --no-install-recommends is what makes the primary verdict a validity
# question.  A Recommends is soft on both sides -- apt calls it optional
# and our solver's Soft clauses need not be satisfied -- so a set that
# omits one is still a resolution; with recommends left on, apt would
# add it and the extra Inst would be preference, not a closure failure.
# The recs= column re-runs the same request at apt's default to report
# how much the set misses by that softer standard, without failing it.
#
# APT names the binary when apt-get is not on PATH.  Requires the root
# setup.sh builds.
# usage: valid.sh <exe> <tag> [goal]       EXTRA=<flags> passes flags to <exe>
# With no goal it sweeps goals.txt and totals; with one it checks that one.
set -u
S="$(cd "$(dirname "$0")" && pwd)"
ROOT="${APTROOT:-/tmp/apt-cmp-root}"
APT="${APT:-apt-get}"
exe=$1; tag=$2

if [ $# -lt 3 ]; then
  mkdir -p "$S/out"
  xargs -P 8 -I{} bash "$0" "$exe" "$tag" {} < "$S/goals.txt" \
    > "$S/out/$tag.valid" 2>&1
  sort "$S/out/$tag.valid" -o "$S/out/$tag.valid"
  awk '/ unsat / {un++; next} / NO SOLUTION/ {bad++; next}
       {n++; if ($NF=="VALID") ok++; else print}
       END {printf "TOTAL valid=%d/%d unsat=%d nosol=%d\n", ok, n, un, bad}' \
    "$S/out/$tag.valid"
  exit 0
fi
goal=$3
read -r -a extra <<< "${EXTRA:-}"
out="$S/out/$tag"
mkdir -p "$out"
cd "$S/../.."

"$exe" debian ${extra[@]+"${extra[@]}"} --native amd64 "$goal" repos/debian/Packages \
  > "$out/$goal.vout" 2>&1
rc=$?
if [ "$rc" -ne 0 ] && head -n 1 "$out/$goal.vout" | grep -q '^unsatisfiable:'; then
  printf '%-18s %-7s unsat (no answer to verify)\n' "$goal" "$tag"
  exit 0
fi

# name=version, the form apt's install pins with, for every :amd64 row
sed -n 's/^\([^ :]*\):amd64 \(.*\)$/\1=\2/p' "$out/$goal.vout" | sort -u \
  > "$out/$goal.req"
if [ ! -s "$out/$goal.req" ]; then
  printf '%-18s %-7s NO SOLUTION (see %s)\n' "$goal" "$tag" "$out/$goal.vout"
  exit 1
fi
mapfile -t req < "$out/$goal.req"

export APT_CONFIG="$ROOT/etc/apt/apt.conf"
"$APT" -s install --no-install-recommends "${req[@]}" > "$out/$goal.apt" 2>&1
arc=$?
# "Inst name (ver repo [arch])", with name carrying :arch when not native
sed -n 's/^Inst \([^ :]*\)\(:[^ ]*\)\{0,1\} (\([^ ]*\) .*/\1=\3/p' "$out/$goal.apt" \
  | sort -u > "$out/$goal.inst"

n=$(wc -l < "$out/$goal.req")
comm -13 "$out/$goal.req" "$out/$goal.inst" > "$out/$goal.aptextra"
comm -23 "$out/$goal.req" "$out/$goal.inst" > "$out/$goal.notinst"
ex=$(wc -l < "$out/$goal.aptextra")
mi=$(wc -l < "$out/$goal.notinst")
rm=$(grep -c '^Remv ' "$out/$goal.apt")

# same request at apt's default, where Recommends are pulled in: reported,
# never failed on, because a Recommends binds neither solver
"$APT" -s install "${req[@]}" > "$out/$goal.aptrecs" 2>&1
sed -n 's/^Inst \([^ :]*\)\(:[^ ]*\)\{0,1\} (\([^ ]*\) .*/\1=\3/p' "$out/$goal.aptrecs" \
  | sort -u > "$out/$goal.instrecs"
re=$(comm -13 "$out/$goal.req" "$out/$goal.instrecs" | wc -l)

if [ "$arc" -eq 0 ] && [ "$ex" -eq 0 ] && [ "$mi" -eq 0 ] && [ "$rm" -eq 0 ]; then
  v=VALID
else
  v=INVALID
fi
printf '%-18s %-7s n=%-5s extra=%-4s missing=%-4s remv=%-3s rc=%-3s recs=%-4s %s\n' \
  "$goal" "$tag" "$n" "$ex" "$mi" "$rm" "$arc" "$re" "$v"
