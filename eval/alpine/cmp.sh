#!/usr/bin/env bash
# Compare a pac binary's Alpine install set against apk add --simulate.
# Baselines were taken with apk-tools 3.0.5 (nixpkgs); regenerate them all
# or none.  APK names the binary when apk is not on PATH (setup.sh prints
# the invocation it resolved).
# EXTRA adds names to our world only, so a divergence can be re-run with
# apk's provider pick forced: if the sets then coincide, apk's answer was
# one our instance already admitted and only our preference ordering
# differed.
# usage: cmp.sh <exe> <tag> <goal>
set -u
# comm expects its inputs in its own collation, and the baselines are in byte order
export LC_ALL=C
S="$(cd "$(dirname "$0")" && pwd)"
ROOT="${APKROOT:-/tmp/apk-cmp-root}"
APK="${APK:-apk}"
exe=$1; tag=$2; goal=$3
mkdir -p "$S/out/$tag"
cd "$S/../.."

"$exe" alpine repos/alpine/APKINDEX "$goal" ${EXTRA:-} > "$S/out/$tag/$goal.out" 2>&1
sed -n '/^packages (/,/^encoded solution/p' "$S/out/$tag/$goal.out" \
  | sed -n 's/^  \([^ ]*\) .*/\1/p' | sort -u > "$S/out/$tag/$goal.ours"

if [ ! -s "$S/apk-$goal.names" ]; then
  "$APK" add --root "$ROOT/root" --usermode --allow-untrusted --no-network \
    --repository "$ROOT/repo" --simulate "$goal" 2>"$S/out/$tag/$goal.apkerr" \
    | sed -n 's/^( *[0-9]*\/[0-9]*) Installing \([^ ]*\) .*/\1/p' \
    | sort -u > "$S/apk-$goal.names"
fi
# Every goal installs at least itself, so an empty answer is apk failing,
# typically for want of the root setup.sh builds, which it cannot as root;
# kept as a baseline it would score as a total divergence, not an error.
if [ ! -s "$S/apk-$goal.names" ]; then
  rm -f "$S/apk-$goal.names"
  printf '%-18s %-7s NO BASELINE (apk: %s)\n' "$goal" "$tag" \
    "$(head -n 1 "$S/out/$tag/$goal.apkerr" 2>/dev/null)"
  exit 1
fi

ours=$(wc -l < "$S/out/$tag/$goal.ours")
apk=$(wc -l < "$S/apk-$goal.names")
agree=$(comm -12 "$S/out/$tag/$goal.ours" "$S/apk-$goal.names" | wc -l)
comm -23 "$S/out/$tag/$goal.ours" "$S/apk-$goal.names" > "$S/out/$tag/$goal.oursonly"
comm -13 "$S/out/$tag/$goal.ours" "$S/apk-$goal.names" > "$S/out/$tag/$goal.apkonly"
oo=$(wc -l < "$S/out/$tag/$goal.oursonly")
ao=$(wc -l < "$S/out/$tag/$goal.apkonly")
printf '%-18s %-7s ours=%-5s apk=%-5s agree=%-5s ours-only=%-5s apk-only=%-5s\n' \
  "$goal" "$tag" "$ours" "$apk" "$agree" "$oo" "$ao"
