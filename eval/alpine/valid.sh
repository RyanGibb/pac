#!/usr/bin/env bash
# Ask apk whether OUR Alpine answer is a resolution by apk's own rules,
# rather than whether it is the one apk would have picked.  scale.sh asks
# the second question; this one can pass where that fails, because apk
# preferring a different provider is preference, not error.
#
# Our answer becomes the installed database, each package's stanza taken
# from the same APKINDEX the loader reads, and the world is the original
# goal; `apk fix --simulate` must then succeed with nothing to do.  Making
# the answer itself the world would name every package in it, and apk
# lets a bare provides without k: satisfy a dependency only once some
# requirer names its owner -- a world naming the owner is such a
# requirer, so that query could never fail on it.
#
# apk keeps an installed package only while it still resolves from the
# world, so any Installing, Purging, Upgrading, Downgrading, Replacing or
# Re-installing line means the set was not a resolution as it stood, and
# a non-zero exit is an inconsistency.  install_if is no exception: apk
# installs such a package as soon as its triggers are present, and our
# model makes the rule hard too; nor can an Installing line be excused by
# what the index says of the name, since the same name may be one a
# dependency needs.  The closing "OK: ... in K packages" must count
# exactly our set, so no change can pass unprinted.
#
# apk's changeset tracks one installed package per name, so two versions
# of one name both installed go unreported by fix; that is checked here.
#
# `fix` rejects --usermode, so each goal gets its own copy of the root
# setup.sh built; the repository is shared.  APK names the binary when
# apk is not on PATH (setup.sh prints the invocation it resolved);
# INDEX overrides the index, for a scratch fixture.
# usage: valid.sh <exe> <tag> [goal]        EXTRA=<flags> passes flags to <exe>
# With no goal it sweeps goals.txt and totals; with one it checks that one.
set -u
# byte order, so the output is the same whatever the host's locale
export LC_ALL=C
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
# a world atom can be a path (/bin/sh), so the goal is escaped as
# scale-lib.sh escapes its keys, which keeps distinct goals distinct files
key=${goal//[%]/%25}; key=${key//[+]/%2B}; key=${key//\//%2F}; key=${key// /+}
out="$S/out/$tag"
mkdir -p "$out"
cd "$S/../.."
INDEX="${INDEX:-repos/alpine/APKINDEX}"

"$exe" alpine "$INDEX" $goal ${EXTRA:-} > "$out/$key.vout" 2>&1
sed -n '/^packages (/,/^encoded solution/p' "$out/$key.vout" \
  | sed -n 's/^  \([^ ]*\) \([^ ]*\)$/\1=\2/p' | sort -u > "$out/$key.req"
if [ ! -s "$out/$key.req" ]; then
  printf '%-18s %-7s NO SOLUTION (see %s)\n' "$goal" "$tag" "$out/$key.vout"
  exit 1
fi
n=$(wc -l < "$out/$key.req")
dup=$(sed 's/=.*//' "$out/$key.req" | sort | uniq -d | wc -l)

r="$out/$key.root"
rm -rf "$r"
cp -r "$ROOT/root" "$r"
awk 'NR==FNR {want[$0]=1; nw++; next}
     {p=""; v=""; k=split($0, ls, "\n")
      for (i=1; i<=k; i++) {
        if (ls[i] ~ /^P:/) p=substr(ls[i], 3)
        if (ls[i] ~ /^V:/) v=substr(ls[i], 3)
      }
      if ((p "=" v) in want) {print $0 "\n"; got++}}
     END {if (got != nw) exit 1}' \
  "$out/$key.req" RS= "$INDEX" > "$r/lib/apk/db/installed"
stanzas=$?
printf '%s\n' $goal > "$r/etc/apk/world"

"$APK" --root "$r" --allow-untrusted --no-network \
  --repository "$ROOT/repo" fix --simulate > "$out/$key.apk" 2>&1
arc=$?
rm -rf "$r"

ch=$(grep -c '^( *[0-9]*/[0-9]*) ' "$out/$key.apk")
kept=$(sed -n 's/^OK: .* in \([0-9]*\) packages$/\1/p' "$out/$key.apk")

if [ "$arc" -eq 0 ] && [ "$stanzas" -eq 0 ] && [ "$ch" -eq 0 ] &&
   [ "$dup" -eq 0 ] && [ "${kept:-x}" = "$n" ]; then
  v=VALID
else
  v=INVALID
fi
printf '%-18s %-7s n=%-5s changes=%-4s kept=%-5s rc=%-3s dup=%-3s %s\n' \
  "$goal" "$tag" "$n" "$ch" "${kept:-?}" "$arc" "$dup" "$v"
