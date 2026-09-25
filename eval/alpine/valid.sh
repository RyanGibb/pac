#!/usr/bin/env bash
# Our answer becomes the installed database, each package's stanza taken
# from the same APKINDEX the loader reads, and the world is the original
# query; `apk fix --simulate` must then succeed with nothing to do.  Making
# the answer itself the world would name every package in it, and apk
# lets a bare provides without k: satisfy a dependency only once some
# requirer names its owner -- a world naming the owner is such a
# requirer, so that query could never fail on it.
#
# apk keeps an installed package only while it still resolves from the
# world, so any Installing, Purging, Upgrading, Downgrading, Replacing or
# Re-installing line means apk would not keep the set as it stood (which
# a resolution can still fail: controls.sh f5-prio), and a non-zero exit
# is an inconsistency.  install_if is no exception: apk
# installs such a package as soon as its triggers are present, and our
# model makes the rule hard too; nor can an Installing line be excused by
# what the index says of the name, since the same name may be one a
# dependency needs.  The closing "OK: ... in K packages" must count
# exactly our set, so no change can pass unprinted.
#
# apk's changeset tracks one installed package per name, so two versions
# of one name both installed go unreported by fix; that is checked here.
#
# `fix` rejects --usermode, so each query gets its own copy of the root
# setup.sh built; the repository is shared.  APK names the binary when
# apk is not on PATH (setup.sh prints the invocation it resolved);
# INDEX overrides the index, for a scratch fixture.
# usage: valid.sh <exe> <tag> [query]        EXTRA=<flags> passes flags to <exe>
# With no query it sweeps queries.txt and totals; with one it checks that one.
set -u
# byte order, so the output is the same whatever the host's locale
export LC_ALL=C
S="$(cd "$(dirname "$0")" && pwd)"
ROOT="${APKROOT:-/tmp/apk-cmp-root}"
APK="${APK:-apk}"
exe=$1; tag=$2

if [ $# -lt 3 ]; then
  mkdir -p "$S/out"
  xargs -P 8 -I{} bash "$0" "$exe" "$tag" {} < "$S/queries.txt" \
    > "$S/out/$tag.valid" 2>&1
  sort "$S/out/$tag.valid" -o "$S/out/$tag.valid"
  awk '/ NO SOLUTION/ {bad++; next}
       {n++; if ($NF=="VALID") ok++; else print}
       END {printf "TOTAL valid=%d/%d nosol=%d\n", ok, n, bad}' "$S/out/$tag.valid"
  exit 0
fi
query=$3
# a world atom can be a path (/bin/sh), so the query is escaped as
# scale-lib.sh escapes its keys, which keeps distinct queries distinct files
key=${query//[%]/%25}; key=${key//[+]/%2B}; key=${key//\//%2F}; key=${key// /+}
out="$S/out/$tag"
mkdir -p "$out"
cd "$S/../.."
INDEX="${INDEX:-repos/alpine/APKINDEX}"

"$exe" alpine "$INDEX" $query ${EXTRA:-} > "$out/$key.vout" 2>&1
sed -n '/^packages (/,/^encoded solution/p' "$out/$key.vout" \
  | sed -n 's/^  \([^ ]*\) \([^ ]*\)$/\1=\2/p' | sort -u > "$out/$key.req"
if [ ! -s "$out/$key.req" ]; then
  printf '%-18s %-7s NO SOLUTION (see %s)\n' "$query" "$tag" "$out/$key.vout"
  exit 1
fi
n=$(wc -l < "$out/$key.req")
# the extraction above skips any line that is not a row, so such a line
# would leave apk judging fewer packages than the answer names
malformed=$(awk '/^encoded solution/ {exit} s && !/^  [^[:space:]]+ [^[:space:]]+$/
                 /^packages \(/ {s=1}' "$out/$key.vout" | wc -l)
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
printf '%s\n' $query > "$r/etc/apk/world"

"$APK" --root "$r" --allow-untrusted --no-network \
  --repository "$ROOT/repo" fix --simulate > "$out/$key.apk" 2>&1
arc=$?
rm -rf "$r"

ch=$(grep -c '^( *[0-9]*/[0-9]*) ' "$out/$key.apk")
kept=$(sed -n 's/^OK: .* in \([0-9]*\) packages$/\1/p' "$out/$key.apk")

if [ "$arc" -eq 0 ] && [ "$stanzas" -eq 0 ] && [ "$ch" -eq 0 ] &&
   [ "$dup" -eq 0 ] && [ "$malformed" -eq 0 ] && [ "${kept:-x}" = "$n" ]; then
  v=VALID
else
  v=INVALID
fi
printf '%-18s %-7s n=%-5s changes=%-4s kept=%-5s rc=%-3s dup=%-3s malformed=%-3s %s\n' \
  "$query" "$tag" "$n" "$ch" "${kept:-?}" "$arc" "$dup" "$malformed" "$v"
