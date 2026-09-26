#!/usr/bin/env bash
# Our answer becomes the installed database, each package's stanza taken
# from the same APKINDEX the loader reads, and `apk fix --simulate` must
# then succeed with nothing to do, twice over.
#
# Valid: the world is the whole answer, each package pinned at its version,
# and the query.  apk then keeps every package we named and can only report
# an inconsistency: a dependency missing, a conflict, an install_if whose
# conditions hold and whose package is absent (apk installs it as soon as
# they hold, and our model makes the rule hard too).  Naming every package
# also names every owner of a bare provides, which apk lets count only once
# something names it, so bare.py asks that rule of the answer itself.
#
# Minimal: the world is the query alone.  apk keeps an installed package
# only while it still resolves from the world, and takes a name's provider
# by its own preference, so it purges what nothing leads to and swaps a
# provider it ranks lower (controls.sh f5-prio); neither is an
# inconsistency.
#
# Any Installing, Purging, Upgrading, Downgrading, Replacing or
# Re-installing line is a change; the closing "OK: ... in K packages" must
# count exactly our set, so no change can pass unprinted.  apk's changeset
# tracks one installed package per name, so two versions of one name both
# installed go unreported by fix; that is checked here.  apk failing other
# than by being unable to select packages leaves the answer unchecked.
#
# `fix` rejects --usermode, so each answer gets its own copy of the root
# setup.sh built; the repository is shared.  APKROOT is that root; APK
# names the binary when apk is not on PATH (setup.sh prints the invocation
# it resolved); INDEX overrides the index, for a fixture.
# usage: check.sh <answer> <out-dir> <query...>, through eval/check.sh
set -u
# byte order, so the output is the same whatever the host's locale
export LC_ALL=C
S="$(cd "$(dirname "$0")" && pwd)"
. "$S/refused.sh"
ROOT=${APKROOT:?}
APK="${APK:-apk}"
INDEX="${INDEX:-$S/../../repos/alpine/APKINDEX}"
ans=$1 out=$2; shift 2
[ -r "$INDEX" ] || { echo "no index $INDEX valid=ERR minimal=-"; exit 0; }

rows "$ans" | sed -n 's/^\([^ ]*\) \([^ ]*\)$/\1=\2/p' | sort -u > "$out/req"
n=$(wc -l < "$out/req")
# the extraction above skips any line that is not a row, so such a line
# would leave apk judging fewer packages than the answer names
malformed=$(rows "$ans" | awk '!/^[^[:space:]]+ [^[:space:]]+$/' | wc -l)
whole "$ans" || malformed=$((malformed + 1))
dup=$(sed 's/=.*//' "$out/req" | sort | uniq -d | wc -l)
python3 "$S/bare.py" "$INDEX" "$out/req" "$@" > "$out/bare" 2>&1
brc=$?

awk 'NR==FNR {want[$0]=1; nw++; next}
     {p=""; v=""; k=split($0, ls, "\n")
      for (i=1; i<=k; i++) {
        if (ls[i] ~ /^P:/) p=substr(ls[i], 3)
        if (ls[i] ~ /^V:/) v=substr(ls[i], 3)
      }
      if ((p "=" v) in want) {print $0 "\n"; got++}}
     END {if (got != nw) exit 1}' \
  "$out/req" RS= "$INDEX" > "$out/installed"
stanzas=$?

err=0
case $brc in 0|3) ;; *) err=1 ;; esac
fix() {  # <name> <world...>: sets ch, kept and fixrc
  local r=$out/root.$1 name=$1; shift
  ch=0 kept= fixrc=1
  rm -rf "$r"
  cp -r "$ROOT/root" "$r" && cp "$out/installed" "$r/lib/apk/db/installed" || { err=1; return; }
  printf '%s\n' "$@" | awk '!seen[$0]++' > "$r/etc/apk/world"
  "$APK" --root "$r" --allow-untrusted --no-network \
    --repository "$ROOT/repo" fix --simulate > "$out/$name" 2>&1
  fixrc=$?
  rm -rf "$r"
  [ "$fixrc" -eq 0 ] || refused "$fixrc" "$out/$name" || err=1
  ch=$(grep -c '^( *[0-9]*/[0-9]*) ' "$out/$name")
  kept=$(sed -n 's/^OK: .* in \([0-9]*\) packages$/\1/p' "$out/$name")
}

mapfile -t pinned < "$out/req"
fix fix-answer ${pinned[@]+"${pinned[@]}"} "$@"
vch=$ch vkept=$kept vrc=$fixrc
# an answer that is no selection fails whatever apk made of it
m=-
if [ "$n" -eq 0 ] || [ "$stanzas" -ne 0 ] || [ "$dup" -ne 0 ] || [ "$malformed" -ne 0 ] ||
   [ "$brc" -eq 3 ]; then
  v=INVALID
elif [ "$err" -ne 0 ]; then
  v=ERR
elif [ "$vrc" -eq 0 ] && [ "$vch" -eq 0 ] && [ "${vkept:-x}" = "$n" ]; then
  v=VALID
  fix fix-query "$@"
  if [ "$err" -ne 0 ]; then v=ERR
  elif [ "$fixrc" -eq 0 ] && [ "$ch" -eq 0 ] && [ "${kept:-x}" = "$n" ]; then m=yes
  else m=no; fi
else
  v=INVALID
fi
printf '%-18s n=%-5s changes=%-4s kept=%-5s rc=%-3s dup=%-3s malformed=%-3s bare=%-3s valid=%s minimal=%s\n' \
  "$*" "$n" "$vch" "${vkept:-?}" "$vrc" "$dup" "$malformed" "$brc" "$v" "$m"
