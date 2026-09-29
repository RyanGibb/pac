#!/usr/bin/env bash
# Our answer becomes the dpkg status, each package's stanza taken from the
# same Packages file the loader reads and marked installed, and
# extended_states marks every package but the query's automatically
# installed.  Valid asks two questions that must have nothing to do:
# `apt-get check`, that no installed package has a Depends, Pre-Depends,
# Conflicts or Breaks unmet; and `apt-get install <query>`, that the query
# as asked is satisfied.  Minimal asks a third, `apt-get autoremove`: that
# the query needs everything installed.
#
# What autoremove counts as needed has to be what installing the query
# installs: Recommends exactly when they were installed -- apt's default,
# which --no-install-recommends turns off -- and Suggests never.  apt's
# own default for autoremove follows Suggests too, which would pass a
# package only a Suggests reaches.
#
# A dpkg status holds one version of a package, and apt reads the last
# stanza of a name and architecture as installed, silently; the status
# holds rows only at the architectures the root's APT::Architectures
# names, amd64 native.  So a name at two versions of one architecture, or
# a row at any other architecture, fails before apt is asked.  A
# Multi-Arch: same name at two architectures and two versions is apt's to
# refuse: it gives each such version an implicit Breaks on the others.
#
# The recs= column reports, and never fails on, the Recommends the answer
# leaves out: the whole answer asked for fresh at apt's default.  Naming
# every package asks the same question as naming the query here, since apt
# follows the Recommends of every package it installs, requested or not.
#
# apt exits 100 for an inconsistency and for a broken environment alike,
# so an exit is read as an inconsistency only beside one of the errors apt
# gives for one (refusals, the errors scale.sh reads as apt refusing a
# query); any other failure leaves the answer unchecked (ERR).
#
# APTROOT is the root setup.sh builds, whose lists each answer's own
# status is read beside; APT names the binary when apt-get is not on PATH;
# INDEX overrides the index, for a fixture, and must hold what that root
# holds: with a foreign architecture, its Packages after the native one,
# whose Architecture: all stanzas it repeats, which count once.
# usage: check.sh <answer> <out-dir> <query...>, through eval/check.sh
set -u
# byte order, so the output is the same whatever the host's locale
export LC_ALL=C
S="$(cd "$(dirname "$0")" && pwd)"
. "$S/refused.sh"
ROOT=${APTROOT:?}
APT="${APT:-apt-get}"
INDEX="${INDEX:-$S/../../repos/debian/Packages}"
ans=$1 out=$2; shift 2
[ -r "$INDEX" ] || { echo "no index $INDEX valid=ERR minimal=-"; exit 0; }

atoms=(); recs=true
for a; do
  case $a in
    --no-install-recommends) recs=false ;;
    -*) ;;
    *) atoms+=("$a") ;;
  esac
done

err=0
ran() {  # <rc> <log>: whether apt ran to an answer, a refusal included
  [ "$1" -eq 0 ] || refused "$1" "$2" || err=1
}
# a root with no lists has apt locate nothing, which reads as a refusal
ls "$ROOT"/var/lib/apt/lists/*Packages > /dev/null 2>&1 || err=1
# the root's architectures, amd64 native and first
archs=$(sed -n 's/^APT::Architectures { \(.*\) };$/\1/p' "$ROOT/etc/apt/apt.conf" 2> /dev/null | tr -d '";')
archs=${archs:-amd64}

# name[:arch]=version, the form apt's install pins with, the native
# architecture left out as apt leaves it out, for every row at one of them
rows "$ans" | awk -v as="$archs" 'BEGIN {split(as, a, " "); for (i in a) ok[a[i]]}
  NF == 2 && split($1, n, ":") == 2 && n[2] in ok {print (n[2] == "amd64" ? n[1] : $1) "=" $2}' |
  sort -u > "$out/req"
mapfile -t req < "$out/req"
n=${#req[@]}
dups=$(cut -d= -f1 "$out/req" | sort | uniq -d | wc -l)
foreign=$(rows "$ans" | awk -v as="$archs" 'BEGIN {split(as, a, " "); for (i in a) ok[a[i]]}
  NF == 2 && $1 ~ /:/ && !(substr($1, index($1, ":") + 1) in ok)' | wc -l)
# the extraction above skips any line that is not a row, so such a line
# would leave apt judging fewer packages than the answer names
malformed=$(rows "$ans" | awk '!/^[^[:space:]:]+:[^[:space:]:]+ [^[:space:]]+$/' | wc -l)
whole "$ans" || malformed=$((malformed + 1))

r="$out/root"
rm -rf "$r"
mkdir -p "$r/etc/apt.conf.d" "$r/etc/preferences.d"
cp "$ROOT/etc/apt/sources.list" "$r/etc/" || err=1
cat > "$r/etc/apt.conf" <<EOF
Dir "$r";
Dir::State "$ROOT/var/lib/apt";
Dir::State::status "$r/status";
Dir::State::extended_states "$r/extended_states";
Dir::Cache "$r/cache";
Dir::Cache::pkgcache "";
Dir::Cache::srcpkgcache "";
Dir::Etc "$r/etc";
APT::Architecture "amd64";
APT::Architectures { $(printf '"%s"; ' $archs)};
Acquire::Languages "none";
APT::Install-Recommends "$recs";
APT::AutoRemove::RecommendsImportant "$recs";
APT::AutoRemove::SuggestsImportant "false";
EOF
awk 'NR==FNR {want[$0]=1; nw++; next}
     {p=""; v=""; a=""; k=split($0, ls, "\n")
      for (i=1; i<=k; i++) {
        if (ls[i] ~ /^Package: /) p=substr(ls[i], 10)
        if (ls[i] ~ /^Version: /) v=substr(ls[i], 10)
        if (ls[i] ~ /^Architecture: /) a=substr(ls[i], 15)
      }
      k=(a == "amd64" || a == "all" ? p : p ":" a) "=" v
      if (k in want && !(k in seen)) {
        seen[k]; sub(/\n/, "\nStatus: install ok installed\n"); print $0 "\n"; got++
      }}
     END {if (got != nw) exit 1}' \
  "$out/req" RS= "$INDEX" > "$r/status"
stanzas=$?
# the rows name native packages bare, and an atom qualified with the
# native architecture, or pinned to a version, names the same package; an
# unqualified one names another architecture's where the answer holds no
# native package of that name, as apt's FindPreferredPkg takes the first
# architecture with a version
names=" $(cut -d= -f1 "$out/req" | tr '\n' ' ')"
for p in "${req[@]}"; do
  asked=
  for a in "${atoms[@]}"; do
    a=${a%%[=/]*} a=${a%:amd64}
    case $a in
      *:*) ;;
      *) if [[ $names != *" $a "* ]]; then
           for b in $archs; do [[ $names == *" $a:$b "* ]] && { a=$a:$b; break; }; done
         fi ;;
    esac
    [ "${p%%=*}" = "$a" ] && asked=1
  done
  k=${p%%=*}
  case $k in *:*) b=${k#*:} ;; *) b=amd64 ;; esac
  [ -n "$asked" ] || printf 'Package: %s\nArchitecture: %s\nAuto-Installed: 1\n\n' "${k%%:*}" "$b"
done > "$r/extended_states"

export APT_CONFIG="$r/etc/apt.conf"
"$APT" -s check > "$out/check" 2>&1
crc=$?; ran $crc "$out/check"
"$APT" -s install "${atoms[@]}" > "$out/install" 2>&1
irc=$?; ran $irc "$out/install"
# autoremove roots every Essential, Protected and Priority: required
# package, and apt itself whatever its stanza says, so it is asked over
# the status alone, those fields removed and apt's forced Essential
# turned off: then the query is the only root
mkdir -p "$r/bare/lists/partial" "$r/bare/etc/apt.conf.d" "$r/bare/etc/preferences.d"
: > "$r/bare/etc/sources.list"
awk -v RS= '{gsub(/(^|\n)(Essential|Protected|Important|Priority):[^\n]*/, ""); print $0 "\n"}' \
  "$r/status" > "$r/bare/status"
sed -e "s|^Dir::State::status .*|Dir::State::status \"$r/bare/status\";|" \
    -e "s|^Dir::Etc .*|Dir::Etc \"$r/bare/etc\";|" "$r/etc/apt.conf" > "$r/bare/apt.conf"
printf 'Dir::State::Lists "%s";\npkgCacheGen::ForceEssential "pac-none";\n' \
  "$r/bare/lists" >> "$r/bare/apt.conf"
APT_CONFIG="$r/bare/apt.conf" "$APT" -s autoremove > "$out/autoremove" 2>&1
arc=$?
rm -rf "$r"

ch=$(grep -c '^\(Inst\|Remv\|Conf\|Purg\) ' "$out/install")
un=$(grep -c '^Remv ' "$out/autoremove")
none='0 upgraded, 0 newly installed, 0 to remove and 0 not upgraded.'

export APT_CONFIG="$ROOT/etc/apt/apt.conf"
"$APT" -s install "${req[@]}" > "$out/aptrecs" 2>&1
sed -n 's/^Inst \([^ ]*\) (\([^ ]*\) .*/\1=\2/p' "$out/aptrecs" | sed 's/:amd64=/=/' \
  | sort -u > "$out/instrecs"
re=$(comm -13 "$out/req" "$out/instrecs" | wc -l)
# the installed state skips the one question installing asks: whether
# dpkg can be walked through the set in some order.  A Pre-Depends cycle
# is consistent installed and cannot be installed, and apt says so only
# while ordering an install, so the whole answer is installed fresh, as
# asked, with nothing added
"$APT" -s -o APT::Install-Recommends=false install "${req[@]}" > "$out/order" 2>&1
orc=$?; ran $orc "$out/order"

rc=$((crc ? crc : irc))
# an answer that is no selection fails whatever apt made of it
m=-
if [ "$n" -eq 0 ] || [ "$stanzas" -ne 0 ] || [ "$dups" -ne 0 ] || [ "$foreign" -ne 0 ] ||
   [ "$malformed" -ne 0 ]; then
  v=INVALID
elif [ "$err" -ne 0 ]; then
  v=ERR
elif [ "$rc" -eq 0 ] && [ "$ch" -eq 0 ] && grep -qxF "$none" "$out/install"; then
  if grep -q 'probably a dependency cycle' "$out/order"; then
    v=CYCLIC
  elif [ "$orc" -eq 0 ]; then
    v=VALID
    # a consistent state autoremove fails on is not one it can settle
    if [ "$arc" -eq 0 ] && [ "$un" -eq 0 ] && grep -qxF "$none" "$out/autoremove"; then m=yes
    elif [ "$arc" -eq 0 ]; then m=no
    else v=ERR; fi
  else
    v=INVALID
  fi
else
  v=INVALID
fi
printf '%-18s n=%-5s changes=%-4s unneeded=%-4s dups=%-3s foreign=%-3s malformed=%-3s rc=%-3s order=%-3s recs=%-4s valid=%s minimal=%s\n' \
  "${atoms[*]}" "$n" "$ch" "$un" "$dups" "$foreign" "$malformed" "$rc" "$orc" "$re" "$v" "$m"
