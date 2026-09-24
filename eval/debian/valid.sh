#!/usr/bin/env bash
# Ask apt whether OUR Debian answer is a resolution by apt's own rules,
# rather than whether it is the one apt would have picked.  scale.sh asks
# the second question; a goal can fail that and still pass this, which is
# the whole point: apt prefers one resolution among many, and preferring
# another is not an error.
#
# Our answer becomes the dpkg status, each package's stanza taken from the
# same Packages file the loader reads and marked installed, and
# extended_states marks every package but the goal automatically
# installed.  Three questions must then have nothing to do: `apt-get
# check`, that no installed package has a Depends, Pre-Depends, Conflicts
# or Breaks unmet; `apt-get install <goal>`, that the goal as asked is
# satisfied; and `apt-get autoremove`, that the goal needs everything
# installed.  Asking instead for the whole answer at exact versions makes
# every package one the user asked for, so none of them could ever be
# found unneeded.
#
# What autoremove counts as needed has to be what installing the goal
# installs: Recommends exactly when they were installed -- apt's default,
# which --no-install-recommends turns off -- and Suggests never.  apt's
# own default for autoremove follows Suggests too, which would pass a
# package only a Suggests reaches.  apt never counts an Essential,
# Protected or Priority: required package as unneeded, so an unneeded one
# of those passes, with whatever only it needs.
#
# The recs= column reports, and never fails on, the Recommends the answer
# leaves out: the whole answer asked for fresh at apt's default.  Naming
# every package asks the same question as naming the goal here, since apt
# follows the Recommends of every package it installs, requested or not.
#
# APT names the binary when apt-get is not on PATH.  Each goal gets its
# own status beside the lists of the root setup.sh builds.
# usage: valid.sh <exe> <tag> [goal]       EXTRA=<flags> passes flags to <exe>
# With no goal it sweeps goals.txt and totals; with one it checks that one.
set -u
# byte order, so the output is the same whatever the host's locale
export LC_ALL=C
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
INDEX=repos/debian/Packages

"$exe" debian ${extra[@]+"${extra[@]}"} --native amd64 "$goal" "$INDEX" \
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
n=${#req[@]}

recs=true
for a in ${extra[@]+"${extra[@]}"}; do
  [ "$a" = --no-install-recommends ] && recs=false
done

r="$out/$goal.root"
rm -rf "$r"
mkdir -p "$r/etc/apt.conf.d" "$r/etc/preferences.d"
cp "$ROOT/etc/apt/sources.list" "$r/etc/"
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
APT::Architectures { "amd64"; };
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
      if ((p "=" v) in want && (a == "amd64" || a == "all")) {
        sub(/\n/, "\nStatus: install ok installed\n"); print $0 "\n"; got++
      }}
     END {if (got != nw) exit 1}' \
  "$out/$goal.req" RS= "$INDEX" > "$r/status"
stanzas=$?
# the rows name packages bare, and a goal qualified with the native
# architecture names the same package
for p in "${req[@]}"; do
  [ "${p%%=*}" = "${goal%:amd64}" ] ||
    printf 'Package: %s\nArchitecture: amd64\nAuto-Installed: 1\n\n' "${p%%=*}"
done > "$r/extended_states"

export APT_CONFIG="$r/etc/apt.conf"
"$APT" -s check > "$out/$goal.check" 2>&1
crc=$?
"$APT" -s install "$goal" > "$out/$goal.install" 2>&1
irc=$?
"$APT" -s autoremove > "$out/$goal.autoremove" 2>&1
arc=$?
rm -rf "$r"

ch=$(grep -c '^\(Inst\|Remv\|Conf\|Purg\) ' "$out/$goal.install")
un=$(grep -c '^Remv ' "$out/$goal.autoremove")
none='0 upgraded, 0 newly installed, 0 to remove and 0 not upgraded.'

# the whole answer asked for fresh from the empty root, at apt's default
export APT_CONFIG="$ROOT/etc/apt/apt.conf"
"$APT" -s install "${req[@]}" > "$out/$goal.aptrecs" 2>&1
sed -n 's/^Inst \([^ :]*\)\(:[^ ]*\)\{0,1\} (\([^ ]*\) .*/\1=\3/p' "$out/$goal.aptrecs" \
  | sort -u > "$out/$goal.instrecs"
re=$(comm -13 "$out/$goal.req" "$out/$goal.instrecs" | wc -l)

rc=$((crc ? crc : irc ? irc : arc))
if [ "$rc" -eq 0 ] && [ "$stanzas" -eq 0 ] && [ "$ch" -eq 0 ] && [ "$un" -eq 0 ] &&
   grep -qxF "$none" "$out/$goal.install" &&
   grep -qxF "$none" "$out/$goal.autoremove"; then
  v=VALID
else
  v=INVALID
fi
printf '%-18s %-7s n=%-5s changes=%-4s unneeded=%-4s rc=%-3s recs=%-4s %s\n' \
  "$goal" "$tag" "$n" "$ch" "$un" "$rc" "$re" "$v"
