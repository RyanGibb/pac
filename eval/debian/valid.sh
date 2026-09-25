#!/usr/bin/env bash
# Our answer becomes the dpkg status, each package's stanza taken from the
# same Packages file the loader reads and marked installed, and
# extended_states marks every package but the query automatically
# installed.  Three questions must then have nothing to do: `apt-get
# check`, that no installed package has a Depends, Pre-Depends, Conflicts
# or Breaks unmet; `apt-get install <query>`, that the query as asked is
# satisfied; and `apt-get autoremove`, that the query needs everything
# installed.
#
# What autoremove counts as needed has to be what installing the query
# installs: Recommends exactly when they were installed -- apt's default,
# which --no-install-recommends turns off -- and Suggests never.  apt's
# own default for autoremove follows Suggests too, which would pass a
# package only a Suggests reaches.
#
# A dpkg status holds one version of a package, and apt reads the last
# stanza of a name as installed, silently; the status holds amd64 rows
# only.  So a name at two versions, or a row at any other architecture,
# fails before apt is asked.
#
# The recs= column reports, and never fails on, the Recommends the answer
# leaves out: the whole answer asked for fresh at apt's default.  Naming
# every package asks the same question as naming the query here, since apt
# follows the Recommends of every package it installs, requested or not.
#
# APT names the binary when apt-get is not on PATH.  Each query gets its
# own status beside the lists of the root setup.sh builds.  INDEX
# overrides the index, for a fixture, and must be the one that root holds.
# usage: valid.sh <exe> <tag> [query]       EXTRA=<flags> passes flags to <exe>
# With no query it sweeps queries.txt and totals; with one it checks that one.
set -u
# byte order, so the output is the same whatever the host's locale
export LC_ALL=C
S="$(cd "$(dirname "$0")" && pwd)"
ROOT="${APTROOT:-/tmp/apt-cmp-root}"
APT="${APT:-apt-get}"
exe=$1; tag=$2

if [ $# -lt 3 ]; then
  mkdir -p "$S/out"
  xargs -P 8 -I{} bash "$0" "$exe" "$tag" {} < "$S/queries.txt" \
    > "$S/out/$tag.valid" 2>&1
  sort "$S/out/$tag.valid" -o "$S/out/$tag.valid"
  awk '/ unsat / {un++; next} / NO SOLUTION/ {bad++; next}
       {n++; if ($NF=="VALID") ok++; else print}
       END {printf "TOTAL valid=%d/%d unsat=%d nosol=%d\n", ok, n, un, bad}' \
    "$S/out/$tag.valid"
  exit 0
fi
query=$3
read -r -a extra <<< "${EXTRA:-}"
out="$S/out/$tag"
mkdir -p "$out"
cd "$S/../.."
INDEX="${INDEX:-repos/debian/Packages}"

"$exe" debian ${extra[@]+"${extra[@]}"} --native amd64 "$query" "$INDEX" \
  > "$out/$query.vout" 2>&1
rc=$?
if [ "$rc" -ne 0 ] && head -n 1 "$out/$query.vout" | grep -q '^unsatisfiable:'; then
  printf '%-18s %-7s unsat (no answer to verify)\n' "$query" "$tag"
  exit 0
fi

# name=version, the form apt's install pins with, for every :amd64 row
sed -n 's/^\([^ :]*\):amd64 \(.*\)$/\1=\2/p' "$out/$query.vout" | sort -u \
  > "$out/$query.req"
if [ ! -s "$out/$query.req" ]; then
  printf '%-18s %-7s NO SOLUTION (see %s)\n' "$query" "$tag" "$out/$query.vout"
  exit 1
fi
mapfile -t req < "$out/$query.req"
n=${#req[@]}
dups=$(cut -d= -f1 "$out/$query.req" | sort | uniq -d | wc -l)
foreign=$(awk 'NF == 2 && $1 ~ /:/ && $1 !~ /:amd64$/' "$out/$query.vout" | wc -l)
# the extraction above skips any line that is not a row, so such a line
# would leave apt judging fewer packages than the answer names
malformed=$(awk '/^parse / {exit}
                 !/^[^[:space:]:]+:[^[:space:]:]+ [^[:space:]]+$/' "$out/$query.vout" | wc -l)

recs=true
for a in ${extra[@]+"${extra[@]}"}; do
  [ "$a" = --no-install-recommends ] && recs=false
done

r="$out/$query.root"
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
  "$out/$query.req" RS= "$INDEX" > "$r/status"
stanzas=$?
# the rows name packages bare, and a query qualified with the native
# architecture names the same package
for p in "${req[@]}"; do
  [ "${p%%=*}" = "${query%:amd64}" ] ||
    printf 'Package: %s\nArchitecture: amd64\nAuto-Installed: 1\n\n' "${p%%=*}"
done > "$r/extended_states"

export APT_CONFIG="$r/etc/apt.conf"
"$APT" -s check > "$out/$query.check" 2>&1
crc=$?
"$APT" -s install "$query" > "$out/$query.install" 2>&1
irc=$?
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
APT_CONFIG="$r/bare/apt.conf" "$APT" -s autoremove > "$out/$query.autoremove" 2>&1
arc=$?
rm -rf "$r"

ch=$(grep -c '^\(Inst\|Remv\|Conf\|Purg\) ' "$out/$query.install")
un=$(grep -c '^Remv ' "$out/$query.autoremove")
none='0 upgraded, 0 newly installed, 0 to remove and 0 not upgraded.'

export APT_CONFIG="$ROOT/etc/apt/apt.conf"
"$APT" -s install "${req[@]}" > "$out/$query.aptrecs" 2>&1
sed -n 's/^Inst \([^ :]*\)\(:[^ ]*\)\{0,1\} (\([^ ]*\) .*/\1=\3/p' "$out/$query.aptrecs" \
  | sort -u > "$out/$query.instrecs"
re=$(comm -13 "$out/$query.req" "$out/$query.instrecs" | wc -l)
# the installed state skips the one question installing asks: whether
# dpkg can be walked through the set in some order.  A Pre-Depends cycle
# is consistent installed and cannot be installed, and apt says so only
# while ordering an install, so the whole answer is installed fresh, as
# asked, with nothing added
"$APT" -s -o APT::Install-Recommends=false install "${req[@]}" \
  > "$out/$query.order" 2>&1
orc=$?

rc=$((crc ? crc : irc ? irc : arc))
if [ "$rc" -eq 0 ] && [ "$stanzas" -eq 0 ] && [ "$ch" -eq 0 ] && [ "$un" -eq 0 ] &&
   [ "$dups" -eq 0 ] && [ "$foreign" -eq 0 ] && [ "$malformed" -eq 0 ] &&
   grep -qxF "$none" "$out/$query.install" &&
   grep -qxF "$none" "$out/$query.autoremove"; then
  if grep -q 'probably a dependency cycle' "$out/$query.order"; then
    v=CYCLIC
  elif [ "$orc" -eq 0 ]; then
    v=VALID
  else
    v=INVALID
  fi
else
  v=INVALID
fi
printf '%-18s %-7s n=%-5s changes=%-4s unneeded=%-4s dups=%-3s foreign=%-3s malformed=%-3s rc=%-3s order=%-3s recs=%-4s %s\n' \
  "$query" "$tag" "$n" "$ch" "$un" "$dups" "$foreign" "$malformed" "$rc" "$orc" "$re" "$v"
