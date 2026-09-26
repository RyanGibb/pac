#!/usr/bin/env bash
# usage: controls.sh <scratch-dir>        APT as check.sh takes it
set -u
export LC_ALL=C
S="$(cd "$(dirname "$0")" && pwd)"
T=$(mkdir -p "$1" && cd "$1" && pwd)
bad=0

st() {  # <name> <version> [field...]
  printf 'Package: %s\nVersion: %s\nArchitecture: amd64\nMaintainer: x <x@x>\n' "$1" "$2"
  printf 'Filename: pool/%s_%s_amd64.deb\nSize: 1\nDescription: fx\n' "$1" "$2"
  shift 2
  for f; do printf '%s\n' "$f"; done
  echo
}

answer() {  # <row>...: the answer as pac prints it
  echo "packages ($#):"
  printf '  %s\n' "$@"
}

# the index on stdin; the answer one row per argument; the expected
# verdicts as valid/minimal
ctl() {  # <name> <expected> <row>...
  local d=$T/$1 want=$2 got; shift 2
  rm -rf "$d"; mkdir -p "$d"
  cat > "$d/Packages"
  answer "$@" > "$d/ans.out"
  if ! INDEX=$d/Packages bash "$S/setup.sh" "$d/aptroot" > "$d/setup.log" 2>&1; then
    got=SETUP
  else
    got=$(APTROOT=$d/aptroot INDEX=$d/Packages \
      bash "$S/../check.sh" debian "$d/ans.out" "$d/check" --no-install-recommends goal |
      tail -n 1 | sed -n 's/.* valid=\([A-Z]*\) minimal=\(.*\)$/\1\/\2/p')
  fi
  printf '%-10s expect %-11s got %s\n' "$(basename "$d")" "$want" "$got"
  [ "$got" = "$want" ] || bad=1
}

{ st goal 1 'Depends: a (>= 1)'; st a 1 'Provides: v (= 3)'; } |
  ctl ok VALID/yes 'goal:amd64 1' 'a:amd64 1'
{ st goal 1 'Depends: a'; st a 1 'Depends: goal'; } |
  ctl ok-cycle VALID/yes 'goal:amd64 1' 'a:amd64 1'
# apt counts every installed satisfier of an atom as needed
{ st goal 1 'Depends: a | b'; st a 1; st b 1; } |
  ctl alt VALID/yes 'goal:amd64 1' 'a:amd64 1' 'b:amd64 1'
{ st goal 1 'Depends: mta'; st p1 1 'Provides: mta'; st p2 1 'Provides: mta'; } |
  ctl virt VALID/yes 'goal:amd64 1' 'p1:amd64 1' 'p2:amd64 1'

{ st goal 1 'Depends: a'; st a 1; } | ctl c-missing INVALID/- 'goal:amd64 1'
{ st goal 1 'Pre-Depends: a'; st a 1; } | ctl c-predep INVALID/- 'goal:amd64 1'
{ st goal 1 'Depends: a'; st a 1 'Conflicts: goal'; } |
  ctl c-conflict INVALID/- 'goal:amd64 1' 'a:amd64 1'
{ st goal 1 'Depends: a'; st a 1 'Breaks: goal (<< 2)'; } |
  ctl c-breaks INVALID/- 'goal:amd64 1' 'a:amd64 1'
{ st goal 1 'Depends: v (>= 2)'; st a 1 'Provides: v (= 1)'; } |
  ctl c-vprov INVALID/- 'goal:amd64 1' 'a:amd64 1'
# a package nothing needs, whose own dependency is still unmet
{ st goal 1; st z 1 'Depends: y'; st y 1; } |
  ctl c-extra INVALID/- 'goal:amd64 1' 'z:amd64 1'

{ st goal 1 'Depends: foo'; st foo 1; st foo 2; } |
  ctl dup INVALID/- 'goal:amd64 1' 'foo:amd64 1' 'foo:amd64 2'
{ st goal 1; } | ctl foreign INVALID/- 'goal:amd64 1' 'bogus:i386 9'
{ st goal 1; st z 1; } | ctl noarch INVALID/- 'goal:amd64 1' 'z 1'
{ st goal 1 'Pre-Depends: a'; st a 1 'Pre-Depends: goal'; } |
  ctl prcycle CYCLIC/- 'goal:amd64 1' 'a:amd64 1'

# consistent, but holding what the query does not need: autoremove must see
# past every root apt adds of its own
{ st goal 1; st z 1; } | ctl extra VALID/no 'goal:amd64 1' 'z:amd64 1'
{ st goal 1; st r 1 'Priority: required' 'Depends: s'; st s 1; } |
  ctl req VALID/no 'goal:amd64 1' 'r:amd64 1' 's:amd64 1'
{ st goal 1; st e 1 'Essential: yes'; } | ctl ess VALID/no 'goal:amd64 1' 'e:amd64 1'
{ st goal 1; st pr 1 'Protected: yes'; } | ctl prot VALID/no 'goal:amd64 1' 'pr:amd64 1'
{ st goal 1; st apt 1; } | ctl aptpkg VALID/no 'goal:amd64 1' 'apt:amd64 1'

# apt failing for want of an environment says nothing of the answer: a root
# that is gone, and one whose lists are
for broken in noroot nolists; do
  d=$T/$broken
  rm -rf "$d"; mkdir -p "$d"
  st goal 1 > "$d/Packages"; answer 'goal:amd64 1' > "$d/ans.out"
  INDEX=$d/Packages bash "$S/setup.sh" "$d/aptroot" > "$d/setup.log" 2>&1
  case $broken in
    noroot) rm -rf "$d/aptroot" ;;
    nolists) rm -rf "$d/aptroot/var/lib/apt/lists" ;;
  esac
  got=$(APTROOT=$d/aptroot INDEX=$d/Packages bash "$S/../check.sh" debian "$d/ans.out" "$d/check" goal |
    tail -n 1 | sed -n 's/.* valid=\([A-Z]*\) minimal=\(.*\)$/\1\/\2/p')
  printf '%-10s expect %-11s got %s\n' "$broken" ERR/- "$got"
  [ "$got" = ERR/- ] || bad=1
done

exit $bad
