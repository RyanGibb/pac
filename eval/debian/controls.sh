#!/usr/bin/env bash
# usage: controls.sh <scratch-dir>        APT as valid.sh takes it
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

# the index on stdin; the answer as pac prints it, one row per argument
ctl() {  # <name> <expected> <row>...
  local d=$T/$1 want=$2 got; shift 2
  rm -rf "$d"; mkdir -p "$d"
  cat > "$d/Packages"
  printf '%s\n' "$@" > "$d/ans.out"; echo 0 > "$d/ans.rc"
  if ! INDEX=$d/Packages bash "$S/setup.sh" "$d/aptroot" > "$d/setup.log" 2>&1; then
    got=SETUP
  else
    got=$(APTROOT=$d/aptroot INDEX=$d/Packages REPLAY=$d/ans EXTRA=--no-install-recommends \
      bash "$S/valid.sh" "$S/scale.sh" "$(realpath -m --relative-to="$S/out" "$d/out")" goal |
      awk '{print $NF}')
  fi
  printf '%-10s expect %-7s got %s\n' "$(basename "$d")" "$want" "$got"
  [ "$got" = "$want" ] || bad=1
}

{ st goal 1 'Depends: a (>= 1)'; st a 1 'Provides: v (= 3)'; } |
  ctl ok VALID 'goal:amd64 1' 'a:amd64 1'
{ st goal 1 'Depends: a'; st a 1 'Depends: goal'; } |
  ctl ok-cycle VALID 'goal:amd64 1' 'a:amd64 1'
# apt counts every installed satisfier of an atom as needed
{ st goal 1 'Depends: a | b'; st a 1; st b 1; } |
  ctl alt VALID 'goal:amd64 1' 'a:amd64 1' 'b:amd64 1'
{ st goal 1 'Depends: mta'; st p1 1 'Provides: mta'; st p2 1 'Provides: mta'; } |
  ctl virt VALID 'goal:amd64 1' 'p1:amd64 1' 'p2:amd64 1'

{ st goal 1 'Depends: a'; st a 1; } | ctl c-missing INVALID 'goal:amd64 1'
{ st goal 1 'Pre-Depends: a'; st a 1; } | ctl c-predep INVALID 'goal:amd64 1'
{ st goal 1 'Depends: a'; st a 1 'Conflicts: goal'; } |
  ctl c-conflict INVALID 'goal:amd64 1' 'a:amd64 1'
{ st goal 1 'Depends: a'; st a 1 'Breaks: goal (<< 2)'; } |
  ctl c-breaks INVALID 'goal:amd64 1' 'a:amd64 1'
{ st goal 1 'Depends: v (>= 2)'; st a 1 'Provides: v (= 1)'; } |
  ctl c-vprov INVALID 'goal:amd64 1' 'a:amd64 1'

{ st goal 1 'Depends: foo'; st foo 1; st foo 2; } |
  ctl dup INVALID 'goal:amd64 1' 'foo:amd64 1' 'foo:amd64 2'
{ st goal 1; } | ctl foreign INVALID 'goal:amd64 1' 'bogus:i386 9'
{ st goal 1; st z 1; } | ctl noarch INVALID 'goal:amd64 1' 'z 1'
{ st goal 1 'Pre-Depends: a'; st a 1 'Pre-Depends: goal'; } |
  ctl prcycle CYCLIC 'goal:amd64 1' 'a:amd64 1'
{ st goal 1; st r 1 'Priority: required' 'Depends: s'; st s 1; } |
  ctl req INVALID 'goal:amd64 1' 'r:amd64 1' 's:amd64 1'
{ st goal 1; st e 1 'Essential: yes'; } | ctl ess INVALID 'goal:amd64 1' 'e:amd64 1'
{ st goal 1; st pr 1 'Protected: yes'; } | ctl prot INVALID 'goal:amd64 1' 'pr:amd64 1'
{ st goal 1; st apt 1; } | ctl aptpkg INVALID 'goal:amd64 1' 'apt:amd64 1'

exit $bad
