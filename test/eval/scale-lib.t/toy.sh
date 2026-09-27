#!/usr/bin/env bash
# An ecosystem whose tool answers each query with its own name and whose
# pac answers the name at version 1, but "a" at version 2 under seed 1;
# the query "u" has no answer, and "broken" is one the two sides cannot be
# compared on.
ECO=toy
. "$EVAL/scale-lib.sh"

prepare() { :; }

ask_tool() {
  echo "$1" >> "$run/asked"
  echo "$2" > "$o.theirs"
  tool=ok
}

run_pac() {
  local v=1 t=0.01
  [ "$1" != random-1 ] || [ "$3" != a ] || v=2
  [ "$1" != random-2 ] || t=0.02
  if [ "$3" = u ]; then printf 'unsatisfiable:\n  u\n'
  else printf 'packages (1):\n  %s %s\nencoded solution: 3 core nodes (5 lookups)\n' "$3" "$v"; fi > "$2.out"
  printf 'loaded: 7 names, 9 versions, 2 extra\nparse 0.10s\nsolve %ss\n' "$t" >> "$2.out"
  [ "$3" != u ]
}

extract() { rows "$1.out" | cut -d' ' -f1 > "$1.ours"; }

correspond() { ! grep -qx broken "$1.ours" && compare "$1.ours" "$o.theirs"; }

check() { valid=VALID minimal=yes; }

main "$@"
