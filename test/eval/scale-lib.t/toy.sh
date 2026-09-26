#!/usr/bin/env bash
# An ecosystem whose tool answers each query with its own name and whose
# pac answers the name at version 1; the query "u" has no answer, and
# "broken" is one the two sides cannot be compared on.
ECO=toy
. "$EVAL/scale-lib.sh"

prepare() { :; }

ask_tool() {
  echo "$1" >> "$run/asked"
  echo "$2" > "$o.theirs"
  tool=ok
}

run_pac() {
  : > "$2.out"
  [ "$3" != u ] || return 1
  printf 'packages (1):\n  %s 1\n' "$3" > "$2.out"
}

extract() { rows "$1.out" | cut -d' ' -f1 > "$1.ours"; }

correspond() { ! grep -qx broken "$1.ours" && compare "$1.ours" "$o.theirs"; }

check() { valid=VALID minimal=yes; }

main "$@"
