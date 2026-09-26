# opam's exit 5, not found, is not the query's alone, so it counts only
# beside an error saying the query names nothing opam could install
refused() {  # <rc> <log>
  [ "$1" -eq 20 ] || { [ "$1" -eq 5 ] && grep -qE -f "$S/refusals" "$2"; }
}
