# apt exits 100 for a broken root as for a query it cannot satisfy, so an
# exit counts as a refusal only beside one of the errors that say the query
# is what apt would not take
refused() {  # <rc> <log>
  [ "$1" -eq 100 ] && grep -qE -f "$S/refusals" "$2"
}
