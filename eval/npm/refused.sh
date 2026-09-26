# npm exits 1 for every error, a shim that stopped answering included, so
# an exit counts as a refusal only under one of the codes npm gives a query
# it will not take
refused() {  # <rc> <log>
  [ "$1" -eq 1 ] && grep -qE -f "$S/refusals" "$2"
}
