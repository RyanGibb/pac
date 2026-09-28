# npm exits 1 for every error, a shim that stopped answering included, so
# an exit counts as a refusal only under one of the codes npm gives a query
# it will not take
refused() {  # <rc> <log>
  [ "$1" -eq 1 ] && grep -qE -f "$S/refusals" "$2"
}

# whether npm refused for the host's platform: a package whose os, cpu or
# libc excludes this host, which npm's resolver places like any other and
# its installer then will not take (EBADPLATFORM)
platform() {  # <rc> <log>
  [ "$1" -eq 1 ] && grep -q '^npm error code EBADPLATFORM$' "$2"
}
