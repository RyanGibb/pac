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

# whether npm's resolver, with its platform check alone skipped, gives
# exactly the packages of our lock: the evidence a PLATFORM verdict rests
# on.  --force skips arborist's checkPlatform; --os and --cpu do not, for a
# package that is not optional.  npmc is the calling check's npm.
resolves() {  # <our lock> <package.json> <scratch dir>
  rm -rf "$3"; mkdir -p "$3"; cp "$2" "$3/package.json"
  npmc "$3" install --package-lock-only --force --ignore-scripts > "$3.log" 2>&1 &&
    cmp -s <(lockset "$1") <(lockset "$3/package-lock.json")
}
lockset() {  # <package-lock.json>: its packages, name and version, links aside
  jq -r '.packages | to_entries[] | select(.key != "" and .value.link != true)
         | "\(.value.name // (.key | sub(".*node_modules/"; ""))) \(.value.version)"' "$1" | sort -u
}
