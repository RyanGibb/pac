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

# The evidence a PLATFORM verdict rests on, for an answer npm ci refuses
# as EBADPLATFORM and every other clause holds, as "ci-force=<rc>
# resolver=same|diff": whether `npm ci`, its platform check alone skipped,
# takes our lock (exit 0 and no peer overridden), which PLATFORM requires;
# and whether npm's resolver, that check skipped too, gives exactly our
# packages, which a preference may make it not.  --force skips arborist's
# checkPlatform; --os and --cpu do not, for a package that is not
# optional.  npmc is the calling check's npm.
forced() {  # <dir holding our package.json and lock> <out-dir>
  local rc res=diff
  rm -rf "$1.force" "$1.resolver"; cp -r "$1" "$1.force"; mkdir -p "$1.resolver"
  npmc "$1.force" ci --dry-run --force > "$2/ci-force.log" 2>&1
  rc=$?
  grep -q 'ERESOLVE overriding peer dependency' "$2/ci-force.log" && rc=peer
  cp "$1/package.json" "$1.resolver/"
  npmc "$1.resolver" install --package-lock-only --force --ignore-scripts > "$2/resolver.log" 2>&1 &&
    cmp -s <(lockset "$1/package-lock.json") <(lockset "$1.resolver/package-lock.json") && res=same
  echo "ci-force=$rc resolver=$res"
}
lockset() {  # <package-lock.json>: its packages, name and version, links aside
  jq -r '.packages | to_entries[] | select(.key != "" and .value.link != true)
         | "\(.value.name // (.key | sub(".*node_modules/"; ""))) \(.value.version)"' "$1" | sort -u
}
