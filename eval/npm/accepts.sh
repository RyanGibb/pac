# Sourced by scale.sh, valid.sh and controls.sh, each of which defines
# npmc <dir> <npm args...> to run npm in <dir> against its own registry.
#
# ci builds the tree the lock describes and checks it against every
# manifest, but it repairs as it builds and fails only when the repair
# changes the inventory: an invalid peerOptional, or a peer resolving
# inside its requirer where npm's repair keeps that copy, passes it.
# install --package-lock-only runs the same repair and writes it back, so
# the lock it leaves must name the same version at every path; that also
# rejects a package nothing reaches.  ci stays, since nothing shows install
# rejecting everything ci does.

paths() { jq -r '.packages | to_entries[] | select(.key != "") | "\(.key) \(.value.version)"' "$1" | sort; }

# accepts <dir> <log stem>: whether npm takes the lock in <dir> as it
# stands; sets ci_rc, relock_rc and moved, and logs to <stem>.ci, .plo
accepts() {
  npmc "$1" ci --dry-run > "$2.ci" 2>&1
  ci_rc=$?
  rm -rf "$1.plo"; cp -r "$1" "$1.plo"
  npmc "$1.plo" install --package-lock-only --ignore-scripts > "$2.plo" 2>&1
  relock_rc=$?
  moved=$(diff <(paths "$1/package-lock.json") <(paths "$1.plo/package-lock.json") | grep -c '^[<>]')
  [ "$ci_rc" -eq 0 ] && [ "$relock_rc" -eq 0 ] && [ "$moved" -eq 0 ]
}
