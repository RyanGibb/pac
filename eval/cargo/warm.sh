#!/usr/bin/env bash
# The one online pass of the cargo validity harness: fill CARGO_HOME with
# every crate body the verification pass will need, so that pass can run
# --offline and reach no network at all.  It runs the identical repair
# with the network reachable, which is what makes the offline repair
# reproduce it: whatever cargo chooses there, overrules of our picks
# included, is downloaded here.
#
# Warming goes through the same sparse-index proxy the verification pass
# reads, which is not a detail: fetching against the live crates.io index
# would resolve a different universe -- whatever has been published since
# the snapshot -- and could warm the wrong versions entirely.  valid.sh
# owns the proxy, so this is a mode of valid.sh rather than a second
# implementation of it.
#
# Run once per snapshot.  Afterwards record the cache's identity in
# eval/SNAPSHOTS, by the command written there: a validity verdict is an
# answer about one fixed universe, and with the measured pass offline the
# cache is part of that universe.
#
# usage: warm.sh [goals-file | goal ...]       (default goals.txt)
# env: PAC, CARGO_CMP_OUT (run dir), PORT
set -uo pipefail
S="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WARM=1 exec bash "$S/valid.sh" "$@"
