#!/usr/bin/env bash
# Build the run root both sides answer from: a snapshot directory that is
# repos/npm as a symlink farm, plus a scratch HOME and npm cache so no
# global config, no ~/.npmrc and no global cache can leak into a run, and
# plus one wrapper root package per goal.
#
# The farm rather than repos/npm itself is what lets seed.sh close the
# snapshot over whatever either side asks for without writing into the
# checked-out repos/ tree: a filled name lands in the farm as a real file
# beside the symlinks, and both sides read the farm.
#
# usage: setup.sh [run-dir]   (default /tmp/npm-cmp)
set -eu
S="$(cd "$(dirname "$0")" && pwd)"
RUN="${1:-/tmp/npm-cmp}"
SNAP="$S/../../repos/npm"

mkdir -p "$RUN/cache" "$RUN/home" "$RUN/work"
ln -sfn "$SNAP"/*.json "$RUN/cache/"
: > "$RUN/home/.npmrc"
: > "$RUN/home/npmrc-global"

# npm-version is the host the recorded locks were taken on and the host
# cmp.sh hands our side, so a different one is refused, not recorded over it
have="$(npm --version 2>/dev/null || true) $(node --version 2>/dev/null || true)"
want=$(tr '\n' ' ' < "$S/npm-version")
if [ "$have " != "$want" ]; then
  echo "setup.sh: npm and node here are '$have', but npm-version records" \
       "'${want% }'; run inside nix develop ./nix, where nix/flake.lock pins them" >&2
  exit 1
fi
cat "$S/npm-version"
