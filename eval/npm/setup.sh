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

npm --version > "$S/npm-version"
node --version >> "$S/npm-version"
cat "$S/npm-version"
