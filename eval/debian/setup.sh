#!/usr/bin/env bash
# Build the apt root cmp.sh solves against: a local flat repo holding
# repos/debian/Packages, an empty dpkg status, and apt's own lists cache.
# usage: setup.sh [aptroot-dir]   (default /tmp/apt-cmp-root; ~200M)
set -eu
S="$(cd "$(dirname "$0")" && pwd)"
ROOT="${1:-/tmp/apt-cmp-root}"
APT="${APT:-apt-get}"
PACKAGES="$S/../../repos/debian/Packages"

mkdir -p "$ROOT/repo" "$ROOT/etc/apt" "$ROOT/var/lib/apt" \
  "$ROOT/var/lib/dpkg" "$ROOT/var/cache/apt"
cp "$PACKAGES" "$ROOT/repo/Packages"
: > "$ROOT/var/lib/dpkg/status"
cat > "$ROOT/etc/apt/apt.conf" <<EOF
Dir "$ROOT";
Dir::State "$ROOT/var/lib/apt";
Dir::State::status "$ROOT/var/lib/dpkg/status";
Dir::Cache "$ROOT/var/cache/apt";
Dir::Etc "$ROOT/etc/apt";
APT::Architecture "amd64";
APT::Architectures { "amd64"; };
Acquire::Languages "none";
EOF
echo "deb [trusted=yes] file:$ROOT/repo ./" > "$ROOT/etc/apt/sources.list"
APT_CONFIG="$ROOT/etc/apt/apt.conf" "$APT" update
