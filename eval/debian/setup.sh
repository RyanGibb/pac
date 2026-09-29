#!/usr/bin/env bash
# Build the apt root scale.sh solves against: a local flat repo holding
# repos/debian/Packages, an empty dpkg status, and apt's own lists cache.
# usage: setup.sh [aptroot-dir]   (default /tmp/apt-cmp-root; ~200M)
#        INDEX=<Packages> builds it from another index
#        FOREIGN="<dir>/Packages.<arch> ..." adds each file as a flat repo of
#          its own and <arch> to APT::Architectures after the native amd64,
#          as dpkg --add-architecture <arch> would
set -eu
S="$(cd "$(dirname "$0")" && pwd)"
ROOT="${1:-/tmp/apt-cmp-root}"
APT="${APT:-apt-get}"
PACKAGES="${INDEX:-$S/../../repos/debian/Packages}"
FOREIGN="${FOREIGN:-}"

v=$("$APT" --version 2>/dev/null | head -n 1)
case $v in
  "apt 3.3.0 "*) ;;
  *) echo "setup.sh: $APT reports '$v', but the baselines were taken with" \
          "apt 3.3.0; run inside nix develop ./nix, where nix/flake.lock pins it" >&2
     exit 1 ;;
esac

mkdir -p "$ROOT/repo" "$ROOT/etc/apt" "$ROOT/var/lib/apt" \
  "$ROOT/var/lib/dpkg" "$ROOT/var/cache/apt"
cp "$PACKAGES" "$ROOT/repo/Packages"
echo "deb [trusted=yes] file:$ROOT/repo ./" > "$ROOT/etc/apt/sources.list"
arches='"amd64";'
for f in $FOREIGN; do
  a=${f##*/Packages.}
  mkdir -p "$ROOT/repo-$a"
  cp "$f" "$ROOT/repo-$a/Packages"
  echo "deb [trusted=yes] file:$ROOT/repo-$a ./" >> "$ROOT/etc/apt/sources.list"
  arches="$arches \"$a\";"
done
: > "$ROOT/var/lib/dpkg/status"
cat > "$ROOT/etc/apt/apt.conf" <<EOF
Dir "$ROOT";
Dir::State "$ROOT/var/lib/apt";
Dir::State::status "$ROOT/var/lib/dpkg/status";
Dir::Cache "$ROOT/var/cache/apt";
Dir::Etc "$ROOT/etc/apt";
APT::Architecture "amd64";
APT::Architectures { $arches };
Acquire::Languages "none";
EOF
APT_CONFIG="$ROOT/etc/apt/apt.conf" "$APT" update
