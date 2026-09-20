#!/usr/bin/env bash
# Build the apk root cmp.sh solves against: a local repo holding nothing
# but repos/alpine/APKINDEX repacked as x86_64/APKINDEX.tar.gz, an empty
# world, and an empty installed db, so apk answers from the same rows our
# loader reads and from no others.
# usage: setup.sh [apkroot-dir]   (default /tmp/apk-cmp-root; ~3M)
set -eu
S="$(cd "$(dirname "$0")" && pwd)"
ROOT="${1:-/tmp/apk-cmp-root}"
INDEX="$S/../../repos/alpine/APKINDEX"

# apk is not packaged for every host; where it is absent the nixpkgs build
# stands in, and the resolved path is echoed rather than recorded, because a
# store path is local to the machine that built it.  Export APK=<that path>
# so cmp.sh finds the same binary without paying a flake evaluation per goal.
APK="${APK:-}"
if [ -z "$APK" ]; then
  if command -v apk >/dev/null 2>&1; then APK=$(command -v apk)
  else APK="$(nix build --no-link --print-out-paths nixpkgs#apk-tools)/bin/apk"
  fi
fi
echo "export APK=$APK"

rm -rf "$ROOT"
mkdir -p "$ROOT/repo/x86_64" "$ROOT/root/etc/apk"
tar -C "$(dirname "$INDEX")" -czf "$ROOT/repo/x86_64/APKINDEX.tar.gz" APKINDEX
"$APK" add --root "$ROOT/root" --usermode --initdb \
  --allow-untrusted --no-network --repository "$ROOT/repo"
: > "$ROOT/root/etc/apk/world"
: > "$ROOT/root/lib/apk/db/installed"
"$APK" --version
