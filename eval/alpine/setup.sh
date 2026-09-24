#!/usr/bin/env bash
# Build the apk root scale.sh solves against: a local repo holding nothing
# but repos/alpine/APKINDEX repacked as x86_64/APKINDEX.tar.gz, an empty
# world, and an empty installed db, so apk answers from the same rows our
# loader reads and from no others.
# usage: setup.sh [apkroot-dir]   (default /tmp/apk-cmp-root; ~3M)
#        INDEX=<dir>/APKINDEX builds it from another index
set -eu
S="$(cd "$(dirname "$0")" && pwd)"
ROOT="${1:-/tmp/apk-cmp-root}"
INDEX="${INDEX:-$S/../../repos/alpine/APKINDEX}"

if [ "$(id -u)" -eq 0 ]; then
  echo "setup.sh: apk refuses --usermode --initdb as root, so the root scale.sh" \
       "and valid.sh answer from cannot be built; run as an ordinary user" >&2
  exit 1
fi

# apk is not packaged for every host; where it is absent the build nix/flake.lock
# pins stands in.  Export the APK=<path> echoed below so scale.sh finds the
# same binary without paying a flake evaluation per goal.
APK="${APK:-}"
if [ -z "$APK" ]; then
  if command -v apk >/dev/null 2>&1; then APK=$(command -v apk)
  else APK="$(nix build --no-link --print-out-paths "$(cd "$S/../.." && pwd)/nix#apk-tools")/bin/apk"
  fi
fi
v=$("$APK" --version 2>/dev/null || true)
case $v in
  "apk-tools 3.0.5,"*) ;;
  *) echo "setup.sh: $APK reports '$v', but the baselines were taken with" \
          "apk-tools 3.0.5; run inside nix develop ./nix, where nix/flake.lock pins it" >&2
     exit 1 ;;
esac
echo "export APK=$APK"

rm -rf "$ROOT"
mkdir -p "$ROOT/repo/x86_64" "$ROOT/root/etc/apk"
tar -C "$(dirname "$INDEX")" -czf "$ROOT/repo/x86_64/APKINDEX.tar.gz" APKINDEX
"$APK" add --root "$ROOT/root" --usermode --initdb \
  --allow-untrusted --no-network --repository "$ROOT/repo"
: > "$ROOT/root/etc/apk/world"
: > "$ROOT/root/lib/apk/db/installed"
"$APK" --version
