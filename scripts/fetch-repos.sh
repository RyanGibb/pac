#!/bin/sh
# Fetch a repository index for each package manager into repos/.
# Usage: scripts/fetch-repos.sh [debian|opam|cargo|alpine|npm]...  (default: all)

set -eu

root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
out=$root/repos

DEBIAN_SUITE=${DEBIAN_SUITE:-stable}
DEBIAN_ARCH=${DEBIAN_ARCH:-amd64}
ALPINE_VER=${ALPINE_VER:-v3.21}
ALPINE_ARCH=${ALPINE_ARCH:-x86_64}
# npm has no bulk index, so the cache is seeded per package; pac npm fetches
# anything else it needs on demand.  This is the cone of a react library with
# a genuine mandatory peer dependency.
NPM_DEMO=${NPM_DEMO:-"use-sync-external-store react loose-envify js-tokens"}

fetch() {
  if command -v curl >/dev/null 2>&1; then
    curl -fsSL "$1" -o "$2"
  else
    wget -q "$1" -O "$2"
  fi
}

debian() {
  dir=$out/debian
  [ -f "$dir/Packages" ] && { echo "debian: already present"; return; }
  mkdir -p "$dir"
  url=https://deb.debian.org/debian/dists/$DEBIAN_SUITE/main/binary-$DEBIAN_ARCH/Packages.gz
  echo "debian: $url"
  fetch "$url" "$dir/Packages.gz"
  gunzip -f "$dir/Packages.gz"
}

alpine() {
  dir=$out/alpine
  [ -f "$dir/APKINDEX" ] && { echo "alpine: already present"; return; }
  mkdir -p "$dir"
  url=https://dl-cdn.alpinelinux.org/alpine/$ALPINE_VER/main/$ALPINE_ARCH/APKINDEX.tar.gz
  echo "alpine: $url"
  fetch "$url" "$dir/APKINDEX.tar.gz"
  tar -xzf "$dir/APKINDEX.tar.gz" -C "$dir" APKINDEX
  rm -f "$dir/APKINDEX.tar.gz"
}

clone() {
  dir=$out/$2
  [ -d "$dir" ] && { echo "$2: already present"; return; }
  mkdir -p "$out"
  echo "$2: $1"
  git clone --depth 1 --quiet "$1" "$dir"
}

npm() {
  dir=$out/npm
  mkdir -p "$dir"
  for p in $NPM_DEMO; do
    esc=$(printf '%s' "$p" | sed 's|/|%2F|g')
    f=$dir/$esc.json
    [ -f "$f" ] && { echo "npm: $p already present"; continue; }
    echo "npm: $p"
    fetch "https://registry.npmjs.org/$esc" "$f"
  done
}

opam() { clone https://github.com/ocaml/opam-repository opam-repository; }
cargo() { clone https://github.com/rust-lang/crates.io-index crates.io-index; }

[ $# -gt 0 ] || set -- debian opam cargo alpine npm
for eco; do
  case $eco in
  debian | opam | cargo | alpine | npm) "$eco" ;;
  *)
    echo "unknown: $eco (want debian, opam, cargo, alpine or npm)" >&2
    exit 2
    ;;
  esac
done
