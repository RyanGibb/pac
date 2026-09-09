#!/bin/sh
# Fetch a repository index for each package manager into repos/.
# Usage: scripts/fetch-repos.sh [debian|opam|cargo]...  (default: all)

set -eu

root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
out=$root/repos

DEBIAN_SUITE=${DEBIAN_SUITE:-stable}
DEBIAN_ARCH=${DEBIAN_ARCH:-amd64}

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

clone() {
  dir=$out/$2
  [ -d "$dir" ] && { echo "$2: already present"; return; }
  mkdir -p "$out"
  echo "$2: $1"
  git clone --depth 1 --quiet "$1" "$dir"
}

opam() { clone https://github.com/ocaml/opam-repository opam-repository; }
cargo() { clone https://github.com/rust-lang/crates.io-index crates.io-index; }

[ $# -gt 0 ] || set -- debian opam cargo
for eco; do
  case $eco in
  debian | opam | cargo) "$eco" ;;
  *)
    echo "unknown: $eco (want debian, opam or cargo)" >&2
    exit 2
    ;;
  esac
done
