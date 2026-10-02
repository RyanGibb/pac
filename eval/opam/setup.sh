#!/usr/bin/env bash
# Build the throwaway OPAMROOT scale.sh solves against: repos/opam-repository
# as the only repository, an empty switch with an empty invariant and
# nothing installed, and the platform variables, PLATFORM (platform.sh),
# pinned through `opam var --global`, so opam answers the same question pac
# does rather than the host's.
# Without the pinning opam infers os-distribution=nixos here, which changes
# what is available (srt's conf-srt-openssl, for one): a different instance,
# not a different preference.
#
# opam-version is left as opam's own (OPAMVAR_opam_version or a variable
# would override it); scale.sh hands that to our driver instead, as
# --opam-version.
#
# usage: setup.sh [opamroot-dir]   (default $TMPDIR/pac-opam-root)
#        REPO=<dir> builds it over another repository
#        PLATFORM=<var=value,...> pins another platform
set -eu
S="$(cd "$(dirname "$0")" && pwd)"
. "$S/platform.sh"
REPO="$(cd "${REPO:-$S/../../repos/opam-repository}" && pwd)"
export OPAMROOT="${1:-${TMPDIR:-/tmp}/pac-opam-root}"

v=$(opam --version 2>/dev/null || true)
if [ "$v" != 2.5.2 ]; then
  echo "setup.sh: opam reports '$v', but the baselines were taken with opam" \
       "2.5.2; run inside nix develop ./nix, where nix/flake.lock pins it" >&2
  exit 1
fi

rm -rf "$OPAMROOT"
opam init --bare --no-setup --disable-sandboxing --bypass-checks -y \
  -k local snapshot "$REPO"
opam switch create cmp --empty -y

IFS=, read -ra kvs <<< "$PLATFORM"
for kv in "${kvs[@]}"; do
  opam var "$kv" --global -y
done

opam --version
opam var --global
p=$(root_platform)
[ "$p" = "$PLATFORM" ] || {
  echo "setup.sh: the root holds $p, not PLATFORM=$PLATFORM" >&2; exit 1; }
