#!/usr/bin/env bash
# Build the throwaway OPAMROOT scale.sh solves against: repos/opam-repository
# as the only repository, an empty switch with an empty invariant and
# nothing installed, and the environment variables our driver assumes
# (src/opam/opam_solve.ml, [globals]) pinned through `opam var --global`,
# so opam answers the same question our loader does rather than the host's.
# Without the pinning opam infers os-distribution=nixos here and picks a
# different host-system-* package, which is a different instance, not a
# different preference.
#
# opam-version is left as opam's own (OPAMVAR_opam_version or a variable
# would override it); scale.sh and valid.sh hand that to our driver
# instead, as --opam-version.
#
# usage: setup.sh [opamroot-dir]   (default /tmp/claude-1000/opam-cmp-root)
#        REPO=<dir> builds it over another repository
set -eu
S="$(cd "$(dirname "$0")" && pwd)"
REPO="$(cd "${REPO:-$S/../../repos/opam-repository}" && pwd)"
export OPAMROOT="${1:-/tmp/claude-1000/opam-cmp-root}"

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

for kv in os=linux os-family=debian os-distribution=debian os-version=12 \
          arch=x86_64; do
  opam var "$kv" --global -y
done

opam --version
opam var --global
