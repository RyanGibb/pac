#!/usr/bin/env bash
# Build the throwaway OPAMROOT cmp.sh solves against: repos/opam-repository
# as the only repository, an empty switch with an empty invariant and
# nothing installed, and the environment variables our driver assumes
# (src/opam/opam_solve.ml, [globals]) pinned through `opam var --global`,
# so opam answers the same question our loader does rather than the host's.
# Without the pinning opam infers os-distribution=nixos here and picks a
# different host-system-* gadget, which is a different instance, not a
# different preference.
#
# opam-version is the one global that cannot be set: opam reports its own
# (2.5.2), our rho says "2.2.0".  In this snapshot that separates only
# opam-build / opam-test / opam-check-npm-deps, none of which is in any
# goal's cone; see findings.md.
#
# usage: setup.sh [opamroot-dir]   (default /tmp/claude-1000/opam-cmp-root)
set -eu
S="$(cd "$(dirname "$0")" && pwd)"
REPO="$(cd "$S/../../repos/opam-repository" && pwd)"
export OPAMROOT="${1:-/tmp/claude-1000/opam-cmp-root}"

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
