# pac

Unified package manager dependency resolution.
We mechanise the Package Calculus -- a minimal core semantics of dependency resolution -- extend it with the dependency features of real package managers, and verify each extension's reduction to the core sound and complete in Rocq.
The reductions and their per-package lookup theorems extract to OCaml; an unmodified PubGrub solves the reduced instances, and the verified soundness witnesses decode its answers back into the extended calculi.

## Build

```sh
opam install . --deps-only
dune build
```

## Usage

Fetch a repository index for each ecosystem into `repos/` (or name a subset):

```sh
scripts/fetch-repos.sh
```

```sh
# Debian: nano for amd64
pac debian --native amd64 nano repos/debian/Packages

# opam: lwt
pac opam repos/opam-repository lwt

# Cargo: serde with a feature enabled
pac cargo repos/crates.io-index serde --features derive

# Alpine: nginx
pac alpine repos/alpine/APKINDEX nginx

# npm: a library whose mandatory peer dependency is installed beside it
pac npm --tree use-sync-external-store
```

## Evaluation

The harnesses in `eval/` compare pac's answers with those of apt, apk, opam, cargo and npm, and a recorded baseline holds only for the version of the tool that produced it.
`nix/flake.nix` provides each of them at its recorded version, pinned by `nix/flake.lock`, so run the evaluation inside its shell:

```sh
nix develop ./nix
```

The flake sits in `nix/` so that entering the shell copies only that directory into the Nix store, not `repos/` with it.
pac itself is still built with opam, as above.
Each `eval/*/setup.sh`, and `eval/cargo/run_goal.py`, refuses a tool at any other version.
The Alpine harness builds its apk root with `apk --usermode --initdb`, which apk refuses as root, so run it as an ordinary user.

*Programmed with [Claude Code](https://claude.ai/code)*
