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
```

*Programmed with [Claude Code](https://claude.ai/code)*
