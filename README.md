# pac

pac is a mechanised package calculus in Rocq: a minimal core semantics of dependency resolution, extended with the features of real package managers, each extension reduced to the core with the reduction proved sound and complete.
The reductions extract to OCaml, and frontends for Debian, Alpine, opam, Cargo and npm use them to drive PubGrub.

## Build

`rocq-stdlib` comes from the `coq-released` opam repository.

```sh
opam repo add coq-released https://coq.inria.fr/opam/released
opam install . --deps-only
dune build
```

## Usage

Fetch an index for each ecosystem into `repos/` (or name a subset):

```sh
scripts/fetch-repos.sh
```

```sh
pac debian --native amd64 nano repos/debian/Packages
pac alpine repos/alpine/APKINDEX nginx
pac opam repos/opam-repository lwt
pac cargo repos/crates.io-index path/to/Cargo.toml
pac npm --tree use-sync-external-store
```

## Evaluation

See [eval/README.md](eval/README.md) for the tests and for comparing pac against apt, apk, opam, cargo and npm.
