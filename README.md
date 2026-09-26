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
pac npm --cache repos/npm --tree use-sync-external-store
```

## Trusted base

The reductions and their decoders are proved; what a frontend feeds them and does with their answer is trusted.
Every frontend trusts PubGrub, whose solution is decoded without a check although the decoders' theorems assume it is a core resolution, and the command line around it.
The `--order` hooks are not trusted: they only pick among the names and versions PubGrub offers them.
Beyond that each trusts:

| frontend | trusted |
|---|---|
| Debian | the Packages parser, the version comparator (`lib/version/debian.ml`), the reading of apt-get's arguments with the Strict-Pinning cut, and the tables' faithfulness to the parsed index |
| Alpine | the APKINDEX parser, apk's version comparator with its prefix and hash matches, the provider preference, and the choice of the condition an install-if rule is filed under |
| opam | the opam-file parser, the version comparator (Debian's without the epoch), and the valuation's defaults |
| Cargo | the index parser, the TOML and root-manifest readers, the version comparator (`lib/version/semver.ml`) and requirement syntax, and the MSRV policy |
| npm | the packument parser and the registry it reads, taken at face value, the range parser and version comparator, the engines test, and the fetch |

## Evaluation

See [eval/README.md](eval/README.md) for the tests and for comparing pac against apt, apk, opam, cargo and npm.
