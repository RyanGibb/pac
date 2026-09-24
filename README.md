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

The evaluation has three levels: the unit tests in `test/`, a regression set of a few dozen goals per ecosystem whose answers from the real tool are recorded, and runs at scale that ask the tool afresh over thousands of goals.

### Unit tests

`test/` holds cram tests: the reductions on small instances in `test/reductions/`, and each frontend on fixtures in `test/frontends/<eco>.t`.

```sh
dune test
dune test test/frontends/debian.t
```

### The harness

`eval/<eco>/scale.sh` runs the other two levels, comparing pac's answers with those of apt, apk, opam, cargo and npm, and a recorded answer holds only for the version of the tool that produced it.
`nix/flake.nix` provides each of them at its recorded version, pinned by `nix/flake.lock`, so run the harness inside its shell:

```sh
nix develop ./nix
```

The flake sits in `nix/` so that entering the shell copies only that directory into the Nix store, not `repos/` with it.
pac itself is still built with opam, as above.
Each `eval/*/setup.sh`, and `eval/cargo/run_goal.py`, refuses a tool at any other version.
The Alpine harness builds its apk root with `apk --usermode --initdb`, which apk refuses as root, so run it as an ordinary user.

`scale.sh [--regress | --record] <pac-exe> <run-dir> [goals-file]` checks each goal twice: whether pac answers as the tool does, and whether the tool accepts pac's answer as a resolution of its own, the question `eval/<eco>/valid.sh` asks.
It runs `P` goals at a time (default: every core), gives each tool call `TIMEOUT` seconds (default 900), and resumes a killed run where it stopped.
Where pac has more than one search mode, `MODES` names those to run by flag: Debian's `apt-heap` and opam's `0install-order` each run beside `default` unless it says otherwise.
Keep the run directory outside the source tree, which dune scans.
The run ends with a line per mode, such as `default: 62 goals, exact 46/60, valid 60/60`: pac's answers that are exactly the tool's, of the goals the tool answers, and pac's answers the tool accepts, of those it checked.

### The regression set

`eval/<eco>/goals.txt` lists a few dozen hand-picked goals, and `eval/<eco>/baseline/` holds the tool's answer to each, or, for a goal the tool refuses, an empty `.absent` file in its place.
`--regress` compares pac against those answers rather than asking the tool, whose check of pac's answers still runs.
npm's goals are pinned to the versions in `baseline/roots.txt`, which `eval/npm/seed.sh` chose.
Cargo records no answers: cargo is run for validity anyway, against the snapshot `sparse_proxy.py` serves, and the question it is asked depends on pac's answer, so its `--regress` asks cargo afresh.

```sh
eval/debian/scale.sh --regress _build/default/src/main.exe /tmp/regress/debian
eval/opam/scale.sh --regress _build/default/src/main.exe /tmp/regress/opam
eval/alpine/scale.sh --regress _build/default/src/main.exe /tmp/regress/alpine
eval/cargo/scale.sh --regress _build/default/src/main.exe /tmp/regress/cargo
eval/npm/scale.sh --regress _build/default/src/main.exe /tmp/regress/npm
```

`--record` asks the tool instead, and writes its answers into `baseline/`; record them all or none, since each holds only for one version of the tool.

```sh
eval/debian/scale.sh --record _build/default/src/main.exe /tmp/record/debian
```

### At scale

With neither flag, `scale.sh` asks the tool afresh over every package in the index, or for cargo a seeded sample of 3000 crates, or over the goals a file lists one per line, optionally after a pool name and a tab.

```sh
eval/alpine/scale.sh _build/default/src/main.exe /tmp/scale/alpine
MODES=apt-heap P=32 eval/debian/scale.sh _build/default/src/main.exe /tmp/scale/debian
eval/opam/scale.sh _build/default/src/main.exe /tmp/scale/opam-test <(ls repos/opam-repository/packages | sed 's/^/--with-test /')
python3 eval/cargo/scale.py targets 20260923 150 > /tmp/pools.txt && eval/cargo/scale.sh _build/default/src/main.exe /tmp/scale/cargo /tmp/pools.txt
node eval/npm/goals.js repos/npm targeted > /tmp/ranges.txt && eval/npm/scale.sh _build/default/src/main.exe /tmp/scale/npm /tmp/ranges.txt
```

At either level the run directory gets one line per goal and mode in `results.txt`, `goal= mode= pac= tool= corr= valid= oo= to= wall=`, and each goal's raw answers under `out/`.
Some ecosystems add fields: opam's `pin` and `mccs`, npm's `closed`, `nodes` and `edges`, and cargo's `kept` and `identical`.
`eval/<eco>/triage.py <run-dir>` sorts the goals into classes, per mode and per pool, and clusters the divergences:

| class | meaning |
|---|---|
| `exact` | both answer with the same set, and the tool accepts ours |
| `preference-gap` | both answer, the sets differ, and the tool accepts ours |
| `error` | both answer, the sets differ, and the tool rejects ours |
| `exact-invalid` | the tool rejects an answer that matches its own, which points at the check |
| `post-resolution` | the tool accepts our answer as a resolution but cannot install it: for opam, its install order has a cycle |
| `instance-gap` | the tool's answer is not a resolution of our instance: we are unsatisfiable where it answers, or for opam its answer, pinned, is unsatisfiable for us |
| `tool-declines` | we answer and the tool refuses |
| `both-refuse` | neither answers |
| `pac-timeout`, `pac-crash`, `tool-timeout` | a side gave no verdict |
| `unchecked` | we answer, but the validity check could not run |
| `unrecorded` | `--regress` found no recorded answer to the goal |

npm's goals are split further by whether they are closed: whether neither side asked for a name the snapshot lacks.
npm's edges are scored after `edges.py --peer-parent`, which attributes a peer's edge as pac does; `NORM=` scores them as npm's lock records them.
`eval/alpine/pin.sh <run-dir>` and `eval/npm/pin.sh <run-dir>` re-ask a run's divergent goals with the tool's picks forced, which tells a preference gap from an instance gap.
`eval/cargo/features.py` also compares the feature set of each crate in pac's answer with `cargo metadata`'s.
It is not part of the scale run because it downloads crate sources.

*Programmed with [Claude Code](https://claude.ai/code)*
