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

### At scale

The committed sweeps check a few dozen hand-picked goals against recorded baselines.
`eval/<eco>/scale.sh` runs the same two checks, correspondence with the tool and the tool's verdict on pac's answer, over thousands of goals, asking the tool afresh each time.
It covers every package in the index, or for cargo a seeded sample of 3000 crates, or the goals a file lists one per line, optionally after a pool name and a tab.
It runs `P` goals at a time (default: every core), gives each tool call `TIMEOUT` seconds (default 900), and resumes a killed run where it stopped.
Where pac has more than one search mode, `MODES` names those to run by flag: Debian's `apt-heap` and opam's `0install-order` each run beside `default` unless it says otherwise.

```sh
eval/alpine/scale.sh _build/default/src/main.exe /tmp/scale/alpine
MODES=apt-heap P=32 eval/debian/scale.sh _build/default/src/main.exe /tmp/scale/debian
eval/opam/scale.sh _build/default/src/main.exe /tmp/scale/opam-test <(ls repos/opam-repository/packages | sed 's/^/--with-test /')
python3 eval/cargo/scale.py targets 20260923 150 > /tmp/pools.txt && eval/cargo/scale.sh _build/default/src/main.exe /tmp/scale/cargo /tmp/pools.txt
node eval/npm/goals.js repos/npm targeted > /tmp/ranges.txt && eval/npm/scale.sh _build/default/src/main.exe /tmp/scale/npm /tmp/ranges.txt
```

Keep the run directory outside the source tree, which dune scans.
It gets one line per goal and mode in `results.txt`, `goal= mode= pac= tool= corr= valid= oo= to= wall=`, and each goal's raw answers under `out/`.
Some ecosystems add fields: opam's `pin` and `mccs`, npm's `closed`, and cargo's `kept` and `identical`.
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

npm's goals are split further by whether they are closed: whether neither side asked for a name the snapshot lacks.
`eval/cargo/features.py` also compares the feature set of each crate in pac's answer with `cargo metadata`'s.
It is not part of the scale run because it downloads crate sources.

*Programmed with [Claude Code](https://claude.ai/code)*
