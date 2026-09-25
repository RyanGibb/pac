# Running the evaluation

There are three levels: the unit tests, a regression set of a few dozen queries per ecosystem, and runs at scale over thousands.

## Unit tests

```sh
dune test                            # everything in test/, plus lib/<eco>/test_*.ml
dune test test/frontends/debian.t    # one frontend
dune build @axioms                   # Print Assumptions over scripts/check-axioms.sh; peaks near 8 GB
```

## Setup

Recorded answers hold only against the index snapshots listed in `eval/SNAPSHOTS`.
`scripts/fetch-repos.sh` pins nothing, so copy `repos/` or check out those commits rather than fetching afresh; `scale.sh` refuses a `repos/` that doesn't match.

The tools are pinned by `nix/flake.lock`. Run the harness inside:

```sh
nix develop ./nix
```

Build pac with opam as usual. Each `setup.sh` (and `eval/cargo/run_query.py`) refuses a tool at any other version.
Run Alpine as an ordinary user, not root. opam refuses to run with `ocamlc` on `PATH`.

## The harness

```sh
eval/<eco>/scale.sh [--regress | --record] <pac-exe> <run-dir> [queries-file]
```

Each query is checked twice: does pac answer as the tool does, and does the tool accept pac's answer (`eval/<eco>/valid.sh`)?
Keep the run directory outside the source tree. A killed run resumes where it stopped.

- `P`: queries at a time (default: every core).
- `TIMEOUT`: seconds per call (default 900).
- `MODES`: pac search modes to run. Default `default apt-heap` for Debian, `default 0install-order` for opam, `default` elsewhere.

The run ends with a line per mode, such as `default: 62 queries, exact 46/60, valid 60/60`: exact answers of those the tool answered, valid answers of those checked.
Exact compares names for Debian and Alpine, name and version for opam, and edges too for cargo and npm.

## Validity check

pac's answer is installed as the tool's own state with only the goal requested; the tool must then find nothing to do.
A set that is a resolution but has a cycle in its install order gets `CYCLIC` (Debian and opam).

`controls.sh` runs the check on small hand-written answers, each of which must get the verdict it names (every ecosystem but cargo; npm takes `PORT`):

```sh
eval/debian/controls.sh /tmp/controls/debian
```

## Regression set

`eval/<eco>/queries.txt` lists the queries, one per line in the tool's command-line syntax, flags included (cargo's name a crate).
`eval/<eco>/baseline/` holds the tool's answer to each, or an empty `.absent` file where it refused.
npm's queries are pinned to the versions in `baseline/roots.txt`.

`--regress` compares against the recorded answers instead of asking the tool; the validity check still runs.

```sh
eval/debian/scale.sh --regress _build/default/bin/main.exe /tmp/regress/debian
eval/opam/scale.sh --regress _build/default/bin/main.exe /tmp/regress/opam
eval/alpine/scale.sh --regress _build/default/bin/main.exe /tmp/regress/alpine
eval/cargo/scale.sh --regress _build/default/bin/main.exe /tmp/regress/cargo
eval/npm/scale.sh --regress _build/default/bin/main.exe /tmp/regress/npm
```

`--record` asks the tool and writes its answers into `baseline/`. Record all ecosystems or none.
Cargo records nothing and refuses `--record`; its `--regress` asks cargo afresh.

```sh
eval/debian/scale.sh --record _build/default/bin/main.exe /tmp/record/debian
```

## At scale

With neither flag, `scale.sh` asks the tool over every package in the index (cargo: a seeded sample of 3000 crates), or over a queries file, one per line, optionally prefixed by a pool name and a tab.

```sh
eval/alpine/scale.sh _build/default/bin/main.exe /tmp/scale/alpine
MODES=apt-heap P=32 eval/debian/scale.sh _build/default/bin/main.exe /tmp/scale/debian
eval/opam/scale.sh _build/default/bin/main.exe /tmp/scale/opam-test <(ls repos/opam-repository/packages | sed 's/^/--with-test /')
python3 eval/cargo/scale.py targets 20260923 150 > /tmp/pools.txt && eval/cargo/scale.sh _build/default/bin/main.exe /tmp/scale/cargo /tmp/pools.txt
node eval/npm/queries.js repos/npm targeted > /tmp/ranges.txt && eval/npm/scale.sh _build/default/bin/main.exe /tmp/scale/npm /tmp/ranges.txt
```

## Results

The run directory gets `results.txt`, one line per query and mode, and raw answers under `out/`:

```
query= mode= pac= tool= corr= valid= oo= to= wall=
```

`oo` and `to` count packages only in ours and only in the tool's. Extra fields: opam `pin` and `mccs`; npm `twall` (the tool's wall time, `-` under `--regress`), `closed`, `nodes`, `edges`; cargo `kept`, `identical`.

`eval/<eco>/triage.py <run-dir>` sorts queries into classes, per mode and per pool:

| class | meaning |
|---|---|
| `exact` | same set, and the tool accepts ours |
| `preference-gap` | sets differ, and the tool accepts ours |
| `error` | sets differ, and the tool rejects ours |
| `exact-invalid` | the tool rejects an answer matching its own: suspect the check |
| `post-resolution` | ours is a resolution the tool cannot install (install-order cycle; opam, Debian) |
| `instance-gap` | the tool's answer is not a resolution of our instance |
| `tool-declines` | we answer, the tool refuses |
| `both-refuse` | neither answers |
| `pac-timeout`, `pac-crash`, `tool-timeout` | a side gave no verdict |
| `unchecked` | we answer, but the check could not run |
| `unrecorded` | `--regress` found no recorded answer |

## Ecosystem notes

- npm: queries are also split by `closed`, whether neither side asked for a name the snapshot lacks. Edges are scored with `edges.py --peer-parent`; set `NORM=` to score them as npm's lock records them. `FILL=1` runs `scale.sh` as the pass that closes the snapshot, fetching each miss into the run's farm.
- `eval/alpine/pin.sh <run-dir>` and `eval/npm/pin.sh <run-dir>` re-ask a run's divergent queries with the tool's picks forced, separating preference gaps from instance gaps.
- `eval/cargo/features.py <crate>...` compares feature sets with `cargo metadata`, with `sparse_proxy.py` serving on `PORT` (default 8991). It is not part of the scale run because it downloads crate sources.
