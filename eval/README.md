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

Build pac with opam as usual. Each `setup.sh` (and cargo's `scale.sh`) refuses a tool at any other version.
Run Alpine as an ordinary user, not root. opam refuses to run with `ocamlc` on `PATH`.

## The harness

```sh
eval/<eco>/scale.sh [--regress | --record] <pac-exe> <run-dir> [queries-file]
```

Each query is asked of pac in each mode, and of the tool once. Two questions follow: does pac answer as the tool does, and does the tool accept pac's answer (`eval/check.sh`)?
Keep the run directory outside the source tree. A killed run resumes where it stopped, and refuses to resume with another pac, other parameters or another queries file.

- `P`: queries at a time (default: every core).
- `TIMEOUT`: seconds per call (default 900).
- `MODES`: the orders pac decides in, each passed as `--order`: `tool`, the tool's own, and `pubgrub`, PubGrub's. Default `tool pubgrub`.

The run ends with a line per mode, such as `tool: 62 queries, exact 60/60, valid 60/60, minimal 58/60`: exact answers of those the tool answered, valid answers of those checked, and minimal answers of the valid.
Answers the check could not run on (`unchecked`), install-order cycles (`cyclic`), the tool's own errors and unrecorded baselines are counted apart, and excluded from those fractions.
A query whose worker died is named as missing, and the run then exits non-zero.
Exact compares names for Debian and Alpine, name and version for opam, and edges too for cargo and npm.

## pac's output

Every frontend prints the same shape.
A `root` line comes first where the query names a root package (cargo, npm).
An answer is a `packages (N):` line and N rows under it, each `name version` indented two spaces (Debian's name carries its architecture, `name:arch`; cargo's row ends in its features, `[f,g]`).
Sections a flag asks for follow in the same shape: opam's `system packages`, cargo's `parent edges` (`--print-parents`), npm's `node_modules` (`--tree`).
Then `encoded solution: N core nodes (K lookups)`.
Where no answer exists, an `unsatisfiable:` line and PubGrub's explanation take the place of all of these.
Either way the output ends in `loaded: N names, M versions` (with a frontend's own counts after), `parser dropped N declarations` where the parser dropped any, and the `parse` and `solve` times.
`eval/answer.sh` is the one reader of the rows.

The exit status, as `pac --help` lists it:

| status | meaning | `pac=` |
|---|---|---|
| 0 | an answer | `ok` |
| 1 | no answer exists | `unsat` |
| 2 | the query or an input is refused, a command-line error included | `refuse` |
| 3 | an index, a file or the registry cannot be read | `io-error` |
| 124 | timeout(1) killed pac | `timeout` |
| other | an internal error | `crash` |

A refusal or a read error prints `error:` and its reason on stderr, and nothing on stdout but cargo's and npm's `root` line.

## Validity check

```sh
eval/check.sh <eco> <answer> <out-dir> <query...>
```

The answer is pac's output; the query is what pac was asked, in the words pac took (cargo's is the `Cargo.toml` pac read; npm's may be a `package.json`).
The check writes its files under the out directory and ends in two verdicts:

- `valid=`: `VALID` if the tool takes the answer as consistent, installed as it stands: every package's dependencies met (packages nothing needs included), no conflict, one version of a name where the tool allows one; `INVALID` if not; `CYCLIC` for a resolution with a cycle in its install order (Debian and opam); `ERR` if the check could not run to a verdict (a timeout, a dead shim or proxy, a broken tool root).
- `minimal=`: `yes` if the tool, left to settle the answer for the query alone, would keep it as it stands; `no` if it would remove or swap something. Only for `VALID` answers; the core calculus asks a resolution for no minimality, so a non-minimal answer is never an error.

| ecosystem | valid | minimal |
|---|---|---|
| Debian | `apt-get check` and `install <query>` on the answer as the dpkg status | `apt-get autoremove`, the query the only root |
| Alpine | `apk fix` with the whole answer and the query as the world, and apk's rule for a bare provides without `k:` (its owner must be named by the query or by a package of the answer) | `apk fix` with the query alone as the world |
| opam | `opam install <query>` and `upgrade --fixup` on the answer as the switch state | the same fixup told to remove what it can |
| cargo | `cargo update --locked` keeps our `Cargo.lock`, or its unlocked repair only drops packages the root does not reach, whose requirements the answer meets | `cargo update --locked` keeps it |
| npm | `npm ci` accepts our lock, a relock changes nothing but pruning what nothing reaches, and every edge lands on the package its manifest names | the relock changes nothing |

`controls.sh` runs the check on small hand-written answers, each of which must get the verdicts it names; npm takes `PORT` for its shim, and cargo for its proxy:

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
Only an answer or a refusal is recorded; a tool that fails otherwise, or times out, leaves the baseline as it was, with a warning.
Cargo records nothing and refuses `--record`; its `--regress` asks cargo afresh.

```sh
eval/debian/scale.sh --record _build/default/bin/main.exe /tmp/record/debian
```

## At scale

With neither flag, `scale.sh` asks the tool over every package in the index (cargo: a seeded sample of 3000 crates), or over a queries file, one per line, optionally prefixed by a pool name and a tab.

```sh
MODES=pubgrub eval/alpine/scale.sh _build/default/bin/main.exe /tmp/scale/alpine
MODES=tool P=32 eval/debian/scale.sh _build/default/bin/main.exe /tmp/scale/debian
eval/opam/scale.sh _build/default/bin/main.exe /tmp/scale/opam-test <(ls repos/opam-repository/packages | sed 's/^/--with-test /')
python3 eval/cargo/scale.py targets 20260923 150 > /tmp/pools.txt && eval/cargo/scale.sh _build/default/bin/main.exe /tmp/scale/cargo /tmp/pools.txt
node eval/npm/queries.js repos/npm targeted > /tmp/ranges.txt && eval/npm/scale.sh _build/default/bin/main.exe /tmp/scale/npm /tmp/ranges.txt
```

## Results

The run directory gets `results.txt`, one line per query and mode, and raw answers under `out/`, `<key>.<mode>.*` for pac's and the check's, `<key>.*` for the tool's:

```
query= mode= pac= tool= corr= valid= minimal= oo= to= wall= pin=
```

`pac` is pac's exit status, as the table above names it.
`tool` is `ok`, `refuse` (the tool says the query has no answer), `error` (it failed otherwise), `timeout` or, under `--regress`, `unrecorded`.
`oo` and `to` count packages only in ours and only in the tool's.
`pin` is pac asked for the tool's own answer, where the tool answered (Alpine and opam; `-` elsewhere): `ok`, `unsat`, or no verdict.
Extra fields: opam `mccs`; npm `twall` (the tool's wall time, `-` under `--regress`), `closed`, `nodes`, `edges`; cargo `kept`, `identical`.

`eval/<eco>/triage.py <run-dir>` sorts queries into classes, per mode and per pool, and shows `minimal` apart:

| class | meaning |
|---|---|
| `exact` | same set, and the tool accepts ours |
| `preference-gap` | sets differ, and the tool accepts ours; pac asked for the tool's answer gives one, where a pin ran |
| `instance-gap` | the tool's answer is not a resolution of our instance: pac refuses it when pinned |
| `unconfirmed` | we refuse, the tool answers, and no pin says whether its answer is a resolution of our instance |
| `error` | the tool rejects ours, whatever the tool's own answer |
| `exact-invalid` | the tool rejects an answer matching its own: suspect the check |
| `post-resolution` | ours is a resolution the tool cannot install (install-order cycle; opam, Debian) |
| `tool-declines` | we answer, the tool refuses, and it accepts ours |
| `both-refuse` | neither answers |
| `pac-timeout`, `pac-crash`, `pac-refuse`, `pac-io-error`, `tool-timeout`, `tool-error` | a side gave no verdict |
| `unchecked` | we answer, but the check, or the pin that would say which gap, could not run |
| `unrecorded` | `--regress` found no recorded answer |

## Ecosystem notes

- npm: queries are also split by `closed`, whether neither side asked for a name the snapshot lacks. Edges are scored with `edges.py --peer-parent`; set `NORM=` to score them as npm's lock records them. `FILL=1` runs `scale.sh` as the pass that closes the snapshot, fetching each miss into the run's farm.
- `eval/alpine/pin.sh <run-dir>` counts a run's divergent queries pac answers exactly as apk does once every package of apk's answer is in the world. `eval/npm/pin.sh <run-dir>` re-asks a run's divergent queries with npm's picks forced. Both separate preference gaps from instance gaps.
- `eval/cargo/features.py <crate>...` compares feature sets with `cargo metadata`, with `sparse_proxy.py` serving on `PORT` (default 8991). It is not part of the scale run because it downloads crate sources.
