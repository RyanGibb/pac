# Running the evaluation on a remote machine

The solves in `eval/` are larger than a laptop comfortably holds.  Two
steps in particular want a big machine:

- `dune build @axioms`, which runs `Print Assumptions` over the whole
  development.  This is the memory-hungry step, and on a 16 G machine it
  is liable to be OOM-killed -- silently, since the killer takes the
  shell with it and leaves an empty log.
- the archive-scale sweeps, where a frontend is run across an entire
  index rather than the curated query list.

Nothing here is required to build `pac` or to run the cram tests; a
laptop is fine for those.

## Setting a machine up

    opam switch create . ocaml-base-compiler.5.4.0 --no-install -y
    opam repo add coq-released https://coq.inria.fr/opam/released --rank 2
    opam install . --deps-only -y
    dune build

`rocq-stdlib.9.2.0` comes from `coq-released` rather than the default
repository, whose index stops at 9.1.0 even though `rocq-core` 9.2.0 is
there; without that repository the install fails with "Package
rocq-stdlib has no version 9.2.0".

`pac.opam` is the dependency list.  Do not maintain a second one by hand
-- an earlier version of this file did, and it drifted.

On a machine without a C toolchain on `PATH` (`cc`, `ld`, `as`,
`pkg-config`, `m4`, `unzip`), install one into a profile of its own
rather than the user's, and export `CPATH`, `LIBRARY_PATH` and
`PKG_CONFIG_PATH` at it -- that is how `zarith` finds `gmp`.  `opam
option depext=false` stops opam trying to install system packages it
cannot see are already present; left interactive it silently picks
"abort" and exits 0, so the failure is invisible unless the log is read.

## Getting the repository snapshots there

`repos/` holds the pinned index snapshots every baseline in `eval/` is
taken against.  `eval/SNAPSHOTS` records their identities.

**Never re-fetch them with `scripts/fetch-repos.sh`.**  It pins nothing,
so a fresh fetch gets whatever upstream holds today and invalidates every
recorded baseline.

Those that are git repositories are best re-created from their pinned
commit rather than copied, which is both faster and safer -- git content
is hash-addressed, so checking out the recorded SHA is byte-identical by
construction, where a file copy is only as good as the copy:

    git init -q && git remote add origin <upstream>
    git fetch --depth 1 -q origin <sha from eval/SNAPSHOTS>
    git checkout -q FETCH_HEAD

The npm packument snapshot has no upstream of its own and must be copied.
Compress in transit (`rsync -az`): it is JSON, and the link rather than
the CPU is the bottleneck -- roughly 17x here.

## Verifying a snapshot

Check the working tree, not just the commit:

    git -C repos/<snapshot> rev-parse HEAD      # against eval/SNAPSHOTS
    git -C repos/<snapshot> status --porcelain  # must be empty

The second line is the one that matters.  A machine here once returned
from a RAID controller fault that had **zeroed files on disk**, and
nothing reported an error: `repos/opam-repository` still had all 4638
package directories and a matching `HEAD`, while 19031 of its `opam`
files were empty.  A solve against it would have answered, and answered
wrongly.  `HEAD` is metadata and survives what the working tree does not.

A quick sweep for the same class of damage:

    find repos _opam -type f -size 0 | wc -l

## A vendored checkout must live outside the tree

If `pubgrub` is pinned to a local checkout, keep that checkout outside
the `pac` directory.  Inside it, dune scans it, finds a `pubgrub` package
with no stanzas attached, and refuses to build.  Pinning the published
repository (which `pac.opam.template` does) avoids the question.

## Running a long job

Detach it and poll the log rather than holding a session open:

    nohup bash -c 'source env.sh; dune build @axioms' > axioms.log 2>&1 &
