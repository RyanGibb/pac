# pac on a remote compute box

Runbook for the remote compute box.  Set up 2026-09-20; the alpine
reproduction did not finish, see "Unfinished" at the bottom.

## The box

`iphito.caelum.ci.dev` = `hippo.freumh.org` = 128.232.124.251.  NixOS,
256 cores, 1 TB RAM, `/` 439 G with 393 G free.  Passwordless SSH as
`ryan`.  (`elephant` is a *different* machine -- do not use it for this.)

Everything pac lives under `~/pac`.  Nothing outside it was touched except
`~/.opam` (the opam root) and a transient `nix profile` entry in
`~/.nix-profile` that was removed again, so the home profile is as it was.

## Getting a build

    ssh iphito.caelum.ci.dev
    source ~/pac/env.sh
    cd ~/pac && dune build

`env.sh` is written by hand and is *not* part of the repo, so a re-sync
from the workstation must not delete it -- see "Syncing" below.

## Why nix is pinned by revision

The box's `nixpkgs` flake registry points at rev `4e92bbc` (2026-04-06),
several months behind the workstation's `5dfba62` (2026-08-31).  Plain
`nixpkgs#foo` there therefore resolves to older tools than the baselines
were taken with: opam 2.4.1 rather than 2.5.2, and the preinstalled
`cargo` 1.91.0 / `npm` 10.9.7 rather than 1.97.0 / 11.17.0.  Every tool
whose version a recorded baseline depends on is pinned explicitly:

    N=github:NixOS/nixpkgs/5dfba6236110080a54247d6460bc2ff5dda939cc

`apk-tools` and `apt` built from `$N` come out at the *same store paths* as
on the workstation, so those two are bit-identical binaries, not merely
equal version strings:

    /nix/store/x6vpmm9r4wkl3a4h76hf4pjpn0bnfq50-apk-tools-3.0.5/bin/apk
    /nix/store/9ij684h9xx6gnnhl37jplaksycwi1bgl-apt-3.3.0/bin/apt-get

opam 2.5.2 is *not* in `$N` (which has 2.5.1); the workstation's copy comes
from an overlay in its NixOS config.  It was copied over wholesale, which
works because ryan is a trusted nix user on the box:

    nix copy --to ssh://iphito.caelum.ci.dev \
      /nix/store/h0m8cfjivx3iv7sb4wgqmd5jjl402hki-opam-2.5.2

## The toolchain profile

The box has no `cc`, `ld`, `as`, `pkg-config`, `m4`, `unzip` or `bwrap` on
PATH, and its home-manager profile already owns `make`, so adding these to
`~/.nix-profile` collides.  They live in a separate profile instead, which
keeps ryan's own profile untouched:

    P=$HOME/pac/.nixenv
    nix profile add --profile $P --priority 3 /nix/store/h0m8cf...-opam-2.5.2
    nix profile add --profile $P --priority 4 $N#gcc
    nix profile add --profile $P --priority 6 $N#binutils
    for pkg in gnumake pkg-config m4 patch unzip bubblewrap gnutar gzip \
               diffutils findutils; do
      nix profile add --profile $P --priority 7 $N#$pkg
    done
    nix profile add --profile $P --priority 7 $N#gmp.dev

The priorities matter: `gcc` and `binutils` both ship `ld`/`ar` and a
same-priority add aborts the whole transaction.  Add them one at a time --
a single `nix profile add` with several conflicting attrs installs nothing
and still exits 0.

`env.sh` then puts `$P/bin` on PATH and sets `CPATH`, `LIBRARY_PATH` and
`PKG_CONFIG_PATH` at `$P`, which is how zarith finds gmp.

## The opam switch

    source ~/pac/env.sh
    opam init --bare --no-setup -y
    cd ~/pac && opam switch create . ocaml-base-compiler.5.4.0 --no-install -y
    opam repo add coq-released https://coq.inria.fr/opam/released --rank 2
    opam option depext=false
    opam pin add -n -y pubgrub ~/pac/vendor/ocaml-pubgrub
    OPAMJOBS=32 opam install -y dune.3.23.1 rocq-stdlib.9.2.0 coq-core.9.2.0 \
      cmdliner.2.1.1 zarith.1.14 pubgrub

Two things that are easy to miss:

`rocq-stdlib.9.2.0` is not on opam.ocaml.org -- its index stops at 9.1.0
even though `rocq-core` 9.2.0 is there.  It comes from `coq-released`,
which the workstation's pac switch also carries at rank 2.  Without that
repo the install fails with "Package rocq-stdlib has no version 9.2.0".

`opam option depext=false` is needed because opam asks to `nix-build` gmp
and pkg-config as system packages and cannot see that `.nixenv` already
supplies them.  Left interactive it picks "abort" and exits 0, so the
failure is silent unless you read the log.

`pubgrub` is a `pin-depends` on `git+file:///home/ryan/projects/ocaml-pubgrub`,
a path that does not exist on the box.  The repo was rsync'd to
`~/pac/vendor/ocaml-pubgrub` and pinned from there; it sits at the same
commit as the workstation, `533ebc3`.

## Syncing from the workstation

`main` is ahead of both git remotes and unpushed, so the box gets a copy of
the working tree, never a clone.  `repos/` is separate and must never be
re-fetched -- `scripts/fetch-repos.sh` pins nothing, so a fresh fetch gets
different data and invalidates every baseline.

    rsync -a --exclude '_build/' --exclude '_opam/' --exclude 'repos/' \
      --exclude 'notes/' --exclude '__pycache__/' \
      ~/projects/pac/ iphito.caelum.ci.dev:pac/

    rsync -az --partial --info=progress2 \
      ~/projects/pac/repos/ iphito.caelum.ci.dev:pac/repos/

**Use `-z`.**  Without it the crates.io-index copy ran at 1.8 MB/s (~70
min); with it, 29.8 MB/s -- the index is JSON and the link, not the CPU,
is the bottleneck.  Roughly 17x.

**Do not pass `--delete`** on a re-sync without also excluding `env.sh`,
`.nixenv/`, `vendor/` and `repos/`: those are not in the workstation tree
and `--delete` would remove the whole toolchain.

## Snapshot verification

`repos/` transferred complete (rsync exit 0, 7.5 G, 354778 files).  Of the
five identities in `eval/SNAPSHOTS`, only alpine was checked before the box
became unreachable:

    repos/alpine/APKINDEX  5473e1e9...c6ad7383  matches

The workstation side was re-verified in full and all five still match what
`eval/SNAPSHOTS` records, so any remote mismatch would be a transfer fault
rather than local drift.  The remaining four still need checking on the box:

    cd ~/pac
    git -C repos/opam-repository rev-parse HEAD   # 0bb592dd...ebd7375
    git -C repos/crates.io-index rev-parse HEAD   # 26195c27...cbc13fe
    git -C repos/opam-repository status --porcelain   # must be empty
    git -C repos/crates.io-index status --porcelain   # must be empty
    sha256sum repos/debian/Packages repos/alpine/APKINDEX
    cd repos/npm && find . -type f -printf '%P\n' | LC_ALL=C sort | tr '\n' '\0' \
      | xargs -0 sha256sum | awk '{print $1}' | LC_ALL=C sort | sha256sum

## Running a sweep

`eval/*/setup.sh` falls back to `nix build nixpkgs#apk-tools` when `APK` is
unset, which on this box resolves to the *older* registry and the wrong
version.  `env.sh` exports `APK` and `APT` at the pinned store paths to
stop that happening; never run a sweep without sourcing it.

    source ~/pac/env.sh
    cd ~/pac
    bash eval/alpine/setup.sh          # prints the `export APK=` it resolved
    bash eval/alpine/sweep.sh _build/default/src/main.exe iphito

Expected, and what the workstation produces: `TOTAL exact=58 ours-only=0
apk-only=0`.  A workstation reference run with per-goal counts is worth
keeping around to diff against, since the total alone hides a compensating
pair of differences.

## Unfinished

Two things are outstanding, both blocked on the same event.

`rocq-stdlib.9.2.0` failed to compile at `make -j 32`; everything else in
the dependency set installed (dune, cmdliner, zarith, pubgrub, rocq-runtime,
coq-core, rocq-core).  Immediately afterwards opam could not clean up its
build tree -- `unlink` on
`_opam/.opam-switch/build/cmdliner.2.1.1/src/cmdliner.mllib` returned
`Input/output error` -- and within a minute sshd stopped completing key
exchange from this host: TCP to port 22 is accepted and the host answers
ICMP, but every connection is reset at `kex_exchange_identification`.

So `dune build` has never run on the box, and the alpine sweep has never
run there either.  Whether the rocq-stdlib failure is a real build problem
or the first symptom of whatever the `Input/output error` is, is exactly
what to work out first next time.  Check `dmesg` for disk errors and
whether `/` went read-only before assuming the build recipe is wrong.  The
`-j 32` is also worth dropping to `-j 8` on a retry to rule out a
parallelism-sensitive build.

On the SSH refusal, three explanations were considered.

A rate limit tripped by this setup -- it ran an rsync plus a good many
concurrent `ssh` invocations, which can hit sshd's `MaxStartups` or
fail2ban.  Prefer an SSH `ControlMaster` next time regardless.

The lab firewall (128.232/16 is the Computer Lab) reacting to a sustained
30 MB/s transfer.  Against it: a firewall cannot produce an EIO on `unlink`
inside `~/pac`, and that came first.

The root filesystem faulting, which is the one that fits everything.  The
errors just before the box went quiet were `Input/output error` on `unlink`
under `~/pac/_opam`, and then on *exec* of binaries out of `/nix/store`
(`du`, `git`, `wc`, `sha256sum`, and `id` from home-manager's session vars
all failed the same way).  EIO on reading executables off `/dev/sda2` is a
block-device read error; a full disk gives ENOSPC and memory pressure gives
ENOMEM, so neither of those fits.  A root fs that has erred and remounted
read-only would also stop sshd completing a handshake, which is what is
seen: TCP to port 22 completes, the server then sends *zero* bytes -- no
version banner at all -- and resets.

Check the console or IPMI, `dmesg` for `sda` errors, and whether `/` is
read-only, before assuming the rocq-stdlib build recipe above is at fault.


## 2026-09-21: the RAID controller firmware bug, and what it cost

The box came back after a RAID controller firmware fix.  It had not merely
been unreachable: the fault had **zeroed files on disk**, and nothing
errored to say so.

    _opam                    20717 zero-byte files, `coqc` among them
    repos/npm                  888 zero-byte packuments
    repos/opam-repository    19031 empty package files
    alpine, crates, debian       clean

The dangerous part is the silence.  `repos/opam-repository` still had all
4638 package directories and a `git rev-parse HEAD` that matched; only
`git status` showed 19031 modified files, each an emptied `opam` file.  A
solve against it would have answered, and answered wrongly.  **Verify the
four snapshot identities after any hardware event**, and prefer
`git status --porcelain` over a HEAD comparison -- HEAD is metadata and
survives what the working tree does not.

### Re-fetch a git snapshot rather than rsync it

`repos/opam-repository` is a depth-1 shallow clone at a pinned commit, so
the box can fetch that one commit itself in seconds, where pushing 168 M of
small files over a home uplink took many minutes:

    cd ~/pac/repos && mkdir opam-new && cd opam-new
    git init -q
    git remote add origin https://github.com/ocaml/opam-repository
    git fetch --depth 1 -q origin 0bb592dddd707b91459622e5b5f600ffdebd7375
    git checkout -q FETCH_HEAD

This is also *safer* than rsync: git content is hash-addressed, so
checking out the pinned SHA is byte-identical by construction rather than
trusted to a file copy -- which is exactly what had failed.  The runbook's
"never re-fetch" rule is about `fetch-repos.sh` pinning nothing; pinning
the exact SHA is not that.

`repos/npm` has no upstream of its own and must still come over the wire.

### vendor/ must live outside the dune workspace

`~/pac/vendor/ocaml-pubgrub` is inside the tree, so dune scans it, finds a
`pubgrub` package with no stanzas, and refuses to build.  It now lives at
`~/pac-vendor/ocaml-pubgrub`; the opam pin points there.  On the
workstation the question does not arise, the repo being a sibling of
`pac` rather than a child.

### The dependency list is `pac.opam`, not this file

The install list further up was hand-maintained and had drifted: it was
missing `yojson` and `opam-file-format`, without which the build fails at
`src/npm`, `src/cargo` and `src/opam`.  `dune-project` now declares
`cmdliner`, `yojson` and `opam-file-format`, so

    opam install . --deps-only -y

is the whole of it and this file should not list packages again.
`zarith` is not declared: it arrives through `coq-core`.

### Checking the proofs here

`dune build @axioms` runs `scripts/check-axioms.sh`, which is the audit of
the named theorems.  It is worth running here rather than on a laptop:
`Print Assumptions` over the whole development is the memory-hungry step,
and a 16 G machine is where it gets OOM-killed -- silently, taking the
editing session with it.
