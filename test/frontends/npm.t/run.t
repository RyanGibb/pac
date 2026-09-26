untimed (../untimed.sh) drops the timings from pac's output and keeps its
exit status:

  $ . ../untimed.sh

A mandatory peer dependency is installed beside its declarer: app depends
on plugin and widget but on neither core nor theme.  plugin's peer on core
is not optional, so core arrives as app's own sibling of plugin; widget's
peer on theme is optional, so theme is not installed at all.  core 2.1.0
declares os win32 and is still the newest ^2 -- resolution does not read
os -- so it is the one installed, although npm then refuses this tree
off win32 (EBADPLATFORM).  lodash is an alias
directory holding the util-lib package, and tester is a devDependency, so
it participates only from the root.

The root's own peers get the same treatment, from the calculus rather than
from the driver: nothing installs the root, so the edges that install its
peers leave the root's own granular node instead of a parent's directory
node.  app's mandatory peer on runtime is installed at 1.1.0, the newest
^1, while its optional peer on polyfill is not installed even though
polyfill is in the cache.

  $ untimed ../../../bin/main.exe npm --offline --cache . --tree ./app/package.json
  root app 1.0.0
  packages (7):
    app 1.0.0
    core 2.1.0
    util-lib 1.2.0 at lodash
    plugin 1.0.0
    runtime 1.1.0
    tester 1.0.0
    widget 1.0.0
  node_modules (6):
    app 1.0.0 <- core 2.1.0
    app 1.0.0 <- util-lib 1.2.0 at lodash
    app 1.0.0 <- plugin 1.0.0
    app 1.0.0 <- runtime 1.1.0
    app 1.0.0 <- tester 1.0.0
    app 1.0.0 <- widget 1.0.0
  encoded solution: 13 core nodes (18 lookups)
  loaded: 9 names, 15 versions, 0 packuments fetched

A name the root both depends on and declares a peer for is a dependency
only, as it is for any package: npm keeps one edge per name and a
dependency replaces the peer.  dual-app depends on dual >=1.1.0 and
declares a peer on dual <=1.2.0, and 1.3.0 installs, as the dependency
alone picks it.  shim is the same pair with the peer optional, and shim ^1
lands on 1.1.0.

  $ untimed ../../../bin/main.exe npm --offline --cache . --tree ./dual-app/package.json
  root dual-app 1.0.0
  packages (3):
    dual 1.3.0
    dual-app 1.0.0
    shim 1.1.0
  node_modules (2):
    dual-app 1.0.0 <- dual 1.3.0
    dual-app 1.0.0 <- shim 1.1.0
  encoded solution: 5 core nodes (7 lookups)
  loaded: 3 names, 7 versions, 0 packuments fetched

Prerelease admission is scoped to a single comparator set rather than to
the range that holds it.  codec publishes 1.0.0 and the newer 1.0.1-alpha,
and ^1 names no prerelease, so 1.0.0 is the newest candidate.  parser
publishes nothing but prereleases: ^1.0.0-alpha names one at 1.0.0's core
and so admits 1.0.0-alpha.1, while 2.0.0-beta.1 is refused even though the
alternative >=1.5.0 <3.0.0 orders it in range, because that set names no
prerelease and the set that does is the other alternative.

  $ untimed ../../../bin/main.exe npm --offline --cache . ./beta-app/package.json
  root beta-app 1.0.0
  packages (3):
    beta-app 1.0.0
    codec 1.0.0
    parser 1.0.0-alpha.1
  encoded solution: 5 core nodes (5 lookups)
  loaded: 3 names, 5 versions, 0 packuments fetched

The literal range * is the exception, and so is an empty range, which npm
reads as *: npm-pick-manifest takes dist-tags.latest for it even when that
is a prerelease, provided it is not deprecated and the host can run it.
pre-only publishes nothing but prereleases, and its latest 1.0.0-beta.2 is
installed rather than nothing; pre-ahead's latest 1.0.0-alpha.0 wins over
the release 0.1.0.  pre-depr's latest prerelease is deprecated and
pre-engine's wants node >=99, so both fall back to 0.1.0, the release *
admits without the exception.

  $ untimed ../../../bin/main.exe npm --offline --cache . --node-version v24.19.0 --npm-version 11.17.0 ./star-app/package.json
  root star-app 1.0.0
  packages (5):
    pre-ahead 1.0.0-alpha.0
    pre-depr 0.1.0
    pre-engine 0.1.0
    pre-only 1.0.0-beta.2
    star-app 1.0.0
  encoded solution: 9 core nodes (10 lookups)
  loaded: 5 names, 9 versions, 0 packuments fetched

npm's semver reads versions loosely, and a prerelease may drop its hyphen:
1.0.1rc1 is 1.0.1-rc1.  loose tags it latest, but ^1.0.0 names no
prerelease, so 1.0.0 is installed.

  $ untimed ../../../bin/main.exe npm --offline --cache . ./loose-app/package.json
  root loose-app 1.0.0
  packages (2):
    loose 1.0.0
    loose-app 1.0.0
  encoded solution: 3 core nodes (3 lookups)
  loaded: 2 names, 3 versions, 0 packuments fetched

An optionalDependencies entry is an ordinary dependency, abandoned
only where npm abandons it: when its manifest cannot be fetched.  opt-app
lists three.  gadget ^1 resolves and is installed exactly as a plain
dependency would be -- and it also demonstrates the override rule, since
opt-app's dependencies name gadget ^9, which no version satisfies: the
optional entry replaces that dependency rather than standing beside it.
native ^9 names a package that exists at 1.0.0 only, so the range matches
nothing and the dependency goes; absent ^1 names a package with no
packument at
all, the other half of the same failure.  native-core is in the cache and
native 1.0.0 depends on it, but nothing else does, so dropping the
dependency
takes it with it: transitivity needs no separate rule.

  $ untimed ../../../bin/main.exe npm --offline --cache . --tree ./opt-app/package.json
  root opt-app 1.0.0
  packages (3):
    gadget 1.0.0
    opt-app 1.0.0
    theme 1.0.0
  node_modules (2):
    opt-app 1.0.0 <- gadget 1.0.0
    opt-app 1.0.0 <- theme 1.0.0
  encoded solution: 5 core nodes (5 lookups)
  loaded: 5 names, 5 versions, 0 packuments fetched, 2 of 3 optionalDependencies (target, range) pairs dropped

--omit=optional drops the class outright, without asking the registry
anything: gadget goes even though it resolves, and no availability check
runs, so there is no optionalDependencies line and neither gadget nor
native is loaded at all.

  $ untimed ../../../bin/main.exe npm --offline --cache . --tree --omit=optional ./opt-app/package.json
  root opt-app 1.0.0
  packages (2):
    opt-app 1.0.0
    theme 1.0.0
  node_modules (1):
    opt-app 1.0.0 <- theme 1.0.0
  encoded solution: 3 core nodes (3 lookups)
  loaded: 2 names, 2 versions, 0 packuments fetched

--omit=dev is not the same kind of omission.  npm resolves the
devDependencies as always and leaves out only what dev edges alone reach
(calc-dep-flags.js), so they still shape what the rest gets.  omit-app
depends on taker and has holder and host as devDependencies: holder's
tok 3.0.2 is placed before taker is reached, so taker's tok stays 3.0.2
though latest is 4.0.0, and host's peer gadget goes with host.  npm
11.17.0 flags holder, host and gadget dev in its lock, and nothing else.

  $ untimed ../../../bin/main.exe npm --offline --cache . ./omit-app/package.json
  root omit-app 1.0.0
  packages (6):
    gadget 2.0.0
    holder 1.0.0
    host 1.0.0
    omit-app 1.0.0
    taker 1.0.0
    tok 3.0.2
  encoded solution: 12 core nodes (14 lookups)
  loaded: 6 names, 8 versions, 0 packuments fetched
  $ untimed ../../../bin/main.exe npm --offline --cache . --tree --omit=dev ./omit-app/package.json
  root omit-app 1.0.0
  packages (3):
    omit-app 1.0.0
    taker 1.0.0
    tok 3.0.2
  node_modules (2):
    omit-app 1.0.0 <- taker 1.0.0
    taker 1.0.0 <- tok 3.0.2
  encoded solution: 12 core nodes (14 lookups)
  loaded: 6 names, 8 versions, 0 packuments fetched

npm's third class, peer, is refused rather than ignored:

  $ ../../../bin/main.exe npm --offline --cache . --omit=peer ./omit-app/package.json 2> err
  [2]
  $ grep -- --omit err
  pac: option --omit: invalid value peer, expected either dev or optional

os, cpu and libc are not read at all: npm-pick-manifest reads none of
them, and an optional package the host cannot run stays in the lock.
nativefs publishes only 1.0.0 and only for darwin, and the host here is
linux, yet opt-plat-app's optional dependency on it stands -- and brings
native-core, which nativefs depends on and nothing else does.  This is
fsevents, the best-known optional dependency, and npm puts it in the
lockfile on linux too; dropping it here would make our answer smaller than npm's on every
platform but macOS.

  $ untimed ../../../bin/main.exe npm --offline --cache . --tree ./opt-plat-app/package.json
  root opt-plat-app 1.0.0
  packages (4):
    native-core 1.0.0
    nativefs 1.0.0
    opt-plat-app 1.0.0
    theme 1.0.0
  node_modules (3):
    nativefs 1.0.0 <- native-core 1.0.0
    opt-plat-app 1.0.0 <- nativefs 1.0.0
    opt-plat-app 1.0.0 <- theme 1.0.0
  encoded solution: 7 core nodes (7 lookups)
  loaded: 4 names, 4 versions, 0 packuments fetched, 0 of 1 optionalDependencies (target, range) pairs dropped

A non-optional dependency on the same package resolves alike, which is
what plat-app shows: the same dependency against the same cache, and
nothing about the host enters ours.  npm refuses this tree off darwin
(EBADPLATFORM), even with --package-lock-only, so this pins our reading,
not npm's answer.

  $ untimed ../../../bin/main.exe npm --offline --cache . --tree ./plat-app/package.json
  root plat-app 1.0.0
  packages (4):
    native-core 1.0.0
    nativefs 1.0.0
    plat-app 1.0.0
    theme 1.0.0
  node_modules (3):
    nativefs 1.0.0 <- native-core 1.0.0
    plat-app 1.0.0 <- nativefs 1.0.0
    plat-app 1.0.0 <- theme 1.0.0
  encoded solution: 7 core nodes (7 lookups)
  loaded: 4 names, 4 versions, 0 packuments fetched

A satisfiable optional entry that conflicts is a conflict, not a drop.
opt-peer-app depends on host, whose peer on gadget is ^2, and optionally
on gadget ^1; gadget publishes both, so the dependency's manifest is
fetchable and the dependency stands.  The two ranges fill the same directory and cannot
agree, which is npm's ERESOLVE rather than a reason to abandon the entry.

  $ untimed ../../../bin/main.exe npm --offline --cache . --tree ./opt-peer-app/package.json
  root opt-peer-app 1.0.0
  unsatisfiable:
  Because <opt-peer-app@1.0.0=>host> 1.0.0 -> <opt-peer-app@1.0.0=>gadget> 2.0.0 and opt-peer-app@1.0.0 1.0.0 -> <opt-peer-app@1.0.0=>gadget> 1.0.0, <opt-peer-app@1.0.0=>host> * or opt-peer-app@1.0.0 * is forbidden..
  And because opt-peer-app@1.0.0 1.0.0 -> <opt-peer-app@1.0.0=>host> 1.0.0 and root -> opt-peer-app@1.0.0 1.0.0, version solving failed.
  loaded: 3 names, 4 versions, 0 packuments fetched
  [1]

That the optional dependency is what fails the solve, rather than
something else in the fixture, is what --omit=optional shows: with the
dependency gone the peer
installs gadget 2.0.0 by itself.

  $ untimed ../../../bin/main.exe npm --offline --cache . --tree --omit=optional ./opt-peer-app/package.json
  root opt-peer-app 1.0.0
  packages (3):
    gadget 2.0.0
    host 1.0.0
    opt-peer-app 1.0.0
  node_modules (2):
    opt-peer-app 1.0.0 <- gadget 2.0.0
    opt-peer-app 1.0.0 <- host 1.0.0
  encoded solution: 5 core nodes (6 lookups)
  loaded: 3 names, 4 versions, 0 packuments fetched

A root override binds a peer slot too, and wins over the peer's own range
rather than being intersected with it.  ovr-peer-app depends on host and
on nothing else; host's mandatory peer on gadget is ^2, so gadget is a
directory only the peer asks for.  The root overrides gadget to 1.0.0,
which ^2 refuses, and 1.0.0 is what installs -- the override replaces a
peer dependency's range exactly as it replaces a dependency's.

  $ untimed ../../../bin/main.exe npm --offline --cache . --tree ./ovr-peer-app/package.json
  root ovr-peer-app 1.0.0
  packages (3):
    gadget 1.0.0
    host 1.0.0
    ovr-peer-app 1.0.0
  node_modules (2):
    ovr-peer-app 1.0.0 <- gadget 1.0.0
    ovr-peer-app 1.0.0 <- host 1.0.0
  encoded solution: 5 core nodes (6 lookups)
  loaded: 3 names, 4 versions, 0 packuments fetched

An override to * is no override at all: npm reads an edge's range from an
override only when its value is not * (arborist edge.js, spec), and it
reads an empty value as *.  ovr-star-app overrides tok to * and ovr-empty-app
to "", and in both holder's ^3.0.0 still binds: tok 3.0.2, not the latest
4.0.0.

  $ untimed ../../../bin/main.exe npm --offline --cache . --tree ./ovr-star-app/package.json
  root ovr-star-app 1.0.0
  packages (3):
    holder 1.0.0
    ovr-star-app 1.0.0
    tok 3.0.2
  node_modules (2):
    ovr-star-app 1.0.0 <- holder 1.0.0
    holder 1.0.0 <- tok 3.0.2
  encoded solution: 5 core nodes (5 lookups)
  loaded: 3 names, 4 versions, 0 packuments fetched

  $ untimed ../../../bin/main.exe npm --offline --cache . --tree ./ovr-empty-app/package.json
  root ovr-empty-app 1.0.0
  packages (3):
    holder 1.0.0
    ovr-empty-app 1.0.0
    tok 3.0.2
  node_modules (2):
    ovr-empty-app 1.0.0 <- holder 1.0.0
    holder 1.0.0 <- tok 3.0.2
  encoded solution: 5 core nodes (5 lookups)
  loaded: 3 names, 4 versions, 0 packuments fetched

npm leaves an edge on a version its tree already holds when the range
admits it: a slot whose node_modules lookup finds a satisfying copy is not a
problem edge, and nothing is fetched for it.  reuse-app depends on holder,
whose tok is ^3.0.0, and on taker, whose tok is ^3.0.0 || ^4.0.0.  holder
sorts first, so npm places its tok 3.0.2 before it reaches taker, whose slot
then finds that copy: one tok, 3.0.2, although latest is 4.0.0.

  $ untimed ../../../bin/main.exe npm --offline --cache . --tree ./reuse-app/package.json
  root reuse-app 1.0.0
  packages (4):
    holder 1.0.0
    reuse-app 1.0.0
    taker 1.0.0
    tok 3.0.2
  node_modules (4):
    reuse-app 1.0.0 <- holder 1.0.0
    reuse-app 1.0.0 <- taker 1.0.0
    holder 1.0.0 <- tok 3.0.2
    taker 1.0.0 <- tok 3.0.2
  encoded solution: 8 core nodes (9 lookups)
  loaded: 4 names, 5 versions, 0 packuments fetched

That is npm's order at work, which --order=pubgrub gives up for PubGrub's
own: each directory takes its newest admissible version, so taker gets a
tok 4.0.0 of its own.

  $ ../../../bin/main.exe npm --offline --cache . --tree --order=pubgrub ./reuse-app/package.json | sed -n '/^node_modules/,/^loaded/p'
  node_modules (4):
    reuse-app 1.0.0 <- holder 1.0.0
    reuse-app 1.0.0 <- taker 1.0.0
    holder 1.0.0 <- tok 3.0.2
    taker 1.0.0 <- tok 4.0.0
  encoded solution: 9 core nodes (10 lookups)
  loaded: 4 names, 5 versions, 0 packuments fetched

--order=random picks the next name and the version to try uniformly, from
a generator seeded by --seed: the same seed gives the same answer, and
another seed may give another, a resolution all the same:

  $ seed0() { ../../../bin/main.exe npm --offline --cache . --tree --order=random --seed 0 ./reuse-app/package.json | sed -n '/^node_modules/,/^loaded/p'; }; [ "$(seed0)" = "$(seed0)" ] && seed0
  node_modules (4):
    reuse-app 1.0.0 <- holder 1.0.0
    reuse-app 1.0.0 <- taker 1.0.0
    holder 1.0.0 <- tok 3.0.2
    taker 1.0.0 <- tok 4.0.0
  encoded solution: 9 core nodes (10 lookups)
  loaded: 4 names, 5 versions, 0 packuments fetched
  $ ../../../bin/main.exe npm --offline --cache . --tree --order=random --seed 2 ./reuse-app/package.json | sed -n '/^node_modules/,/^loaded/p'
  node_modules (4):
    reuse-app 1.0.0 <- holder 1.0.0
    reuse-app 1.0.0 <- taker 1.0.0
    holder 1.0.0 <- tok 3.0.2
    taker 1.0.0 <- tok 3.0.2
  encoded solution: 8 core nodes (9 lookups)
  loaded: 4 names, 5 versions, 0 packuments fetched

Only a copy already placed is reused, and npm reaches a package only after
the one requiring it has placed it.  reach-app depends on early, which
depends on tok at * and on late, whose tok is ^3.0.0.  npm places early's
tok 4.0.0 before it reaches late, which gets a 3.0.2 of its own: a copy
that only a later package requires is not there to be reused.

  $ untimed ../../../bin/main.exe npm --offline --cache . --tree ./reach-app/package.json
  root reach-app 1.0.0
  packages (5):
    early 1.0.0
    late 1.0.0
    reach-app 1.0.0
    tok 3.0.2
    tok 4.0.0
  node_modules (4):
    reach-app 1.0.0 <- early 1.0.0
    early 1.0.0 <- late 1.0.0
    late 1.0.0 <- tok 3.0.2
    early 1.0.0 <- tok 4.0.0
  encoded solution: 9 core nodes (10 lookups)
  loaded: 4 names, 5 versions, 0 packuments fetched

npm's queue is ordered by where a copy sits in node_modules, not by how
far it is from the root, and npm hoists: every package in hoist-app's tree
sits at the top, so npm reaches them by name.  alpha brings mid, mid brings
stream, and stream's tok ~3.0.0 is placed before npm reaches zeta, whose
^3.0.0 || ^4.0.0 then finds it: one tok, 3.0.2.

  $ untimed ../../../bin/main.exe npm --offline --cache . --tree ./hoist-app/package.json
  root hoist-app 1.0.0
  packages (6):
    alpha 1.0.0
    hoist-app 1.0.0
    mid 1.0.0
    stream 1.0.0
    tok 3.0.2
    zeta 1.0.0
  node_modules (6):
    hoist-app 1.0.0 <- alpha 1.0.0
    alpha 1.0.0 <- mid 1.0.0
    mid 1.0.0 <- stream 1.0.0
    stream 1.0.0 <- tok 3.0.2
    zeta 1.0.0 <- tok 3.0.2
    hoist-app 1.0.0 <- zeta 1.0.0
  encoded solution: 12 core nodes (13 lookups)
  loaded: 6 names, 7 versions, 0 packuments fetched

A copy nested in one package's node_modules is not there for another.
nest-app depends on mark ^4 and on inner, whose mark ~3.0.0 is nested
under it since 4.0.0 holds the top; outer's ^3.0.0 || ^4.0.0 looks up the
top and keeps 4.0.0, although 3.0.2 is tagged latest.

  $ untimed ../../../bin/main.exe npm --offline --cache . --tree ./nest-app/package.json
  root nest-app 1.0.0
  packages (5):
    inner 1.0.0
    mark 3.0.2
    mark 4.0.0
    nest-app 1.0.0
    outer 1.0.0
  node_modules (5):
    nest-app 1.0.0 <- inner 1.0.0
    inner 1.0.0 <- mark 3.0.2
    nest-app 1.0.0 <- mark 4.0.0
    outer 1.0.0 <- mark 4.0.0
    nest-app 1.0.0 <- outer 1.0.0
  encoded solution: 10 core nodes (11 lookups)
  loaded: 4 names, 5 versions, 0 packuments fetched

An optional peer that is never installed is no constraint, and the replay
does not model arborist's #loadPeerSet, which loads it into its declarer's
peer set anyway.  resolver peers on linter at * and optionally on
linter-plugin, whose own peer on linter is ^8.0.0 || ^9.0.0.  npm replaces
linter 10.0.0 with 9.0.0 there, the pick for linter-plugin's range; the
driver keeps 10.0.0, the pick for resolver's *:

  $ untimed ../../../bin/main.exe npm --offline --cache . --tree ./resolver-app/package.json
  root resolver-app 1.0.0
  packages (3):
    linter 10.0.0
    resolver 1.0.0
    resolver-app 1.0.0
  node_modules (2):
    resolver-app 1.0.0 <- linter 10.0.0
    resolver-app 1.0.0 <- resolver 1.0.0
  encoded solution: 5 core nodes (6 lookups)
  loaded: 4 names, 5 versions, 0 packuments fetched

npm never places a peer inside a non-root package that declares it, so
when a package peers on a name, the peers its own dependencies declare on that
name land in the directory its own peer does.  preset peers on compiler
^7.0.0 || ^8.0.0 and depends on syntax-a and syntax-b, which peer on
compiler ^7.0.0.  npm places compiler 8.0.0 for preset, then replaces it
with 7.0.0, the pick for the syntax packages' range, since preset's range
accepts it too: one compiler, 7.0.0, in both preset-app's directory and
preset's.

  $ untimed ../../../bin/main.exe npm --offline --cache . --tree ./preset-app/package.json
  root preset-app 1.0.0
  packages (5):
    compiler 7.0.0
    preset 1.0.0
    preset-app 1.0.0
    syntax-a 1.2.0
    syntax-b 1.2.0
  node_modules (5):
    preset 1.0.0 <- compiler 7.0.0
    preset-app 1.0.0 <- compiler 7.0.0
    preset-app 1.0.0 <- preset 1.0.0
    preset 1.0.0 <- syntax-a 1.2.0
    preset 1.0.0 <- syntax-b 1.2.0
  encoded solution: 10 core nodes (16 lookups)
  loaded: 5 names, 10 versions, 0 packuments fetched

However deep the chain of dependencies that each peer on the name, the
last one's range is met too.  deep-preset peers on compiler ^7.0.0 ||
^8.0.0 and so does each of deep-1 to deep-4, each depending on the next;
only deep-5, five dependencies down, peers on ^7.0.0.  npm installs one
compiler, 7.0.0:

  $ ../../../bin/main.exe npm --offline --cache . --tree ./deep-app/package.json | sed -E '/^(parse|solve) [0-9.]+s$/d' | sed -n '/^node_modules/,$p' | grep compiler
    deep-1 1.0.0 <- compiler 7.0.0
    deep-2 1.0.0 <- compiler 7.0.0
    deep-3 1.0.0 <- compiler 7.0.0
    deep-4 1.0.0 <- compiler 7.0.0
    deep-app 1.0.0 <- compiler 7.0.0
    deep-preset 1.0.0 <- compiler 7.0.0

npm meets a package's edges in the collation it sorts names by
(build-ideal-tree.js, localeCompare), where "_" comes before "-".
coll-preset peers on gauge at * and depends on coll_a, which peers on
^6.0.0 || ^7.0.0, and on coll-a, which peers on ^6.0.0 || ^8.0.0.  Met
first, coll_a's range replaces gauge 9.0.0 with 7.0.0 in coll-app's
directory, and coll-a's pick, 8.0.0, is then refused, since coll_a's range
does not accept it.  npm's answer has the same gauge at the top; below it,
the calculus puts the one version both ranges accept, 6.0.0, where npm
leaves coll-a's peer unmet:

  $ ../../../bin/main.exe npm --offline --cache . --tree ./coll-app/package.json | sed -E '/^(parse|solve) [0-9.]+s$/d' | grep 'gauge'
    gauge 6.0.0
    gauge 7.0.0
    coll-preset 1.0.0 <- gauge 6.0.0
    coll-app 1.0.0 <- gauge 7.0.0

A peer slot reuses the copy its declarer's node_modules lookup finds, not
one the tree holds out of its sight.  sight-left's dial 1.0.0 is nested
under it, below sight-app's dial 2.0.0, and sight-right's sight-host peers
on dial ^1.0.0; npm places sight-host and its peer under sight-right, where
the lookup finds only 2.0.0, and fetches ^1.0.0's newest, 1.1.0:

  $ untimed ../../../bin/main.exe npm --offline --cache . --tree ./sight-app/package.json
  root sight-app 1.0.0
  packages (7):
    dial 1.0.0
    dial 1.1.0
    dial 2.0.0
    sight-app 1.0.0
    sight-host 1.0.0
    sight-left 1.0.0
    sight-right 1.0.0
  node_modules (6):
    sight-left 1.0.0 <- dial 1.0.0
    sight-right 1.0.0 <- dial 1.1.0
    sight-app 1.0.0 <- dial 2.0.0
    sight-right 1.0.0 <- sight-host 1.0.0
    sight-app 1.0.0 <- sight-left 1.0.0
    sight-app 1.0.0 <- sight-right 1.0.0
  encoded solution: 13 core nodes (15 lookups)
  loaded: 5 names, 7 versions, 0 packuments fetched

A name a package both depends on and peers on is a dependency only: npm
keeps one edge per name and loads dependencies after peers, each
replacing the edge before it (arborist node.js, _loadDeps).  twin depends
on tok ^3.0.0 and peers on tok ^4.0.0 and on theme ^1; theme is installed
beside it as its peer, while tok is its own 3.0.2 and nothing asks for a
4.0.0.

  $ untimed ../../../bin/main.exe npm --offline --cache . --tree ./twin-app/package.json
  root twin-app 1.0.0
  packages (4):
    theme 1.0.0
    tok 3.0.2
    twin 1.0.0
    twin-app 1.0.0
  node_modules (3):
    twin-app 1.0.0 <- theme 1.0.0
    twin 1.0.0 <- tok 3.0.2
    twin-app 1.0.0 <- twin 1.0.0
  encoded solution: 7 core nodes (7 lookups)
  loaded: 4 names, 5 versions, 0 packuments fetched

deprecated is a resolution preference, not a warning printed over a pick
already made: npm-pick-manifest ranks a non-deprecated version above a
deprecated one and above semver order, and the dist-tags.latest fast path
is taken only when the tagged version is not deprecated.  depr publishes
1.0.0 clean and 2.0.0 deprecated and tags 2.0.0 latest, so the fast path
is refused and 1.0.0 is picked.  depr-old is the same shape one major
down, where the tag never enters into it: latest is 3.0.0, which ^1
refuses, and the sort alone demotes the deprecated 1.1.0 to leave 1.0.0.
depr-all is the guard that this is a preference: every version in range
is deprecated, the key ties, and the newest is picked exactly as before.
npm tests the field for truth, so an empty message deprecates nothing:
depr-empty's latest 2.0.0, deprecated with "", is picked as any latest is.

  $ untimed ../../../bin/main.exe npm --offline --cache . --tree ./depr-app/package.json
  root depr-app 1.0.0
  packages (5):
    depr 1.0.0
    depr-all 2.0.0
    depr-app 1.0.0
    depr-empty 2.0.0
    depr-old 1.0.0
  node_modules (4):
    depr-app 1.0.0 <- depr 1.0.0
    depr-app 1.0.0 <- depr-all 2.0.0
    depr-app 1.0.0 <- depr-empty 2.0.0
    depr-app 1.0.0 <- depr-old 1.0.0
  encoded solution: 9 core nodes (13 lookups)
  loaded: 5 names, 10 versions, 0 packuments fetched

engines is the other half of the same sort, so it needs a host to rank
against and there is none unless one is given.  Unset, every candidate
passes the engine test, the key ties, and only deprecated and semver
decide: engine and engine-npm take their newest, and engine-depr takes
the non-deprecated 2.0.0.

  $ untimed ../../../bin/main.exe npm --offline --cache . --tree ./engine-app/package.json
  root engine-app 1.0.0
  packages (4):
    engine 2.0.0
    engine-app 1.0.0
    engine-depr 2.0.0
    engine-npm 2.0.0
  node_modules (3):
    engine-app 1.0.0 <- engine 2.0.0
    engine-app 1.0.0 <- engine-depr 2.0.0
    engine-app 1.0.0 <- engine-npm 2.0.0
  encoded solution: 7 core nodes (10 lookups)
  loaded: 4 names, 7 versions, 0 packuments fetched

Versions that differ only in build metadata compare equal under
node-semver, and satisfies ignores the metadata too, so npm-pick-manifest
never tells them apart but by its sort's other keys and its stable order:
the latest tag where it names one, then the non-deprecated, then whichever
the packument lists first.  bmo lists 1.0.0+b first; bmd's 1.0.0+a is
deprecated; bml tags 1.0.0+b latest though it lists 1.0.0+a first; bmp
lists 1.0.0+1 before 1.0.0.  npm 11.17 locks the same four:

  $ untimed ../../../bin/main.exe npm --offline --cache . --tree ./bmeta-app/package.json
  root bmeta-app 1.0.0
  packages (5):
    bmd 1.0.0+b
    bmeta-app 1.0.0
    bml 1.0.0+b
    bmo 1.0.0+b
    bmp 1.0.0+1
  node_modules (4):
    bmeta-app 1.0.0 <- bmd 1.0.0+b
    bmeta-app 1.0.0 <- bml 1.0.0+b
    bmeta-app 1.0.0 <- bmo 1.0.0+b
    bmeta-app 1.0.0 <- bmp 1.0.0+1
  encoded solution: 9 core nodes (9 lookups)
  loaded: 5 names, 8 versions, 0 packuments fetched

The latest tag is a shortcut only past its own version's test: bmx tags
the deprecated 1.0.0+a, so npm sorts, and takes 2.0.0, not 1.0.0+a's twin
1.0.0+b, as npm 11.17 does:

  $ untimed ../../../bin/main.exe npm --offline --cache . ./bmx-app/package.json
  root bmx-app 1.0.0
  packages (2):
    bmx 2.0.0
    bmx-app 1.0.0
  encoded solution: 3 core nodes (4 lookups)
  loaded: 2 names, 3 versions, 0 packuments fetched

Given a host, the preference acts, and engines.npm is as live a sub-key as
engines.node: engine's 2.0.0 wants node >=99 and engine-npm's wants npm
>=99, and both fall back to 1.0.0.  engine-depr fixes the order of the two
keys against each other.  Its 1.0.0 is deprecated and buildable, its 2.0.0
is current and unbuildable, and npm sorts on (not deprecated and engine
ok) before engine ok before not deprecated -- the first key ties at false,
so the engine key decides and the deprecated 1.0.0 wins.

  $ untimed ../../../bin/main.exe npm --offline --cache . --tree --node-version v24.19.0 --npm-version 11.17.0 ./engine-app/package.json
  root engine-app 1.0.0
  packages (4):
    engine 1.0.0
    engine-app 1.0.0
    engine-depr 1.0.0
    engine-npm 1.0.0
  node_modules (3):
    engine-app 1.0.0 <- engine 1.0.0
    engine-app 1.0.0 <- engine-depr 1.0.0
    engine-app 1.0.0 <- engine-npm 1.0.0
  encoded solution: 7 core nodes (10 lookups)
  loaded: 4 names, 7 versions, 0 packuments fetched

Neither key is a gate, so pinning past the preference still resolves: the
root asked for * and engine 2.0.0 is a version the host cannot run, yet
naming it directly installs it, exactly as npm records an EBADENGINE
package in a lockfile and complains at install time.

  $ untimed ../../../bin/main.exe npm --offline --cache . --node-version v24.19.0 engine@2.0.0
  root .
  packages (2):
    .
    engine 2.0.0
  encoded solution: 3 core nodes (3 lookups)
  loaded: 2 names, 3 versions, 0 packuments fetched

The query is what npm install takes: a project's package.json, and specs
it adds to it.  proj is a project with no name or version, as npm init
does not require one.  Its dependencies, devDependencies and peers are the
root's, and its overrides pin core, which plugin's peer ^2 would otherwise
take at 2.1.0.  A root with no name is called ".", which no registry
package can be.  npm 11.17.0 answers the next four cases the same over
these fixtures, and refuses plugin@next (ETARGET).

  $ untimed ../../../bin/main.exe npm --offline --cache . --tree ./proj/package.json
  root .
  packages (6):
    .
    core 2.0.0
    util-lib 1.0.0 at lodash
    plugin 1.0.0
    runtime 1.1.0
    tester 1.0.0
  node_modules (5):
    . <- core 2.0.0
    . <- util-lib 1.0.0 at lodash
    . <- plugin 1.0.0
    . <- runtime 1.1.0
    . <- tester 1.0.0
  encoded solution: 11 core nodes (15 lookups)
  loaded: 6 names, 12 versions, 0 packuments fetched

A spec added to a project goes where the project already names it, so
tester@1.0.0 replaces the devDependency rather than adding a dependency.

  $ ../../../bin/main.exe npm --offline --cache . --tree ./proj/package.json tester@1.0.0 | grep tester
    tester 1.0.0
    . <- tester 1.0.0

With no package.json the project is empty and the specs are all of it.  A
bare name asks for *, a later spec for the same name replaces an earlier
one, and a tag is the version the packument tags.

  $ untimed ../../../bin/main.exe npm --offline --cache . --tree plugin core@2.0.0 runtime runtime@1.0 util-lib@latest
  root .
  packages (5):
    .
    core 2.0.0
    plugin 1.0.0
    runtime 1.0.0
    util-lib 1.2.0
  node_modules (4):
    . <- core 2.0.0
    . <- plugin 1.0.0
    . <- runtime 1.0.0
    . <- util-lib 1.2.0
  encoded solution: 9 core nodes (9 lookups)
  loaded: 5 names, 11 versions, 0 packuments fetched

An alias spec names the directory and the package apart, so one package
can be installed twice under two names.

  $ untimed ../../../bin/main.exe npm --offline --cache . --tree lodash@npm:util-lib@1.0.0 util-lib
  root .
  packages (3):
    .
    util-lib 1.0.0 at lodash
    util-lib 1.2.0
  node_modules (2):
    . <- util-lib 1.0.0 at lodash
    . <- util-lib 1.2.0
  encoded solution: 5 core nodes (6 lookups)
  loaded: 2 names, 3 versions, 0 packuments fetched

A spec that is not the registry's, and a tag the packument lacks, are
refused rather than dropped, with status 2, which no answer about the
registry has: 1 is unsatisfiable.

  $ ../../../bin/main.exe npm --offline --cache . plugin git+https://example.com/x.git
  error: git+https://example.com/x.git: not a registry spec (name, name@range, name@tag, key@npm:name@range)
  [2]
  $ ../../../bin/main.exe npm --offline --cache . plugin@next
  error: plugin@next: no such dist-tag
  [2]

A name validate-npm-package-name refuses is not a registry spec either,
and npm, which reads it as a nameless spec, fails too:

  $ ../../../bin/main.exe npm --offline --cache . node_modules
  error: node_modules: not a registry spec (name, name@range, name@tag, key@npm:name@range)
  [2]
  $ ../../../bin/main.exe npm --offline --cache . @scope/.x
  error: @scope/.x: not a registry spec (name, name@range, name@tag, key@npm:name@range)
  [2]

arborist loads a root's devDependencies after its dependencies, and the
later entry of a name replaces the earlier, so devprod-app, which asks for
devprod ^1 in dependencies and ^2 in devDependencies, gets 2.0.0:

  $ untimed ../../../bin/main.exe npm --offline --cache . ./devprod-app/package.json
  root devprod-app 1.0.0
  packages (2):
    devprod 2.0.0
    devprod-app 1.0.0
  encoded solution: 3 core nodes (3 lookups)
  loaded: 2 names, 3 versions, 0 packuments fetched

No range semver reads holds a '!', so npa takes !=1.0.0 for a tag name and
refuses it (EINVALIDTAGNAME); the dependency is dropped and counted, as
other specs no registry lookup resolves are:

  $ untimed ../../../bin/main.exe npm --offline --cache . ./bang-app/package.json
  root bang-app 1.0.0
  packages (1):
    bang-app 1.0.0
  encoded solution: 1 core nodes (1 lookups)
  loaded: 1 names, 1 versions, 0 packuments fetched
  parser dropped 1 declarations

A dist-tag is resolved from the target's packument, to the tagged version
exactly: devprod's old is 1.0.0.  A tag the packument lacks matches
nothing, so alpha, whose optional entry asks for nosuch, is abandoned:

  $ untimed ../../../bin/main.exe npm --offline --cache . ./tag-app/package.json
  root tag-app 1.0.0
  packages (2):
    devprod 1.0.0
    tag-app 1.0.0
  encoded solution: 3 core nodes (3 lookups)
  loaded: 3 names, 4 versions, 0 packuments fetched, 1 of 1 optionalDependencies (target, range) pairs dropped

A spec is a range where semver, reading loosely, finds one, and a dist-tag
otherwise, as npa reads it; nothing unread becomes *.  spec-app's
devprod is a hyphen range between v-prefixed versions, 1.0.0 to 1.9.0;
digtag's beta2 is no range, so it is the tag, and 1.0.0 rather than the
latest 2.0.0; and kit is an alias however its prefix is cased, so it holds
util-lib 1.0.0.  A peer or an override that is an alias puts another
package under the name, which a peer's range and an override's cannot
say, so both are dropped and counted:

  $ untimed ../../../bin/main.exe npm --offline --cache . ./spec-app/package.json
  root spec-app 1.0.0
  packages (4):
    devprod 1.0.0
    digtag 1.0.0
    util-lib 1.0.0 at kit
    spec-app 1.0.0
  encoded solution: 7 core nodes (7 lookups)
  loaded: 4 names, 7 versions, 0 packuments fetched
  parser dropped 2 declarations

The same on the command line, where the alias prefix is cased as npa
allows and a spec that is neither a range nor a name a tag may have is
refused:

  $ untimed ../../../bin/main.exe npm --offline --cache . kit@NPM:util-lib@1.0.0 digtag@beta2
  root .
  packages (3):
    .
    digtag 1.0.0
    util-lib 1.0.0 at kit
  encoded solution: 5 core nodes (5 lookups)
  loaded: 3 names, 5 versions, 0 packuments fetched
  $ ../../../bin/main.exe npm --offline --cache . 'digtag@^beta'
  error: digtag@^beta: not a registry spec (name, name@range, name@tag, key@npm:name@range)
  [2]

The cases from here to the fetch race pin where we deliberately differ
from npm; each states npm's answer, taken from npm 11.17.0 over the same
fixtures.

An override applies to a dependency by the package it targets; npm
applies it by the key the dependency is written under (arborist override-set.js:87, edge.js:206).
The two differ only on an alias, and there npm's override replaces the
alias spec wholesale.  carrier depends on kit as an alias of util-lib ^1.
ovr-key-app overrides kit to 1.0.0: npm installs the registry's own kit
1.0.0 at kit, while here the override names no target in the cone and
util-lib 1.2.0 stands.  ovr-target-app overrides util-lib to 1.0.0: npm
leaves the aliased dependency alone and installs util-lib 1.2.0, while
here the override binds and 1.0.0 is installed.

  $ untimed ../../../bin/main.exe npm --offline --cache . --tree ./ovr-key-app/package.json
  root ovr-key-app 1.0.0
  packages (3):
    carrier 1.0.0
    util-lib 1.2.0 at kit
    ovr-key-app 1.0.0
  node_modules (2):
    ovr-key-app 1.0.0 <- carrier 1.0.0
    carrier 1.0.0 <- util-lib 1.2.0 at kit
  encoded solution: 5 core nodes (6 lookups)
  loaded: 3 names, 4 versions, 0 packuments fetched

  $ untimed ../../../bin/main.exe npm --offline --cache . --tree ./ovr-target-app/package.json
  root ovr-target-app 1.0.0
  packages (3):
    carrier 1.0.0
    util-lib 1.0.0 at kit
    ovr-target-app 1.0.0
  node_modules (2):
    ovr-target-app 1.0.0 <- carrier 1.0.0
    carrier 1.0.0 <- util-lib 1.0.0 at kit
  encoded solution: 5 core nodes (5 lookups)
  loaded: 3 names, 4 versions, 0 packuments fetched

A dependency is met only by the package it names: a source name pairs
the key with the package installed under it.  npm reads the version
alone, so a node_modules/tok holding any package at a version in range
meets a dependency on tok (arborist dep-valid.js:66-74,82-84).
alias-sat-app installs mark 3.0.2 at tok, as an alias, and depends on
needer, whose tok is ^3.0.0.  npm finds 3.0.2 at tok and installs no tok
at all; here needer gets a tok 3.0.2 of its own.

  $ untimed ../../../bin/main.exe npm --offline --cache . --tree ./alias-sat-app/package.json
  root alias-sat-app 1.0.0
  packages (4):
    alias-sat-app 1.0.0
    needer 1.0.0
    mark 3.0.2 at tok
    tok 3.0.2
  node_modules (3):
    alias-sat-app 1.0.0 <- needer 1.0.0
    alias-sat-app 1.0.0 <- mark 3.0.2 at tok
    needer 1.0.0 <- tok 3.0.2
  encoded solution: 7 core nodes (7 lookups)
  loaded: 4 names, 6 versions, 0 packuments fetched

A peer dependency resolves in its declarer's depender's directory,
whichever package holds it; npm resolves it wherever it places the
declarer, and it hoists.  vplus depends on mocker and on vite as an alias
of vp-core 1.0.0, and mocker's optional peer on vite is ^6.  Here the
peer meets vplus's vite, vp-core 1.0.0, which ^6 refuses, and the
optional peer excuses only an empty directory, so nothing resolves.  npm
places mocker at the top beside vplus, where vite is not the alias, and
installs: vite 6.0.0 at the top, vp-core 1.0.0 at vplus's vite.  Choosing
where a declarer sits is placement, which the logical model does not
decide.

  $ untimed ../../../bin/main.exe npm --offline --cache . --tree ./vp-app/package.json
  root vp-app 1.0.0
  unsatisfiable:
  Because vp-app@1.0.0 1.0.0 -> <vp-app@1.0.0=>vplus> 1.0.0 and <vp-app@1.0.0=>vplus> 1.0.0 -> vplus@1.0.0 1.0.0, vp-app@1.0.0 * requires vplus@1.0.0 1.0.0.
  And because vplus@1.0.0 1.0.0 -> <vplus@1.0.0=>mocker> 1.0.0, vp-app@1.0.0 * requires <vplus@1.0.0=>mocker> 1.0.0
  And because <vplus@1.0.0=>mocker> 1.0.0 -> <vplus@1.0.0=>vite(npm:vp-core)> ∅ and root -> vp-app@1.0.0 1.0.0, version solving failed.
  loaded: 5 names, 5 versions, 0 packuments fetched
  [1]

A dependency is decided once, when npm's order reaches it; npm's edges
are live, and one already met from above moves to a copy placed nearer it
later.  live-app installs buf 5.2.1 at the top, and listy's buf ^5.1.1
finds it.  listy's rstream 2.0.0, nested under listy, wants buf ~5.1.1,
which the top refuses, so npm places 5.1.2 in listy's node_modules, the
highest level whose packages accept it (arborist can-place-dep.js:313-333),
and listy's edge now resolves there: npm has listy on buf 5.1.2.  Here
listy keeps 5.2.1 and only rstream takes 5.1.2.  Both answers meet every
range, so the difference is one of preference, not validity.

  $ untimed ../../../bin/main.exe npm --offline --cache . --tree ./live-app/package.json
  root live-app 1.0.0
  packages (6):
    buf 5.1.2
    buf 5.2.1
    listy 1.0.0
    live-app 1.0.0
    rstream 2.0.0
    rstream 3.0.0
  node_modules (6):
    rstream 2.0.0 <- buf 5.1.2
    listy 1.0.0 <- buf 5.2.1
    live-app 1.0.0 <- buf 5.2.1
    live-app 1.0.0 <- listy 1.0.0
    listy 1.0.0 <- rstream 2.0.0
    live-app 1.0.0 <- rstream 3.0.0
  encoded solution: 12 core nodes (14 lookups)
  loaded: 4 names, 6 versions, 0 packuments fetched

bundleDependencies are not read, so a bundled dependency resolves from
the registry like any other: a bundled copy is shipped inside its
package's tarball rather than resolved, which is out of scope.  bundler
bundles tok, and its tarball carries tok 3.0.1, a version the registry
never published; npm takes that copy, nested in bundler, while here tok
3.0.2 is resolved.

  $ untimed ../../../bin/main.exe npm --offline --cache . --tree ./bundle-app/package.json
  root bundle-app 1.0.0
  packages (3):
    bundle-app 1.0.0
    bundler 1.0.0
    tok 3.0.2
  node_modules (2):
    bundle-app 1.0.0 <- bundler 1.0.0
    bundler 1.0.0 <- tok 3.0.2
  encoded solution: 5 core nodes (5 lookups)
  loaded: 3 names, 4 versions, 0 packuments fetched

An optional dependency is abandoned only when its own range matches
nothing, not when something below it fails.  opt-deep-app optionally
depends on frail, whose tok ^9.0.0 matches nothing.  Here frail stands,
its dependency cannot be met, and nothing resolves; npm records frail,
optional, and no tok.

  $ untimed ../../../bin/main.exe npm --offline --cache . --tree ./opt-deep-app/package.json
  root opt-deep-app 1.0.0
  unsatisfiable:
  Because opt-deep-app@1.0.0 1.0.0 -> <opt-deep-app@1.0.0=>frail> 1.0.0 and <opt-deep-app@1.0.0=>frail> 1.0.0 -> frail@1.0.0 1.0.0, opt-deep-app@1.0.0 * requires frail@1.0.0 1.0.0.
  And because frail@1.0.0 1.0.0 -> <frail@1.0.0=>tok> ∅ and root -> opt-deep-app@1.0.0 1.0.0, version solving failed.
  loaded: 4 names, 5 versions, 0 packuments fetched
  [1]

A path-scoped override is dropped and counted: which chain of parents
reaches a package is an output of resolution, not an input.  ovr-path-app
overrides tok to 4.0.0 under holder only; npm installs holder's tok at
4.0.0, while here holder's ^3.0.0 picks 3.0.2.

  $ untimed ../../../bin/main.exe npm --offline --cache . --tree ./ovr-path-app/package.json
  root ovr-path-app 1.0.0
  packages (3):
    holder 1.0.0
    ovr-path-app 1.0.0
    tok 3.0.2
  node_modules (2):
    ovr-path-app 1.0.0 <- holder 1.0.0
    holder 1.0.0 <- tok 3.0.2
  encoded solution: 5 core nodes (5 lookups)
  loaded: 3 names, 4 versions, 0 packuments fetched
  parser dropped 1 declarations

An optional peer binds only a copy its declarer's depender holds itself.
perch-app depends on tok ^3.0.0 and on perch, whose lurker optionally
peers on tok ^4.0.0.  perch holds no tok, so here the peer forces nothing
and the only tok is the top's 3.0.2.  npm checks whatever copy lurker's
lookup finds, refuses 3.0.2, and nests lurker and a tok 4.0.0 under perch.

  $ untimed ../../../bin/main.exe npm --offline --cache . --tree ./perch-app/package.json
  root perch-app 1.0.0
  packages (4):
    lurker 1.0.0
    perch 1.0.0
    perch-app 1.0.0
    tok 3.0.2
  node_modules (3):
    perch 1.0.0 <- lurker 1.0.0
    perch-app 1.0.0 <- perch 1.0.0
    perch-app 1.0.0 <- tok 3.0.2
  encoded solution: 7 core nodes (7 lookups)
  loaded: 4 names, 5 versions, 0 packuments fetched

Processes sharing a cache fetch into it concurrently, each into a scratch
file of its own that it renames into place.  This curl writes the
packument and then waits for the other process's curl to have written its
own, so the two fetches of theme overlap and the first rename lands while
the second is still open.

  $ mkdir fetched bin
  $ cat > bin/curl <<'EOF'
  > #!/bin/sh
  > while [ $# -gt 0 ]; do case $1 in -o) o=$2; shift;; esac; shift; done
  > cp theme.json "$o"; touch "started.$$"; n=0
  > while [ "$(ls started.* | wc -l)" -lt 2 ] && [ $n -lt 100 ]; do sleep 0.1; n=$((n + 1)); done
  > EOF
  $ chmod +x bin/curl
  $ PATH=$PWD/bin:$PATH ../../../bin/main.exe npm --cache fetched theme > a.out 2>&1 &
  $ PATH=$PWD/bin:$PATH ../../../bin/main.exe npm --cache fetched theme > b.out 2>&1; wait
  $ cat a.out b.out | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root .
  packages (2):
    .
    theme 1.0.0
  encoded solution: 3 core nodes (3 lookups)
  loaded: 2 names, 2 versions, 1 packuments fetched
  root .
  packages (2):
    .
    theme 1.0.0
  encoded solution: 3 core nodes (3 lookups)
  loaded: 2 names, 2 versions, 1 packuments fetched
  $ ls fetched
  theme.json

A package with no packument in the cache cannot be fetched when offline.

  $ ../../../bin/main.exe npm --offline --cache . missing
  error: no packument for missing under . (offline)
  [2]

Only a 404 says the registry has no such package.  Any other failure to
fetch says nothing about the registry, so it stops the run with status 3
rather than reading the name as unpublished.  plugin is cached and its
peer core is not: with the registry answering 404 the peer cannot be met,
and with it unreachable, or failing, there is no answer at all.

  $ mkdir partial gone down broken
  $ cp plugin.json partial/
  $ printf '#!/bin/sh\nprintf 404; exit 22\n' > gone/curl
  $ printf '#!/bin/sh\necho "curl: (6) Could not resolve host: registry.npmjs.org" >&2; exit 6\n' > down/curl
  $ printf '#!/bin/sh\nprintf 503; exit 22\n' > broken/curl
  $ chmod +x gone/curl down/curl broken/curl
  $ untimed env PATH=$PWD/gone:$PATH ../../../bin/main.exe npm --cache partial plugin
  root .
  unsatisfiable:
  Because .@  -> <.@=>plugin> 1.0.0 and <.@=>plugin> 1.0.0 -> <.@=>core> ∅, .@ * is forbidden..
  And because root -> .@ , version solving failed.
  loaded: 3 names, 2 versions, 1 packuments fetched
  [1]
  $ PATH=$PWD/down:$PATH ../../../bin/main.exe npm --cache partial plugin
  root .
  error: fetching https://registry.npmjs.org/core: curl exited 6: curl: (6) Could not resolve host: registry.npmjs.org
  [3]
  $ PATH=$PWD/broken:$PATH ../../../bin/main.exe npm --cache partial plugin
  root .
  error: fetching https://registry.npmjs.org/core: curl exited 22, HTTP 503
  [3]
  $ ls partial
  plugin.json

A packument that does not parse says no more about the name's versions,
so it stops the run with status 3 too, whether it is fetched, when it is
not cached, or already in the cache:

  $ mkdir junk corrupt
  $ printf '#!/bin/sh\nwhile [ $# -gt 0 ]; do case $1 in -o) o=$2; shift;; esac; shift; done\nprintf "<html>" > "$o"; printf 200\n' > junk/curl
  $ chmod +x junk/curl
  $ PATH=$PWD/junk:$PATH ../../../bin/main.exe npm --cache partial plugin
  root .
  error: fetching https://registry.npmjs.org/core: not a packument
  [3]
  $ ls partial
  plugin.json
  $ cp plugin.json corrupt/
  $ printf '<html>' > corrupt/core.json
  $ ../../../bin/main.exe npm --offline --cache corrupt plugin
  root .
  error: reading corrupt/core.json: not a packument
  [3]

So is a package.json that cannot be read, while one that is not a
package.json is refused:

  $ ../../../bin/main.exe npm --offline --cache . ./nope/package.json
  error: ./nope/package.json: No such file or directory
  [3]
  $ ../../../bin/main.exe npm --offline --cache . ./app
  error: ./app: Is a directory
  [3]
  $ printf '[]' > list.json
  $ ../../../bin/main.exe npm --offline --cache . ./list.json
  error: ./list.json: not a package.json
  [2]

The packument cache defaults to $XDG_CACHE_HOME/pac/npm, else
~/.cache/pac/npm, so that where pac runs from does not decide what it
reads.  With neither variable set there is no such place, and pac refuses
rather than fall back on the working directory:

  $ env -u HOME -u XDG_CACHE_HOME ../../../bin/main.exe npm --offline ./app/package.json
  error: no packument cache: pass --cache, or set XDG_CACHE_HOME or HOME
  [2]
