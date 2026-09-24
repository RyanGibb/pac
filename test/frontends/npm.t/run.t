A mandatory peer dependency is installed beside its declarer: app depends
on plugin and widget but on neither core nor theme.  plugin's peer on core
is not optional, so core arrives as app's own sibling of plugin; widget's
peer on theme is optional, so theme is not installed at all.  core 2.1.0
declares os win32 and is still the newest ^2 -- resolution does not read
os -- so it is the one installed.  lodash is an alias
directory holding the util-lib package, and tester is a devDependency, so
it participates only from the root.

The root's own peers get the same treatment, from the calculus rather than
from the driver: nothing installs the root, so the edges that install its
peers leave the root's own granular node instead of a parent's directory
node.  app's mandatory peer on runtime is installed at 1.1.0, the newest
^1, while its optional peer on polyfill is not installed even though
polyfill is in the cache.

  $ ../../../src/main.exe npm --offline --cache . --tree app | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root app 1.0.0
  packages (7):
    app 1.0.0
    core 2.1.0
    util-lib 1.2.0 at lodash
    plugin 1.0.0
    runtime 1.1.0
    tester 1.0.0
    widget 1.0.0
  node_modules (6 edges):
    app 1.0.0 <- core 2.1.0
    app 1.0.0 <- util-lib 1.2.0 at lodash
    app 1.0.0 <- plugin 1.0.0
    app 1.0.0 <- runtime 1.1.0
    app 1.0.0 <- tester 1.0.0
    app 1.0.0 <- widget 1.0.0
  cone: 9 packages, 15 versions, 0 packuments fetched
  encoded solution: 13 core nodes (31 lookups)

A name the root both depends on and declares a peer for is a dependency
only, as it is for any package: npm keeps one edge per name and a
dependency replaces the peer.  dual-app depends on dual >=1.1.0 and
declares a peer on dual <=1.2.0, and 1.3.0 installs, as the dependency
alone picks it.  shim is the same pair with the peer optional, and shim ^1
lands on 1.1.0.

  $ ../../../src/main.exe npm --offline --cache . --tree dual-app | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root dual-app 1.0.0
  packages (3):
    dual 1.3.0
    dual-app 1.0.0
    shim 1.1.0
  node_modules (2 edges):
    dual-app 1.0.0 <- dual 1.3.0
    dual-app 1.0.0 <- shim 1.1.0
  cone: 3 packages, 7 versions, 0 packuments fetched
  encoded solution: 5 core nodes (12 lookups)

Prerelease admission is scoped to a single comparator set rather than to
the range that holds it.  codec publishes 1.0.0 and the newer 1.0.1-alpha,
and ^1 names no prerelease, so 1.0.0 is the newest candidate.  parser
publishes nothing but prereleases: ^1.0.0-alpha names one at 1.0.0's core
and so admits 1.0.0-alpha.1, while 2.0.0-beta.1 is refused even though the
alternative >=1.5.0 <3.0.0 orders it in range, because that set names no
prerelease and the set that does is the other alternative.

  $ ../../../src/main.exe npm --offline --cache . beta-app | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root beta-app 1.0.0
  packages (3):
    beta-app 1.0.0
    codec 1.0.0
    parser 1.0.0-alpha.1
  node_modules edges: 2
  cone: 3 packages, 5 versions, 0 packuments fetched
  encoded solution: 5 core nodes (10 lookups)

The literal range * is the exception, and so is an empty range, which npm
reads as *: npm-pick-manifest takes dist-tags.latest for it even when that
is a prerelease, provided it is not deprecated and the host can run it.
pre-only publishes nothing but prereleases, and its latest 1.0.0-beta.2 is
installed rather than nothing; pre-ahead's latest 1.0.0-alpha.0 wins over
the release 0.1.0.  pre-depr's latest prerelease is deprecated and
pre-engine's wants node >=99, so both fall back to 0.1.0, the release *
admits without the exception.

  $ ../../../src/main.exe npm --offline --cache . --node-version v24.19.0 --npm-version 11.17.0 star-app | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root star-app 1.0.0
  packages (5):
    pre-ahead 1.0.0-alpha.0
    pre-depr 0.1.0
    pre-engine 0.1.0
    pre-only 1.0.0-beta.2
    star-app 1.0.0
  node_modules edges: 4
  cone: 5 packages, 9 versions, 0 packuments fetched
  encoded solution: 9 core nodes (19 lookups)

npm's semver reads versions loosely, and a prerelease may drop its hyphen:
1.0.1rc1 is 1.0.1-rc1.  loose tags it latest, but ^1.0.0 names no
prerelease, so 1.0.0 is installed.

  $ ../../../src/main.exe npm --offline --cache . loose-app | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root loose-app 1.0.0
  packages (2):
    loose 1.0.0
    loose-app 1.0.0
  node_modules edges: 1
  cone: 2 packages, 3 versions, 0 packuments fetched
  encoded solution: 3 core nodes (6 lookups)

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

  $ ../../../src/main.exe npm --offline --cache . --tree opt-app | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root opt-app 1.0.0
  packages (3):
    gadget 1.0.0
    opt-app 1.0.0
    theme 1.0.0
  node_modules (2 edges):
    opt-app 1.0.0 <- gadget 1.0.0
    opt-app 1.0.0 <- theme 1.0.0
  cone: 5 packages, 5 versions, 0 packuments fetched
  optionalDependencies: 3 entries, 2 dropped
  encoded solution: 5 core nodes (10 lookups)

--omit=optional drops the class outright, without asking the registry
anything: gadget goes even though it resolves, and no availability check
runs, so nothing is counted as dropped and neither gadget nor native is
loaded at all.

  $ ../../../src/main.exe npm --offline --cache . --tree --omit=optional opt-app | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root opt-app 1.0.0
  packages (2):
    opt-app 1.0.0
    theme 1.0.0
  node_modules (1 edges):
    opt-app 1.0.0 <- theme 1.0.0
  cone: 2 packages, 2 versions, 0 packuments fetched
  optionalDependencies: 3 entries, 0 dropped
  encoded solution: 3 core nodes (6 lookups)

os, cpu and libc are not read at all: npm resolves for every platform at
once and filters at install time, and a package-lock.json records every
variant whatever host wrote it.  nativefs publishes only 1.0.0 and only
for darwin, and the host here is linux, yet opt-plat-app's optional
dependency on it stands -- and brings native-core, which nativefs
depends on and nothing else does.  This is fsevents, the commonest
optional dependency there is, and npm puts it in the lockfile on linux
too; dropping it here would make our answer smaller than npm's on every
platform but macOS.

  $ ../../../src/main.exe npm --offline --cache . --tree opt-plat-app | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root opt-plat-app 1.0.0
  packages (4):
    native-core 1.0.0
    nativefs 1.0.0
    opt-plat-app 1.0.0
    theme 1.0.0
  node_modules (3 edges):
    nativefs 1.0.0 <- native-core 1.0.0
    opt-plat-app 1.0.0 <- nativefs 1.0.0
    opt-plat-app 1.0.0 <- theme 1.0.0
  cone: 4 packages, 4 versions, 0 packuments fetched
  optionalDependencies: 1 entries, 0 dropped
  encoded solution: 7 core nodes (14 lookups)

A non-optional dependency on the same package resolves alike, which is
what plat-app shows: the same dependency against the same cache, and
nothing about the host enters into it.

  $ ../../../src/main.exe npm --offline --cache . --tree plat-app | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root plat-app 1.0.0
  packages (4):
    native-core 1.0.0
    nativefs 1.0.0
    plat-app 1.0.0
    theme 1.0.0
  node_modules (3 edges):
    nativefs 1.0.0 <- native-core 1.0.0
    plat-app 1.0.0 <- nativefs 1.0.0
    plat-app 1.0.0 <- theme 1.0.0
  cone: 4 packages, 4 versions, 0 packuments fetched
  encoded solution: 7 core nodes (14 lookups)

A satisfiable optional entry that conflicts is a conflict, not a drop.
opt-peer-app depends on host, whose peer on gadget is ^2, and optionally
on gadget ^1; gadget publishes both, so the dependency's manifest is
fetchable and the dependency stands.  The two ranges fill the same directory and cannot
agree, which is npm's ERESOLVE rather than a reason to abandon the entry.

  $ ../../../src/main.exe npm --offline --cache . --tree opt-peer-app
  root opt-peer-app 1.0.0
  unsatisfiable:
  Because <opt-peer-app@1.0.0=>host> 1.0.0 -> <opt-peer-app@1.0.0=>gadget> 2.0.0 and opt-peer-app@1.0.0 1.0.0 -> <opt-peer-app@1.0.0=>gadget> 1.0.0, <opt-peer-app@1.0.0=>host> * or opt-peer-app@1.0.0 * is forbidden..
  And because opt-peer-app@1.0.0 1.0.0 -> <opt-peer-app@1.0.0=>host> 1.0.0 and root -> opt-peer-app@1.0.0 1.0.0, version solving failed.
  [1]

That the optional dependency is what fails the solve, rather than
something else in the fixture, is what --omit=optional shows: with the
dependency gone the peer
installs gadget 2.0.0 by itself.

  $ ../../../src/main.exe npm --offline --cache . --tree --omit=optional opt-peer-app | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root opt-peer-app 1.0.0
  packages (3):
    gadget 2.0.0
    host 1.0.0
    opt-peer-app 1.0.0
  node_modules (2 edges):
    opt-peer-app 1.0.0 <- gadget 2.0.0
    opt-peer-app 1.0.0 <- host 1.0.0
  cone: 3 packages, 4 versions, 0 packuments fetched
  optionalDependencies: 1 entries, 0 dropped
  encoded solution: 5 core nodes (11 lookups)

A root override binds a peer slot too, and wins over the peer's own range
rather than being intersected with it.  ovr-peer-app depends on host and
on nothing else; host's mandatory peer on gadget is ^2, so gadget is a
directory only the peer asks for.  The root overrides gadget to 1.0.0,
which ^2 refuses, and 1.0.0 is what installs -- the override replaces a
peer dependency's range exactly as it replaces a dependency's.

  $ ../../../src/main.exe npm --offline --cache . --tree ovr-peer-app | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root ovr-peer-app 1.0.0
  packages (3):
    gadget 1.0.0
    host 1.0.0
    ovr-peer-app 1.0.0
  node_modules (2 edges):
    ovr-peer-app 1.0.0 <- gadget 1.0.0
    ovr-peer-app 1.0.0 <- host 1.0.0
  cone: 3 packages, 4 versions, 0 packuments fetched
  encoded solution: 5 core nodes (11 lookups)

An override to * is no override at all: npm reads an edge's range from an
override only when its value is not * (arborist edge.js, spec), and it
reads an empty value as *.  ovr-star-app overrides tok to * and ovr-empty-app
to "", and in both holder's ^3.0.0 still binds: tok 3.0.2, not the latest
4.0.0.

  $ ../../../src/main.exe npm --offline --cache . --tree ovr-star-app | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root ovr-star-app 1.0.0
  packages (3):
    holder 1.0.0
    ovr-star-app 1.0.0
    tok 3.0.2
  node_modules (2 edges):
    ovr-star-app 1.0.0 <- holder 1.0.0
    holder 1.0.0 <- tok 3.0.2
  cone: 3 packages, 4 versions, 0 packuments fetched
  encoded solution: 5 core nodes (10 lookups)

  $ ../../../src/main.exe npm --offline --cache . --tree ovr-empty-app | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root ovr-empty-app 1.0.0
  packages (3):
    holder 1.0.0
    ovr-empty-app 1.0.0
    tok 3.0.2
  node_modules (2 edges):
    ovr-empty-app 1.0.0 <- holder 1.0.0
    holder 1.0.0 <- tok 3.0.2
  cone: 3 packages, 4 versions, 0 packuments fetched
  encoded solution: 5 core nodes (10 lookups)

npm leaves an edge on a version its tree already holds when the range
admits it: a slot whose node_modules lookup finds a satisfying copy is not a
problem edge, and nothing is fetched for it.  reuse-app depends on holder,
whose tok is ^3.0.0, and on taker, whose tok is ^3.0.0 || ^4.0.0.  holder
sorts first, so npm places its tok 3.0.2 before it reaches taker, whose slot
then finds that copy: one tok, 3.0.2, although latest is 4.0.0.

  $ ../../../src/main.exe npm --offline --cache . --tree reuse-app | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root reuse-app 1.0.0
  packages (4):
    holder 1.0.0
    reuse-app 1.0.0
    taker 1.0.0
    tok 3.0.2
  node_modules (4 edges):
    reuse-app 1.0.0 <- holder 1.0.0
    reuse-app 1.0.0 <- taker 1.0.0
    holder 1.0.0 <- tok 3.0.2
    taker 1.0.0 <- tok 3.0.2
  cone: 4 packages, 5 versions, 0 packuments fetched
  encoded solution: 8 core nodes (17 lookups)

Only a copy already placed is reused, and npm reaches a package only after
the one requiring it has placed it.  reach-app depends on early, which
depends on tok at * and on late, whose tok is ^3.0.0.  npm places early's
tok 4.0.0 before it reaches late, which gets a 3.0.2 of its own: a copy
that only a later package requires is not there to be reused.

  $ ../../../src/main.exe npm --offline --cache . --tree reach-app | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root reach-app 1.0.0
  packages (5):
    early 1.0.0
    late 1.0.0
    reach-app 1.0.0
    tok 3.0.2
    tok 4.0.0
  node_modules (4 edges):
    reach-app 1.0.0 <- early 1.0.0
    early 1.0.0 <- late 1.0.0
    late 1.0.0 <- tok 3.0.2
    early 1.0.0 <- tok 4.0.0
  cone: 4 packages, 5 versions, 0 packuments fetched
  encoded solution: 9 core nodes (19 lookups)

npm's queue is ordered by where a copy sits in node_modules, not by how
far it is from the root, and npm hoists: every package in hoist-app's tree
sits at the top, so npm reaches them by name.  alpha brings mid, mid brings
stream, and stream's tok ~3.0.0 is placed before npm reaches zeta, whose
^3.0.0 || ^4.0.0 then finds it: one tok, 3.0.2.

  $ ../../../src/main.exe npm --offline --cache . --tree hoist-app | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root hoist-app 1.0.0
  packages (6):
    alpha 1.0.0
    hoist-app 1.0.0
    mid 1.0.0
    stream 1.0.0
    tok 3.0.2
    zeta 1.0.0
  node_modules (6 edges):
    hoist-app 1.0.0 <- alpha 1.0.0
    alpha 1.0.0 <- mid 1.0.0
    mid 1.0.0 <- stream 1.0.0
    stream 1.0.0 <- tok 3.0.2
    zeta 1.0.0 <- tok 3.0.2
    hoist-app 1.0.0 <- zeta 1.0.0
  cone: 6 packages, 7 versions, 0 packuments fetched
  encoded solution: 12 core nodes (25 lookups)

A copy nested in one package's node_modules is not there for another.
nest-app depends on mark ^4 and on inner, whose mark ~3.0.0 is nested
under it since 4.0.0 holds the top; outer's ^3.0.0 || ^4.0.0 looks up the
top and keeps 4.0.0, although 3.0.2 is tagged latest.

  $ ../../../src/main.exe npm --offline --cache . --tree nest-app | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root nest-app 1.0.0
  packages (5):
    inner 1.0.0
    mark 3.0.2
    mark 4.0.0
    nest-app 1.0.0
    outer 1.0.0
  node_modules (5 edges):
    nest-app 1.0.0 <- inner 1.0.0
    inner 1.0.0 <- mark 3.0.2
    nest-app 1.0.0 <- mark 4.0.0
    outer 1.0.0 <- mark 4.0.0
    nest-app 1.0.0 <- outer 1.0.0
  cone: 4 packages, 5 versions, 0 packuments fetched
  encoded solution: 10 core nodes (21 lookups)

An optional peer that is never installed still narrows its declarer's peer
set.  resolver peers on linter at * and optionally on linter-plugin, whose
own peer on linter is ^8.0.0 || ^9.0.0.  npm loads the optional peer into
resolver's peer set, to catch a conflict before placing it, and there
replaces linter 10.0.0 with 9.0.0, the pick for linter-plugin's range, since
resolver's * accepts it too; linter-plugin itself is not installed.

  $ ../../../src/main.exe npm --offline --cache . --tree resolver-app | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root resolver-app 1.0.0
  packages (3):
    linter 9.0.0
    resolver 1.0.0
    resolver-app 1.0.0
  node_modules (2 edges):
    resolver-app 1.0.0 <- linter 9.0.0
    resolver-app 1.0.0 <- resolver 1.0.0
  cone: 4 packages, 5 versions, 0 packuments fetched
  encoded solution: 5 core nodes (11 lookups)

npm never places a peer inside the package that declares it, so when a
package peers on a name, the peers its own dependencies declare on that
name land in the directory its own peer does.  preset peers on compiler
^7.0.0 || ^8.0.0 and depends on syntax-a and syntax-b, which peer on
compiler ^7.0.0.  npm places compiler 8.0.0 for preset, then replaces it
with 7.0.0, the pick for the syntax packages' range, since preset's range
accepts it too: one compiler, 7.0.0, in both preset-app's directory and
preset's.

  $ ../../../src/main.exe npm --offline --cache . --tree preset-app | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root preset-app 1.0.0
  packages (5):
    compiler 7.0.0
    preset 1.0.0
    preset-app 1.0.0
    syntax-a 1.2.0
    syntax-b 1.2.0
  node_modules (5 edges):
    preset 1.0.0 <- compiler 7.0.0
    preset-app 1.0.0 <- compiler 7.0.0
    preset-app 1.0.0 <- preset 1.0.0
    preset 1.0.0 <- syntax-a 1.2.0
    preset 1.0.0 <- syntax-b 1.2.0
  cone: 5 packages, 10 versions, 0 packuments fetched
  encoded solution: 10 core nodes (26 lookups)

A name a package both depends on and peers on is a dependency only: npm
keeps one edge per name and loads dependencies after peers, each
replacing the edge before it (arborist node.js, _loadDeps).  twin depends
on tok ^3.0.0 and peers on tok ^4.0.0 and on theme ^1; theme is installed
beside it as its peer, while tok is its own 3.0.2 and nothing asks for a
4.0.0.

  $ ../../../src/main.exe npm --offline --cache . --tree twin-app | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root twin-app 1.0.0
  packages (4):
    theme 1.0.0
    tok 3.0.2
    twin 1.0.0
    twin-app 1.0.0
  node_modules (3 edges):
    twin-app 1.0.0 <- theme 1.0.0
    twin 1.0.0 <- tok 3.0.2
    twin-app 1.0.0 <- twin 1.0.0
  cone: 4 packages, 5 versions, 0 packuments fetched
  encoded solution: 7 core nodes (14 lookups)

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

  $ ../../../src/main.exe npm --offline --cache . --tree depr-app | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root depr-app 1.0.0
  packages (5):
    depr 1.0.0
    depr-all 2.0.0
    depr-app 1.0.0
    depr-empty 2.0.0
    depr-old 1.0.0
  node_modules (4 edges):
    depr-app 1.0.0 <- depr 1.0.0
    depr-app 1.0.0 <- depr-all 2.0.0
    depr-app 1.0.0 <- depr-empty 2.0.0
    depr-app 1.0.0 <- depr-old 1.0.0
  cone: 5 packages, 10 versions, 0 packuments fetched
  encoded solution: 9 core nodes (22 lookups)

engines is the other half of the same sort, so it needs a host to rank
against and there is none unless one is given.  Unset, every candidate
passes the engine test, the key ties, and only deprecated and semver
decide: engine and engine-npm take their newest, and engine-depr takes
the non-deprecated 2.0.0.

  $ ../../../src/main.exe npm --offline --cache . --tree engine-app | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root engine-app 1.0.0
  packages (4):
    engine 2.0.0
    engine-app 1.0.0
    engine-depr 2.0.0
    engine-npm 2.0.0
  node_modules (3 edges):
    engine-app 1.0.0 <- engine 2.0.0
    engine-app 1.0.0 <- engine-depr 2.0.0
    engine-app 1.0.0 <- engine-npm 2.0.0
  cone: 4 packages, 7 versions, 0 packuments fetched
  encoded solution: 7 core nodes (17 lookups)

Given a host, the preference acts, and engines.npm is as live a sub-key as
engines.node: engine's 2.0.0 wants node >=99 and engine-npm's wants npm
>=99, and both fall back to 1.0.0.  engine-depr fixes the order of the two
keys against each other.  Its 1.0.0 is deprecated and buildable, its 2.0.0
is current and unbuildable, and npm sorts on (not deprecated and engine
ok) before engine ok before not deprecated -- the first key ties at false,
so the engine key decides and the deprecated 1.0.0 wins.

  $ ../../../src/main.exe npm --offline --cache . --tree --node-version v24.19.0 --npm-version 11.17.0 engine-app | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root engine-app 1.0.0
  packages (4):
    engine 1.0.0
    engine-app 1.0.0
    engine-depr 1.0.0
    engine-npm 1.0.0
  node_modules (3 edges):
    engine-app 1.0.0 <- engine 1.0.0
    engine-app 1.0.0 <- engine-depr 1.0.0
    engine-app 1.0.0 <- engine-npm 1.0.0
  cone: 4 packages, 7 versions, 0 packuments fetched
  encoded solution: 7 core nodes (17 lookups)

Neither key is a gate, so pinning past the preference still resolves: the
root asked for * and engine 2.0.0 is a version the host cannot run, yet
naming it directly installs it, exactly as npm records an EBADENGINE
package in a lockfile and complains at install time.

  $ ../../../src/main.exe npm --offline --cache . --node-version v24.19.0 engine 2.0.0 | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root engine 2.0.0
  packages (1):
    engine 2.0.0
  node_modules edges: 0
  cone: 1 packages, 2 versions, 0 packuments fetched
  encoded solution: 1 core nodes (2 lookups)

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
  $ PATH=$PWD/bin:$PATH ../../../src/main.exe npm --cache fetched theme > a.out 2>&1 &
  $ PATH=$PWD/bin:$PATH ../../../src/main.exe npm --cache fetched theme > b.out 2>&1; wait
  $ cat a.out b.out | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root theme 1.0.0
  packages (1):
    theme 1.0.0
  node_modules edges: 0
  cone: 1 packages, 1 versions, 1 packuments fetched
  encoded solution: 1 core nodes (2 lookups)
  root theme 1.0.0
  packages (1):
    theme 1.0.0
  node_modules edges: 0
  cone: 1 packages, 1 versions, 1 packuments fetched
  encoded solution: 1 core nodes (2 lookups)
  $ ls fetched
  theme.json

A package with no packument in the cache cannot be fetched when offline.

  $ ../../../src/main.exe npm --offline --cache . missing
  no packument for missing under . (offline)
  [1]
