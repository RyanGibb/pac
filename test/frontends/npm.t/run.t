A mandatory peer dependency is installed beside its declarer: app depends
on plugin and widget but on neither core nor theme.  plugin's peer on core
is not optional, so core arrives as app's own sibling of plugin; widget's
peer on theme is optional, so theme is not installed at all.  core 2.1.0 is
cut by its os gate, leaving 2.0.0 as the newest ^2.  lodash is an alias
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
    core 2.0.0
    util-lib 1.2.0 at lodash
    plugin 1.0.0
    runtime 1.1.0
    tester 1.0.0
    widget 1.0.0
  node_modules (6 edges):
    app 1.0.0 <- core 2.0.0
    app 1.0.0 <- util-lib 1.2.0 at lodash
    app 1.0.0 <- plugin 1.0.0
    app 1.0.0 <- runtime 1.1.0
    app 1.0.0 <- tester 1.0.0
    app 1.0.0 <- widget 1.0.0
  cone: 9 packages, 15 versions, 0 packuments fetched
  encoded solution: 13 core nodes (31 lookups)

A root peer edge is an ordinary peer edge, so a name the root both depends
on and declares a peer for is narrowed by both ranges at once.  dual-app
depends on dual >=1.1.0 and declares a peer on dual <=1.2.0, so 1.2.0 is
the only newest version satisfying both -- 1.3.0 would win on the
dependency alone.  shim is the same pair with the peer optional: the root
fills the directory itself, so the peer range still binds and shim ^1
lands on 1.0.0 rather than 1.1.0.

  $ ../../../src/main.exe npm --offline --cache . --tree dual-app | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root dual-app 1.0.0
  packages (3):
    dual 1.2.0
    dual-app 1.0.0
    shim 1.0.0
  node_modules (2 edges):
    dual-app 1.0.0 <- dual 1.2.0
    dual-app 1.0.0 <- shim 1.0.0
  cone: 3 packages, 7 versions, 0 packuments fetched
  encoded solution: 5 core nodes (13 lookups)

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

A package with no packument in the cache cannot be fetched when offline.

  $ ../../../src/main.exe npm --offline --cache . missing
  no packument for missing under . (offline)
  [1]
