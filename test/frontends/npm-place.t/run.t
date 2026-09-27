untimed (../untimed.sh) drops the timings from pac's output and keeps its
exit status:

  $ . ../untimed.sh

Under --reading=placement the answer is the node_modules layout, one row
per directory: the lock's path and the registry package there.  c needs b
^1 and the root b ^2, so c holds its own b.  d's b is an npm: alias of baz,
a directory holding another package.  op's optional peer on oq ^1 would see
the root's oq 2.0.0 from or's node_modules, so op and an oq 1.x sit under
or.  od's optional gone ^9 matches no published version, so nothing is
placed for it, while its optional b ^2 is met, as npm fetches it.  ap's
peer on pb is itself an alias of baz, which the root's pb holds.

  $ untimed ../../../bin/main.exe npm --reading=placement --offline --cache . ./place-app/package.json
  root place-app 1.0.0
  packages (12):
    node_modules/ap ap@1.0.0
    node_modules/b b@2.0.0
    node_modules/c c@1.0.0
    node_modules/c/node_modules/b b@1.0.0
    node_modules/d d@1.0.0
    node_modules/d/node_modules/b baz@1.0.0
    node_modules/od od@1.0.0
    node_modules/oq oq@2.0.0
    node_modules/or or@1.0.0
    node_modules/or/node_modules/op op@1.0.0
    node_modules/or/node_modules/oq oq@1.1.0
    node_modules/pb baz@1.0.0
  encoded solution: 35 core nodes (93 lookups)
  loaded: 11 names, 14 versions, 0 packuments fetched

The layout is found within a depth bound, 8 by default: at depth 1 c's b
cannot nest, and there is no answer.

  $ untimed ../../../bin/main.exe npm --reading=placement --depth 1 --offline --cache . ./nest-app/package.json
  root nest-app 1.0.0
  unsatisfiable:
  (within depth 1)
  Because no versions of <c⇑b> match (c,b@1.0.0) and <c⇑b> (ε,b@1.0.0) -> <ε⇑b> (ε,b@1.0.0), <c⇑b> (c,b@1.0.0) ∪ (ε,b@1.0.0) requires <ε⇑b> (ε,b@1.0.0).
  Because <ε⇑c> (ε,c@1.0.0) -> <ε,c> c@1.0.0 and <ε,c> c@1.0.0 -> <c⇑b> (c,b@1.0.0) ∪ (ε,b@1.0.0), <ε⇑c> (ε,c@1.0.0) requires <c⇑b> (c,b@1.0.0) ∪ (ε,b@1.0.0).
  Thus, <ε⇑c> (ε,c@1.0.0) requires <ε⇑b> (ε,b@1.0.0).
  And because <ε> project -> <ε⇑c> (ε,c@1.0.0), <ε> project requires <ε⇑b> (ε,b@1.0.0).
  And because <ε> project -> <ε⇑b> (ε,b@2.0.0) and root -> <ε> project, version solving failed.
  loaded: 3 names, 4 versions, 0 packuments fetched
  [1]

  $ untimed ../../../bin/main.exe npm --reading=placement --depth 2 --offline --cache . ./nest-app/package.json
  root nest-app 1.0.0
  packages (3):
    node_modules/b b@2.0.0
    node_modules/c c@1.0.0
    node_modules/c/node_modules/b b@1.0.0
  encoded solution: 7 core nodes (14 lookups)
  loaded: 3 names, 4 versions, 0 packuments fetched

sx 2 needs sx ^1, which needs sx ^2: each copy sees the other above it, and
only a link, which the calculus leaves out, closes the loop.  The search
refutes every nesting down to the bound.

  $ untimed ../../../bin/main.exe npm --reading=placement --offline --cache . ./loop-app/package.json > loop.out; echo $?
  1
  $ head -n 3 loop.out
  root loop-app 1.0.0
  unsatisfiable:
  (within depth 8)

dq pins tm 1.2.0; its dr peers on tm ^1, dr's ds on tm 1.1.0 and ds's dt on
tm 1.0.0.  A declarer's own node_modules holds no copy of what it peers on,
so dt, whether beside ds or inside it, walks on to the tm ds sees.  npm
overrides the peer; here there is no layout.

  $ untimed ../../../bin/main.exe npm --reading=placement --offline --cache . ./torn-app/package.json > torn.out; echo $?
  1
  $ head -n 3 torn.out
  root torn-app 1.0.0
  unsatisfiable:
  (within depth 8)

A root override applies to the key an edge is written under and replaces
its spec, alias included.  In ovr/, p depends on x as an alias of b ^2,
and q peers on it so: an override of x makes each edge the registry's own
x, and one of b, the alias's target, leaves them alone, as npm 11.17.0
answers over these fixtures.

  $ for a in key-app peer-key-app target-app root-target-app; do untimed ../../../bin/main.exe npm --reading=placement --offline --cache ovr ./ovr/$a/package.json | grep node_modules/x; done
    node_modules/x x@1.0.0
    node_modules/x x@1.0.0
    node_modules/x b@2.0.0
    node_modules/x b@2.0.0

The project is not the registry's package of its name, even at its
version.  In self/, both projects are b 3.0.0: in low-app c takes the
registry's b ^1, and in same-app d takes its b ^3, whose 3.0.0 needs an
e the project does not, as npm 11.17.0 answers over these fixtures.  The
npm reading keys the project as it keys that package, and refuses.

  $ untimed ../../../bin/main.exe npm --reading=placement --offline --cache self ./self/low-app/package.json
  root b 3.0.0
  packages (2):
    node_modules/b b@1.0.0
    node_modules/c c@1.0.0
  encoded solution: 7 core nodes (13 lookups)
  loaded: 3 names, 4 versions, 0 packuments fetched

  $ untimed ../../../bin/main.exe npm --reading=placement --offline --cache self ./self/same-app/package.json
  root b 3.0.0
  packages (3):
    node_modules/b b@3.0.0
    node_modules/d d@1.0.0
    node_modules/e e@1.0.0
  encoded solution: 11 core nodes (23 lookups)
  loaded: 4 names, 5 versions, 0 packuments fetched

  $ untimed ../../../bin/main.exe npm --offline --cache self ./self/same-app/package.json
  root b 3.0.0
  error: the project is named b, as is a package it reaches, which only --reading=placement tells apart
  [2]

--core prints the reachable core, finite under the bound.

  $ untimed ../../../bin/main.exe npm --reading=placement --core --depth 1 --offline --cache . c@1.0.0 | head -n 12
  root .
  core: 15 packages, 13 edges
  <c,b> ⊥
  <c⇑b> (ε,b@1.0.0)
    -> <c,b> {⊥}
    -> <ε⇑b> {(ε,b@1.0.0)}
  <c⇑b> (ε,b@2.0.0)
    -> <c,b> {⊥}
    -> <ε⇑b> {(ε,b@2.0.0)}
  <c⇑b> ⊥
    -> <c,b> {⊥}
    -> <ε⇑b> {⊥}
