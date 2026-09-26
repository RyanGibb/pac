untimed drops the timings from pac's output and keeps its exit status:

  $ untimed() { "$@" > out 2>&1; s=$?; sed -E '/^(parse|solve) [0-9.]+s$/d' out; return $s; }

  $ untimed ../../../bin/main.exe opam . app
  packages (2):
    app 1
    c 1
  encoded solution: 4 core nodes (6 lookups)
  loaded: 2 names, 2 versions

A dependency constrained to the depender's own version takes that version,
not the newest one available:

  $ untimed ../../../bin/main.exe opam . tool
  packages (2):
    lib 2
    tool 2
  encoded solution: 3 core nodes (4 lookups)
  loaded: 2 names, 3 versions

A parenthesised group conjoins its elements, as the top level of a brace
does, so both ends of (>= "2" < "4") bind and dep.9 is out of range:

  $ untimed ../../../bin/main.exe opam . grp
  packages (2):
    dep 3
    grp 1
  encoded solution: 3 core nodes (4 lookups)
  loaded: 2 names, 3 versions

A version disjunction inside one brace is one set of versions, as opam reads
it, so dep takes the newest version in either range, not the lower range's
dep.3 for being written first:

  $ untimed ../../../bin/main.exe opam . bdisj
  packages (2):
    bdisj 1
    dep 9
  encoded solution: 3 core nodes (4 lookups)
  loaded: 2 names, 3 versions

A brace mixing a filter into the disjunction stays two atoms under a
disjunction, each with its own filter.  Without --with-test only < "5" is
left, and with it the unconstrained alternative, written first, is taken:

  $ untimed ../../../bin/main.exe opam . bmix
  packages (2):
    bmix 1
    dep 3
  encoded solution: 3 core nodes (4 lookups)
  loaded: 2 names, 3 versions

  $ untimed ../../../bin/main.exe opam --with-test . bmix
  packages (2):
    bmix 1
    dep 9
  encoded solution: 4 core nodes (6 lookups)
  loaded: 2 names, 3 versions

pin-depends is read only when its owner is pinned, and nothing is pinned
here, so pind.1's entry for dep.dev constrains nothing:

  $ untimed ../../../bin/main.exe opam . pind
  packages (2):
    dep 9
    pind 1
  encoded solution: 3 core nodes (4 lookups)
  loaded: 2 names, 3 versions

Depexts constrain nothing: they are read off the finished resolution, so
what is reported is the union over the selected packages of the depext
entries whose
filter holds under the environment.  sys.1 asks for libfoo-dev and
pkg-config on a debian family and libbar-dev on alpine; helper.1 asks
unconditionally for pkg-config, which is named once:

  $ untimed ../../../bin/main.exe opam . sys
  packages (2):
    helper 1
    sys 1
  system packages (2):
    libfoo-dev
    pkg-config
  encoded solution: 3 core nodes (4 lookups)
  loaded: 2 names, 2 versions

The avoid-version and deprecated flags say "select this only if nothing
else works", which is a preference and not a constraint.  A flagged
version is ranked below every unflagged version of its name, so the older
avoid.1 and depr.1 are taken over the newer flagged ones:

  $ untimed ../../../bin/main.exe opam . avoid
  packages (1):
    avoid 1
  encoded solution: 2 core nodes (2 lookups)
  loaded: 1 names, 2 versions

  $ untimed ../../../bin/main.exe opam . depr
  packages (1):
    depr 1
  encoded solution: 2 core nodes (2 lookups)
  loaded: 1 names, 2 versions

Nothing else works when a dependency pins the flagged version, and it is
selected:

  $ untimed ../../../bin/main.exe opam . needav
  packages (2):
    avoid 2
    needav 1
  encoded solution: 3 core nodes (4 lookups)
  loaded: 2 names, 3 versions

opam's builtin-0install takes a disjunction's first satisfiable alternative
(unless opam's CNF rewrite has reshaped it), so a dependency on three
installable packages selects the one written first.  The encoding
reverses the alternatives -- PubGrub decides the larger version and the
disjunct package's largest index selects the last alternative -- so that
this is what falls out:

  $ untimed ../../../bin/main.exe opam . pick
  packages (2):
    alt1 1
    pick 1
  encoded solution: 4 core nodes (6 lookups)
  loaded: 4 names, 4 versions

A conflict class admits at most one name.  cc-a.1, cc-b.1 and cc-b.2 all
declare the class "ccls"; the class package for it has one version per
declaring name, each declarer depends on it at its own name, and version
uniqueness does the excluding -- so two versions of cc-b never exclude each
other, exactly as opam's own rule, which removes the declarer's own name
from the member map, does not.  cc-pick prefers cc-b, being the alternative
written first, but cannot have it beside cc-a and falls back to cc-plain.
The class name is also a package name here, and ccls.1 is installed
regardless: a class and a real package of the same name are separate target
names, as opam's ocaml-system -- both a class and a package -- requires.

  $ untimed ../../../bin/main.exe opam . cc-pick
  packages (4):
    cc-a 1
    cc-pick 1
    cc-plain 1
    ccls 1
  encoded solution: 7 core nodes (13 lookups)
  loaded: 5 names, 6 versions

Asking for both names of the class outright has no resolution, and the
class package is what the explanation names:

  $ untimed ../../../bin/main.exe opam . cc-both
  unsatisfiable:
  Because cc-a 1 -> conflict-class:ccls cc-a and cc-b 2 -> conflict-class:ccls cc-b, cc-a (-∞, ⊥) or cc-b (-∞, ⊥) is forbidden..
  And because cc-both 1 -> cc-a 1 and cc-both 1 -> cc-b 1 ∪ 2, cc-both (-∞, ⊥) is forbidden.
  And because root () -> cc-both 1 and root -> root (), version solving failed.
  loaded: 3 names, 4 versions
  [1]

A conflict holds whichever side of it the solver decides first.  cfl-a.1
conflicts with cfl-b and cfl-c.1 depends on cfl-a; asking for cfl-c and
cfl-b.1 has PubGrub decide cfl-b before it reaches cfl-c, let alone cfl-a.
The conflict is cfl-a's own edge: every name has an absent version ⊥
besides its real ones, and a conflict on cfl-b is a dependency on cfl-b at
the versions the conflict does not name, or absent -- here ⊥ alone, the
conflict naming every version.  Nothing hangs on cfl-b's side, so the order
in which the two are decided cannot lose it:

  $ untimed ../../../bin/main.exe opam . cfl-c cfl-b.1
  unsatisfiable:
  Because cfl-c 1 -> cfl-a 1 and cfl-a 1 -> cfl-b ⊥, cfl-c (-∞, ⊥) requires cfl-b ⊥.
  And because root () -> cfl-b 1, cfl-c (-∞, ⊥) or root * is forbidden.
  And because root () -> cfl-c 1 and root -> root (), version solving failed.
  loaded: 3 names, 4 versions
  [1]

A name only a conflict reaches is left absent rather than installed: ⊥ is
the greatest version, and PubGrub decides the greatest:

  $ untimed ../../../bin/main.exe opam . cfl-c
  packages (2):
    cfl-a 1
    cfl-c 1
  encoded solution: 4 core nodes (6 lookups)
  loaded: 3 names, 4 versions

A request is a query -- a set of names, each with a set of acceptable
versions -- realised as the dependencies of the synthetic root.  Naming
two packages asks for both, and each is solved against the same
repository:

  $ untimed ../../../bin/main.exe opam . app tool
  packages (4):
    app 1
    c 1
    lib 2
    tool 2
  encoded solution: 6 core nodes (9 lookups)
  loaded: 4 names, 5 versions

An atom's version constraint is the set of versions its name is accepted
at.  Unconstrained, dep takes its newest version:

  $ untimed ../../../bin/main.exe opam . dep
  packages (1):
    dep 9
  encoded solution: 2 core nodes (2 lookups)
  loaded: 1 names, 2 versions

An operator narrows that set, in opam's own command-line syntax:

  $ untimed ../../../bin/main.exe opam . 'dep<9'
  packages (1):
    dep 3
  encoded solution: 2 core nodes (2 lookups)
  loaded: 1 names, 2 versions

and NAME.VERSION is opam's shorthand for the =-constraint:

  $ untimed ../../../bin/main.exe opam . dep.3
  packages (1):
    dep 3
  encoded solution: 2 core nodes (2 lookups)
  loaded: 1 names, 2 versions

Constraints and several names compose, the query being one per name:

  $ untimed ../../../bin/main.exe opam . 'dep<9' app
  packages (3):
    app 1
    c 1
    dep 3
  encoded solution: 5 core nodes (7 lookups)
  loaded: 3 names, 4 versions

An element opam's command line cannot read is refused, with status 2, as
opam refuses it, rather than solved as the name of nothing: an operator
left without a version, an empty name, a character no name may hold, and
a path, which opam install takes for a local package to pin:

  $ ../../../bin/main.exe opam . 'dep>='
  error: "dep>=": "=" is not a version
  [2]
  $ ../../../bin/main.exe opam . ''
  error: "": not a package name or atom
  [2]
  $ ../../../bin/main.exe opam . 'dep!1'
  error: "dep!1": not a package name or atom
  [2]
  $ ../../../bin/main.exe opam . ./packages/dep
  error: "./packages/dep": a local package, which is not a query
  [2]

with-test, with-doc and with-dev-setup are query-scoped: each flag turns
its variable on for the names the query asks for and leaves every package
they pull in at false, which is what opam does (opamSwitchState.ml, the
universe's [requested_allpkgs]).  tst.1 asks for tlib under with-test,
tdoc under with-doc and dsetup under with-dev-setup, and mid.1 asks for
mlib under with-test.  Off, none of the four is in:

  $ untimed ../../../bin/main.exe opam . tst
  packages (2):
    mid 1
    tst 1
  encoded solution: 3 core nodes (5 lookups)
  loaded: 6 names, 6 versions

--with-test brings in tlib, the queried package's own test dependency, and
not mlib, which belongs to a package the query merely reaches:

  $ untimed ../../../bin/main.exe opam --with-test . tst
  packages (3):
    mid 1
    tlib 1
    tst 1
  encoded solution: 4 core nodes (6 lookups)
  loaded: 6 names, 6 versions

The other two flags scope the same way, each over its own variable:

  $ untimed ../../../bin/main.exe opam --with-doc . tst
  packages (3):
    mid 1
    tdoc 1
    tst 1
  encoded solution: 4 core nodes (6 lookups)
  loaded: 6 names, 6 versions

  $ untimed ../../../bin/main.exe opam --with-dev-setup . tst
  packages (3):
    dsetup 1
    mid 1
    tst 1
  encoded solution: 4 core nodes (6 lookups)
  loaded: 6 names, 6 versions

Naming mid too puts it in the query, so with-test holds of it as well and
mlib comes in beside tlib.  mlib's own test dependency mleaf stays out:
mlib is reached, not asked for.

  $ untimed ../../../bin/main.exe opam --with-test . tst mid
  packages (4):
    mid 1
    mlib 1
    tlib 1
    tst 1
  encoded solution: 5 core nodes (8 lookups)
  loaded: 7 names, 7 versions

In opam a conflict's filter sees only switch and global variables and the
package's own name and version.  So with-test is undefined there even for
a queried name, and cflt.1's conflict
on dep >= "5" under with-test is void, while its conflict on lib >= "3" on
linux holds:

  $ untimed ../../../bin/main.exe opam --with-test . cflt
  packages (3):
    cflt 1
    dep 9
    lib 2
  encoded solution: 4 core nodes (5 lookups)
  loaded: 3 names, 5 versions

opam-version is the one global variable opam answers with its own version
(unless OPAMVAR_opam_version or a variable overrides it), so the valuation
carries the version of the opam whose answers are being matched, 2.5.2
unless told otherwise.  ov.1 is available
below 2.3 and ov.2 from 2.3 on:

  $ untimed ../../../bin/main.exe opam . ov
  packages (1):
    ov 2
  encoded solution: 2 core nodes (2 lookups)
  loaded: 1 names, 2 versions

--opam-version asks the same question as another opam would:

  $ untimed ../../../bin/main.exe opam --opam-version 2.2.0 . ov
  packages (1):
    ov 1
  encoded solution: 2 core nodes (2 lookups)
  loaded: 1 names, 2 versions

In builtin-0install's order, the default, the query's atoms are walked
last first, as opam hands them to 0install (create_spec conses each onto
the list it builds).  ord-p.2 and ord-q.2 each need ord-r on the other side
of 2, so whichever name is decided first keeps its newest: asked for ord-p
then ord-q, opam installs ord-q.2, ord-p.1 and ord-r.1:

  $ untimed ../../../bin/main.exe opam . ord-p ord-q
  packages (3):
    ord-p 1
    ord-q 2
    ord-r 1
  encoded solution: 4 core nodes (8 lookups)
  loaded: 3 names, 6 versions

In PubGrub's own order the answer is as valid, but which name keeps its
newest is PubGrub's choice:

  $ untimed ../../../bin/main.exe opam --order=pubgrub . ord-p ord-q
  packages (3):
    ord-p 2
    ord-q 1
    ord-r 2
  encoded solution: 4 core nodes (8 lookups)
  loaded: 3 names, 6 versions

--order=random picks the next name and the version to try uniformly, from
a generator seeded by --seed: the same seed gives the same answer, and
another seed may give another, a resolution all the same:

  $ seed0() { untimed ../../../bin/main.exe opam --order=random --seed 0 . ord-p ord-q; }; [ "$(seed0)" = "$(seed0)" ] && seed0
  packages (3):
    ord-p 2
    ord-q 1
    ord-r 2
  encoded solution: 4 core nodes (7 lookups)
  loaded: 3 names, 6 versions
  $ untimed ../../../bin/main.exe opam --order=random --seed 2 . ord-p ord-q
  packages (3):
    ord-p 1
    ord-q 2
    ord-r 1
  encoded solution: 4 core nodes (7 lookups)
  loaded: 3 names, 6 versions

Every filter reads the package's own version as version, _:version or
<name>:version: svd.2 is available from 2 on, its dependency on svl holds
at 2, and its conflict with svl >= "2" too, so opam installs svd.2 beside
svl.1:

  $ untimed ../../../bin/main.exe opam . svd
  packages (2):
    svd 2
    svl 1
  encoded solution: 3 core nodes (5 lookups)
  loaded: 2 names, 4 versions

opam ignores a field it cannot read.  available: is one filter
expression, so two leave avm.1 available; flags: are idents, so a string
leaves flg.2 unflagged, while a tags: entry flags:avoid-version flags tg.2;
and brk.2, which does not parse, is skipped:

  $ untimed ../../../bin/main.exe opam . avm
  packages (1):
    avm 1
  encoded solution: 2 core nodes (2 lookups)
  loaded: 1 names, 1 versions
  parser dropped 1 declarations

  $ untimed ../../../bin/main.exe opam . flg
  packages (1):
    flg 2
  encoded solution: 2 core nodes (2 lookups)
  loaded: 1 names, 2 versions
  parser dropped 1 declarations

  $ untimed ../../../bin/main.exe opam . tg
  packages (1):
    tg 1
  encoded solution: 2 core nodes (2 lookups)
  loaded: 1 names, 2 versions

  $ untimed ../../../bin/main.exe opam . brk
  packages (1):
    brk 1
  encoded solution: 2 core nodes (2 lookups)
  loaded: 1 names, 1 versions
  parser dropped 1 declarations

opam keys a package by its version's order, so eqv.1.0 and eqv.1.00,
whose versions compare equal, are one package to it: the directory it
reads last, the later in byte order, and that directory's opam file.
eqv.1.00 needs dep.3 where eqv.1.0 needs dep.9, and asking for either
version installs eqv.1.00 with dep.3:

  $ untimed ../../../bin/main.exe opam . eqv.1.0
  packages (2):
    dep 3
    eqv 1.00
  encoded solution: 3 core nodes (4 lookups)
  loaded: 2 names, 3 versions

  $ untimed ../../../bin/main.exe opam . eqv.1.00
  packages (2):
    dep 3
    eqv 1.00
  encoded solution: 3 core nodes (4 lookups)
  loaded: 2 names, 3 versions

A repository that cannot be read is a read error, not a refused query:

  $ ../../../bin/main.exe opam nope eqv
  error: nope: No such file or directory
  [3]
  $ ../../../bin/main.exe opam packages/eqv/eqv.1.0/opam eqv
  error: packages/eqv/eqv.1.0/opam: Not a directory
  [3]

opam install refuses an atom no package of the repository meets, whether
or not it is available, and first matches a name that differs only in case
from one other name:

  $ ../../../bin/main.exe opam . nosuch
  error: No package named nosuch found.
  [2]
  $ ../../../bin/main.exe opam . dep nosuch.1
  error: No package named nosuch found.
  [2]
  $ ../../../bin/main.exe opam . dep.99
  error: Package dep has no version 99.
  [2]
  $ ../../../bin/main.exe opam . 'dep>=99'
  error: Package dep has no version >=99.
  [2]
  $ ../../../bin/main.exe opam . 'dep<3'
  error: Package dep has no version <3.
  [2]
  $ untimed ../../../bin/main.exe opam . Dep
  packages (1):
    dep 9
  encoded solution: 2 core nodes (2 lookups)
  loaded: 1 names, 2 versions
