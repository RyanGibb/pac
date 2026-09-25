  $ ../../../bin/main.exe opam . app | sed -E '/^(parse|solve) [0-9.]+s$/d'
  opam packages (2, core solution 4 nodes):
    app.1
    c.1
  loaded: 3 names, 2 package versions

A dependency constrained to the depender's own version takes that version,
not the newest one available:

  $ ../../../bin/main.exe opam . tool | sed -E '/^(parse|solve) [0-9.]+s$/d'
  opam packages (2, core solution 3 nodes):
    lib.2
    tool.2
  loaded: 2 names, 3 package versions

A parenthesised group conjoins its elements, as the top level of a brace
does, so both ends of (>= "2" < "4") bind and dep.9 is out of range:

  $ ../../../bin/main.exe opam . grp | sed -E '/^(parse|solve) [0-9.]+s$/d'
  opam packages (2, core solution 3 nodes):
    dep.3
    grp.1
  loaded: 2 names, 3 package versions

A version disjunction inside one brace is one set of versions, as opam reads
it, so dep takes the newest version in either range, not the lower range's
dep.3 for being written first:

  $ ../../../bin/main.exe opam . bdisj | sed -E '/^(parse|solve) [0-9.]+s$/d'
  opam packages (2, core solution 3 nodes):
    bdisj.1
    dep.9
  loaded: 2 names, 3 package versions

A brace mixing a filter into the disjunction stays two atoms under a
disjunction, each with its own filter.  Without --with-test only < "5" is
left, and with it the unconstrained alternative, written first, is taken:

  $ ../../../bin/main.exe opam . bmix | sed -E '/^(parse|solve) [0-9.]+s$/d'
  opam packages (2, core solution 3 nodes):
    bmix.1
    dep.3
  loaded: 2 names, 3 package versions

  $ ../../../bin/main.exe opam --with-test . bmix | sed -E '/^(parse|solve) [0-9.]+s$/d'
  opam packages (2, core solution 4 nodes):
    bmix.1
    dep.9
  loaded: 2 names, 3 package versions

pin-depends is read only when its owner is pinned, and nothing is pinned
here, so pind.1's entry for dep.dev constrains nothing:

  $ ../../../bin/main.exe opam . pind | sed -E '/^(parse|solve) [0-9.]+s$/d'
  opam packages (2, core solution 3 nodes):
    dep.9
    pind.1
  loaded: 2 names, 3 package versions

Depexts constrain nothing: they are read off the finished resolution, so
what is reported is the union over the selected packages of the depext
entries whose
filter holds under the environment.  sys.1 asks for libfoo-dev and
pkg-config on a debian family and libbar-dev on alpine; helper.1 asks
unconditionally for pkg-config, which is named once:

  $ ../../../bin/main.exe opam . sys | sed -E '/^(parse|solve) [0-9.]+s$/d'
  opam packages (2, core solution 3 nodes):
    helper.1
    sys.1
  system packages (2):
    libfoo-dev
    pkg-config
  loaded: 2 names, 2 package versions

The avoid-version and deprecated flags say "select this only if nothing
else works", which is a preference and not a constraint.  A flagged
version is ranked below every unflagged version of its name, so the older
avoid.1 and depr.1 are taken over the newer flagged ones:

  $ ../../../bin/main.exe opam . avoid | sed -E '/^(parse|solve) [0-9.]+s$/d'
  opam packages (1, core solution 2 nodes):
    avoid.1
  loaded: 1 names, 2 package versions

  $ ../../../bin/main.exe opam . depr | sed -E '/^(parse|solve) [0-9.]+s$/d'
  opam packages (1, core solution 2 nodes):
    depr.1
  loaded: 1 names, 2 package versions

Nothing else works when a dependency pins the flagged version, and it is
selected:

  $ ../../../bin/main.exe opam . needav | sed -E '/^(parse|solve) [0-9.]+s$/d'
  opam packages (2, core solution 3 nodes):
    avoid.2
    needav.1
  loaded: 2 names, 3 package versions

opam's builtin-0install takes a disjunction's first satisfiable alternative
(unless opam's CNF rewrite has reshaped it), so a dependency on three
installable packages selects the one written first.  The encoding
reverses the alternatives -- PubGrub decides the larger version and the
disjunct package's largest index selects the last alternative -- so that
this is what falls out:

  $ ../../../bin/main.exe opam . pick | sed -E '/^(parse|solve) [0-9.]+s$/d'
  opam packages (2, core solution 4 nodes):
    alt1.1
    pick.1
  loaded: 4 names, 4 package versions

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

  $ ../../../bin/main.exe opam . cc-pick | sed -E '/^(parse|solve) [0-9.]+s$/d'
  opam packages (4, core solution 7 nodes):
    cc-a.1
    cc-pick.1
    cc-plain.1
    ccls.1
  loaded: 5 names, 6 package versions

Asking for both names of the class outright has no resolution, and the
class package is what the explanation names:

  $ ../../../bin/main.exe opam . cc-both | sed -E '/^(parse|solve) [0-9.]+s$/d'
  unsatisfiable:
  Because cc-a 1 -> conflict-class:ccls cc-a and cc-b 2 -> conflict-class:ccls cc-b, cc-a (-∞, ⊥) or cc-b (-∞, ⊥) is forbidden..
  And because cc-both 1 -> cc-a 1 and cc-both 1 -> cc-b 1 ∪ 2, cc-both (-∞, ⊥) is forbidden.
  And because root () -> cc-both 1 and root -> root (), version solving failed.
  loaded: 3 names, 4 package versions

A conflict holds whichever side of it the solver decides first.  cfl-a.1
conflicts with cfl-b and cfl-c.1 depends on cfl-a; asking for cfl-c and
cfl-b.1 has PubGrub decide cfl-b before it reaches cfl-c, let alone cfl-a.
The conflict is cfl-a's own edge: every name has an absent version ⊥
besides its real ones, and a conflict on cfl-b is a dependency on cfl-b at
the versions the conflict does not name, or absent -- here ⊥ alone, the
conflict naming every version.  Nothing hangs on cfl-b's side, so the order
in which the two are decided cannot lose it:

  $ ../../../bin/main.exe opam . cfl-c cfl-b.1 | sed -E '/^(parse|solve) [0-9.]+s$/d'
  unsatisfiable:
  Because cfl-c 1 -> cfl-a 1 and cfl-a 1 -> cfl-b ⊥, cfl-c (-∞, ⊥) requires cfl-b ⊥.
  And because root () -> cfl-b 1, cfl-c (-∞, ⊥) or root * is forbidden.
  And because root () -> cfl-c 1 and root -> root (), version solving failed.
  loaded: 3 names, 4 package versions

A name only a conflict reaches is left absent rather than installed: ⊥ is
the greatest version, and PubGrub decides the greatest:

  $ ../../../bin/main.exe opam . cfl-c | sed -E '/^(parse|solve) [0-9.]+s$/d'
  opam packages (2, core solution 4 nodes):
    cfl-a.1
    cfl-c.1
  loaded: 3 names, 4 package versions

A request is a query -- a set of names, each with a set of acceptable
versions -- realised as the dependencies of the synthetic root.  Naming
two packages asks for both, and each is solved against the same
repository:

  $ ../../../bin/main.exe opam . app tool | sed -E '/^(parse|solve) [0-9.]+s$/d'
  opam packages (4, core solution 6 nodes):
    app.1
    c.1
    lib.2
    tool.2
  loaded: 5 names, 5 package versions

An atom's version constraint is the set of versions its name is accepted
at.  Unconstrained, dep takes its newest version:

  $ ../../../bin/main.exe opam . dep | sed -E '/^(parse|solve) [0-9.]+s$/d'
  opam packages (1, core solution 2 nodes):
    dep.9
  loaded: 1 names, 2 package versions

An operator narrows that set, in opam's own command-line syntax:

  $ ../../../bin/main.exe opam . 'dep<9' | sed -E '/^(parse|solve) [0-9.]+s$/d'
  opam packages (1, core solution 2 nodes):
    dep.3
  loaded: 1 names, 2 package versions

and NAME.VERSION is opam's shorthand for the =-constraint:

  $ ../../../bin/main.exe opam . dep.3 | sed -E '/^(parse|solve) [0-9.]+s$/d'
  opam packages (1, core solution 2 nodes):
    dep.3
  loaded: 1 names, 2 package versions

Constraints and several names compose, the query being one per name:

  $ ../../../bin/main.exe opam . 'dep<9' app | sed -E '/^(parse|solve) [0-9.]+s$/d'
  opam packages (3, core solution 5 nodes):
    app.1
    c.1
    dep.3
  loaded: 4 names, 4 package versions

with-test, with-doc and with-dev-setup are query-scoped: each flag turns
its variable on for the names the query asks for and leaves every package
they pull in at false, which is what opam does (opamSwitchState.ml, the
universe's [requested_allpkgs]).  tst.1 asks for tlib under with-test,
tdoc under with-doc and dsetup under with-dev-setup, and mid.1 asks for
mlib under with-test.  Off, none of the four is in:

  $ ../../../bin/main.exe opam . tst | sed -E '/^(parse|solve) [0-9.]+s$/d'
  opam packages (2, core solution 3 nodes):
    mid.1
    tst.1
  loaded: 6 names, 6 package versions

--with-test brings in tlib, the queried package's own test dependency, and
not mlib, which belongs to a package the query merely reaches:

  $ ../../../bin/main.exe opam --with-test . tst | sed -E '/^(parse|solve) [0-9.]+s$/d'
  opam packages (3, core solution 4 nodes):
    mid.1
    tlib.1
    tst.1
  loaded: 6 names, 6 package versions

The other two flags scope the same way, each over its own variable:

  $ ../../../bin/main.exe opam --with-doc . tst | sed -E '/^(parse|solve) [0-9.]+s$/d'
  opam packages (3, core solution 4 nodes):
    mid.1
    tdoc.1
    tst.1
  loaded: 6 names, 6 package versions

  $ ../../../bin/main.exe opam --with-dev-setup . tst | sed -E '/^(parse|solve) [0-9.]+s$/d'
  opam packages (3, core solution 4 nodes):
    dsetup.1
    mid.1
    tst.1
  loaded: 6 names, 6 package versions

Naming mid too puts it in the query, so with-test holds of it as well and
mlib comes in beside tlib.  mlib's own test dependency mleaf stays out:
mlib is reached, not asked for.

  $ ../../../bin/main.exe opam --with-test . tst mid | sed -E '/^(parse|solve) [0-9.]+s$/d'
  opam packages (4, core solution 5 nodes):
    mid.1
    mlib.1
    tlib.1
    tst.1
  loaded: 7 names, 7 package versions

In opam a conflict's filter sees only switch and global variables and the
package's own name and version.  So with-test is undefined there even for
a queried name, and cflt.1's conflict
on dep >= "5" under with-test is void, while its conflict on lib >= "3" on
linux holds:

  $ ../../../bin/main.exe opam --with-test . cflt | sed -E '/^(parse|solve) [0-9.]+s$/d'
  opam packages (3, core solution 4 nodes):
    cflt.1
    dep.9
    lib.2
  loaded: 3 names, 5 package versions

opam-version is the one global variable opam answers with its own version
(unless OPAMVAR_opam_version or a variable overrides it), so the valuation
carries the version of the opam whose answers are being matched, 2.5.2
unless told otherwise.  ov.1 is available
below 2.3 and ov.2 from 2.3 on:

  $ ../../../bin/main.exe opam . ov | sed -E '/^(parse|solve) [0-9.]+s$/d'
  opam packages (1, core solution 2 nodes):
    ov.2
  loaded: 1 names, 2 package versions

--opam-version asks the same question as another opam would:

  $ ../../../bin/main.exe opam --opam-version 2.2.0 . ov | sed -E '/^(parse|solve) [0-9.]+s$/d'
  opam packages (1, core solution 2 nodes):
    ov.1
  loaded: 1 names, 2 package versions

Under --0install-order the query's atoms are walked last first, as opam
hands them to 0install (create_spec conses each onto the list it builds).
ord-p.2 and ord-q.2 each need ord-r on the other side of 2, so whichever
name is decided first keeps its newest: asked for ord-p then ord-q, opam
installs ord-q.2, ord-p.1 and ord-r.1:

  $ ../../../bin/main.exe opam --0install-order . ord-p ord-q | sed -E '/^(parse|solve) [0-9.]+s$/d'
  opam packages (3, core solution 4 nodes):
    ord-p.1
    ord-q.2
    ord-r.1
  loaded: 3 names, 6 package versions

Every filter reads the package's own version as version, _:version or
<name>:version: svd.2 is available from 2 on, its dependency on svl holds
at 2, and its conflict with svl >= "2" too, so opam installs svd.2 beside
svl.1:

  $ ../../../bin/main.exe opam . svd | sed -E '/^(parse|solve) [0-9.]+s$/d'
  opam packages (2, core solution 3 nodes):
    svd.2
    svl.1
  loaded: 2 names, 4 package versions

opam ignores a field it cannot read.  available: is one filter
expression, so two leave avm.1 available; flags: are idents, so a string
leaves flg.2 unflagged, while a tags: entry flags:avoid-version flags tg.2;
and brk.2, which does not parse, is skipped:

  $ ../../../bin/main.exe opam . avm | sed -E '/^(parse|solve) [0-9.]+s$/d'
  opam packages (1, core solution 2 nodes):
    avm.1
  loaded: 1 names, 1 package versions
  parser dropped 1 declarations

  $ ../../../bin/main.exe opam . flg | sed -E '/^(parse|solve) [0-9.]+s$/d'
  opam packages (1, core solution 2 nodes):
    flg.2
  loaded: 1 names, 2 package versions
  parser dropped 1 declarations

  $ ../../../bin/main.exe opam . tg | sed -E '/^(parse|solve) [0-9.]+s$/d'
  opam packages (1, core solution 2 nodes):
    tg.1
  loaded: 1 names, 2 package versions

  $ ../../../bin/main.exe opam . brk | sed -E '/^(parse|solve) [0-9.]+s$/d'
  opam packages (1, core solution 2 nodes):
    brk.1
  loaded: 1 names, 1 package versions
  parser dropped 1 declarations
