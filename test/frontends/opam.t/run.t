  $ ../../../src/main.exe opam . app | sed -E '/^(parse|solve) [0-9.]+s$/d'
  opam packages (2, core solution 5 nodes):
    app.1
    c.1
  loaded: 3 names, 2 package versions

A dependency constrained to the depender's own version takes that version,
not the newest one available:

  $ ../../../src/main.exe opam . tool | sed -E '/^(parse|solve) [0-9.]+s$/d'
  opam packages (2, core solution 4 nodes):
    lib.2
    tool.2
  loaded: 2 names, 3 package versions

A parenthesised group conjoins its elements, as the top level of a brace
does, so both ends of (>= "2" < "4") bind and dep.9 is out of range:

  $ ../../../src/main.exe opam . grp | sed -E '/^(parse|solve) [0-9.]+s$/d'
  opam packages (2, core solution 4 nodes):
    dep.3
    grp.1
  loaded: 2 names, 3 package versions

Depexts constrain nothing: they are read off the finished resolution, so
what is reported is the union over the selected packages of the depext
entries whose
filter holds under the environment.  sys.1 asks for libfoo-dev and
pkg-config on a debian family and libbar-dev on alpine; helper.1 asks
unconditionally for pkg-config, which is named once:

  $ ../../../src/main.exe opam . sys | sed -E '/^(parse|solve) [0-9.]+s$/d'
  opam packages (2, core solution 4 nodes):
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

  $ ../../../src/main.exe opam . avoid | sed -E '/^(parse|solve) [0-9.]+s$/d'
  opam packages (1, core solution 3 nodes):
    avoid.1
  loaded: 1 names, 2 package versions

  $ ../../../src/main.exe opam . depr | sed -E '/^(parse|solve) [0-9.]+s$/d'
  opam packages (1, core solution 3 nodes):
    depr.1
  loaded: 1 names, 2 package versions

Nothing else works when a dependency pins the flagged version, and it is
selected:

  $ ../../../src/main.exe opam . needav | sed -E '/^(parse|solve) [0-9.]+s$/d'
  opam packages (2, core solution 4 nodes):
    avoid.2
    needav.1
  loaded: 2 names, 3 package versions

opam takes a disjunction's first satisfiable alternative, so a dependency
on three installable packages selects the one written first.  The encoding
reverses the alternatives -- PubGrub decides the larger version and the
disjunct package's largest index selects the last alternative -- so that
this is what falls out:

  $ ../../../src/main.exe opam . pick | sed -E '/^(parse|solve) [0-9.]+s$/d'
  opam packages (2, core solution 5 nodes):
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

  $ ../../../src/main.exe opam . cc-pick | sed -E '/^(parse|solve) [0-9.]+s$/d'
  opam packages (4, core solution 8 nodes):
    cc-a.1
    cc-pick.1
    cc-plain.1
    ccls.1
  loaded: 5 names, 6 package versions

Asking for both names of the class outright has no resolution, and the
class package is what the explanation names:

  $ ../../../src/main.exe opam . cc-both | sed -E '/^(parse|solve) [0-9.]+s$/d'
  unsatisfiable:
  Because cc-a 1 -> conflict-class:ccls cc-a and cc-b 2 -> conflict-class:ccls cc-b, cc-a * or cc-b * is forbidden..
  And because cc-both 1 -> cc-a 1 and cc-both 1 -> cc-b 1 ∪ 2, cc-both * is forbidden.
  And because root () -> cc-both 1 and root -> root (), version solving failed.
  loaded: 3 names, 4 package versions

A request is a query -- a set of names, each with a set of acceptable
versions -- realised as the dependencies of the synthetic root.  Naming
two packages asks for both, and each is solved against the same
repository:

  $ ../../../src/main.exe opam . app tool | sed -E '/^(parse|solve) [0-9.]+s$/d'
  opam packages (4, core solution 7 nodes):
    app.1
    c.1
    lib.2
    tool.2
  loaded: 5 names, 5 package versions

An atom's version constraint is the set of versions its name is accepted
at.  Unconstrained, dep takes its newest version:

  $ ../../../src/main.exe opam . dep | sed -E '/^(parse|solve) [0-9.]+s$/d'
  opam packages (1, core solution 3 nodes):
    dep.9
  loaded: 1 names, 2 package versions

An operator narrows that set, in opam's own command-line syntax:

  $ ../../../src/main.exe opam . 'dep<9' | sed -E '/^(parse|solve) [0-9.]+s$/d'
  opam packages (1, core solution 3 nodes):
    dep.3
  loaded: 1 names, 2 package versions

and NAME.VERSION is opam's shorthand for the =-constraint:

  $ ../../../src/main.exe opam . dep.3 | sed -E '/^(parse|solve) [0-9.]+s$/d'
  opam packages (1, core solution 3 nodes):
    dep.3
  loaded: 1 names, 2 package versions

Constraints and several names compose, the query being one per name:

  $ ../../../src/main.exe opam . 'dep<9' app | sed -E '/^(parse|solve) [0-9.]+s$/d'
  opam packages (3, core solution 6 nodes):
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

  $ ../../../src/main.exe opam . tst | sed -E '/^(parse|solve) [0-9.]+s$/d'
  opam packages (2, core solution 4 nodes):
    mid.1
    tst.1
  loaded: 6 names, 6 package versions

--with-test brings in tlib, the queried package's own test dependency, and
not mlib, which belongs to a package the query merely reaches:

  $ ../../../src/main.exe opam --with-test . tst | sed -E '/^(parse|solve) [0-9.]+s$/d'
  opam packages (3, core solution 5 nodes):
    mid.1
    tlib.1
    tst.1
  loaded: 6 names, 6 package versions

The other two flags scope the same way, each over its own variable:

  $ ../../../src/main.exe opam --with-doc . tst | sed -E '/^(parse|solve) [0-9.]+s$/d'
  opam packages (3, core solution 5 nodes):
    mid.1
    tdoc.1
    tst.1
  loaded: 6 names, 6 package versions

  $ ../../../src/main.exe opam --with-dev-setup . tst | sed -E '/^(parse|solve) [0-9.]+s$/d'
  opam packages (3, core solution 5 nodes):
    dsetup.1
    mid.1
    tst.1
  loaded: 6 names, 6 package versions

Naming mid too puts it in the query, so with-test holds of it as well and
mlib comes in beside tlib.  mlib's own test dependency mleaf stays out:
mlib is reached, not asked for.

  $ ../../../src/main.exe opam --with-test . tst mid | sed -E '/^(parse|solve) [0-9.]+s$/d'
  opam packages (4, core solution 6 nodes):
    mid.1
    mlib.1
    tlib.1
    tst.1
  loaded: 7 names, 7 package versions
