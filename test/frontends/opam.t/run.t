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
what is reported is the union over the selected packages of the rows whose
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
inverts the pair -- PubGrub decides the larger version and the disjunction
gadget's One selects the right branch -- so that this is what falls out:

  $ ../../../src/main.exe opam . pick | sed -E '/^(parse|solve) [0-9.]+s$/d'
  opam packages (2, core solution 6 nodes):
    alt1.1
    pick.1
  loaded: 4 names, 4 package versions
