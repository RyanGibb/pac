  $ ../../../src/main.exe opam . app | sed -E 's/, [0-9.]+s$//; /^solve [0-9.]+s$/d'
  archive loaded: 1 variables
  opam packages (2, core solution 9 nodes):
    app.1
    c.1

A dependency constrained to the depender's own version takes that version,
not the newest one available:

  $ ../../../src/main.exe opam . tool | sed -E 's/, [0-9.]+s$//; /^solve [0-9.]+s$/d'
  archive loaded: 1 variables
  opam packages (2, core solution 8 nodes):
    lib.2
    tool.2

A parenthesised group conjoins its elements, as the top level of a brace
does, so both ends of (>= "2" < "4") bind and dep.9 is out of range:

  $ ../../../src/main.exe opam . grp | sed -E 's/, [0-9.]+s$//; /^solve [0-9.]+s$/d'
  archive loaded: 1 variables
  opam packages (2, core solution 8 nodes):
    dep.3
    grp.1

Depexts constrain nothing: they are read off the finished resolution, so
what is reported is the union over the selected packages of the rows whose
filter holds under the environment.  sys.1 asks for libfoo-dev and
pkg-config on a debian family and libbar-dev on alpine; helper.1 asks
unconditionally for pkg-config, which is named once:

  $ ../../../src/main.exe opam . sys | sed -E 's/, [0-9.]+s$//; /^solve [0-9.]+s$/d'
  archive loaded: 1 variables
  opam packages (2, core solution 8 nodes):
    helper.1
    sys.1
  system packages (2):
    libfoo-dev
    pkg-config
