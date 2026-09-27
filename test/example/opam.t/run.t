opam install saturn ocaml-system over seven packages: saturn's with-test
atom on alcotest is filtered away, ocaml 5.2.0 asks for either of two
compilers, and the two share a conflict class.

  $ . ../../frontends/untimed.sh

root () carries the query and depends on itself.  The disjunction is
<ocaml-system{5.2.0} | ocaml-base-compiler{5.2.0}>, emitted reversed so
that its version z0 is ocaml-system, and conflict-class:ocaml-core-compiler
is the class, its versions the two compilers.  The core is 16 packages and
9 edges, among them the ⊥ of saturn, ocaml, both compilers and the class,
which no edge admits.

  $ untimed ../../../bin/main.exe opam --core . saturn ocaml-system
  core: 16 packages, 9 edges
  <ocaml-system{5.2.0} | ocaml-base-compiler{5.2.0}> z0
    -> ocaml-system {5.2.0}
  <ocaml-system{5.2.0} | ocaml-base-compiler{5.2.0}> z1
    -> ocaml-base-compiler {5.2.0}
  conflict-class:ocaml-core-compiler ocaml-base-compiler
  conflict-class:ocaml-core-compiler ocaml-system
  conflict-class:ocaml-core-compiler ⊥
  ocaml 4.14.2
  ocaml 5.1.1
  ocaml 5.2.0
    -> <ocaml-system{5.2.0} | ocaml-base-compiler{5.2.0}> {z0, z1}
  ocaml ⊥
  ocaml-base-compiler 5.2.0
    -> conflict-class:ocaml-core-compiler {ocaml-base-compiler}
  ocaml-base-compiler ⊥
  ocaml-system 5.2.0
    -> conflict-class:ocaml-core-compiler {ocaml-system}
  ocaml-system ⊥
  root ()
    -> ocaml-system {5.2.0}
    -> root {()}
    -> saturn {1.0.0}
  saturn 1.0.0
    -> ocaml {4.14.2, 5.2.0}
  saturn ⊥
  packages (3):
    ocaml 5.2.0
    ocaml-system 5.2.0
    saturn 1.0.0
  encoded solution: 6 core nodes (13 lookups)
  loaded: 5 names, 7 versions

Asked for saturn alone, the same reduction yields ocaml-base-compiler in
ocaml-system's place:

  $ untimed ../../../bin/main.exe opam . saturn
  packages (3):
    ocaml 5.2.0
    ocaml-base-compiler 5.2.0
    saturn 1.0.0
  encoded solution: 6 core nodes (11 lookups)
  loaded: 5 names, 7 versions
