The paper's opam worked example: opam install saturn ocaml-system over
seven packages, saturn's with-test atom on alcotest filtered away, ocaml
5.2.0's disjunction between the two compilers, and their conflict class.

  $ . ../../frontends/untimed.sh

In the figure's notation, pac's names read:
- root () is r *, the root carrying the query, whose edge to itself is the
figure's loop;
- <ocaml-system{5.2.0} | ocaml-base-compiler{5.2.0}> is <chi_0, chi_1>,
emitted reversed so that chi_0 is sys, and its versions z0 and z1 are
the figure's 0 and 1;
- conflict-class:ocaml-core-compiler is <occ>, its versions
ocaml-base-compiler and ocaml-system the figure's obc and sys;
- ocaml-base-compiler and ocaml-system are obc and sys.
Every node and all 9 edges of the figure's reduction are here.  The figure
omits on purpose the absent versions, which no edge admits: the ⊥ of
saturn, ocaml, ocaml-base-compiler, ocaml-system and <occ>, the 5 packages
beyond its 11.

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
