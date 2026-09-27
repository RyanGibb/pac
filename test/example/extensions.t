An instance of each extension.  Each run prints the global reduction
(reduceReal and reduceDeps), whole or, for a placement, whose reduction
runs to hundreds of lines, as its size; checks the core walked from the
root through the calculus's lookup theorems against that reduction
restricted to the root's reach, and solves with PubGrub, decoding the
answer through the soundness decoder.  A reduced name is written <...>,
and a package (n,v) inside a name as (n,v).

Conflict classes: A 1 depends on B 1 or 2 and on C 1, and B 1, C 1 and
D 1 are in the class k.  The class is the name <k>, its versions the
names B, C and D.  The reduction has 5 edges, among them D 1's edge to
(<k>,{D}), though D 1 is unreachable from A 1.  The answer takes B 2
beside C 1.

  $ ./extensions/extensions.exe conflict-class
  core: 8 packages, 5 edges
  <k> B
  <k> C
  <k> D
  A 1
    -> B {1, 2}
    -> C {1}
  B 1
    -> <k> {B}
  B 2
  C 1
    -> <k> {C}
  D 1
    -> <k> {D}
  lookups agree with the global reduction from the root
  packages (3):
    A 1
    B 2
    C 1

Conflicts: A 1 conflicts with B 2, over A 1, B 1 and B 2.  The reduction
has one edge.

  $ ./extensions/extensions.exe conflict
  core: 5 packages, 1 edges
  A 1
    -> B {1, ⊥}
  A ⊥
  B 1
  B 2
  B ⊥
  lookups agree with the global reduction from the root
  packages (1):
    A 1

Concurrent versions, g(x.y.z) = x: A 1.0.0 depends on B 1.0.0 and
C 1.0.0, B on D 1.0.0, 2.0.0 or 2.0.1, and C on D 2.0.0, 2.0.1 or 3.0.0.
The reduction has 8 edges.

  $ ./extensions/extensions.exe concurrent
  core: 11 packages, 8 edges
  <A,1> 1.0.0
    -> <B,1> {1.0.0}
    -> <C,1> {1.0.0}
  <B,1.0.0,D> 1
    -> <D,1> {1.0.0}
  <B,1.0.0,D> 2
    -> <D,2> {2.0.0, 2.0.1}
  <B,1> 1.0.0
    -> <B,1.0.0,D> {1, 2}
  <C,1.0.0,D> 2
    -> <D,2> {2.0.0, 2.0.1}
  <C,1.0.0,D> 3
    -> <D,3> {3.0.0}
  <C,1> 1.0.0
    -> <C,1.0.0,D> {2, 3}
  <D,1> 1.0.0
  <D,2> 2.0.0
  <D,2> 2.0.1
  <D,3> 3.0.0
  lookups agree with the global reduction from the root
  packages (5):
    A 1.0.0
    B 1.0.0
    C 1.0.0
    D 2.0.1
    D 3.0.0
  parents (4):
    B 1.0.0 <- A 1.0.0
    C 1.0.0 <- A 1.0.0
    D 2.0.1 <- B 1.0.0
    D 3.0.0 <- C 1.0.0

Peer dependencies, g(v) = v: A 1 depends on B 1 and on C 2 or 3, and B 1
peers on C 1 or 2.  The reduction has 6 edges, and <C,1> 1, which no edge
reaches, since (<A,1,C>,1) has no dependency.

  $ ./extensions/extensions.exe peer
  core: 9 packages, 6 edges
  <A,1,B> 1
    -> <A,1,C> {1, 2}
    -> <B,1> {1}
  <A,1,C> 1
  <A,1,C> 2
    -> <C,2> {2}
  <A,1,C> 3
    -> <C,3> {3}
  <A,1> 1
    -> <A,1,B> {1}
    -> <A,1,C> {2, 3}
  <B,1> 1
  <C,1> 1
  <C,2> 2
  <C,3> 3
  lookups agree with the global reduction from the root
  packages (3):
    A 1
    B 1
    C 2
  parents (2):
    B 1 <- A 1
    C 2 <- A 1

Visibility: A 1 depends on B 1, on C 1 or 2 and on D 1, B 1 on C 1, and
D 1 on C 2 and E 1; every dependency is public but D 1's on C.  <n,(A,1)>
is n's occurrence under the origin A 1, and <n,(D,1)> under D 1.  The
reduction has 38 edges, 24 of them reached from <A,(A,1)> 1.  <A,(D,1)> 1
and <B,(D,1)> 1, with their intermediates and 14 edges, and
<D,1,C,(A,1)> 2, which has none, are unreachable from it.  <C,(D,1)> 1 is
reached: an occurrence has every version of its name, though no edge
admits this one.

  $ ./extensions/extensions.exe visibility
  core: 33 packages, 38 edges
  <A,(A,1)> 1
    -> <A,1,B,(A,1)> {1}
    -> <A,1,C,(A,1)> {1, 2}
    -> <A,1,D,(A,1)> {1}
  <A,(D,1)> 1
    -> <A,1,B,(D,1)> {1}
    -> <A,1,C,(D,1)> {1, 2}
    -> <A,1,D,(D,1)> {1}
  <A,1,B,(A,1)> 1
    -> <A,1,B> {1}
    -> <B,(A,1)> {1}
  <A,1,B,(D,1)> 1
    -> <A,1,B> {1}
    -> <B,(D,1)> {1}
  <A,1,B> 1
  <A,1,C,(A,1)> 1
    -> <A,1,C> {1}
    -> <C,(A,1)> {1}
  <A,1,C,(A,1)> 2
    -> <A,1,C> {2}
    -> <C,(A,1)> {2}
  <A,1,C,(D,1)> 1
    -> <A,1,C> {1}
    -> <C,(D,1)> {1}
  <A,1,C,(D,1)> 2
    -> <A,1,C> {2}
    -> <C,(D,1)> {2}
  <A,1,C> 1
  <A,1,C> 2
  <A,1,D,(A,1)> 1
    -> <A,1,D> {1}
    -> <D,(A,1)> {1}
  <A,1,D,(D,1)> 1
    -> <A,1,D> {1}
    -> <D,(D,1)> {1}
  <A,1,D> 1
  <B,(A,1)> 1
    -> <B,1,C,(A,1)> {1}
  <B,(D,1)> 1
    -> <B,1,C,(D,1)> {1}
  <B,1,C,(A,1)> 1
    -> <B,1,C> {1}
    -> <C,(A,1)> {1}
  <B,1,C,(D,1)> 1
    -> <B,1,C> {1}
    -> <C,(D,1)> {1}
  <B,1,C> 1
  <C,(A,1)> 1
  <C,(A,1)> 2
  <C,(D,1)> 1
  <C,(D,1)> 2
  <D,(A,1)> 1
    -> <D,(D,1)> {1}
    -> <D,1,E,(A,1)> {1}
  <D,(D,1)> 1
    -> <D,1,C,(D,1)> {2}
    -> <D,1,E,(D,1)> {1}
  <D,1,C,(A,1)> 2
  <D,1,C,(D,1)> 2
    -> <C,(D,1)> {2}
    -> <D,1,C> {2}
  <D,1,C> 2
  <D,1,E,(A,1)> 1
    -> <D,1,E> {1}
    -> <E,(A,1)> {1}
  <D,1,E,(D,1)> 1
    -> <D,1,E> {1}
    -> <E,(D,1)> {1}
  <D,1,E> 1
  <E,(A,1)> 1
  <E,(D,1)> 1
  lookups agree with the global reduction from the root
  packages (6):
    A 1
    B 1
    C 1
    C 2
    D 1
    E 1
  parents (6):
    B 1 <- A 1
    C 1 <- A 1
    C 1 <- B 1
    C 2 <- D 1
    D 1 <- A 1
    E 1 <- D 1

Features: A 1 depends on B 1 and C 1, B 1 on D 1 with features α and β,
and C 1 on D 1 with β; D 1's α adds a dependency on E 1 and its β one on
F 1.  The reduction has 9 edges.

  $ ./extensions/extensions.exe features
  core: 8 packages, 9 edges
  <D,α> 1
    -> D {1}
    -> E {1}
  <D,β> 1
    -> D {1}
    -> F {1}
  A 1
    -> B {1}
    -> C {1}
  B 1
    -> <D,α> {1}
    -> <D,β> {1}
  C 1
    -> <D,β> {1}
  D 1
  E 1
  F 1
  lookups agree with the global reduction from the root
  packages (6):
    A 1 {}
    B 1 {}
    C 1 {}
    D 1 {α, β}
    E 1 {}
    F 1 {}

Package formulas: A 1 depends on (B 2 ∧ C 1) ∨ (B 1 ∧ ¬C 1).  The
reduction has 5 edges and one disjunct.

  $ ./extensions/extensions.exe package-formula
  core: 9 packages, 5 edges
  <((B,{2}) ∧ (C,{1})) ∨ ((B,{1}) ∧ ¬(C,{1}))> 0
    -> B {2}
    -> C {1}
  <((B,{2}) ∧ (C,{1})) ∨ ((B,{1}) ∧ ¬(C,{1}))> 1
    -> B {1}
    -> C {⊥}
  A 1
    -> <((B,{2}) ∧ (C,{1})) ∨ ((B,{1}) ∧ ¬(C,{1}))> {0, 1}
  A ⊥
  B 1
  B 2
  B ⊥
  C 1
  C ⊥
  lookups agree with the global reduction from the root
  packages (2):
    A 1
    B 1

Variable formulas, Y_os = {linux, macos}: A 1 depends on
¬(os = linux) ∨ B 1.  The variable is the name <os>, and the disjunct
<¬(<os>,{linux}) ∨ (B,{1})> holds the comparison as the atom it lifts to.
The reduction has 3 edges, and A ⊥ and B ⊥, which no edge admits.  The
answer takes alternative 1, so no version of <os> is selected and the
assignment is the decoder's default.

  $ ./extensions/extensions.exe variable-formula
  core: 8 packages, 3 edges
  <os> linux
  <os> macos
  <¬(<os>,{linux}) ∨ (B,{1})> 0
    -> <os> {macos}
  <¬(<os>,{linux}) ∨ (B,{1})> 1
    -> B {1}
  A 1
    -> <¬(<os>,{linux}) ∨ (B,{1})> {0, 1}
  A ⊥
  B 1
  B ⊥
  lookups agree with the global reduction from the root
  packages (2):
    A 1
    B 1
  assignment: os = linux

Virtual packages: A 1 depends on D 1 and E 1; B 1 and C 1 provide D 1,
and F 1 provides E 1.  The reduction has 6 edges.

  $ ./extensions/extensions.exe virtual
  core: 9 packages, 6 edges
  <(A,1),D> <B,1>
    -> B {1}
  <(A,1),D> <C,1>
    -> C {1}
  <(A,1),E> <E,1>
    -> E {1}
  <(A,1),E> <F,1>
    -> F {1}
  A 1
    -> <(A,1),D> {<B,1>, <C,1>}
    -> <(A,1),E> {<E,1>, <F,1>}
  B 1
  C 1
  E 1
  F 1
  lookups agree with the global reduction from the root
  packages (3):
    A 1
    C 1
    F 1
  providers (2):
    C 1 for D <- A 1
    F 1 for E <- A 1

Concurrent versions with features, g(v) = v: A 1 depends on B 1 and
C 1, B 1 on D 1 or 2 with α, and C 1 on D 2 or 3 with β; D 1's α adds a
dependency on F 1 with γ, and its β one on F 1 with δ.  <<D,α>,1> is D's
feature α at granularity 1.  The reduction has 36 edges.  The walk from
A 1 does not reach <<D,β>,1>, <D,1,β,F,δ> or <<F,δ>,1>, C 1 admitting D
only at 2 and 3.

  $ ./extensions/extensions.exe concurrent-features
  core: 27 packages, 36 edges
  <<D,α>,1> 1
    -> <D,1,F> {1}
    -> <D,1,α,F,γ> {1}
    -> <D,1> {1}
  <<D,α>,2> 2
    -> <D,2> {2}
  <<D,β>,1> 1
    -> <D,1,F> {1}
    -> <D,1,β,F,δ> {1}
    -> <D,1> {1}
  <<D,β>,2> 2
    -> <D,2> {2}
  <<D,β>,3> 3
    -> <D,3> {3}
  <<F,γ>,1> 1
    -> <F,1> {1}
  <<F,δ>,1> 1
    -> <F,1> {1}
  <A,1,B> 1
    -> <B,1> {1}
  <A,1,C> 1
    -> <C,1> {1}
  <A,1> 1
    -> <A,1,B> {1}
    -> <A,1,C> {1}
  <B,1,D,α> 1
    -> <<D,α>,1> {1}
    -> <B,1,D> {1}
  <B,1,D,α> 2
    -> <<D,α>,2> {2}
    -> <B,1,D> {2}
  <B,1,D> 1
    -> <D,1> {1}
  <B,1,D> 2
    -> <D,2> {2}
  <B,1> 1
    -> <B,1,D,α> {1, 2}
    -> <B,1,D> {1, 2}
  <C,1,D,β> 2
    -> <<D,β>,2> {2}
    -> <C,1,D> {2}
  <C,1,D,β> 3
    -> <<D,β>,3> {3}
    -> <C,1,D> {3}
  <C,1,D> 2
    -> <D,2> {2}
  <C,1,D> 3
    -> <D,3> {3}
  <C,1> 1
    -> <C,1,D,β> {2, 3}
    -> <C,1,D> {2, 3}
  <D,1,F> 1
    -> <F,1> {1}
  <D,1,α,F,γ> 1
    -> <<F,γ>,1> {1}
    -> <D,1,F> {1}
  <D,1,β,F,δ> 1
    -> <<F,δ>,1> {1}
    -> <D,1,F> {1}
  <D,1> 1
  <D,2> 2
  <D,3> 3
  <F,1> 1
  lookups agree with the global reduction from the root
  packages (5):
    A 1 {}
    B 1 {}
    C 1 {}
    D 2 {α}
    D 3 {β}
  parents (4):
    B 1 <- A 1
    C 1 <- A 1
    D 2 <- B 1
    D 3 <- C 1

Placement, with depth bound 2: R 1 depends on A 1 and B 1, A 1 on C 1,
B 1 on A 1 and C 2, and C 2 peers on A 1, which it resolves by walking up
from its own location as a dependency would, except that the walk may not
land in C 2's own directory.  A location <ℓ,a> holds a version of a or ⊥,
and only ⊥ at depth 2; a walk <ℓ⇑a> holds where the first-match walk up
from ℓ for a lands, (ℓ',v), or ⊥.  The reduction over the names A, B and
C has 195 packages and 289 edges.  The answer hoists A 1, which serves R
and B, and C 1, which serves A, and nests C 2 under B, where it shadows
C 1 for B; C 2's peer walks from B/C through the absent B/C/A and B/A to
the hoisted A 1.

  $ ./extensions/extensions.exe placement
  core: 195 packages, 289 edges
  lookups agree with the global reduction from the root
  layout (4):
    A 1
    B 1
    B/C 2
    C 1

The npm reading's placement instance, with depth bound 1: the project
depends on x, an npm: alias of b 1, and on a 1, which depends on b 2.  The
lookups read an occupant's edges off its manifest alone, each edge's
accepted set off the package it names, and each key's versions off the
packages aliased to it.  Key x holds b 1 and key b holds b 2.

  $ ./extensions/extensions.exe npm-placement
  core: 50 packages, 59 edges
  lookups agree with the global reduction from the root
  layout (3):
    a a@1
    b b@2
    x b@1
