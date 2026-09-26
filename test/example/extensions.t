The paper's §4 extension figures, each instance exactly the figure's.
Each run prints the core walked from the root through the calculus's
lookup theorems, checks that walk against the global reduction
(reduceReal and reduceDeps) restricted to the root's reach, and solves
with PubGrub, decoding the answer through the soundness decoder.  A
reduced name is written as the paper writes it, <...> for ⟨...⟩, and a
package (n,v) inside a name as (n,v).

Fig. conflict-class: the class <k> is the figure's ⟨k⟩, its versions
the names B, C and D.  D 1 is in k but unreachable from A 1, so its edge
(D,1) Δ (⟨k⟩,{D}) is not here, though ⟨k⟩'s version D is.  The answer
takes B 2 beside C 1, as the caption says.

  $ ./extensions/extensions.exe conflict-class
  core: 7 packages, 4 edges
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
  lookups agree with the global reduction from the root
  packages (3):
    A 1
    B 2
    C 1

Fig. conflict: (A,1) Γ (B,{2}) over A 1, B 1 and B 2.  Every node and
the one edge of the figure's reduction, and nothing else.

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

Fig. concurrent, g(x.y.z) = x: every node and all 8 edges of the
figure's reduction, and nothing else.

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

Fig. peer-dependency, g(v) = v: all 6 edges of the figure's reduction.
The figure also draws ⟨C,1⟩ 1, which is real but which no edge reaches,
since (<A,1,C>,1) has no dependency, as its caption says.

  $ ./extensions/extensions.exe peer
  core: 8 packages, 6 edges
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

Fig. visibility: <n,(A,1)> and <n,(D,1)> are the figure's ⟨n,a⟩ and
⟨n,d⟩, and <n,v,m,(A,1)> is ⟨n,v,m,a⟩.  Every node and all 24 edges of
the figure's reduction are here.  <C,(D,1)> 1 is not drawn: an
occurrence has every version of its name, and no edge admits this one.

  $ ./extensions/extensions.exe visibility
  core: 25 packages, 24 edges
  <A,(A,1)> 1
    -> <A,1,B,(A,1)> {1}
    -> <A,1,C,(A,1)> {1, 2}
    -> <A,1,D,(A,1)> {1}
  <A,1,B,(A,1)> 1
    -> <A,1,B> {1}
    -> <B,(A,1)> {1}
  <A,1,B> 1
  <A,1,C,(A,1)> 1
    -> <A,1,C> {1}
    -> <C,(A,1)> {1}
  <A,1,C,(A,1)> 2
    -> <A,1,C> {2}
    -> <C,(A,1)> {2}
  <A,1,C> 1
  <A,1,C> 2
  <A,1,D,(A,1)> 1
    -> <A,1,D> {1}
    -> <D,(A,1)> {1}
  <A,1,D> 1
  <B,(A,1)> 1
    -> <B,1,C,(A,1)> {1}
  <B,1,C,(A,1)> 1
    -> <B,1,C> {1}
    -> <C,(A,1)> {1}
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

Fig. features: every node and all 9 edges of the figure's reduction, and
nothing else.

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

Fig. package-formula: every node and all 5 edges of the figure's
reduction, and nothing else; the disjunct's name is the figure's.

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

Fig. variable-formula, Y_os = {linux, macos}: <os> is ⟨os⟩, and the
disjunct <¬(<os>,{linux}) ∨ (B,{1})> is the figure's
⟨¬(os = linux) ∨ (B,{1})⟩, the comparison held as the atom it lifts to.
All 3 edges are the figure's.  The figure omits A ⊥ and B ⊥, which no
edge admits.  The answer takes alternative 1, so no version of <os> is
selected and the assignment is the decoder's default.

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

Fig. virtual: every node and all 6 edges of the figure's reduction, and
nothing else.

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

Fig. concurrent-feature, g(v) = v, reduced in Fig.
concurrent-feature-reduction: <<D,α>,1> is ⟨⟨D,α⟩,1⟩.  The calculus
proves dependees lookups but no versions lookup, so versions here are the
global reduction's, and the check covers the dependees alone.  30 of the
figure's 36 edges are here and nothing else; the other 6 leave
⟨⟨D,β⟩,1⟩, ⟨D,1,β,F,δ⟩ and ⟨⟨F,δ⟩,1⟩, which the figure lists but no edge
from A 1 reaches, C 1 admitting D only at 2 and 3.

  $ ./extensions/extensions.exe concurrent-features
  core: 24 packages, 30 edges
  <<D,α>,1> 1
    -> <D,1,F> {1}
    -> <D,1,α,F,γ> {1}
    -> <D,1> {1}
  <<D,α>,2> 2
    -> <D,2> {2}
  <<D,β>,2> 2
    -> <D,2> {2}
  <<D,β>,3> 3
    -> <D,3> {3}
  <<F,γ>,1> 1
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
