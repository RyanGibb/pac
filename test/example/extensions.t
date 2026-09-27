The paper's §4 extension figures, each instance exactly the figure's.
Each run prints the whole global reduction (reduceReal and reduceDeps),
checks the core walked from the root through the calculus's lookup
theorems against that reduction restricted to the root's reach, and
solves with PubGrub, decoding the answer through the soundness decoder.
A reduced name is written as the paper writes it, <...> for ⟨...⟩, and a
package (n,v) inside a name as (n,v).

Fig. conflict-class: the class <k> is the figure's ⟨k⟩, its versions
the names B, C and D.  Every node and all 5 edges of the figure's
reduction, and nothing else, among them D 1's edge (D,1) Δ (⟨k⟩,{D}),
though D 1 is unreachable from A 1.  The answer takes B 2 beside C 1, as
the caption says.

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

Fig. peer-dependency, g(v) = v: every node and all 6 edges of the
figure's reduction, and nothing else, among them ⟨C,1⟩ 1, which no edge
reaches, since (<A,1,C>,1) has no dependency, as its caption says.

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

Fig. visibility: <n,(A,1)> and <n,(D,1)> are the figure's ⟨n,a⟩ and
⟨n,d⟩, and <n,v,m,(A,1)> is ⟨n,v,m,a⟩.  Every node and all 24 edges of
the figure's reduction are here, and 9 nodes and 14 edges the figure
does not draw.  The figure draws only what ⟨A,a⟩ 1 reaches, on purpose,
since the whole reduction is too large to draw.  ⟨A,d⟩ 1 and ⟨B,d⟩ 1, with their intermediates and all
14 edges, and ⟨D,1,C,a⟩ 2, which has none, are unreachable from ⟨A,a⟩
1.  <C,(D,1)> 1 is reached: an occurrence has every version of its
name, though no edge admits this one.

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
concurrent-feature-reduction: <<D,α>,1> is ⟨⟨D,α⟩,1⟩.  Every node and
all 36 edges of the figure's reduction, and nothing else.  The walk
from A 1 does not reach ⟨⟨D,β⟩,1⟩, ⟨D,1,β,F,δ⟩ or ⟨⟨F,δ⟩,1⟩,
C 1 admitting D only at 2 and 3.

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

Placement, D = 2: R 1 depends on A 1 and B 1, A 1 on C 1, B 1 on A 1
and C 2, and C 2 peers on A 1, which it resolves by walking up from its
own location as a dependency would, except that the walk may not land in
C 2's own directory.  A location <ℓ,a> holds a version of a or ⊥, and only ⊥ at
depth 2; a walk <ℓ⇑a> holds where the first-match walk up from ℓ for a
lands, (ℓ',v), or ⊥.  Every node and all 289 edges of the reduction at
D = 2 over the keys A, B and C, and nothing else.  The answer hoists
A 1, which serves R and B, and C 1, which serves A, and nests C 2 under
B, where it shadows C 1 for B; C 2's peer walks from B/C through the
absent B/C/A and B/A to the hoisted A 1.

  $ ./extensions/extensions.exe placement
  core: 195 packages, 289 edges
  <A,A> 1
    -> <A/A⇑C> {(A,1), (A/A,1), (ε,1)}
    -> <ε,A> {1}
  <A,A> ⊥
  <A,B> 1
    -> <A/B⇑A> {(A,1), (A/B,1), (ε,1)}
    -> <A/B⇑C> {(A,2), (A/B,2), (ε,2)}
    -> <ε,A> {1}
  <A,B> ⊥
  <A,C> 1
    -> <ε,A> {1}
  <A,C> 2
    -> <A/C⇑A> {(A,1), (ε,1)}
    -> <ε,A> {1}
  <A,C> ⊥
  <A/A,A> ⊥
  <A/A,B> ⊥
  <A/A,C> ⊥
  <A/A⇑A> (A,1)
    -> <A/A,A> {⊥}
    -> <A⇑A> {(A,1)}
  <A/A⇑A> (ε,1)
    -> <A/A,A> {⊥}
    -> <A⇑A> {(ε,1)}
  <A/A⇑A> ⊥
    -> <A/A,A> {⊥}
    -> <A⇑A> {⊥}
  <A/A⇑B> (A,1)
    -> <A/A,B> {⊥}
    -> <A⇑B> {(A,1)}
  <A/A⇑B> (ε,1)
    -> <A/A,B> {⊥}
    -> <A⇑B> {(ε,1)}
  <A/A⇑B> ⊥
    -> <A/A,B> {⊥}
    -> <A⇑B> {⊥}
  <A/A⇑C> (A,1)
    -> <A/A,C> {⊥}
    -> <A⇑C> {(A,1)}
  <A/A⇑C> (A,2)
    -> <A/A,C> {⊥}
    -> <A⇑C> {(A,2)}
  <A/A⇑C> (ε,1)
    -> <A/A,C> {⊥}
    -> <A⇑C> {(ε,1)}
  <A/A⇑C> (ε,2)
    -> <A/A,C> {⊥}
    -> <A⇑C> {(ε,2)}
  <A/A⇑C> ⊥
    -> <A/A,C> {⊥}
    -> <A⇑C> {⊥}
  <A/B,A> ⊥
  <A/B,B> ⊥
  <A/B,C> ⊥
  <A/B⇑A> (A,1)
    -> <A/B,A> {⊥}
    -> <A⇑A> {(A,1)}
  <A/B⇑A> (ε,1)
    -> <A/B,A> {⊥}
    -> <A⇑A> {(ε,1)}
  <A/B⇑A> ⊥
    -> <A/B,A> {⊥}
    -> <A⇑A> {⊥}
  <A/B⇑B> (A,1)
    -> <A/B,B> {⊥}
    -> <A⇑B> {(A,1)}
  <A/B⇑B> (ε,1)
    -> <A/B,B> {⊥}
    -> <A⇑B> {(ε,1)}
  <A/B⇑B> ⊥
    -> <A/B,B> {⊥}
    -> <A⇑B> {⊥}
  <A/B⇑C> (A,1)
    -> <A/B,C> {⊥}
    -> <A⇑C> {(A,1)}
  <A/B⇑C> (A,2)
    -> <A/B,C> {⊥}
    -> <A⇑C> {(A,2)}
  <A/B⇑C> (ε,1)
    -> <A/B,C> {⊥}
    -> <A⇑C> {(ε,1)}
  <A/B⇑C> (ε,2)
    -> <A/B,C> {⊥}
    -> <A⇑C> {(ε,2)}
  <A/B⇑C> ⊥
    -> <A/B,C> {⊥}
    -> <A⇑C> {⊥}
  <A/C,A> ⊥
  <A/C,B> ⊥
  <A/C,C> ⊥
  <A/C⇑A> (A,1)
    -> <A/C,A> {⊥}
    -> <A⇑A> {(A,1)}
  <A/C⇑A> (ε,1)
    -> <A/C,A> {⊥}
    -> <A⇑A> {(ε,1)}
  <A/C⇑A> ⊥
    -> <A/C,A> {⊥}
    -> <A⇑A> {⊥}
  <A/C⇑B> (A,1)
    -> <A/C,B> {⊥}
    -> <A⇑B> {(A,1)}
  <A/C⇑B> (ε,1)
    -> <A/C,B> {⊥}
    -> <A⇑B> {(ε,1)}
  <A/C⇑B> ⊥
    -> <A/C,B> {⊥}
    -> <A⇑B> {⊥}
  <A/C⇑C> (A,1)
    -> <A/C,C> {⊥}
    -> <A⇑C> {(A,1)}
  <A/C⇑C> (A,2)
    -> <A/C,C> {⊥}
    -> <A⇑C> {(A,2)}
  <A/C⇑C> (ε,1)
    -> <A/C,C> {⊥}
    -> <A⇑C> {(ε,1)}
  <A/C⇑C> (ε,2)
    -> <A/C,C> {⊥}
    -> <A⇑C> {(ε,2)}
  <A/C⇑C> ⊥
    -> <A/C,C> {⊥}
    -> <A⇑C> {⊥}
  <A⇑A> (A,1)
    -> <A,A> {1}
  <A⇑A> (ε,1)
    -> <A,A> {⊥}
    -> <ε⇑A> {(ε,1)}
  <A⇑A> ⊥
    -> <A,A> {⊥}
    -> <ε⇑A> {⊥}
  <A⇑B> (A,1)
    -> <A,B> {1}
  <A⇑B> (ε,1)
    -> <A,B> {⊥}
    -> <ε⇑B> {(ε,1)}
  <A⇑B> ⊥
    -> <A,B> {⊥}
    -> <ε⇑B> {⊥}
  <A⇑C> (A,1)
    -> <A,C> {1}
  <A⇑C> (A,2)
    -> <A,C> {2}
  <A⇑C> (ε,1)
    -> <A,C> {⊥}
    -> <ε⇑C> {(ε,1)}
  <A⇑C> (ε,2)
    -> <A,C> {⊥}
    -> <ε⇑C> {(ε,2)}
  <A⇑C> ⊥
    -> <A,C> {⊥}
    -> <ε⇑C> {⊥}
  <B,A> 1
    -> <B/A⇑C> {(B,1), (B/A,1), (ε,1)}
    -> <ε,B> {1}
  <B,A> ⊥
  <B,B> 1
    -> <B/B⇑A> {(B,1), (B/B,1), (ε,1)}
    -> <B/B⇑C> {(B,2), (B/B,2), (ε,2)}
    -> <ε,B> {1}
  <B,B> ⊥
  <B,C> 1
    -> <ε,B> {1}
  <B,C> 2
    -> <B/C⇑A> {(B,1), (ε,1)}
    -> <ε,B> {1}
  <B,C> ⊥
  <B/A,A> ⊥
  <B/A,B> ⊥
  <B/A,C> ⊥
  <B/A⇑A> (B,1)
    -> <B/A,A> {⊥}
    -> <B⇑A> {(B,1)}
  <B/A⇑A> (ε,1)
    -> <B/A,A> {⊥}
    -> <B⇑A> {(ε,1)}
  <B/A⇑A> ⊥
    -> <B/A,A> {⊥}
    -> <B⇑A> {⊥}
  <B/A⇑B> (B,1)
    -> <B/A,B> {⊥}
    -> <B⇑B> {(B,1)}
  <B/A⇑B> (ε,1)
    -> <B/A,B> {⊥}
    -> <B⇑B> {(ε,1)}
  <B/A⇑B> ⊥
    -> <B/A,B> {⊥}
    -> <B⇑B> {⊥}
  <B/A⇑C> (B,1)
    -> <B/A,C> {⊥}
    -> <B⇑C> {(B,1)}
  <B/A⇑C> (B,2)
    -> <B/A,C> {⊥}
    -> <B⇑C> {(B,2)}
  <B/A⇑C> (ε,1)
    -> <B/A,C> {⊥}
    -> <B⇑C> {(ε,1)}
  <B/A⇑C> (ε,2)
    -> <B/A,C> {⊥}
    -> <B⇑C> {(ε,2)}
  <B/A⇑C> ⊥
    -> <B/A,C> {⊥}
    -> <B⇑C> {⊥}
  <B/B,A> ⊥
  <B/B,B> ⊥
  <B/B,C> ⊥
  <B/B⇑A> (B,1)
    -> <B/B,A> {⊥}
    -> <B⇑A> {(B,1)}
  <B/B⇑A> (ε,1)
    -> <B/B,A> {⊥}
    -> <B⇑A> {(ε,1)}
  <B/B⇑A> ⊥
    -> <B/B,A> {⊥}
    -> <B⇑A> {⊥}
  <B/B⇑B> (B,1)
    -> <B/B,B> {⊥}
    -> <B⇑B> {(B,1)}
  <B/B⇑B> (ε,1)
    -> <B/B,B> {⊥}
    -> <B⇑B> {(ε,1)}
  <B/B⇑B> ⊥
    -> <B/B,B> {⊥}
    -> <B⇑B> {⊥}
  <B/B⇑C> (B,1)
    -> <B/B,C> {⊥}
    -> <B⇑C> {(B,1)}
  <B/B⇑C> (B,2)
    -> <B/B,C> {⊥}
    -> <B⇑C> {(B,2)}
  <B/B⇑C> (ε,1)
    -> <B/B,C> {⊥}
    -> <B⇑C> {(ε,1)}
  <B/B⇑C> (ε,2)
    -> <B/B,C> {⊥}
    -> <B⇑C> {(ε,2)}
  <B/B⇑C> ⊥
    -> <B/B,C> {⊥}
    -> <B⇑C> {⊥}
  <B/C,A> ⊥
  <B/C,B> ⊥
  <B/C,C> ⊥
  <B/C⇑A> (B,1)
    -> <B/C,A> {⊥}
    -> <B⇑A> {(B,1)}
  <B/C⇑A> (ε,1)
    -> <B/C,A> {⊥}
    -> <B⇑A> {(ε,1)}
  <B/C⇑A> ⊥
    -> <B/C,A> {⊥}
    -> <B⇑A> {⊥}
  <B/C⇑B> (B,1)
    -> <B/C,B> {⊥}
    -> <B⇑B> {(B,1)}
  <B/C⇑B> (ε,1)
    -> <B/C,B> {⊥}
    -> <B⇑B> {(ε,1)}
  <B/C⇑B> ⊥
    -> <B/C,B> {⊥}
    -> <B⇑B> {⊥}
  <B/C⇑C> (B,1)
    -> <B/C,C> {⊥}
    -> <B⇑C> {(B,1)}
  <B/C⇑C> (B,2)
    -> <B/C,C> {⊥}
    -> <B⇑C> {(B,2)}
  <B/C⇑C> (ε,1)
    -> <B/C,C> {⊥}
    -> <B⇑C> {(ε,1)}
  <B/C⇑C> (ε,2)
    -> <B/C,C> {⊥}
    -> <B⇑C> {(ε,2)}
  <B/C⇑C> ⊥
    -> <B/C,C> {⊥}
    -> <B⇑C> {⊥}
  <B⇑A> (B,1)
    -> <B,A> {1}
  <B⇑A> (ε,1)
    -> <B,A> {⊥}
    -> <ε⇑A> {(ε,1)}
  <B⇑A> ⊥
    -> <B,A> {⊥}
    -> <ε⇑A> {⊥}
  <B⇑B> (B,1)
    -> <B,B> {1}
  <B⇑B> (ε,1)
    -> <B,B> {⊥}
    -> <ε⇑B> {(ε,1)}
  <B⇑B> ⊥
    -> <B,B> {⊥}
    -> <ε⇑B> {⊥}
  <B⇑C> (B,1)
    -> <B,C> {1}
  <B⇑C> (B,2)
    -> <B,C> {2}
  <B⇑C> (ε,1)
    -> <B,C> {⊥}
    -> <ε⇑C> {(ε,1)}
  <B⇑C> (ε,2)
    -> <B,C> {⊥}
    -> <ε⇑C> {(ε,2)}
  <B⇑C> ⊥
    -> <B,C> {⊥}
    -> <ε⇑C> {⊥}
  <C,A> 1
    -> <C/A⇑C> {(C,1), (C/A,1), (ε,1)}
    -> <ε,C> {1, 2}
  <C,A> ⊥
  <C,B> 1
    -> <C/B⇑A> {(C,1), (C/B,1), (ε,1)}
    -> <C/B⇑C> {(C,2), (C/B,2), (ε,2)}
    -> <ε,C> {1, 2}
  <C,B> ⊥
  <C,C> 1
    -> <ε,C> {1, 2}
  <C,C> 2
    -> <C/C⇑A> {(C,1), (ε,1)}
    -> <ε,C> {1, 2}
  <C,C> ⊥
  <C/A,A> ⊥
  <C/A,B> ⊥
  <C/A,C> ⊥
  <C/A⇑A> (C,1)
    -> <C/A,A> {⊥}
    -> <C⇑A> {(C,1)}
  <C/A⇑A> (ε,1)
    -> <C/A,A> {⊥}
    -> <C⇑A> {(ε,1)}
  <C/A⇑A> ⊥
    -> <C/A,A> {⊥}
    -> <C⇑A> {⊥}
  <C/A⇑B> (C,1)
    -> <C/A,B> {⊥}
    -> <C⇑B> {(C,1)}
  <C/A⇑B> (ε,1)
    -> <C/A,B> {⊥}
    -> <C⇑B> {(ε,1)}
  <C/A⇑B> ⊥
    -> <C/A,B> {⊥}
    -> <C⇑B> {⊥}
  <C/A⇑C> (C,1)
    -> <C/A,C> {⊥}
    -> <C⇑C> {(C,1)}
  <C/A⇑C> (C,2)
    -> <C/A,C> {⊥}
    -> <C⇑C> {(C,2)}
  <C/A⇑C> (ε,1)
    -> <C/A,C> {⊥}
    -> <C⇑C> {(ε,1)}
  <C/A⇑C> (ε,2)
    -> <C/A,C> {⊥}
    -> <C⇑C> {(ε,2)}
  <C/A⇑C> ⊥
    -> <C/A,C> {⊥}
    -> <C⇑C> {⊥}
  <C/B,A> ⊥
  <C/B,B> ⊥
  <C/B,C> ⊥
  <C/B⇑A> (C,1)
    -> <C/B,A> {⊥}
    -> <C⇑A> {(C,1)}
  <C/B⇑A> (ε,1)
    -> <C/B,A> {⊥}
    -> <C⇑A> {(ε,1)}
  <C/B⇑A> ⊥
    -> <C/B,A> {⊥}
    -> <C⇑A> {⊥}
  <C/B⇑B> (C,1)
    -> <C/B,B> {⊥}
    -> <C⇑B> {(C,1)}
  <C/B⇑B> (ε,1)
    -> <C/B,B> {⊥}
    -> <C⇑B> {(ε,1)}
  <C/B⇑B> ⊥
    -> <C/B,B> {⊥}
    -> <C⇑B> {⊥}
  <C/B⇑C> (C,1)
    -> <C/B,C> {⊥}
    -> <C⇑C> {(C,1)}
  <C/B⇑C> (C,2)
    -> <C/B,C> {⊥}
    -> <C⇑C> {(C,2)}
  <C/B⇑C> (ε,1)
    -> <C/B,C> {⊥}
    -> <C⇑C> {(ε,1)}
  <C/B⇑C> (ε,2)
    -> <C/B,C> {⊥}
    -> <C⇑C> {(ε,2)}
  <C/B⇑C> ⊥
    -> <C/B,C> {⊥}
    -> <C⇑C> {⊥}
  <C/C,A> ⊥
  <C/C,B> ⊥
  <C/C,C> ⊥
  <C/C⇑A> (C,1)
    -> <C/C,A> {⊥}
    -> <C⇑A> {(C,1)}
  <C/C⇑A> (ε,1)
    -> <C/C,A> {⊥}
    -> <C⇑A> {(ε,1)}
  <C/C⇑A> ⊥
    -> <C/C,A> {⊥}
    -> <C⇑A> {⊥}
  <C/C⇑B> (C,1)
    -> <C/C,B> {⊥}
    -> <C⇑B> {(C,1)}
  <C/C⇑B> (ε,1)
    -> <C/C,B> {⊥}
    -> <C⇑B> {(ε,1)}
  <C/C⇑B> ⊥
    -> <C/C,B> {⊥}
    -> <C⇑B> {⊥}
  <C/C⇑C> (C,1)
    -> <C/C,C> {⊥}
    -> <C⇑C> {(C,1)}
  <C/C⇑C> (C,2)
    -> <C/C,C> {⊥}
    -> <C⇑C> {(C,2)}
  <C/C⇑C> (ε,1)
    -> <C/C,C> {⊥}
    -> <C⇑C> {(ε,1)}
  <C/C⇑C> (ε,2)
    -> <C/C,C> {⊥}
    -> <C⇑C> {(ε,2)}
  <C/C⇑C> ⊥
    -> <C/C,C> {⊥}
    -> <C⇑C> {⊥}
  <C⇑A> (C,1)
    -> <C,A> {1}
  <C⇑A> (ε,1)
    -> <C,A> {⊥}
    -> <ε⇑A> {(ε,1)}
  <C⇑A> ⊥
    -> <C,A> {⊥}
    -> <ε⇑A> {⊥}
  <C⇑B> (C,1)
    -> <C,B> {1}
  <C⇑B> (ε,1)
    -> <C,B> {⊥}
    -> <ε⇑B> {(ε,1)}
  <C⇑B> ⊥
    -> <C,B> {⊥}
    -> <ε⇑B> {⊥}
  <C⇑C> (C,1)
    -> <C,C> {1}
  <C⇑C> (C,2)
    -> <C,C> {2}
  <C⇑C> (ε,1)
    -> <C,C> {⊥}
    -> <ε⇑C> {(ε,1)}
  <C⇑C> (ε,2)
    -> <C,C> {⊥}
    -> <ε⇑C> {(ε,2)}
  <C⇑C> ⊥
    -> <C,C> {⊥}
    -> <ε⇑C> {⊥}
  <ε,A> 1
    -> <A⇑C> {(A,1), (ε,1)}
  <ε,A> ⊥
  <ε,B> 1
    -> <B⇑A> {(B,1), (ε,1)}
    -> <B⇑C> {(B,2), (ε,2)}
  <ε,B> ⊥
  <ε,C> 1
  <ε,C> 2
    -> <C⇑A> {(ε,1)}
  <ε,C> ⊥
  <ε> 1
    -> <ε⇑A> {(ε,1)}
    -> <ε⇑B> {(ε,1)}
  <ε⇑A> (ε,1)
    -> <ε,A> {1}
  <ε⇑A> ⊥
    -> <ε,A> {⊥}
  <ε⇑B> (ε,1)
    -> <ε,B> {1}
  <ε⇑B> ⊥
    -> <ε,B> {⊥}
  <ε⇑C> (ε,1)
    -> <ε,C> {1}
  <ε⇑C> (ε,2)
    -> <ε,C> {2}
  <ε⇑C> ⊥
    -> <ε,C> {⊥}
  lookups agree with the global reduction from the root
  layout (4):
    A 1
    B 1
    B/C 2
    C 1
