PubGrub on the core instance of the paper's Fig. 1 (A 1 depends on B 1
and C 1, B 1 on D 1 or 2, C 1 on D 2 or 3), with the resolver's debug
trace, in which each incompatibility is named I1, I2, ... where it is
first printed.  A prior cause is derived from the two it names.

Extended by E, whose one version D 3 depends on and which depends on D 1
or 2, deciding D and E as soon as each is required, then C before B, and
the greatest candidate.  Deciding D 3 conflicts once E is tried, and the
learned incompatibility rules D 3 out at level 0.

  $ ./calculus/calculus.exe extended
  core: 7 packages, 6 edges
  A 1
    -> B {1}
    -> C {1}
  B 1
    -> D {1, 2}
  C 1
    -> D {2, 3}
  D 1
  D 2
  D 3
    -> E {1}
  E 1
    -> D {1, 2}
  initial incompatibilities
  	I1 = (terms: {Root *, not A 1}, cause: dependency root -> A 1)
  unit propagation on: Root
  new assignment on level 0: Derivation A 1 due to incompatibility I1
  unit propagation on: A
  deciding on A: 1
  trying version 1
  dependency incompatibilities
  	I2 = (terms: {A 1, not B 1}, cause: dependency A 1 -> B 1)
  	I3 = (terms: {A 1, not C 1}, cause: dependency A 1 -> C 1)
  assignment on level 1: Decision A 1
  unit propagation on: A
  new assignment on level 1: Derivation C 1 due to incompatibility I3
  new assignment on level 1: Derivation B 1 due to incompatibility I2
  unit propagation on: B
  unit propagation on: C
  deciding on C: 1
  trying version 1
  dependency incompatibilities
  	I4 = (terms: {C 1, not D 2 ∪ 3}, cause: dependency C 1 -> D 2 ∪ 3)
  assignment on level 2: Decision C 1
  unit propagation on: C
  new assignment on level 2: Derivation D 2 ∪ 3 due to incompatibility I4
  unit propagation on: D
  deciding on D: 2 ∪ 3
  trying version 3
  dependency incompatibilities
  	I5 = (terms: {D 3, not E 1}, cause: dependency D 3 -> E 1)
  assignment on level 3: Decision D 3
  unit propagation on: D
  new assignment on level 3: Derivation E 1 due to incompatibility I5
  unit propagation on: E
  deciding on E: 1
  trying version 1
  dependency incompatibilities
  	I6 = (terms: {E 1, not D 1 ∪ 2}, cause: dependency E 1 -> D 1 ∪ 2)
  not adding decision due to conflict
  unit propagation on: E
  conflict resolution on: I6
  satisfiying assignment on level 3: Derivation E 1 due to incompatibility I5
  prior cause I7 = (terms: {D 3}, cause: (I6 and I5))
  conflict resolution on: I7
  satisfiying assignment on level 3: Decision D 3
  backtracking to level 0
  solution: (0: Derivation A 1 due to incompatibility I1), (0: Decision root)
  new incompatibility I7
  new assignment on level 0: Derivation not D 3 due to incompatibility I7
  unit propagation on: D
  deciding on A: 1
  trying version 1
  assignment on level 1: Decision A 1
  unit propagation on: A
  new assignment on level 1: Derivation C 1 due to incompatibility I3
  new assignment on level 1: Derivation B 1 due to incompatibility I2
  unit propagation on: B
  unit propagation on: C
  new assignment on level 1: Derivation D 2 ∪ 3 due to incompatibility I4
  unit propagation on: D
  deciding on D: 2
  trying version 2
  assignment on level 2: Decision D 2
  unit propagation on: D
  deciding on C: 1
  trying version 1
  assignment on level 3: Decision C 1
  unit propagation on: C
  deciding on B: 1
  trying version 1
  dependency incompatibilities
  	I8 = (terms: {B 1, not D 1 ∪ 2}, cause: dependency B 1 -> D 1 ∪ 2)
  assignment on level 4: Decision B 1
  unit propagation on: B
  B 1
  C 1
  D 2
  A 1

Without D 2 the query has no resolution.  In PubGrub's own order the
conflict resolution ends on the root, I11, derived through I7 to I10, and
the explanation reads out that derivation.

  $ ./calculus/calculus.exe missing
  core: 5 packages, 4 edges
  A 1
    -> B {1}
    -> C {1}
  B 1
    -> D {1, 2}
  C 1
    -> D {2, 3}
  D 1
  D 3
  initial incompatibilities
  	I1 = (terms: {Root *, not A 1}, cause: dependency root -> A 1)
  unit propagation on: Root
  new assignment on level 0: Derivation A 1 due to incompatibility I1
  unit propagation on: A
  deciding on A: 1
  trying version 1
  dependency incompatibilities
  	I2 = (terms: {A 1, not B 1}, cause: dependency A 1 -> B 1)
  	I3 = (terms: {A 1, not C 1}, cause: dependency A 1 -> C 1)
  assignment on level 1: Decision A 1
  unit propagation on: A
  new assignment on level 1: Derivation C 1 due to incompatibility I3
  new assignment on level 1: Derivation B 1 due to incompatibility I2
  unit propagation on: B
  unit propagation on: C
  deciding on B: 1
  trying version 1
  dependency incompatibilities
  	I4 = (terms: {B 1, not D 1 ∪ 2}, cause: dependency B 1 -> D 1 ∪ 2)
  assignment on level 2: Decision B 1
  unit propagation on: B
  new assignment on level 2: Derivation D 1 ∪ 2 due to incompatibility I4
  unit propagation on: D
  deciding on C: 1
  trying version 1
  dependency incompatibilities
  	I5 = (terms: {C 1, not D 2 ∪ 3}, cause: dependency C 1 -> D 2 ∪ 3)
  assignment on level 3: Decision C 1
  unit propagation on: C
  new assignment on level 3: Derivation D 2 ∪ 3 due to incompatibility I5
  unit propagation on: D
  deciding on D: 2
  no versions found, adding incompatiblity I6 = (terms: {D 2}, cause: no versions)
  unit propagation on: D
  conflict resolution on: I6
  satisfiying assignment on level 3: Derivation D 2 ∪ 3 due to incompatibility I5
  backtracking to level 2
  solution: (2: Derivation D 1 ∪ 2 due to incompatibility I4), (2: Decision B 1), (1: Derivation B 1 due to incompatibility I2), (1: Derivation C 1 due to incompatibility I3), (1: Decision A 1), (0: Derivation A 1 due to incompatibility I1), (0: Decision root)
  new assignment on level 2: Derivation not D 2 due to incompatibility I6
  unit propagation on: D
  conflict resolution on: I5
  satisfiying assignment on level 2: Derivation not D 2 due to incompatibility I6
  prior cause I7 = (terms: {not D 3, C 1}, cause: (I5 and I6))
  conflict resolution on: I7
  satisfiying assignment on level 2: Derivation D 1 ∪ 2 due to incompatibility I4
  backtracking to level 1
  solution: (1: Derivation B 1 due to incompatibility I2), (1: Derivation C 1 due to incompatibility I3), (1: Decision A 1), (0: Derivation A 1 due to incompatibility I1), (0: Decision root)
  new incompatibility I7
  new assignment on level 1: Derivation D 3 due to incompatibility I7
  unit propagation on: D
  conflict resolution on: I4
  satisfiying assignment on level 1: Derivation D 3 due to incompatibility I7
  prior cause I8 = (terms: {B 1, C 1}, cause: (I4 and I7))
  conflict resolution on: I8
  satisfiying assignment on level 1: Derivation B 1 due to incompatibility I2
  prior cause I9 = (terms: {A 1, C 1}, cause: (I8 and I2))
  conflict resolution on: I9
  satisfiying assignment on level 1: Derivation C 1 due to incompatibility I3
  backtracking to level 0
  solution: (0: Derivation A 1 due to incompatibility I1), (0: Decision root)
  new incompatibility I9
  new assignment on level 0: Derivation not C 1 due to incompatibility I9
  unit propagation on: C
  conflict resolution on: I3
  satisfiying assignment on level 0: Derivation not C 1 due to incompatibility I9
  prior cause I10 = (terms: {A 1}, cause: (I3 and I9))
  conflict resolution on: I10
  satisfiying assignment on level 0: Derivation A 1 due to incompatibility I1
  prior cause I11 = (terms: {Root *}, cause: (I10 and I1))
  conflict resolution on: I11
  Because C 1 -> D 2 ∪ 3 and no versions of D match 2, C 1 requires D 3.
  And because B 1 -> D 1 ∪ 2 and A 1 -> B 1, A 1 or C 1 is forbidden.
  And because A 1 -> C 1 and root -> A 1, version solving failed.
