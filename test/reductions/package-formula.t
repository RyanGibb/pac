  $ ./reductions.exe package-formula
  Package Formula Calculus
    packages R: (A,1) (B,1) (B,2) (C,1)
    dependencies D_Psi:
      (A,1) :- (((B,{2}) /\ (C,{1})) \/ ((B,{1}) /\ ~(C,{1})))
  reduceReal -> core packages:
      (A,1)
      (B,1)
      (B,2)
      (C,1)
      (or<((B,{2}) /\ (C,{1})) ; ((B,{1}) /\ ~(C,{1}))>,0)
      (or<((B,{2}) /\ (C,{1})) ; ((B,{1}) /\ ~(C,{1}))>,1)
      (neg<C,{1}>,0)
      (neg<C,{1}>,1)
  reduceDeps -> core dependencies:
      (A,1) -> (or<((B,{2}) /\ (C,{1})) ; ((B,{1}) /\ ~(C,{1}))>,{0,1})
      (C,1) -> (neg<C,{1}>,{0})
      (or<((B,{2}) /\ (C,{1})) ; ((B,{1}) /\ ~(C,{1}))>,0) -> (B,{2})
      (or<((B,{2}) /\ (C,{1})) ; ((B,{1}) /\ ~(C,{1}))>,0) -> (C,{1})
      (or<((B,{2}) /\ (C,{1})) ; ((B,{1}) /\ ~(C,{1}))>,1) -> (B,{1})
      (or<((B,{2}) /\ (C,{1})) ; ((B,{1}) /\ ~(C,{1}))>,1) -> (neg<C,{1}>,{1})
