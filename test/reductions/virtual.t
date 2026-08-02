  $ ./reductions.exe virtual
  Virtual Package Calculus
    packages R (D is virtual): (A,1) (B,1) (C,1) (E,1) (F,1)
    provides Pi:
      (B,1) provides D (=1)
      (C,1) provides D (=1)
      (F,1) provides E (=1)
    dependencies D_Pi:
      (A,1) -> D {1}
      (A,1) -> E {1}
  reduceReal -> core packages:
      (A,1)
      (B,1)
      (C,1)
      (E,1)
      (F,1)
      (<(A,1),D>,<B,1>)
      (<(A,1),D>,<C,1>)
      (<(A,1),E>,<E,1>)
      (<(A,1),E>,<F,1>)
  reduceDeps -> core dependencies:
      (A,1) -> (<(A,1),D>,{<B,1>,<C,1>})
      (A,1) -> (<(A,1),E>,{<E,1>,<F,1>})
      (<(A,1),D>,<B,1>) -> (B,{1})
      (<(A,1),D>,<C,1>) -> (C,{1})
      (<(A,1),E>,<E,1>) -> (E,{1})
      (<(A,1),E>,<F,1>) -> (F,{1})
