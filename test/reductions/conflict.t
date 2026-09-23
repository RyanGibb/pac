  $ ./reductions.exe conflict
  Conflict Package Calculus
    packages R_G: (A,1) (B,1) (B,2)
    conflicts G:
      (A,1) conflicts B {1,2}
  reduceReal -> core packages:
      (A,1)
      (A,⊥)
      (B,1)
      (B,2)
      (B,⊥)
  reduceDeps -> core dependencies:
      (A,1) -> (B,{⊥})
