  $ ./reductions.exe peer
  Peer Package Calculus, g(v)=v
    packages R: (A,1) (B,1) (C,1) (C,2) (C,3)
    dependencies D_C:
      (A,1) -> B {1}
      (A,1) -> C {2,3}
    peer dependencies Theta:
      (B,1) peer C {1,2}
  reduceReal -> core packages:
      (<A,1>,1)
      (<B,1>,1)
      (<C,1>,1)
      (<C,2>,2)
      (<C,3>,3)
      (<A,1,B>,1)
      (<A,1,C>,1)
      (<A,1,C>,2)
      (<A,1,C>,3)
  reduceDeps -> core dependencies:
      (<A,1>,1) -> (<A,1,B>,{1})
      (<A,1>,1) -> (<A,1,C>,{2,3})
      (<A,1,B>,1) -> (<B,1>,{1})
      (<A,1,B>,1) -> (<A,1,C>,{1,2})
      (<A,1,C>,2) -> (<C,2>,{2})
      (<A,1,C>,3) -> (<C,3>,{3})
