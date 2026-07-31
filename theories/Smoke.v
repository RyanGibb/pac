(* Smoke tests. Functor bodies are checked abstractly, so some errors
   surface only at application time; and the reflexivity examples fail if
   any definition stops computing to a normal form (opaque or classical
   terms in the computational path), which extraction depends on. *)

From Stdlib Require Import MSets.
From PackageCalculus Require Import Prelude Core.

Module C := Core Nat_as_OT Nat_as_OT.
Example core_pkgSet_computes :
  C.PkgSet.mem (1, 2) (C.PkgSet.add (1, 2) C.PkgSet.empty) = true.
Proof. reflexivity. Qed.

Example core_depRel_computes :
  C.DepRel.mem (( (1, 2), (3, C.VSet.singleton 4) ))
    (C.DepRel.add ((1, 2), (3, C.VSet.singleton 4)) C.DepRel.empty) = true.
Proof. reflexivity. Qed.

