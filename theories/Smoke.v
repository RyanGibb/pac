(* Smoke tests. Functor bodies are checked abstractly, so some errors
   surface only at application time; and the reflexivity examples fail if
   any definition stops computing to a normal form (opaque or classical
   terms in the computational path), which extraction depends on. *)

From Stdlib Require Import MSets.
From PackageCalculus Require Import Prelude Core Versions Conflict Concurrent PeerDependency Feature Virtual PackageFormula VariableFormula.

Module C := Core Nat_as_OT Nat_as_OT.
Module Cfl := Conflict Nat_as_OT Nat_as_OT.
Module Ver := Versions Nat_as_OT Nat_as_OT.
Module Conc := Concurrent Nat_as_OT Nat_as_OT Nat_as_OT.
Module Peer := PeerDependency Nat_as_OT Nat_as_OT Nat_as_OT.
Module BoolFin <: FiniteUsualOrderedType.
  Include UOTFromCompare BoolComp.
  Definition enum : list t := (false :: true :: nil).
  Lemma enum_complete : forall x : t, List.In x enum.
  Proof. intros [|]; simpl; auto. Qed.
End BoolFin.

Module Feat := Feature Nat_as_OT Nat_as_OT BoolFin.
Module Virt := Virtual Nat_as_OT Nat_as_OT.
Module PkgF := PackageFormula Nat_as_OT Nat_as_OT.
Module VarF := VariableFormula Nat_as_OT Nat_as_OT BoolFin Nat_as_OT.
Example core_pkgSet_computes :
  C.PkgSet.mem (1, 2) (C.PkgSet.add (1, 2) C.PkgSet.empty) = true.
Proof. reflexivity. Qed.

Example core_depRel_computes :
  C.DepRel.mem (( (1, 2), (3, C.VSet.singleton 4) ))
    (C.DepRel.add ((1, 2), (3, C.VSet.singleton 4)) C.DepRel.empty) = true.
Proof. reflexivity. Qed.

Example core_merge_computes :
  C.DepRel.cardinal
    (C.Merge.merge (C.DepRel.add ((1, 2), (3, C.VSet.singleton 4))
                (C.DepRel.add ((1, 2), (3, C.VSet.singleton 5))
                   C.DepRel.empty))) = 1.
Proof. reflexivity. Qed.

