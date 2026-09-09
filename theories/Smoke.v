(* Smoke tests. Functor bodies are checked abstractly, so some errors
   surface only at application time; and the reflexivity examples fail if
   any definition stops computing to a normal form (opaque or classical
   terms in the computational path), which extraction depends on. *)

From Stdlib Require Import MSets.
From PackageCalculus Require Import Prelude Core Versions Semver Conflict Concurrent PeerDependency Visibility Feature Virtual PackageFormula VariableFormula FeatureConcurrent Debian DebianMA Opam Cargo.

Module C := Core Nat_as_OT Nat_as_OT.
Module Cfl := Conflict Nat_as_OT Nat_as_OT.
Module Ver := Versions Nat_as_OT Nat_as_OT.
Module Conc := Concurrent Nat_as_OT Nat_as_OT Nat_as_OT.
Module Peer := PeerDependency Nat_as_OT Nat_as_OT Nat_as_OT.
Module Vis := Visibility Nat_as_OT Nat_as_OT.

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
Module FC := FeatureConcurrent Nat_as_OT Nat_as_OT BoolFin Nat_as_OT.
Module NatTriv := TrivialGroup Nat_as_OT.
Module Deb := Debian Nat_as_OT Nat_as_OT NatTriv.

Module BoolArch <: ArchParam.
  Module A := BoolFin.

  Definition native : A.t := false.
End BoolArch.
Module DMA := DebianMA Nat_as_OT Nat_as_OT BoolArch.

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

Definition verR : Ver.PkgSet.t := Ver.PkgSet.add (1, 2) Ver.PkgSet.empty.

Definition verD : Ver.DepRel.t :=
  Ver.DepRel.add ((1, 2), (1, Ver.FTop)) Ver.DepRel.empty.

Example versions_reduce_computes :
  Ver.C.DepRel.cardinal (Ver.Reduction.reduce verR verD) = 1.
Proof. reflexivity. Qed.

Example versions_realPreimage_computes :
  Ver.PkgSet.cardinal (Ver.Reduction.Lookup.realPreimage verR verD) = 1.
Proof. reflexivity. Qed.

Example packageFormula_reduceDeps_computes :
  PkgF.Reduction.T.DepRel.cardinal
    (PkgF.Reduction.reduceDeps
       (PkgF.DepRel.add ((1, 2), PkgF.FDep 3 (PkgF.VSet.singleton 4))
          PkgF.DepRel.empty)) = 1.
Proof. reflexivity. Qed.

Example variableFormula_reduceDeps_computes :
  VarF.Reduction.T.DepRel.cardinal
    (VarF.Reduction.reduceDeps (fun _ => VarF.Reduction.YSet.singleton 0)
       (VarF.DepRel.add ((1, 2), VarF.FDep 3 (VarF.VSet.singleton 4))
          VarF.DepRel.empty)) = 1.
Proof. reflexivity. Qed.

Example feature_reduceDeps_computes :
  Feat.Reduction.T.DepRel.cardinal
    (Feat.Reduction.reduceDeps Feat.PkgSet.empty Feat.SupportSet.empty
       (Feat.FeatDepRel.add
          ((1, 2), (3, (Feat.VSet.singleton 4, Feat.FSet.empty)))
          Feat.FeatDepRel.empty)
       Feat.AddlDepRel.empty) = 1.
Proof. reflexivity. Qed.

(* Built in Cfl.C, the core instance living inside the Conflict
   instantiation, rather than in the C above. *)
Definition conflictR : Cfl.C.PkgSet.t :=
  Cfl.C.PkgSet.add (1, 10)
    (Cfl.C.PkgSet.add (1, 11) (Cfl.C.PkgSet.add (2, 20) Cfl.C.PkgSet.empty)).

Example conflict_conflictResolution_roundtrip_computes :
  Cfl.C.PkgSet.equal
    (Cfl.Reduction.conflictResolution (Cfl.Reduction.embedSet conflictR))
    conflictR = true.
Proof. reflexivity. Qed.

Example conflict_reduceReal_computes :
  Cfl.Reduction.T.PkgSet.cardinal
    (Cfl.Reduction.reduceReal conflictR
       (Cfl.ConflictRel.add ((2, 20), (1, Cfl.C.VSet.singleton 11))
          Cfl.ConflictRel.empty)) = 5.
Proof. reflexivity. Qed.

Definition debR : Deb.PkgSet.t :=
  Deb.PkgSet.add (1, 10) (Deb.PkgSet.add (1, 11) Deb.PkgSet.empty).

Definition debD : Deb.Deps.t :=
  Deb.Deps.add ((1, 10), Deb.AtomSet.singleton (1, Deb.Ver.FTop))
    Deb.Deps.empty.

Example debian_vers_computes :
  Deb.T.VSet.cardinal
    (Deb.versions debR debD Deb.Prov.empty Deb.Conf.empty
       (Deb.Name.Orig 1)) = 2.
Proof. reflexivity. Qed.

Example debian_dependees_computes :
  Deb.T.DependeesSet.cardinal
    (Deb.dependees debR debD Deb.Prov.empty Deb.Conf.empty
       (Deb.Name.Orig 1, Deb.Version.Orig 10)) = 1.
Proof. reflexivity. Qed.

Definition maR : DMA.PkgSet.t :=
  DMA.PkgSet.add ((1, false), 10)
    (DMA.PkgSet.add ((1, true), 10) DMA.PkgSet.empty).

Example debianMA_reduceReal_computes :
  DMA.Deb.Ver.C.PkgSet.cardinal (DMA.reduceReal maR) = 2.
Proof. reflexivity. Qed.

Example debianMA_reduceConf_computes :
  DMA.Deb.Conf.cardinal
    (DMA.reduceConf maR DMA.Conf.empty DMA.Cls.empty) = 2.
Proof. reflexivity. Qed.

(* One private dependency, so (1, 1) mints its own subgraph: two occurrences,
   one intermediate and one agreement. *)
Definition visR : Vis.PkgSet.t :=
  Vis.PkgSet.add (1, 1) (Vis.PkgSet.add (2, 1) Vis.PkgSet.empty).

Definition visD : Vis.C.DepRel.t :=
  Vis.C.DepRel.add ((1, 1), (2, Vis.VSet.singleton 1)) Vis.C.DepRel.empty.

Example visibility_reduceReal_computes :
  Vis.Reduction.T.PkgSet.cardinal
    (Vis.Reduction.reduceReal visR visD Vis.PubRel.empty (1, 1)) = 4.
Proof. reflexivity. Qed.

Example visibility_reduceDeps_computes :
  Vis.Reduction.T.DepRel.cardinal
    (Vis.Reduction.reduceDeps visR visD Vis.PubRel.empty (1, 1)) = 3.
Proof. reflexivity. Qed.

Example visibility_sub_computes :
  Vis.PkgSet.cardinal
    (Vis.sub Vis.PubRel.empty
       (Vis.ParentRel.add ((2, 1), (1, 1)) Vis.ParentRel.empty) (1, 1)) = 2.
Proof. reflexivity. Qed.

Example visibility_depBlocks_computes :
  Vis.C.DepRel.cardinal (Vis.Reduction.Lookup.depBlocks visD (1, 1) (1, 1))
  = 1.
Proof. reflexivity. Qed.

Module Op := Opam Nat_as_OT Nat_as_OT BoolFin Nat_as_OT Nat_as_OT.

Definition opRho : Op.Valuation := fun _ => Some 1.
Definition opRepo : Op.PkgSet.t :=
  Op.PkgSet.add (1, 10) (Op.PkgSet.add (2, 20) Op.PkgSet.empty).

(* (1,10) depends on name 2 at >= 15 gated on a variable comparison that
   holds under opRho; (2,20) carries a depext on system package 7; the
   goal wants name 1 and the invariant is gated away entirely. *)
Definition opInst : Op.Inst :=
  Op.MkInst opRepo
    (((1, 10),
      Op.OFAtom 2 (Op.FlCmp OpEq false 1) (Op.VCCmp OpGe 15)) :: nil)
    nil
    nil
    Op.ClsRel.empty
    nil
    (((2, 20), (7, Op.FlTrue)) :: nil)
    Op.PkgSet.empty
    nil
    (Op.OFAtom 1 Op.FlTrue Op.VCTop)
    (Op.OFAtom 1 Op.FlFalse Op.VCTop).

Example opam_transR_computes :
  Op.Reduction.VF.PkgSet.cardinal (Op.Reduction.transR opRho opInst) = 3.
Proof. reflexivity. Qed.

Example opam_transD_computes :
  Op.Reduction.VF.DepRel.cardinal
    (Op.Reduction.transD opRho opInst) = 2.
Proof. reflexivity. Qed.

(* The depext row of (2,20) reaches no formula; it is read off the
   resolution instead. *)
Example opam_depexts_computes :
  Op.ESet.elements
    (Op.depextsOf opRho opInst (Op.PkgSet.add (2, 20) Op.PkgSet.empty))
  = 7 :: nil.
Proof. reflexivity. Qed.

Example opam_depexts_unselected :
  Op.depextsOf opRho opInst (Op.PkgSet.add (1, 10) Op.PkgSet.empty)
  = Op.ESet.empty.
Proof. reflexivity. Qed.

(* Odd versions code prereleases of the release v / 2, so that the
   admission rule is exercised and not just the ordering. *)
Module CgoVM <: SemverMatch Nat_as_OT.
  Definition isPre (v : nat) : bool := Nat.odd v.
  Definition sameCore (a b : nat) : bool :=
    Nat.eqb (Nat.div a 2) (Nat.div b 2).
End CgoVM.

Module Cgo := Cargo Nat_as_OT Nat_as_OT Nat_as_OT BoolFin
  Nat_as_OT Nat_as_OT Nat_as_OT CgoVM.

Definition cgoAny : Cgo.Range := (Cgo.CAny :: nil) :: nil.

Example cargo_rgHolds_computes :
  Cgo.rgHolds cgoAny 4 = true.
Proof. reflexivity. Qed.

Example cargo_evalReq_computes :
  Cgo.VSet.cardinal
    (Cgo.evalReq (Cgo.PkgSet.add (0, 4) (Cgo.PkgSet.add (0, 6)
       Cgo.PkgSet.empty)) 0 cgoAny) = 2.
Proof. reflexivity. Qed.

(* A requirement that names no prerelease admits none, while the whole
   repository of a crate name is still every version of it. *)
Example cargo_prerelease_excluded :
  Cgo.VSet.elements
    (Cgo.evalReq (Cgo.PkgSet.add (0, 4) (Cgo.PkgSet.add (0, 5)
       Cgo.PkgSet.empty)) 0 ((Cgo.COp OpGe 4 :: nil) :: nil)) = 4 :: nil.
Proof. reflexivity. Qed.

Example cargo_prerelease_admitted :
  Cgo.VSet.elements
    (Cgo.evalReq (Cgo.PkgSet.add (0, 4) (Cgo.PkgSet.add (0, 5)
       Cgo.PkgSet.empty)) 0 ((Cgo.COp OpGe 5 :: nil) :: nil)) = 5 :: nil.
Proof. reflexivity. Qed.

Example cargo_srcVersions_computes :
  Cgo.VSet.cardinal
    (Cgo.srcVersions (Cgo.PkgSet.add (0, 4) (Cgo.PkgSet.add (0, 5)
       Cgo.PkgSet.empty)) 0) = 2.
Proof. reflexivity. Qed.

