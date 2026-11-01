From Stdlib Require Import MSets List.
From PackageCalculus Require Import Prelude Core Complexity Versions Semver
  Conflict ConflictClass Concurrent PeerDependency Visibility Feature
  Virtual PackageFormula VariableFormula ConcurrentFeature Debian DebianMA
  Opam Cargo Alpine Npm Placement NpmPlacement.

Module C := Core Nat_as_OT Nat_as_OT.
Module Cx := Complexity Nat_as_OT Nat_as_OT Nat_as_OT.
Module Cfl := Conflict Nat_as_OT Nat_as_OT.
Module Cls := ConflictClass Nat_as_OT Nat_as_OT.
Module Ver := Versions Nat_as_OT Nat_as_OT.
Module Conc := Concurrent Nat_as_OT Nat_as_OT Nat_as_OT.
Module Peer := PeerDependency Nat_as_OT Nat_as_OT Nat_as_OT.
Module Vis := Visibility Nat_as_OT Nat_as_OT.
Module Plc := Placement Nat_as_OT Nat_as_OT.

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
Module CF := ConcurrentFeature Nat_as_OT Nat_as_OT BoolFin Nat_as_OT.
Module NatTriv := TrivialGroup Nat_as_OT.
Module Deb := Debian Nat_as_OT Nat_as_OT NatTriv.

Module BoolArch <: ArchParam.
  Module A := BoolFin.

  Definition native : A.t := false.
End BoolArch.
Module DMA := DebianMA Nat_as_OT Nat_as_OT BoolArch.

Example core_pkgSet_computes :
  C.PackageSet.mem (1, 2) (C.PackageSet.add (1, 2) C.PackageSet.empty) = true.
Proof. reflexivity. Qed.

Example core_depRel_computes :
  C.DependencyRel.mem (( (1, 2), (3, C.VSet.singleton 4) ))
    (C.DependencyRel.add ((1, 2), (3, C.VSet.singleton 4)) C.DependencyRel.empty) = true.
Proof. reflexivity. Qed.

Example core_merge_computes :
  C.DependencyRel.cardinal
    (C.Merge.merge (C.DependencyRel.add ((1, 2), (3, C.VSet.singleton 4))
                (C.DependencyRel.add ((1, 2), (3, C.VSet.singleton 5))
                   C.DependencyRel.empty))) = 1.
Proof. reflexivity. Qed.

Definition ckR : C.PackageSet.t :=
  C.PackageSet.ofList ((0, 0) :: (1, 1) :: (1, 2) :: (2, 0) :: nil).

Definition ckVS : C.VSet.t := C.VSet.ofList (1 :: 2 :: nil).

Definition ckD : C.DependencyRel.t := C.DependencyRel.ofList (((0, 0), (1, ckVS)) :: nil).

Definition ckCheck (S : list (nat * nat)) : option C.CheckFailure :=
  C.check (C.versions ckR) (C.dependees ckD) (C.rootQuery (0, 0))
    (C.PackageSet.ofList S).

Example core_check_accepts : ckCheck ((0, 0) :: (1, 2) :: nil) = None.
Proof. reflexivity. Qed.

Example core_check_subset :
  ckCheck ((0, 0) :: (1, 3) :: nil) = Some (CheckSubset (1, 3)).
Proof. reflexivity. Qed.

Example core_check_version_unique :
  ckCheck ((0, 0) :: (1, 1) :: (1, 2) :: nil) =
  Some (CheckVersionUnique (1, 2)).
Proof. reflexivity. Qed.

Example core_check_root_mem :
  ckCheck ((1, 2) :: nil) = Some (CheckRootMem (0, C.VSet.singleton 0)).
Proof. reflexivity. Qed.

Example core_check_dep_closure :
  ckCheck ((0, 0) :: nil) = Some (CheckDepClosure (0, 0) (1, ckVS)).
Proof. reflexivity. Qed.

Example core_check_reached :
  ckCheck ((0, 0) :: (1, 2) :: (2, 0) :: nil) = Some (CheckReached (2, 0)).
Proof. reflexivity. Qed.

Definition cxPhi : list Cx.ClauseOT.t :=
  ((0, true), ((1, false), (2, true))) :: nil.

Example complexity_reduceReal_computes :
  Cx.Reduction.Reduced.PackageSet.cardinal (Cx.Reduction.reduceReal cxPhi) = 10.
Proof. reflexivity. Qed.

Example complexity_reduceDeps_computes :
  Cx.Reduction.Reduced.DependencyRel.cardinal (Cx.Reduction.reduceDeps cxPhi) = 4.
Proof. reflexivity. Qed.

Definition cxR : Cx.PackageSet.t :=
  Cx.PackageSet.add (1, 1)
    (Cx.PackageSet.add (1, 2) (Cx.PackageSet.add (2, 1) Cx.PackageSet.empty)).

Definition cxD : Cx.Source.DependencyRel.t :=
  Cx.Source.DependencyRel.add ((1, 1), (2, Cx.VSet.singleton 1)) Cx.Source.DependencyRel.empty.

Example complexity_satEncoding_computes :
  List.length (Cx.Encoding.satEncoding cxR cxD (1, 1)) = 3.
Proof. reflexivity. Qed.

Definition verR : Ver.PackageSet.t := Ver.PackageSet.add (1, 2) Ver.PackageSet.empty.

Definition verD : Ver.DependencyRel.t :=
  Ver.DependencyRel.add ((1, 2), (1, Ver.FTop)) Ver.DependencyRel.empty.

Example versions_reduce_computes :
  Ver.Source.DependencyRel.cardinal (Ver.Reduction.reduce verR verD) = 1.
Proof. reflexivity. Qed.

Example versions_realPreimage_computes :
  Ver.PackageSet.cardinal (Ver.Reduction.Lookup.realPreimage verR verD) = 1.
Proof. reflexivity. Qed.

Example packageFormula_reduceDeps_computes :
  PkgF.Reduction.Reduced.DependencyRel.cardinal
    (PkgF.Reduction.reduceDeps PkgF.PackageSet.empty
       (PkgF.DependencyRel.add ((1, 2), PkgF.FAtom 3 (PkgF.VSet.singleton 4))
          PkgF.DependencyRel.empty)) = 1.
Proof. reflexivity. Qed.

Example variableFormula_reduceDeps_computes :
  VarF.Reduction.Reduced.DependencyRel.cardinal
    (VarF.Reduction.reduceDeps (fun _ => VarF.YSet.singleton 0)
       VarF.PackageSet.empty
       (VarF.DependencyRel.add ((1, 2), VarF.FAtom 3 (VarF.VSet.singleton 4))
          VarF.DependencyRel.empty)) = 1.
Proof. reflexivity. Qed.

Example feature_reduceDeps_computes :
  Feat.Reduction.Reduced.DependencyRel.cardinal
    (Feat.Reduction.reduceDeps Feat.PackageSet.empty Feat.SupportRel.empty
       (Feat.ParameterisedDependencyRel.add
          ((1, 2), (3, (Feat.VSet.singleton 4, Feat.FSet.empty)))
          Feat.ParameterisedDependencyRel.empty)
       Feat.AdditionalDependencyRel.empty) = 1.
Proof. reflexivity. Qed.

(* Built in Cfl.C, the core instance living inside the Conflict
   instantiation, rather than in the C above. *)
Definition conflictR : Cfl.Source.PackageSet.t :=
  Cfl.Source.PackageSet.add (1, 10)
    (Cfl.Source.PackageSet.add (1, 11) (Cfl.Source.PackageSet.add (2, 20) Cfl.Source.PackageSet.empty)).

Example conflict_conflictResolution_retraction_computes :
  Cfl.Source.PackageSet.equal
    (Cfl.Reduction.conflictResolution (Cfl.Reduction.embedSet conflictR))
    conflictR = true.
Proof. reflexivity. Qed.

Example conflict_reduceReal_computes :
  Cfl.Reduction.Reduced.PackageSet.cardinal
    (Cfl.Reduction.reduceReal conflictR Cfl.Source.DependencyRel.empty
       (Cfl.ConflictRel.add ((2, 20), (1, Cfl.Source.VSet.singleton 11))
          Cfl.ConflictRel.empty)) = 5.
Proof. reflexivity. Qed.

Definition clsR : Cls.PackageSet.t :=
  Cls.PackageSet.add (1, 10)
    (Cls.PackageSet.add (1, 11) (Cls.PackageSet.add (2, 20) Cls.PackageSet.empty)).

Definition clsOm : Cls.ConflictClassRel.t :=
  Cls.ConflictClassRel.add ((1, 10), 0)
    (Cls.ConflictClassRel.add ((1, 11), 0)
       (Cls.ConflictClassRel.add ((2, 20), 0) Cls.ConflictClassRel.empty)).

Example conflictClass_excludes :
  ~ Cls.ClassExclusion clsOm
      (Cls.PackageSet.add (1, 10) (Cls.PackageSet.add (2, 20) Cls.PackageSet.empty)).
Proof.
  intro H.
  assert (E : ((1, 10) : Cls.Package.t) = (2, 20))
    by (apply (H 0);
        first [apply Cls.PackageSet.mem_spec | apply Cls.ConflictClassRel.mem_spec];
        reflexivity).
  discriminate E.
Qed.

Example conflictClass_reduction_excludes :
  forall S,
    Cls.Reduction.Reduced.IsResolution (Cls.Reduction.reduceReal clsR clsOm)
      (Cls.Reduction.reduceDeps Cls.Source.DependencyRel.empty clsOm)
      (Cls.Reduction.embedPkg (1, 10)) S ->
    ~ Cls.Reduction.Reduced.PackageSet.In (Cls.Reduction.embedPkg (2, 20)) S.
Proof.
  intros S [_ Hr Hdep Huniq] Hq.
  destruct (Hdep _ Hr (Cls.Reduction.Name.Cls 0)
              (Cls.Reduction.Reduced.VSet.singleton (Cls.Reduction.Version.Name 1)))
    as [w [Hw Hwr]]; [apply Cls.Reduction.Reduced.DependencyRel.mem_spec; reflexivity |].
  destruct (Hdep _ Hq (Cls.Reduction.Name.Cls 0)
              (Cls.Reduction.Reduced.VSet.singleton (Cls.Reduction.Version.Name 2)))
    as [w' [Hw' Hwq]]; [apply Cls.Reduction.Reduced.DependencyRel.mem_spec; reflexivity |].
  apply Cls.Reduction.Reduced.VSet.singleton_spec in Hw, Hw'; subst w w'.
  discriminate (Huniq _ _ _ Hwr Hwq).
Qed.

Example conflictClass_reduceReal_computes :
  Cls.Reduction.Reduced.VSet.cardinal
    (Cls.Reduction.Reduced.versions (Cls.Reduction.reduceReal clsR clsOm)
       (Cls.Reduction.Name.Cls 0)) = 2.
Proof. reflexivity. Qed.

Example conflictClass_retraction_computes :
  Cls.Source.PackageSet.equal
    (Cls.Reduction.conflictClassResolution
       (Cls.Reduction.coreResolution clsOm clsR))
    clsR = true.
Proof. reflexivity. Qed.

Definition debR : Deb.PackageSet.t :=
  Deb.PackageSet.add (1, 10) (Deb.PackageSet.add (1, 11) Deb.PackageSet.empty).

Definition debD : Deb.DependencyRel.t :=
  Deb.DependencyRel.add ((1, 10), ((1, Deb.Ver.FTop) :: nil))
    Deb.DependencyRel.empty.

Definition debRec : Deb.DependencyRel.t :=
  Deb.DependencyRel.add ((1, 10), ((2, Deb.Ver.FTop) :: nil))
    Deb.DependencyRel.empty.

Example debian_vers_computes :
  Deb.Reduction.Reduced.VSet.cardinal
    (Deb.Reduction.versions
       (Deb.MkInst debR debD Deb.DependencyRel.empty Deb.ProvidesRel.empty Deb.ConflictRel.empty
          (1, 10))
       (Deb.Reduction.Name.Orig 1)) = 3.
Proof. reflexivity. Qed.

Example debian_dependees_computes :
  Deb.Reduction.Reduced.DependeeSet.cardinal
    (Deb.Reduction.dependees
       (Deb.MkInst debR debD Deb.DependencyRel.empty Deb.ProvidesRel.empty Deb.ConflictRel.empty
          (1, 10))
       (Deb.Reduction.Name.Orig 1, Deb.Reduction.Version.Orig 10)) = 1.
Proof. reflexivity. Qed.

Example debian_soft_vers_computes :
  Deb.Reduction.Reduced.VSet.cardinal
    (Deb.Reduction.versions
       (Deb.MkInst debR debD debRec Deb.ProvidesRel.empty Deb.ConflictRel.empty (1, 10))
       (Deb.Reduction.Name.Soft ((2, Deb.Ver.FTop) :: nil))) = 2.
Proof. reflexivity. Qed.

Example debian_soft_escape_computes :
  Deb.Reduction.Reduced.DependeeSet.cardinal
    (Deb.Reduction.dependees
       (Deb.MkInst debR debD debRec Deb.ProvidesRel.empty Deb.ConflictRel.empty (1, 10))
       (Deb.Reduction.Name.Soft ((2, Deb.Ver.FTop) :: nil),
        Deb.Reduction.Version.Zero)) = 0.
Proof. reflexivity. Qed.

Definition maR : DMA.PackageSet.t :=
  DMA.PackageSet.add ((1, false), 10)
    (DMA.PackageSet.add ((1, true), 10) DMA.PackageSet.empty).

Example debianMA_reduceReal_computes :
  DMA.Deb.Ver.Source.PackageSet.cardinal (DMA.Reduction.reduceReal maR) = 2.
Proof. reflexivity. Qed.

Example debianMA_reduceConf_computes :
  DMA.Deb.ConflictRel.cardinal
    (DMA.Reduction.reduceConf maR DMA.ConflictRel.empty DMA.ClassRel.empty) = 2.
Proof. reflexivity. Qed.

Definition visR : Vis.PackageSet.t :=
  Vis.PackageSet.add (1, 1) (Vis.PackageSet.add (2, 1) Vis.PackageSet.empty).

Definition visD : Vis.Source.DependencyRel.t :=
  Vis.Source.DependencyRel.add ((1, 1), (2, Vis.VSet.singleton 1)) Vis.Source.DependencyRel.empty.

Example visibility_reduceReal_computes :
  Vis.Reduction.Reduced.PackageSet.cardinal
    (Vis.Reduction.reduceReal visR visD Vis.PublicDependencyRel.empty (1, 1)) = 4.
Proof. reflexivity. Qed.

Example visibility_reduceDeps_computes :
  Vis.Reduction.Reduced.DependencyRel.cardinal
    (Vis.Reduction.reduceDeps visR visD Vis.PublicDependencyRel.empty (1, 1)) = 3.
Proof. reflexivity. Qed.

Example visibility_sub_computes :
  Vis.PackageSet.cardinal
    (Vis.sub Vis.PublicDependencyRel.empty
       (Vis.ParentRel.add ((2, 1), (1, 1)) Vis.ParentRel.empty) (1, 1)) = 2.
Proof. reflexivity. Qed.

Module Op := Opam Nat_as_OT Nat_as_OT BoolFin Nat_as_OT Nat_as_OT.

Definition opRho : Op.Valuation := fun _ => Some 1.
Definition opRepo : Op.PackageSet.t :=
  Op.PackageSet.add (1, 10) (Op.PackageSet.add (2, 20) Op.PackageSet.empty).

Definition opInst : Op.Inst :=
  Op.MkInst opRepo
    (((1, 10),
      Op.OFAtom 2 (Op.FlCmp OpEq false 1) (Op.VFCmp OpGe 15)) :: nil)
    nil
    Op.ConflictClassRel.empty
    nil
    (((2, 20), (7, Op.FlTrue)) :: nil)
    Op.PackageSet.empty
    nil
    (Op.OFAtom 1 Op.FlTrue Op.VFTop)
    (Op.OFAtom 1 Op.FlFalse Op.VFTop).

Example opam_reduceReal_computes :
  Op.Reduction.PF.PackageSet.cardinal (Op.Reduction.reduceReal opRho opInst) = 3.
Proof. reflexivity. Qed.

Example opam_reduceDeps_computes :
  Op.Reduction.PF.DependencyRel.cardinal
    (Op.Reduction.reduceDeps opRho opInst) = 2.
Proof. reflexivity. Qed.

Example opam_depexts_computes :
  Op.ESet.elements
    (Op.depextsOf opRho opInst (Op.PackageSet.add (2, 20) Op.PackageSet.empty))
  = 7 :: nil.
Proof. reflexivity. Qed.

Example opam_depexts_unselected :
  Op.depextsOf opRho opInst (Op.PackageSet.add (1, 10) Op.PackageSet.empty)
  = Op.ESet.empty.
Proof. reflexivity. Qed.

Module CgoVM <: SemverMatch Nat_as_OT.
  Definition isPre (v : nat) : bool := Nat.odd v.
  Definition sameCore (a b : nat) : bool :=
    Nat.eqb (Nat.div a 2) (Nat.div b 2).
End CgoVM.

Module Cgo := Cargo Nat_as_OT Nat_as_OT BoolFin
  Nat_as_OT Nat_as_OT Nat_as_OT CgoVM.

Definition cgoAny : Cgo.Range := (Cgo.CAny :: nil) :: nil.

Example cargo_rgHolds_computes :
  Cgo.rgHolds cgoAny 4 = true.
Proof. reflexivity. Qed.

Example cargo_evalReq_computes :
  Cgo.VSet.cardinal
    (Cgo.Reduction.evalReq (Cgo.PackageSet.add (0, 4) (Cgo.PackageSet.add (0, 6)
       Cgo.PackageSet.empty)) 0 cgoAny) = 2.
Proof. reflexivity. Qed.

Example cargo_prerelease_excluded :
  Cgo.VSet.elements
    (Cgo.Reduction.evalReq (Cgo.PackageSet.add (0, 4) (Cgo.PackageSet.add (0, 5)
       Cgo.PackageSet.empty)) 0 ((Cgo.COp OpGe 4 :: nil) :: nil)) = 4 :: nil.
Proof. reflexivity. Qed.

Example cargo_prerelease_admitted :
  Cgo.VSet.elements
    (Cgo.Reduction.evalReq (Cgo.PackageSet.add (0, 4) (Cgo.PackageSet.add (0, 5)
       Cgo.PackageSet.empty)) 0 ((Cgo.COp OpGe 5 :: nil) :: nil)) = 5 :: nil.
Proof. reflexivity. Qed.

Module NatPM <: ApkVerMatch Nat_as_OT.
  Definition prefix := Nat.eqb.
  Definition hash := Nat.eqb.
End NatPM.
Module Alp := Alpine Nat_as_OT Nat_as_OT NatPM.

Definition alpI : Alp.Inst :=
  {| Alp.inst_real :=
       Alp.PackageSet.add (1, 10)
         (Alp.PackageSet.add (2, 20) (Alp.PackageSet.add (3, 30) Alp.PackageSet.empty))
   ; Alp.inst_deps :=
       Alp.DependencyRel.add ((1, 10), Alp.DPos (2, Alp.COp OpGe 20)) Alp.DependencyRel.empty
   ; Alp.inst_prov :=
       Alp.ProvidesRel.add ((3, 30), (4, Alp.PVer 5))
         (Alp.ProvidesRel.add ((2, 20), (6, Alp.PBare)) Alp.ProvidesRel.empty)
   ; Alp.inst_installIf :=
       Alp.InstallIfRuleRel.add ((2, 20), Alp.ConditionSet.add (Alp.DPos (1, Alp.CAny))
                                (Alp.ConditionSet.add (Alp.DNeg (5, Alp.CAny))
                                   Alp.ConditionSet.empty)) Alp.InstallIfRuleRel.empty
   ; Alp.inst_world := Alp.WorldSet.add (Alp.DPos (1, Alp.CAny)) Alp.WorldSet.empty
   ; Alp.inst_prio := Alp.PriorityRel.empty |}.

Example alpine_reduceReal_computes :
  Alp.Reduction.PF.PackageSet.cardinal (Alp.Reduction.reduceReal alpI) = 5.
Proof. reflexivity. Qed.

Example alpine_root_dependees_computes :
  Alp.Reduction.PackageFormulaSet.cardinal
    (Alp.Reduction.dependees alpI Alp.Reduction.rootPkg) = 1.
Proof. reflexivity. Qed.

Example alpine_installif_attaches :
  Alp.InstallIfRuleRel.cardinal (Alp.Reduction.installIfFibre alpI (1, 10)) = 1.
Proof. reflexivity. Qed.

Example alpine_versions_computes :
  Alp.Reduction.PF.VSet.cardinal (Alp.Reduction.versions alpI 4) = 1.
Proof. reflexivity. Qed.

Module NpmVM <: SemverMatch Nat_as_OT.
  Definition isPre (_ : nat) : bool := false.
  Definition sameCore (a b : nat) : bool := Nat.eqb a b.
End NpmVM.

Module NpmS := Npm Nat_as_OT Nat_as_OT NpmVM.

Definition npmA : nat := 1.
Definition npmB : nat := 2.
Definition npmC : nat := 3.
Definition npmX : nat := 4.

Definition npmEq (v : nat) : NpmS.Range := (NpmS.COp OpEq v :: nil) :: nil.

Definition npmBetween (lo hi : nat) : NpmS.Range :=
  (NpmS.COp OpGe lo :: NpmS.COp OpLt hi :: nil) :: nil.

Definition npmRepo : NpmS.RealPackageSet.t :=
  fold_right NpmS.RealPackageSet.add NpmS.RealPackageSet.empty
    ((npmA, 1) :: (npmB, 1) :: (npmC, 1) :: (npmC, 2) :: (npmC, 3) :: nil).

Definition npmDepB : NpmS.Dependency := NpmS.MkDep npmB npmB (npmEq 1) false (Some 1).
Definition npmDepC : NpmS.Dependency :=
  NpmS.MkDep npmC npmC (npmBetween 2 4) false (Some 2).
Definition npmPeerC : NpmS.PeerDependency :=
  NpmS.MkPeer npmC (npmBetween 1 3) false true.
Definition npmPeerCOpt : NpmS.PeerDependency :=
  NpmS.MkPeer npmC (npmBetween 1 3) true true.

Definition kA : NpmS.SourceName.t := (npmA, npmA).
Definition kB : NpmS.SourceName.t := (npmB, npmB).
Definition kC : NpmS.SourceName.t := (npmC, npmC).
Definition kX : NpmS.SourceName.t := (npmX, npmC).

Definition npmShow (h : NpmS.Reduced.Dependee.t)
  : NpmS.Name.t * list NpmS.Version.t :=
  (fst h, NpmS.Reduced.VSet.elements (snd h)).

Definition npmDeps (I : NpmS.Inst) (s : NpmS.Reduced.Package.t) :=
  List.map npmShow
    (NpmS.Reduced.DependeeSet.elements (NpmS.Reduction.dependees I s)).

Definition npmInst : NpmS.Inst :=
  NpmS.MkInst npmRepo
    (((npmA, 1), npmDepB) :: ((npmA, 1), npmDepC) :: nil)
    (((npmB, 1), npmPeerC) :: nil) nil (npmA, 1).

Definition npmInstAuto : NpmS.Inst :=
  NpmS.MkInst npmRepo (((npmA, 1), npmDepB) :: nil)
    (((npmB, 1), npmPeerC) :: nil) nil (npmA, 1).

Definition npmInstRootPeer : NpmS.Inst :=
  NpmS.MkInst npmRepo (((npmA, 1), npmDepC) :: nil)
    (((npmA, 1), npmPeerC) :: nil) nil (npmA, 1).

Definition npmInstRootPeerOpt : NpmS.Inst :=
  NpmS.MkInst npmRepo (((npmA, 1), npmDepC) :: nil)
    (((npmA, 1), npmPeerCOpt) :: nil) nil (npmA, 1).

Definition npmInstRootPeerOptBare : NpmS.Inst :=
  NpmS.MkInst npmRepo (((npmA, 1), npmDepB) :: nil)
    (((npmA, 1), npmPeerCOpt) :: nil) nil (npmA, 1).

Definition npmInstOpt : NpmS.Inst :=
  NpmS.MkInst npmRepo (((npmA, 1), npmDepB) :: nil)
    (((npmB, 1), npmPeerCOpt) :: nil) nil (npmA, 1).

Definition npmDepAlias : NpmS.Dependency :=
  NpmS.MkDep npmX npmC (npmEq 1) false (Some 3).

Definition npmInstAlias : NpmS.Inst :=
  NpmS.MkInst npmRepo
    (((npmA, 1), npmDepC) :: ((npmA, 1), npmDepAlias) :: nil)
    nil nil (npmA, 1).

Definition npmInstOvr : NpmS.Inst :=
  NpmS.MkInst npmRepo (((npmA, 1), npmDepC) :: nil) nil
    ((npmC, npmEq 3) :: nil) (npmA, 1).

Example npm_versions_computes :
  NpmS.Reduced.VSet.elements
    (NpmS.Reduction.versions npmInst (NpmS.Name.Granular kC 2))
  = NpmS.Version.Orig 2 :: nil.
Proof. reflexivity. Qed.

Example npm_entry_edges_computes :
  npmDeps npmInst (NpmS.Name.Granular kA 1, NpmS.Version.Orig 1)
  = (NpmS.Name.Intermediate kA 1 kB, NpmS.Version.Orig 1 :: nil)
    :: (NpmS.Name.Intermediate kA 1 kC,
        NpmS.Version.Orig 2 :: NpmS.Version.Orig 3 :: nil) :: nil.
Proof. reflexivity. Qed.

Example npm_slot_versions_computes :
  NpmS.Reduced.VSet.elements
    (NpmS.Reduction.versions npmInst (NpmS.Name.Intermediate kA 1 kC))
  = NpmS.Version.Orig 2 :: NpmS.Version.Orig 3 :: nil.
Proof. reflexivity. Qed.

(* the directory reads B's descriptor too, which every directory with it
   shares *)
Example npm_peer_edge_computes :
  npmDeps npmInst (NpmS.Name.Intermediate kA 1 kB, NpmS.Version.Orig 1)
  = (NpmS.Name.Granular kB 1, NpmS.Version.Orig 1 :: nil)
    :: (NpmS.Name.Link kA 1 kB 1 npmC,
        NpmS.Version.Orig 1 :: NpmS.Version.Orig 2 :: nil)
    :: (NpmS.Name.Desc npmB npmB 1, NpmS.Version.Orig 1 :: nil) :: nil.
Proof. reflexivity. Qed.

(* The root A has no directory for C, but installs one for B's peer, or
   leaves it empty (Bot) where no peer asks. *)
Example npm_auto_versions_computes :
  NpmS.Reduced.VSet.elements
    (NpmS.Reduction.versions npmInstAuto
       (NpmS.Name.Intermediate kA 1 kC))
  = NpmS.Version.Orig 1 :: NpmS.Version.Orig 2 :: NpmS.Version.Orig 3 :: NpmS.Version.Bot :: nil.
Proof. reflexivity. Qed.

(* the same peer, one the root may not install (p_root false, as for a
   peer only Yarn Berry's packageExtensions add): the root's C is empty *)
Definition npmInstExt : NpmS.Inst :=
  NpmS.MkInst npmRepo (((npmA, 1), npmDepB) :: nil)
    (((npmB, 1), NpmS.MkPeer npmC (npmBetween 1 3) false false) :: nil)
    nil (npmA, 1).

Example npm_ext_versions_computes :
  NpmS.Reduced.VSet.elements
    (NpmS.Reduction.versions npmInstExt (NpmS.Name.Intermediate kA 1 kC))
  = NpmS.Version.Bot :: nil.
Proof. reflexivity. Qed.

Example npm_auto_edge_computes :
  npmDeps npmInstAuto (NpmS.Name.Intermediate kA 1 kB, NpmS.Version.Orig 1)
  = (NpmS.Name.Granular kB 1, NpmS.Version.Orig 1 :: nil)
    :: (NpmS.Name.Link kA 1 kB 1 npmC,
        NpmS.Version.Orig 1 :: NpmS.Version.Orig 2 :: nil)
    :: (NpmS.Name.Desc npmB npmB 1, NpmS.Version.Orig 1 :: nil) :: nil.
Proof. reflexivity. Qed.

Example npm_link_holder_computes :
  npmDeps npmInst (NpmS.Name.Link kA 1 kB 1 npmC, NpmS.Version.Orig 2)
  = (NpmS.Name.Intermediate kA 1 kC, NpmS.Version.Orig 2 :: nil)
    :: (NpmS.Name.Sight kB 1 npmC, NpmS.Version.Orig 2 :: NpmS.Version.Free :: nil)
    :: nil.
Proof. reflexivity. Qed.

(* the same peer, optional: the root's C may be left empty, and the link
   at Bot reads it so *)
Example npm_optional_edge_computes :
  npmDeps npmInstOpt (NpmS.Name.Intermediate kA 1 kB, NpmS.Version.Orig 1)
  = (NpmS.Name.Granular kB 1, NpmS.Version.Orig 1 :: nil)
    :: (NpmS.Name.Link kA 1 kB 1 npmC,
        NpmS.Version.Orig 1 :: NpmS.Version.Orig 2 :: NpmS.Version.Bot :: nil)
    :: (NpmS.Name.Desc npmB npmB 1, NpmS.Version.Orig 1 :: nil) :: nil.
Proof. reflexivity. Qed.

Example npm_optional_bot_computes :
  npmDeps npmInstOpt (NpmS.Name.Link kA 1 kB 1 npmC, NpmS.Version.Bot)
  = (NpmS.Name.Intermediate kA 1 kC, NpmS.Version.Bot :: nil)
    :: (NpmS.Name.Sight kB 1 npmC, NpmS.Version.Bot :: NpmS.Version.Free :: nil) :: nil.
Proof. reflexivity. Qed.

(* B@1 peers on C and depends on D@1, which peers on C too: B's copy holds
   no C (PEER LOCAL), and D's peer resolves to what B's own does. *)
Definition npmD : nat := 5.
Definition kD : NpmS.SourceName.t := (npmD, npmD).

Definition npmChainRepo : NpmS.RealPackageSet.t :=
  NpmS.RealPackageSet.add (npmD, 1) npmRepo.

Definition npmInstChain : NpmS.Inst :=
  NpmS.MkInst npmChainRepo
    (((npmA, 1), npmDepB) :: ((npmB, 1), NpmS.MkDep npmD npmD (npmEq 1) false (Some 4))
       :: nil)
    (((npmB, 1), npmPeerC) :: ((npmD, 1), npmPeerC) :: nil) nil (npmA, 1).

Example npm_peer_local_computes :
  NpmS.Reduced.VSet.elements
    (NpmS.Reduction.versions npmInstChain (NpmS.Name.Intermediate kB 1 kC))
  = nil.
Proof. reflexivity. Qed.

Example npm_chain_computes :
  npmDeps npmInstChain (NpmS.Name.Link kB 1 kD 1 npmC, NpmS.Version.Orig 2)
  = (NpmS.Name.Sight kB 1 npmC, NpmS.Version.Orig 2 :: nil)
    :: (NpmS.Name.Sight kD 1 npmC, NpmS.Version.Orig 2 :: NpmS.Version.Free :: nil)
    :: nil.
Proof. reflexivity. Qed.

(* B@1 depends on D@1, which peers on B: B offers itself. *)
Definition npmInstSelf : NpmS.Inst :=
  NpmS.MkInst npmChainRepo
    (((npmA, 1), npmDepB) :: ((npmB, 1), NpmS.MkDep npmD npmD (npmEq 1) false (Some 4))
       :: nil)
    (((npmD, 1), NpmS.MkPeer npmB (npmBetween 1 3) false true) :: nil) nil (npmA, 1).

Example npm_self_versions_computes :
  NpmS.Reduced.VSet.elements
    (NpmS.Reduction.versions npmInstSelf (NpmS.Name.Link kB 1 kD 1 npmB))
  = NpmS.Version.Orig 1 :: nil.
Proof. reflexivity. Qed.

Example npm_self_computes :
  npmDeps npmInstSelf (NpmS.Name.Link kB 1 kD 1 npmB, NpmS.Version.Orig 1)
  = (NpmS.Name.Sight kD 1 npmB, NpmS.Version.Orig 1 :: NpmS.Version.Free :: nil) :: nil.
Proof. reflexivity. Qed.

(* B@1 depends on D@1, which peers on C: B, not the root, neither holds
   nor peers on C, so it offers D's peer nothing, and no copy of C is put
   into B for it. *)
Definition npmInstSkip : NpmS.Inst :=
  NpmS.MkInst npmChainRepo
    (((npmA, 1), npmDepB) :: ((npmB, 1), NpmS.MkDep npmD npmD (npmEq 1) false (Some 4))
       :: nil)
    (((npmD, 1), npmPeerC) :: nil) nil (npmA, 1).

Example npm_skip_computes :
  NpmS.Reduced.VSet.elements
    (NpmS.Reduction.versions npmInstSkip (NpmS.Name.Link kB 1 kD 1 npmC))
  = nil.
Proof. reflexivity. Qed.

Example npm_skip_versions_computes :
  NpmS.Reduced.VSet.elements
    (NpmS.Reduction.versions npmInstSkip (NpmS.Name.Intermediate kB 1 kC))
  = nil.
Proof. reflexivity. Qed.

Example npm_root_peer_computes :
  npmDeps npmInstRootPeer (NpmS.Name.Granular kA 1, NpmS.Version.Orig 1)
  = (NpmS.Name.Intermediate kA 1 kC, NpmS.Version.Orig 1 :: NpmS.Version.Orig 2 :: nil)
    :: (NpmS.Name.Intermediate kA 1 kC,
        NpmS.Version.Orig 2 :: NpmS.Version.Orig 3 :: nil) :: nil.
Proof. reflexivity. Qed.

Example npm_root_peer_optional_computes :
  npmDeps npmInstRootPeerOpt (NpmS.Name.Granular kA 1, NpmS.Version.Orig 1)
  = npmDeps npmInstRootPeer (NpmS.Name.Granular kA 1, NpmS.Version.Orig 1).
Proof. reflexivity. Qed.

Example npm_root_peer_optional_bare_computes :
  npmDeps npmInstRootPeerOptBare (NpmS.Name.Granular kA 1, NpmS.Version.Orig 1)
  = (NpmS.Name.Intermediate kA 1 kB, NpmS.Version.Orig 1 :: nil) :: nil.
Proof. reflexivity. Qed.

Example npm_alias_computes :
  npmDeps npmInstAlias (NpmS.Name.Granular kA 1, NpmS.Version.Orig 1)
  = (NpmS.Name.Intermediate kA 1 kC,
     NpmS.Version.Orig 2 :: NpmS.Version.Orig 3 :: nil)
    :: (NpmS.Name.Intermediate kA 1 kX, NpmS.Version.Orig 1 :: nil) :: nil.
Proof. reflexivity. Qed.

(* B@1 depends on C in [2,4) and peers on C in [1,3) (a peer with
   default): the root's link may offer C 2, both ranges' meet, or Bot, and
   B's directory holds nothing where it is offered one and its own copy
   where it is not. *)
Definition npmInstDp : NpmS.Inst :=
  NpmS.MkInst npmRepo
    (((npmA, 1), npmDepB) :: ((npmB, 1), npmDepC) :: nil)
    (((npmB, 1), npmPeerC) :: nil) nil (npmA, 1).

Example npm_dp_link_computes :
  NpmS.Reduced.VSet.elements
    (NpmS.Reduction.versions npmInstDp (NpmS.Name.Link kA 1 kB 1 npmC))
  = NpmS.Version.Orig 2 :: NpmS.Version.Bot :: nil.
Proof. reflexivity. Qed.

Example npm_dp_offered_computes :
  npmDeps npmInstDp (NpmS.Name.Link kA 1 kB 1 npmC, NpmS.Version.Orig 2)
  = (NpmS.Name.Intermediate kA 1 kC, NpmS.Version.Orig 2 :: nil)
    :: (NpmS.Name.Intermediate kB 1 kC, NpmS.Version.Bot :: nil)
    :: (NpmS.Name.Sight kB 1 npmC, NpmS.Version.Orig 2 :: NpmS.Version.Free :: nil)
    :: nil.
Proof. reflexivity. Qed.

Example npm_dp_own_computes :
  npmDeps npmInstDp (NpmS.Name.Link kA 1 kB 1 npmC, NpmS.Version.Bot)
  = (NpmS.Name.Intermediate kA 1 kC, NpmS.Version.Bot :: nil)
    :: (NpmS.Name.Intermediate kB 1 kC,
        NpmS.Version.Orig 2 :: NpmS.Version.Orig 3 :: nil)
    :: (NpmS.Name.Sight kB 1 npmC,
        NpmS.Version.Orig 2 :: NpmS.Version.Orig 3 :: NpmS.Version.Free :: nil)
    :: nil.
Proof. reflexivity. Qed.

Example npm_override_computes :
  npmDeps npmInstOvr (NpmS.Name.Granular kA 1, NpmS.Version.Orig 1)
  = (NpmS.Name.Intermediate kA 1 kC, NpmS.Version.Orig 3 :: nil) :: nil.
Proof. reflexivity. Qed.

Definition npmInstOvrAlias (o : list (nat * NpmS.Range)) : NpmS.Inst :=
  NpmS.MkInst (NpmS.RealPackageSet.add (npmX, 1) npmRepo)
    (((npmA, 1), npmDepAlias) :: nil) nil o (npmA, 1).

Example npm_override_key_computes :
  npmDeps (npmInstOvrAlias ((npmX, npmEq 1) :: nil))
    (NpmS.Name.Granular kA 1, NpmS.Version.Orig 1)
  = (NpmS.Name.Intermediate kA 1 (npmX, npmX), NpmS.Version.Orig 1 :: nil) :: nil.
Proof. reflexivity. Qed.

Example npm_override_target_computes :
  npmDeps (npmInstOvrAlias ((npmC, npmEq 3) :: nil))
    (NpmS.Name.Granular kA 1, NpmS.Version.Orig 1)
  = (NpmS.Name.Intermediate kA 1 kX, NpmS.Version.Orig 1 :: nil) :: nil.
Proof. reflexivity. Qed.

Module NpmPreVM <: SemverMatch Nat_as_OT.
  Definition isPre (v : nat) : bool := Nat.odd v.
  Definition sameCore (a b : nat) : bool :=
    Nat.eqb (Nat.div a 2) (Nat.div b 2).
End NpmPreVM.

Module NpmP := Npm Nat_as_OT Nat_as_OT NpmPreVM.

Definition npmPreRepo : NpmP.RealPackageSet.t :=
  fold_right NpmP.RealPackageSet.add NpmP.RealPackageSet.empty
    ((npmC, 4) :: (npmC, 5) :: (npmC, 6) :: (npmC, 7) :: nil).

Example npm_prerelease_excluded :
  NpmP.VSet.elements
    (NpmP.rangeEval ((NpmP.COp OpGe 4 :: NpmP.COp OpLt 8 :: nil) :: nil)
       (NpmP.realVersions npmPreRepo npmC)) = 4 :: 6 :: nil.
Proof. reflexivity. Qed.

Example npm_prerelease_admitted :
  NpmP.VSet.elements
    (NpmP.rangeEval ((NpmP.COp OpGe 5 :: NpmP.COp OpLt 8 :: nil) :: nil)
       (NpmP.realVersions npmPreRepo npmC)) = 5 :: 6 :: nil.
Proof. reflexivity. Qed.

Module NplS := NpmPlacement Nat_as_OT Nat_as_OT NpmVM.

(* The project depends on key 4 aliasing package 2 and on 3 optionally;
   no version of 3 is in range, so that edge may find nothing. *)
Definition nplInst : NplS.Inst :=
  NplS.MkInst
    (fold_right NplS.RealPackageSet.add NplS.RealPackageSet.empty
       ((npmB, 1) :: (npmC, 1) :: nil))
    nil nil nil npmA
    (NplS.MkDep npmX npmB ((NplS.COp OpEq 1 :: nil) :: nil) false false
     :: NplS.MkDep npmC npmC ((NplS.COp OpEq 2 :: nil) :: nil) false true
     :: nil)
    nil.

Example npl_edges :
  List.map (fun e => (NplS.e_dir e, NplS.e_name e, NplS.e_optional e))
    (NplS.edgesOf nplInst NplS.Occupant.Proj) =
  (npmX, npmB, false) :: (npmC, npmC, true) :: nil.
Proof. reflexivity. Qed.

Example npl_key :
  NplS.Pl.VSet.elements
    (NplS.Pl.Source.versions (NplS.Reduction.placeRepo nplInst) npmX) =
  NplS.Occupant.Reg npmB 1 :: nil.
Proof. reflexivity. Qed.

Definition nplInstOvr (o : list (nat * NplS.Range)) : NplS.Inst :=
  NplS.MkInst
    (fold_right NplS.RealPackageSet.add NplS.RealPackageSet.empty
       ((npmB, 1) :: (npmB, 2) :: (npmX, 1) :: nil))
    nil nil o npmA
    (NplS.MkDep npmX npmB ((NplS.COp OpEq 2 :: nil) :: nil) false false :: nil)
    nil.

Definition nplAccepts (I : NplS.Inst) : list (list NplS.Occupant.t) :=
  List.map (fun e => NplS.Pl.VSet.elements (NplS.Reduction.accepts I e))
    (NplS.edgesOf I NplS.Occupant.Proj).

Example npl_override_key :
  nplAccepts (nplInstOvr ((npmX, (NplS.COp OpEq 1 :: nil) :: nil) :: nil)) =
  (NplS.Occupant.Reg npmX 1 :: nil) :: nil.
Proof. reflexivity. Qed.

Example npl_override_target :
  nplAccepts (nplInstOvr ((npmB, (NplS.COp OpEq 1 :: nil) :: nil) :: nil)) =
  (NplS.Occupant.Reg npmB 2 :: nil) :: nil.
Proof. reflexivity. Qed.
