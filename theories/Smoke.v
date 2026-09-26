From Stdlib Require Import MSets List.
From PackageCalculus Require Import Prelude Core Complexity Versions Semver
  Conflict ConflictClass Concurrent PeerDependency Visibility Feature
  Virtual PackageFormula VariableFormula FeatureConcurrent Debian DebianMA
  Opam Cargo Alpine Npm.

Module C := Core Nat_as_OT Nat_as_OT.
Module Cx := Complexity Nat_as_OT Nat_as_OT Nat_as_OT.
Module Cfl := Conflict Nat_as_OT Nat_as_OT.
Module Cls := ConflictClass Nat_as_OT Nat_as_OT.
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

Definition cxPhi : list Cx.ClauseOT.t :=
  ((0, true), ((1, false), (2, true))) :: nil.

Example complexity_reduceReal_computes :
  Cx.Reduction.T.PkgSet.cardinal (Cx.Reduction.reduceReal cxPhi) = 10.
Proof. reflexivity. Qed.

Example complexity_reduceDeps_computes :
  Cx.Reduction.T.DepRel.cardinal (Cx.Reduction.reduceDeps cxPhi) = 4.
Proof. reflexivity. Qed.

Definition cxR : Cx.PkgSet.t :=
  Cx.PkgSet.add (1, 1)
    (Cx.PkgSet.add (1, 2) (Cx.PkgSet.add (2, 1) Cx.PkgSet.empty)).

Definition cxD : Cx.C.DepRel.t :=
  Cx.C.DepRel.add ((1, 1), (2, Cx.VSet.singleton 1)) Cx.C.DepRel.empty.

Example complexity_satEncoding_computes :
  List.length (Cx.Encoding.satEncoding cxR cxD (1, 1)) = 3.
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
    (PkgF.Reduction.reduceDeps PkgF.PkgSet.empty
       (PkgF.DepRel.add ((1, 2), PkgF.FDep 3 (PkgF.VSet.singleton 4))
          PkgF.DepRel.empty)) = 1.
Proof. reflexivity. Qed.

Example variableFormula_reduceDeps_computes :
  VarF.Reduction.T.DepRel.cardinal
    (VarF.Reduction.reduceDeps (fun _ => VarF.Reduction.YSet.singleton 0)
       VarF.PkgSet.empty
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
    (Cfl.Reduction.reduceReal conflictR Cfl.C.DepRel.empty
       (Cfl.ConflictRel.add ((2, 20), (1, Cfl.C.VSet.singleton 11))
          Cfl.ConflictRel.empty)) = 5.
Proof. reflexivity. Qed.

Definition clsR : Cls.PkgSet.t :=
  Cls.PkgSet.add (1, 10)
    (Cls.PkgSet.add (1, 11) (Cls.PkgSet.add (2, 20) Cls.PkgSet.empty)).

Definition clsOm : Cls.InClassRel.t :=
  Cls.InClassRel.add ((1, 10), 0)
    (Cls.InClassRel.add ((1, 11), 0)
       (Cls.InClassRel.add ((2, 20), 0) Cls.InClassRel.empty)).

Example conflictClass_excludes :
  ~ Cls.ClassExclusion clsOm
      (Cls.PkgSet.add (1, 10) (Cls.PkgSet.add (2, 20) Cls.PkgSet.empty)).
Proof.
  intro H.
  assert (E : ((1, 10) : Cls.Pkg.t) = (2, 20))
    by (apply (H 0);
        first [apply Cls.PkgSet.mem_spec | apply Cls.InClassRel.mem_spec];
        reflexivity).
  discriminate E.
Qed.

Example conflictClass_reduction_excludes :
  forall S,
    Cls.Reduction.T.IsResolution (Cls.Reduction.reduceReal clsR clsOm)
      (Cls.Reduction.reduceDeps Cls.C.DepRel.empty clsOm)
      (Cls.Reduction.embedPkg (1, 10)) S ->
    ~ Cls.Reduction.T.PkgSet.In (Cls.Reduction.embedPkg (2, 20)) S.
Proof.
  intros S [_ Hr Hdep Huniq] Hq.
  destruct (Hdep _ Hr (Cls.Reduction.Name.Cls 0)
              (Cls.Reduction.T.VSet.singleton (Cls.Reduction.Version.Name 1)))
    as [w [Hw Hwr]]; [apply Cls.Reduction.T.DepRel.mem_spec; reflexivity |].
  destruct (Hdep _ Hq (Cls.Reduction.Name.Cls 0)
              (Cls.Reduction.T.VSet.singleton (Cls.Reduction.Version.Name 2)))
    as [w' [Hw' Hwq]]; [apply Cls.Reduction.T.DepRel.mem_spec; reflexivity |].
  apply Cls.Reduction.T.VSet.singleton_spec in Hw, Hw'; subst w w'.
  discriminate (Huniq _ _ _ Hwr Hwq).
Qed.

Example conflictClass_reduceReal_computes :
  Cls.Reduction.T.VSet.cardinal
    (Cls.Reduction.T.versions (Cls.Reduction.reduceReal clsR clsOm)
       (Cls.Reduction.Name.Cls 0)) = 2.
Proof. reflexivity. Qed.

Example conflictClass_roundtrip_computes :
  Cls.C.PkgSet.equal
    (Cls.Reduction.classResolution
       (Cls.Reduction.coreResolution clsR clsOm))
    clsR = true.
Proof. reflexivity. Qed.

Definition debR : Deb.PkgSet.t :=
  Deb.PkgSet.add (1, 10) (Deb.PkgSet.add (1, 11) Deb.PkgSet.empty).

Definition debD : Deb.Deps.t :=
  Deb.Deps.add ((1, 10), ((1, Deb.Ver.FTop) :: nil))
    Deb.Deps.empty.

Definition debRec : Deb.Deps.t :=
  Deb.Deps.add ((1, 10), ((2, Deb.Ver.FTop) :: nil))
    Deb.Deps.empty.

Example debian_vers_computes :
  Deb.T.VSet.cardinal
    (Deb.versions debR debD Deb.Deps.empty Deb.Prov.empty Deb.Conf.empty
       (Deb.Name.Orig 1)) = 3.
Proof. reflexivity. Qed.

Example debian_dependees_computes :
  Deb.T.DependeesSet.cardinal
    (Deb.dependees debR debD Deb.Deps.empty Deb.Prov.empty Deb.Conf.empty
       (Deb.Name.Orig 1, Deb.Version.Orig 10)) = 1.
Proof. reflexivity. Qed.

Example debian_soft_vers_computes :
  Deb.T.VSet.cardinal
    (Deb.versions debR debD debRec Deb.Prov.empty Deb.Conf.empty
       (Deb.Name.Soft ((2, Deb.Ver.FTop) :: nil))) = 2.
Proof. reflexivity. Qed.

Example debian_soft_escape_computes :
  Deb.T.DependeesSet.cardinal
    (Deb.dependees debR debD debRec Deb.Prov.empty Deb.Conf.empty
       (Deb.Name.Soft ((2, Deb.Ver.FTop) :: nil),
        Deb.Version.Zero)) = 0.
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

Module Op := Opam Nat_as_OT Nat_as_OT BoolFin Nat_as_OT Nat_as_OT.

Definition opRho : Op.Valuation := fun _ => Some 1.
Definition opRepo : Op.PkgSet.t :=
  Op.PkgSet.add (1, 10) (Op.PkgSet.add (2, 20) Op.PkgSet.empty).

Definition opInst : Op.Inst :=
  Op.MkInst opRepo
    (((1, 10),
      Op.OFAtom 2 (Op.FlCmp OpEq false 1) (Op.VCCmp OpGe 15)) :: nil)
    nil
    Op.ClsRel.empty
    nil
    (((2, 20), (7, Op.FlTrue)) :: nil)
    Op.PkgSet.empty
    nil
    (Op.OFAtom 1 Op.FlTrue Op.VCTop)
    (Op.OFAtom 1 Op.FlFalse Op.VCTop).

Example opam_reduceReal_computes :
  Op.Reduction.PF.PkgSet.cardinal (Op.Reduction.reduceReal opRho opInst) = 3.
Proof. reflexivity. Qed.

Example opam_reduceDeps_computes :
  Op.Reduction.PF.DepRel.cardinal
    (Op.Reduction.reduceDeps opRho opInst) = 2.
Proof. reflexivity. Qed.

Example opam_depexts_computes :
  Op.ESet.elements
    (Op.depextsOf opRho opInst (Op.PkgSet.add (2, 20) Op.PkgSet.empty))
  = 7 :: nil.
Proof. reflexivity. Qed.

Example opam_depexts_unselected :
  Op.depextsOf opRho opInst (Op.PkgSet.add (1, 10) Op.PkgSet.empty)
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
    (Cgo.evalReq (Cgo.PkgSet.add (0, 4) (Cgo.PkgSet.add (0, 6)
       Cgo.PkgSet.empty)) 0 cgoAny) = 2.
Proof. reflexivity. Qed.

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

Module NatPM <: ApkVerMatch Nat_as_OT.
  Definition prefix := Nat.eqb.
  Definition hash := Nat.eqb.
End NatPM.
Module Alp := Alpine Nat_as_OT Nat_as_OT NatPM.

Definition alpI : Alp.Inst :=
  {| Alp.inst_repo :=
       Alp.PkgSet.add (1, 10)
         (Alp.PkgSet.add (2, 20) (Alp.PkgSet.add (3, 30) Alp.PkgSet.empty))
   ; Alp.inst_deps :=
       Alp.Deps.add ((1, 10), Alp.DPos (2, Alp.COp OpGe 20)) Alp.Deps.empty
   ; Alp.inst_prov :=
       Alp.Prov.add ((3, 30), (4, Alp.PVer 5))
         (Alp.Prov.add ((2, 20), (6, Alp.PBare)) Alp.Prov.empty)
   ; Alp.inst_installIf :=
       Alp.InstallIf.add ((2, 20), Alp.CondSet.add (Alp.DPos (1, Alp.CAny))
                                (Alp.CondSet.add (Alp.DNeg (5, Alp.CAny))
                                   Alp.CondSet.empty)) Alp.InstallIf.empty
   ; Alp.inst_world := Alp.WSet.add (Alp.DPos (1, Alp.CAny)) Alp.WSet.empty
   ; Alp.inst_prio := Alp.Prio.empty |}.

Example alpine_reduceReal_computes :
  Alp.Reduction.PF.PkgSet.cardinal (Alp.Reduction.reduceReal alpI) = 5.
Proof. reflexivity. Qed.

Example alpine_root_dependees_computes :
  Alp.Reduction.FSet.cardinal
    (Alp.Reduction.dependees alpI Alp.Reduction.rootPkg) = 1.
Proof. reflexivity. Qed.

Example alpine_installif_attaches :
  Alp.InstallIf.cardinal (Alp.Reduction.installIfFibre alpI (1, 10)) = 1.
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

Definition npmRepo : NpmS.RepoSet.t :=
  fold_right NpmS.RepoSet.add NpmS.RepoSet.empty
    ((npmA, 1) :: (npmB, 1) :: (npmC, 1) :: (npmC, 2) :: (npmC, 3) :: nil).

Definition npmDepB : NpmS.Dependency := NpmS.MkDep npmB npmB (npmEq 1) false.
Definition npmDepC : NpmS.Dependency :=
  NpmS.MkDep npmC npmC (npmBetween 2 4) false.
Definition npmPeerC : NpmS.PeerDependency :=
  NpmS.MkPeer npmC (npmBetween 1 3) false.
Definition npmPeerCOpt : NpmS.PeerDependency :=
  NpmS.MkPeer npmC (npmBetween 1 3) true.

Definition kA : NpmS.NKey.t := (npmA, npmA).
Definition kB : NpmS.NKey.t := (npmB, npmB).
Definition kC : NpmS.NKey.t := (npmC, npmC).
Definition kX : NpmS.NKey.t := (npmX, npmC).

Definition npmShow (h : NpmS.T.Dependees.t)
  : NpmS.Nm.t * list NpmS.Vs.t :=
  (fst h, NpmS.T.VSet.elements (snd h)).

Definition npmDeps (I : NpmS.Inst) (s : NpmS.T.Pkg.t) :=
  List.map npmShow
    (NpmS.T.DependeesSet.elements (NpmS.Reduction.dependees I s)).

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
  NpmS.MkDep npmX npmC (npmEq 1) false.

Definition npmInstAlias : NpmS.Inst :=
  NpmS.MkInst npmRepo
    (((npmA, 1), npmDepC) :: ((npmA, 1), npmDepAlias) :: nil)
    nil nil (npmA, 1).

Definition npmInstOvr : NpmS.Inst :=
  NpmS.MkInst npmRepo (((npmA, 1), npmDepC) :: nil) nil
    ((npmC, npmEq 3) :: nil) (npmA, 1).

Example npm_versions_computes :
  NpmS.T.VSet.elements
    (NpmS.Reduction.versions npmInst (NpmS.Nm.Granular kC 2))
  = NpmS.Vs.Orig 2 :: nil.
Proof. reflexivity. Qed.

Example npm_entry_edges_computes :
  npmDeps npmInst (NpmS.Nm.Granular kA 1, NpmS.Vs.Orig 1)
  = (NpmS.Nm.Intermediate kA 1 kB, NpmS.Vs.Orig 1 :: nil)
    :: (NpmS.Nm.Intermediate kA 1 kC,
        NpmS.Vs.Orig 2 :: NpmS.Vs.Orig 3 :: nil) :: nil.
Proof. reflexivity. Qed.

Example npm_slot_versions_computes :
  NpmS.T.VSet.elements
    (NpmS.Reduction.versions npmInst (NpmS.Nm.Intermediate kA 1 kC))
  = NpmS.Vs.Orig 2 :: NpmS.Vs.Orig 3 :: nil.
Proof. reflexivity. Qed.

Example npm_peer_edge_computes :
  npmDeps npmInst (NpmS.Nm.Intermediate kA 1 kB, NpmS.Vs.Orig 1)
  = (NpmS.Nm.Granular kB 1, NpmS.Vs.Orig 1 :: nil)
    :: (NpmS.Nm.Intermediate kA 1 kC,
        NpmS.Vs.Orig 1 :: NpmS.Vs.Orig 2 :: nil) :: nil.
Proof. reflexivity. Qed.

Example npm_auto_versions_computes :
  NpmS.T.VSet.elements
    (NpmS.Reduction.versions npmInstAuto
       (NpmS.Nm.Intermediate kA 1 kC))
  = NpmS.Vs.Orig 1 :: NpmS.Vs.Orig 2 :: NpmS.Vs.Orig 3 :: nil.
Proof. reflexivity. Qed.

Example npm_auto_edge_computes :
  npmDeps npmInstAuto (NpmS.Nm.Intermediate kA 1 kB, NpmS.Vs.Orig 1)
  = (NpmS.Nm.Granular kB 1, NpmS.Vs.Orig 1 :: nil)
    :: (NpmS.Nm.Intermediate kA 1 kC,
        NpmS.Vs.Orig 1 :: NpmS.Vs.Orig 2 :: nil) :: nil.
Proof. reflexivity. Qed.

Example npm_optional_edge_computes :
  npmDeps npmInstOpt (NpmS.Nm.Intermediate kA 1 kB, NpmS.Vs.Orig 1)
  = (NpmS.Nm.Granular kB 1, NpmS.Vs.Orig 1 :: nil) :: nil.
Proof. reflexivity. Qed.

Example npm_root_peer_computes :
  npmDeps npmInstRootPeer (NpmS.Nm.Granular kA 1, NpmS.Vs.Orig 1)
  = (NpmS.Nm.Intermediate kA 1 kC, NpmS.Vs.Orig 1 :: NpmS.Vs.Orig 2 :: nil)
    :: (NpmS.Nm.Intermediate kA 1 kC,
        NpmS.Vs.Orig 2 :: NpmS.Vs.Orig 3 :: nil) :: nil.
Proof. reflexivity. Qed.

Example npm_root_peer_optional_computes :
  npmDeps npmInstRootPeerOpt (NpmS.Nm.Granular kA 1, NpmS.Vs.Orig 1)
  = npmDeps npmInstRootPeer (NpmS.Nm.Granular kA 1, NpmS.Vs.Orig 1).
Proof. reflexivity. Qed.

Example npm_root_peer_optional_bare_computes :
  npmDeps npmInstRootPeerOptBare (NpmS.Nm.Granular kA 1, NpmS.Vs.Orig 1)
  = (NpmS.Nm.Intermediate kA 1 kB, NpmS.Vs.Orig 1 :: nil) :: nil.
Proof. reflexivity. Qed.

Example npm_alias_computes :
  npmDeps npmInstAlias (NpmS.Nm.Granular kA 1, NpmS.Vs.Orig 1)
  = (NpmS.Nm.Intermediate kA 1 kC,
     NpmS.Vs.Orig 2 :: NpmS.Vs.Orig 3 :: nil)
    :: (NpmS.Nm.Intermediate kA 1 kX, NpmS.Vs.Orig 1 :: nil) :: nil.
Proof. reflexivity. Qed.

Example npm_override_computes :
  npmDeps npmInstOvr (NpmS.Nm.Granular kA 1, NpmS.Vs.Orig 1)
  = (NpmS.Nm.Intermediate kA 1 kC, NpmS.Vs.Orig 3 :: nil) :: nil.
Proof. reflexivity. Qed.

Module NpmPreVM <: SemverMatch Nat_as_OT.
  Definition isPre (v : nat) : bool := Nat.odd v.
  Definition sameCore (a b : nat) : bool :=
    Nat.eqb (Nat.div a 2) (Nat.div b 2).
End NpmPreVM.

Module NpmP := Npm Nat_as_OT Nat_as_OT NpmPreVM.

Definition npmPreRepo : NpmP.RepoSet.t :=
  fold_right NpmP.RepoSet.add NpmP.RepoSet.empty
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
