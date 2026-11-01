From Stdlib Require Import MSets List.
From PackageCalculus Require Import Prelude Core Complexity VersionFormula Semver
  Conflict ConflictClass Concurrent PeerDependency Visibility Feature
  Virtual PackageFormula VariableFormula ConcurrentFeature Debian MultiarchDebian
  Opam Cargo Alpine Npm Placement NpmPlacement.

Module Core := Core Nat_as_OT Nat_as_OT.
Module Complexity := Complexity Nat_as_OT Nat_as_OT Nat_as_OT.
Module Conflict := Conflict Nat_as_OT Nat_as_OT.
Module ConflictClass := ConflictClass Nat_as_OT Nat_as_OT.
Module VersionFormula := VersionFormula Nat_as_OT Nat_as_OT.
Module Concurrent := Concurrent Nat_as_OT Nat_as_OT Nat_as_OT.
Module PeerDependency := PeerDependency Nat_as_OT Nat_as_OT Nat_as_OT.
Module Visibility := Visibility Nat_as_OT Nat_as_OT.
Module Placement := Placement Nat_as_OT Nat_as_OT.

Module BoolFinite <: FiniteUsualOrderedType.
  Include UOTFromCompare BoolComp.
  Definition enum : list t := (false :: true :: nil).
  Lemma enum_complete : forall x : t, List.In x enum.
  Proof. intros [|]; simpl; auto. Qed.
End BoolFinite.

Module Feature := Feature Nat_as_OT Nat_as_OT BoolFinite.
Module Virtual := Virtual Nat_as_OT Nat_as_OT.
Module PackageFormula := PackageFormula Nat_as_OT Nat_as_OT.
Module VariableFormula := VariableFormula Nat_as_OT Nat_as_OT BoolFinite Nat_as_OT.
Module ConcurrentFeature := ConcurrentFeature Nat_as_OT Nat_as_OT BoolFinite Nat_as_OT.
Module NatTrivialGroup := TrivialGroup Nat_as_OT.
Module Debian := Debian Nat_as_OT Nat_as_OT NatTrivialGroup.

Module BoolArchitectureParameter <: ArchitectureParameter.
  Module Architecture := BoolFinite.

  Definition native : Architecture.t := false.
End BoolArchitectureParameter.
Module MultiarchDebian := MultiarchDebian Nat_as_OT Nat_as_OT BoolArchitectureParameter.

Example core_pkgSet_computes :
  Core.PackageSet.mem (1, 2) (Core.PackageSet.add (1, 2) Core.PackageSet.empty) = true.
Proof. reflexivity. Qed.

Example core_depRel_computes :
  Core.DependencyRel.mem (( (1, 2), (3, Core.VSet.singleton 4) ))
    (Core.DependencyRel.add ((1, 2), (3, Core.VSet.singleton 4)) Core.DependencyRel.empty) = true.
Proof. reflexivity. Qed.

Example core_merge_computes :
  Core.DependencyRel.cardinal
    (Core.Merge.merge (Core.DependencyRel.add ((1, 2), (3, Core.VSet.singleton 4))
                (Core.DependencyRel.add ((1, 2), (3, Core.VSet.singleton 5))
                   Core.DependencyRel.empty))) = 1.
Proof. reflexivity. Qed.

Definition ckR : Core.PackageSet.t :=
  Core.PackageSet.ofList ((0, 0) :: (1, 1) :: (1, 2) :: (2, 0) :: nil).

Definition ckVS : Core.VSet.t := Core.VSet.ofList (1 :: 2 :: nil).

Definition ckD : Core.DependencyRel.t := Core.DependencyRel.ofList (((0, 0), (1, ckVS)) :: nil).

Definition ckCheck (S : list (nat * nat)) : option Core.CheckFailure :=
  Core.check (Core.versions ckR) (Core.dependees ckD) (Core.rootQuery (0, 0))
    (Core.PackageSet.ofList S).

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
  ckCheck ((1, 2) :: nil) = Some (CheckRootMem (0, Core.VSet.singleton 0)).
Proof. reflexivity. Qed.

Example core_check_dep_closure :
  ckCheck ((0, 0) :: nil) = Some (CheckDepClosure (0, 0) (1, ckVS)).
Proof. reflexivity. Qed.

Example core_check_reached :
  ckCheck ((0, 0) :: (1, 2) :: (2, 0) :: nil) = Some (CheckReached (2, 0)).
Proof. reflexivity. Qed.

Definition cxPhi : list Complexity.ClauseOT.t :=
  ((0, true), ((1, false), (2, true))) :: nil.

Example complexity_reduceReal_computes :
  Complexity.Reduction.Reduced.PackageSet.cardinal (Complexity.Reduction.reduceReal cxPhi) = 10.
Proof. reflexivity. Qed.

Example complexity_reduceDeps_computes :
  Complexity.Reduction.Reduced.DependencyRel.cardinal (Complexity.Reduction.reduceDeps cxPhi) = 4.
Proof. reflexivity. Qed.

Definition cxR : Complexity.PackageSet.t :=
  Complexity.PackageSet.add (1, 1)
    (Complexity.PackageSet.add (1, 2) (Complexity.PackageSet.add (2, 1) Complexity.PackageSet.empty)).

Definition cxD : Complexity.Source.DependencyRel.t :=
  Complexity.Source.DependencyRel.add ((1, 1), (2, Complexity.VSet.singleton 1)) Complexity.Source.DependencyRel.empty.

Example complexity_satEncoding_computes :
  List.length (Complexity.Encoding.satEncoding cxR cxD (1, 1)) = 3.
Proof. reflexivity. Qed.

Definition verR : VersionFormula.PackageSet.t := VersionFormula.PackageSet.add (1, 2) VersionFormula.PackageSet.empty.

Definition verD : VersionFormula.DependencyRel.t :=
  VersionFormula.DependencyRel.add ((1, 2), (1, VersionFormula.FTop)) VersionFormula.DependencyRel.empty.

Example versions_reduce_computes :
  VersionFormula.Source.DependencyRel.cardinal (VersionFormula.Reduction.reduce verR verD) = 1.
Proof. reflexivity. Qed.

Example versions_realPreimage_computes :
  VersionFormula.PackageSet.cardinal (VersionFormula.Reduction.Lookup.realPreimage verR verD) = 1.
Proof. reflexivity. Qed.

Example packageFormula_reduceDeps_computes :
  PackageFormula.Reduction.Reduced.DependencyRel.cardinal
    (PackageFormula.Reduction.reduceDeps PackageFormula.PackageSet.empty
       (PackageFormula.DependencyRel.add ((1, 2), PackageFormula.FAtom 3 (PackageFormula.VSet.singleton 4))
          PackageFormula.DependencyRel.empty)) = 1.
Proof. reflexivity. Qed.

Example variableFormula_reduceDeps_computes :
  VariableFormula.Reduction.Reduced.DependencyRel.cardinal
    (VariableFormula.Reduction.reduceDeps (fun _ => VariableFormula.YSet.singleton 0)
       VariableFormula.PackageSet.empty
       (VariableFormula.DependencyRel.add ((1, 2), VariableFormula.FAtom 3 (VariableFormula.VSet.singleton 4))
          VariableFormula.DependencyRel.empty)) = 1.
Proof. reflexivity. Qed.

Example feature_reduceDeps_computes :
  Feature.Reduction.Reduced.DependencyRel.cardinal
    (Feature.Reduction.reduceDeps Feature.PackageSet.empty Feature.SupportRel.empty
       (Feature.ParameterisedDependencyRel.add
          ((1, 2), (3, (Feature.VSet.singleton 4, Feature.FSet.empty)))
          Feature.ParameterisedDependencyRel.empty)
       Feature.AdditionalDependencyRel.empty) = 1.
Proof. reflexivity. Qed.

(* Built in Conflict.C, the core instance living inside the Conflict
   instantiation, rather than in the C above. *)
Definition conflictR : Conflict.Source.PackageSet.t :=
  Conflict.Source.PackageSet.add (1, 10)
    (Conflict.Source.PackageSet.add (1, 11) (Conflict.Source.PackageSet.add (2, 20) Conflict.Source.PackageSet.empty)).

Example conflict_conflictResolution_retraction_computes :
  Conflict.Source.PackageSet.equal
    (Conflict.Reduction.conflictResolution (Conflict.Reduction.embedSet conflictR))
    conflictR = true.
Proof. reflexivity. Qed.

Example conflict_reduceReal_computes :
  Conflict.Reduction.Reduced.PackageSet.cardinal
    (Conflict.Reduction.reduceReal conflictR Conflict.Source.DependencyRel.empty
       (Conflict.ConflictRel.add ((2, 20), (1, Conflict.Source.VSet.singleton 11))
          Conflict.ConflictRel.empty)) = 5.
Proof. reflexivity. Qed.

Definition clsR : ConflictClass.PackageSet.t :=
  ConflictClass.PackageSet.add (1, 10)
    (ConflictClass.PackageSet.add (1, 11) (ConflictClass.PackageSet.add (2, 20) ConflictClass.PackageSet.empty)).

Definition clsOm : ConflictClass.ConflictClassRel.t :=
  ConflictClass.ConflictClassRel.add ((1, 10), 0)
    (ConflictClass.ConflictClassRel.add ((1, 11), 0)
       (ConflictClass.ConflictClassRel.add ((2, 20), 0) ConflictClass.ConflictClassRel.empty)).

Example conflictClass_excludes :
  ~ ConflictClass.ClassExclusion clsOm
      (ConflictClass.PackageSet.add (1, 10) (ConflictClass.PackageSet.add (2, 20) ConflictClass.PackageSet.empty)).
Proof.
  intro H.
  assert (E : ((1, 10) : ConflictClass.Package.t) = (2, 20))
    by (apply (H 0);
        first [apply ConflictClass.PackageSet.mem_spec | apply ConflictClass.ConflictClassRel.mem_spec];
        reflexivity).
  discriminate E.
Qed.

Example conflictClass_reduction_excludes :
  forall S,
    ConflictClass.Reduction.Reduced.IsResolution (ConflictClass.Reduction.reduceReal clsR clsOm)
      (ConflictClass.Reduction.reduceDeps ConflictClass.Source.DependencyRel.empty clsOm)
      (ConflictClass.Reduction.embedPkg (1, 10)) S ->
    ~ ConflictClass.Reduction.Reduced.PackageSet.In (ConflictClass.Reduction.embedPkg (2, 20)) S.
Proof.
  intros S [_ Hr Hdep Huniq] Hq.
  destruct (Hdep _ Hr (ConflictClass.Reduction.Name.Class 0)
              (ConflictClass.Reduction.Reduced.VSet.singleton (ConflictClass.Reduction.Version.Name 1)))
    as [w [Hw Hwr]]; [apply ConflictClass.Reduction.Reduced.DependencyRel.mem_spec; reflexivity |].
  destruct (Hdep _ Hq (ConflictClass.Reduction.Name.Class 0)
              (ConflictClass.Reduction.Reduced.VSet.singleton (ConflictClass.Reduction.Version.Name 2)))
    as [w' [Hw' Hwq]]; [apply ConflictClass.Reduction.Reduced.DependencyRel.mem_spec; reflexivity |].
  apply ConflictClass.Reduction.Reduced.VSet.singleton_spec in Hw, Hw'; subst w w'.
  discriminate (Huniq _ _ _ Hwr Hwq).
Qed.

Example conflictClass_reduceReal_computes :
  ConflictClass.Reduction.Reduced.VSet.cardinal
    (ConflictClass.Reduction.Reduced.versions (ConflictClass.Reduction.reduceReal clsR clsOm)
       (ConflictClass.Reduction.Name.Class 0)) = 2.
Proof. reflexivity. Qed.

Example conflictClass_retraction_computes :
  ConflictClass.Source.PackageSet.equal
    (ConflictClass.Reduction.conflictClassResolution
       (ConflictClass.Reduction.coreResolution clsOm clsR))
    clsR = true.
Proof. reflexivity. Qed.

Definition debR : Debian.PackageSet.t :=
  Debian.PackageSet.add (1, 10) (Debian.PackageSet.add (1, 11) Debian.PackageSet.empty).

Definition debD : Debian.DependencyRel.t :=
  Debian.DependencyRel.add ((1, 10), ((1, Debian.VersionFormula.FTop) :: nil))
    Debian.DependencyRel.empty.

Definition debRec : Debian.DependencyRel.t :=
  Debian.DependencyRel.add ((1, 10), ((2, Debian.VersionFormula.FTop) :: nil))
    Debian.DependencyRel.empty.

Example debian_vers_computes :
  Debian.Reduction.Reduced.VSet.cardinal
    (Debian.Reduction.versions
       (Debian.MkInst debR debD Debian.DependencyRel.empty Debian.ProvidesRel.empty Debian.ConflictRel.empty
          (1, 10))
       (Debian.Reduction.Name.Orig 1)) = 3.
Proof. reflexivity. Qed.

Example debian_dependees_computes :
  Debian.Reduction.Reduced.DependeeSet.cardinal
    (Debian.Reduction.dependees
       (Debian.MkInst debR debD Debian.DependencyRel.empty Debian.ProvidesRel.empty Debian.ConflictRel.empty
          (1, 10))
       (Debian.Reduction.Name.Orig 1, Debian.Reduction.Version.Orig 10)) = 1.
Proof. reflexivity. Qed.

Example debian_soft_vers_computes :
  Debian.Reduction.Reduced.VSet.cardinal
    (Debian.Reduction.versions
       (Debian.MkInst debR debD debRec Debian.ProvidesRel.empty Debian.ConflictRel.empty (1, 10))
       (Debian.Reduction.Name.Soft ((2, Debian.VersionFormula.FTop) :: nil))) = 2.
Proof. reflexivity. Qed.

Example debian_soft_escape_computes :
  Debian.Reduction.Reduced.DependeeSet.cardinal
    (Debian.Reduction.dependees
       (Debian.MkInst debR debD debRec Debian.ProvidesRel.empty Debian.ConflictRel.empty (1, 10))
       (Debian.Reduction.Name.Soft ((2, Debian.VersionFormula.FTop) :: nil),
        Debian.Reduction.Version.Zero)) = 0.
Proof. reflexivity. Qed.

Definition maR : MultiarchDebian.PackageSet.t :=
  MultiarchDebian.PackageSet.add ((1, false), 10)
    (MultiarchDebian.PackageSet.add ((1, true), 10) MultiarchDebian.PackageSet.empty).

Example debianMA_reduceReal_computes :
  MultiarchDebian.Debian.VersionFormula.Source.PackageSet.cardinal (MultiarchDebian.Reduction.reduceReal maR) = 2.
Proof. reflexivity. Qed.

Example debianMA_reduceConf_computes :
  MultiarchDebian.Debian.ConflictRel.cardinal
    (MultiarchDebian.Reduction.reduceConf maR MultiarchDebian.ConflictRel.empty MultiarchDebian.ClassRel.empty) = 2.
Proof. reflexivity. Qed.

Definition visR : Visibility.PackageSet.t :=
  Visibility.PackageSet.add (1, 1) (Visibility.PackageSet.add (2, 1) Visibility.PackageSet.empty).

Definition visD : Visibility.Source.DependencyRel.t :=
  Visibility.Source.DependencyRel.add ((1, 1), (2, Visibility.VSet.singleton 1)) Visibility.Source.DependencyRel.empty.

Example visibility_reduceReal_computes :
  Visibility.Reduction.Reduced.PackageSet.cardinal
    (Visibility.Reduction.reduceReal visR visD Visibility.PublicDependencyRel.empty (1, 1)) = 4.
Proof. reflexivity. Qed.

Example visibility_reduceDeps_computes :
  Visibility.Reduction.Reduced.DependencyRel.cardinal
    (Visibility.Reduction.reduceDeps visR visD Visibility.PublicDependencyRel.empty (1, 1)) = 3.
Proof. reflexivity. Qed.

Example visibility_sub_computes :
  Visibility.PackageSet.cardinal
    (Visibility.sub Visibility.PublicDependencyRel.empty
       (Visibility.ParentRel.add ((2, 1), (1, 1)) Visibility.ParentRel.empty) (1, 1)) = 2.
Proof. reflexivity. Qed.

Module Opam := Opam Nat_as_OT Nat_as_OT BoolFinite Nat_as_OT Nat_as_OT.

Definition opRho : Opam.Valuation := fun _ => Some 1.
Definition opRepo : Opam.PackageSet.t :=
  Opam.PackageSet.add (1, 10) (Opam.PackageSet.add (2, 20) Opam.PackageSet.empty).

Definition opInst : Opam.Inst :=
  Opam.MkInst opRepo
    (((1, 10),
      Opam.OFAtom 2 (Opam.FlCmp OpEq false 1) (Opam.VFCmp OpGe 15)) :: nil)
    nil
    Opam.ConflictClassRel.empty
    nil
    (((2, 20), (7, Opam.FlTrue)) :: nil)
    Opam.PackageSet.empty
    nil
    (Opam.OFAtom 1 Opam.FlTrue Opam.VFTop)
    (Opam.OFAtom 1 Opam.FlFalse Opam.VFTop).

Example opam_reduceReal_computes :
  Opam.Reduction.PackageFormula.PackageSet.cardinal (Opam.Reduction.reduceReal opRho opInst) = 3.
Proof. reflexivity. Qed.

Example opam_reduceDeps_computes :
  Opam.Reduction.PackageFormula.DependencyRel.cardinal
    (Opam.Reduction.reduceDeps opRho opInst) = 2.
Proof. reflexivity. Qed.

Example opam_depexts_computes :
  Opam.ESet.elements
    (Opam.depextsOf opRho opInst (Opam.PackageSet.add (2, 20) Opam.PackageSet.empty))
  = 7 :: nil.
Proof. reflexivity. Qed.

Example opam_depexts_unselected :
  Opam.depextsOf opRho opInst (Opam.PackageSet.add (1, 10) Opam.PackageSet.empty)
  = Opam.ESet.empty.
Proof. reflexivity. Qed.

Module CargoSemverMatch <: SemverMatch Nat_as_OT.
  Definition isPre (v : nat) : bool := Nat.odd v.
  Definition sameCore (a b : nat) : bool :=
    Nat.eqb (Nat.div a 2) (Nat.div b 2).
End CargoSemverMatch.

Module Cargo := Cargo Nat_as_OT Nat_as_OT BoolFinite
  Nat_as_OT Nat_as_OT Nat_as_OT CargoSemverMatch.

Definition cgoAny : Cargo.Range := (Cargo.CAny :: nil) :: nil.

Example cargo_rgHolds_computes :
  Cargo.rgHolds cgoAny 4 = true.
Proof. reflexivity. Qed.

Example cargo_evalReq_computes :
  Cargo.VSet.cardinal
    (Cargo.Reduction.evalReq (Cargo.PackageSet.add (0, 4) (Cargo.PackageSet.add (0, 6)
       Cargo.PackageSet.empty)) 0 cgoAny) = 2.
Proof. reflexivity. Qed.

Example cargo_prerelease_excluded :
  Cargo.VSet.elements
    (Cargo.Reduction.evalReq (Cargo.PackageSet.add (0, 4) (Cargo.PackageSet.add (0, 5)
       Cargo.PackageSet.empty)) 0 ((Cargo.COp OpGe 4 :: nil) :: nil)) = 4 :: nil.
Proof. reflexivity. Qed.

Example cargo_prerelease_admitted :
  Cargo.VSet.elements
    (Cargo.Reduction.evalReq (Cargo.PackageSet.add (0, 4) (Cargo.PackageSet.add (0, 5)
       Cargo.PackageSet.empty)) 0 ((Cargo.COp OpGe 5 :: nil) :: nil)) = 5 :: nil.
Proof. reflexivity. Qed.

Module NatApkVersionMatch <: ApkVersionMatch Nat_as_OT.
  Definition prefix := Nat.eqb.
  Definition hash := Nat.eqb.
End NatApkVersionMatch.
Module Alpine := Alpine Nat_as_OT Nat_as_OT NatApkVersionMatch.

Definition alpI : Alpine.Inst :=
  {| Alpine.inst_real :=
       Alpine.PackageSet.add (1, 10)
         (Alpine.PackageSet.add (2, 20) (Alpine.PackageSet.add (3, 30) Alpine.PackageSet.empty))
   ; Alpine.inst_deps :=
       Alpine.DependencyRel.add ((1, 10), Alpine.DPos (2, Alpine.COp OpGe 20)) Alpine.DependencyRel.empty
   ; Alpine.inst_prov :=
       Alpine.ProvidesRel.add ((3, 30), (4, Alpine.PVer 5))
         (Alpine.ProvidesRel.add ((2, 20), (6, Alpine.PBare)) Alpine.ProvidesRel.empty)
   ; Alpine.inst_installIf :=
       Alpine.InstallIfRuleRel.add ((2, 20), Alpine.ConditionSet.add (Alpine.DPos (1, Alpine.CAny))
                                (Alpine.ConditionSet.add (Alpine.DNeg (5, Alpine.CAny))
                                   Alpine.ConditionSet.empty)) Alpine.InstallIfRuleRel.empty
   ; Alpine.inst_world := Alpine.WorldSet.add (Alpine.DPos (1, Alpine.CAny)) Alpine.WorldSet.empty
   ; Alpine.inst_prio := Alpine.PriorityRel.empty |}.

Example alpine_reduceReal_computes :
  Alpine.Reduction.PackageFormula.PackageSet.cardinal (Alpine.Reduction.reduceReal alpI) = 5.
Proof. reflexivity. Qed.

Example alpine_root_dependees_computes :
  Alpine.Reduction.PackageFormulaSet.cardinal
    (Alpine.Reduction.dependees alpI Alpine.Reduction.rootPkg) = 1.
Proof. reflexivity. Qed.

Example alpine_installif_attaches :
  Alpine.InstallIfRuleRel.cardinal (Alpine.Reduction.installIfFibre alpI (1, 10)) = 1.
Proof. reflexivity. Qed.

Example alpine_versions_computes :
  Alpine.Reduction.PackageFormula.VSet.cardinal (Alpine.Reduction.versions alpI 4) = 1.
Proof. reflexivity. Qed.

Module NpmSemverMatch <: SemverMatch Nat_as_OT.
  Definition isPre (_ : nat) : bool := false.
  Definition sameCore (a b : nat) : bool := Nat.eqb a b.
End NpmSemverMatch.

Module Npm := Npm Nat_as_OT Nat_as_OT NpmSemverMatch.

Definition npmA : nat := 1.
Definition npmB : nat := 2.
Definition npmC : nat := 3.
Definition npmX : nat := 4.

Definition npmEq (v : nat) : Npm.Range := (Npm.COp OpEq v :: nil) :: nil.

Definition npmBetween (lo hi : nat) : Npm.Range :=
  (Npm.COp OpGe lo :: Npm.COp OpLt hi :: nil) :: nil.

Definition npmRepo : Npm.RealPackageSet.t :=
  fold_right Npm.RealPackageSet.add Npm.RealPackageSet.empty
    ((npmA, 1) :: (npmB, 1) :: (npmC, 1) :: (npmC, 2) :: (npmC, 3) :: nil).

Definition npmDepB : Npm.Dependency := Npm.MkDep npmB npmB (npmEq 1) false (Some 1).
Definition npmDepC : Npm.Dependency :=
  Npm.MkDep npmC npmC (npmBetween 2 4) false (Some 2).
Definition npmPeerC : Npm.PeerDependency :=
  Npm.MkPeer npmC (npmBetween 1 3) false true.
Definition npmPeerCOpt : Npm.PeerDependency :=
  Npm.MkPeer npmC (npmBetween 1 3) true true.

Definition kA : Npm.SourceName.t := (npmA, npmA).
Definition kB : Npm.SourceName.t := (npmB, npmB).
Definition kC : Npm.SourceName.t := (npmC, npmC).
Definition kX : Npm.SourceName.t := (npmX, npmC).

Definition npmShow (h : Npm.Reduced.Dependee.t)
  : Npm.Name.t * list Npm.Version.t :=
  (fst h, Npm.Reduced.VSet.elements (snd h)).

Definition npmDeps (I : Npm.Inst) (s : Npm.Reduced.Package.t) :=
  List.map npmShow
    (Npm.Reduced.DependeeSet.elements (Npm.Reduction.dependees I s)).

Definition npmInst : Npm.Inst :=
  Npm.MkInst npmRepo
    (((npmA, 1), npmDepB) :: ((npmA, 1), npmDepC) :: nil)
    (((npmB, 1), npmPeerC) :: nil) nil (npmA, 1).

Definition npmInstAuto : Npm.Inst :=
  Npm.MkInst npmRepo (((npmA, 1), npmDepB) :: nil)
    (((npmB, 1), npmPeerC) :: nil) nil (npmA, 1).

Definition npmInstRootPeer : Npm.Inst :=
  Npm.MkInst npmRepo (((npmA, 1), npmDepC) :: nil)
    (((npmA, 1), npmPeerC) :: nil) nil (npmA, 1).

Definition npmInstRootPeerOpt : Npm.Inst :=
  Npm.MkInst npmRepo (((npmA, 1), npmDepC) :: nil)
    (((npmA, 1), npmPeerCOpt) :: nil) nil (npmA, 1).

Definition npmInstRootPeerOptBare : Npm.Inst :=
  Npm.MkInst npmRepo (((npmA, 1), npmDepB) :: nil)
    (((npmA, 1), npmPeerCOpt) :: nil) nil (npmA, 1).

Definition npmInstOpt : Npm.Inst :=
  Npm.MkInst npmRepo (((npmA, 1), npmDepB) :: nil)
    (((npmB, 1), npmPeerCOpt) :: nil) nil (npmA, 1).

Definition npmDepAlias : Npm.Dependency :=
  Npm.MkDep npmX npmC (npmEq 1) false (Some 3).

Definition npmInstAlias : Npm.Inst :=
  Npm.MkInst npmRepo
    (((npmA, 1), npmDepC) :: ((npmA, 1), npmDepAlias) :: nil)
    nil nil (npmA, 1).

Definition npmInstOvr : Npm.Inst :=
  Npm.MkInst npmRepo (((npmA, 1), npmDepC) :: nil) nil
    ((npmC, npmEq 3) :: nil) (npmA, 1).

Example npm_versions_computes :
  Npm.Reduced.VSet.elements
    (Npm.Reduction.versions npmInst (Npm.Name.Granular kC 2))
  = Npm.Version.Orig 2 :: nil.
Proof. reflexivity. Qed.

Example npm_entry_edges_computes :
  npmDeps npmInst (Npm.Name.Granular kA 1, Npm.Version.Orig 1)
  = (Npm.Name.Intermediate kA 1 kB, Npm.Version.Orig 1 :: nil)
    :: (Npm.Name.Intermediate kA 1 kC,
        Npm.Version.Orig 2 :: Npm.Version.Orig 3 :: nil) :: nil.
Proof. reflexivity. Qed.

Example npm_slot_versions_computes :
  Npm.Reduced.VSet.elements
    (Npm.Reduction.versions npmInst (Npm.Name.Intermediate kA 1 kC))
  = Npm.Version.Orig 2 :: Npm.Version.Orig 3 :: nil.
Proof. reflexivity. Qed.

(* the directory reads B's descriptor too, which every directory with it
   shares *)
Example npm_peer_edge_computes :
  npmDeps npmInst (Npm.Name.Intermediate kA 1 kB, Npm.Version.Orig 1)
  = (Npm.Name.Granular kB 1, Npm.Version.Orig 1 :: nil)
    :: (Npm.Name.Link kA 1 kB 1 npmC,
        Npm.Version.Orig 1 :: Npm.Version.Orig 2 :: nil)
    :: (Npm.Name.Desc npmB npmB 1, Npm.Version.Orig 1 :: nil) :: nil.
Proof. reflexivity. Qed.

(* The root A has no directory for C, but installs one for B's peer, or
   leaves it empty (Bot) where no peer asks. *)
Example npm_auto_versions_computes :
  Npm.Reduced.VSet.elements
    (Npm.Reduction.versions npmInstAuto
       (Npm.Name.Intermediate kA 1 kC))
  = Npm.Version.Orig 1 :: Npm.Version.Orig 2 :: Npm.Version.Orig 3 :: Npm.Version.Bot :: nil.
Proof. reflexivity. Qed.

(* the same peer, one the root may not install (p_root false, as for a
   peer only Yarn Berry's packageExtensions add): the root's C is empty *)
Definition npmInstExt : Npm.Inst :=
  Npm.MkInst npmRepo (((npmA, 1), npmDepB) :: nil)
    (((npmB, 1), Npm.MkPeer npmC (npmBetween 1 3) false false) :: nil)
    nil (npmA, 1).

Example npm_ext_versions_computes :
  Npm.Reduced.VSet.elements
    (Npm.Reduction.versions npmInstExt (Npm.Name.Intermediate kA 1 kC))
  = Npm.Version.Bot :: nil.
Proof. reflexivity. Qed.

Example npm_auto_edge_computes :
  npmDeps npmInstAuto (Npm.Name.Intermediate kA 1 kB, Npm.Version.Orig 1)
  = (Npm.Name.Granular kB 1, Npm.Version.Orig 1 :: nil)
    :: (Npm.Name.Link kA 1 kB 1 npmC,
        Npm.Version.Orig 1 :: Npm.Version.Orig 2 :: nil)
    :: (Npm.Name.Desc npmB npmB 1, Npm.Version.Orig 1 :: nil) :: nil.
Proof. reflexivity. Qed.

Example npm_link_holder_computes :
  npmDeps npmInst (Npm.Name.Link kA 1 kB 1 npmC, Npm.Version.Orig 2)
  = (Npm.Name.Intermediate kA 1 kC, Npm.Version.Orig 2 :: nil)
    :: (Npm.Name.Sight kB 1 npmC, Npm.Version.Orig 2 :: Npm.Version.Free :: nil)
    :: nil.
Proof. reflexivity. Qed.

(* the same peer, optional: the root's C may be left empty, and the link
   at Bot reads it so *)
Example npm_optional_edge_computes :
  npmDeps npmInstOpt (Npm.Name.Intermediate kA 1 kB, Npm.Version.Orig 1)
  = (Npm.Name.Granular kB 1, Npm.Version.Orig 1 :: nil)
    :: (Npm.Name.Link kA 1 kB 1 npmC,
        Npm.Version.Orig 1 :: Npm.Version.Orig 2 :: Npm.Version.Bot :: nil)
    :: (Npm.Name.Desc npmB npmB 1, Npm.Version.Orig 1 :: nil) :: nil.
Proof. reflexivity. Qed.

Example npm_optional_bot_computes :
  npmDeps npmInstOpt (Npm.Name.Link kA 1 kB 1 npmC, Npm.Version.Bot)
  = (Npm.Name.Intermediate kA 1 kC, Npm.Version.Bot :: nil)
    :: (Npm.Name.Sight kB 1 npmC, Npm.Version.Bot :: Npm.Version.Free :: nil) :: nil.
Proof. reflexivity. Qed.

(* B@1 peers on C and depends on D@1, which peers on C too: B's copy holds
   no C (PEER LOCAL), and D's peer resolves to what B's own does. *)
Definition npmD : nat := 5.
Definition kD : Npm.SourceName.t := (npmD, npmD).

Definition npmChainRepo : Npm.RealPackageSet.t :=
  Npm.RealPackageSet.add (npmD, 1) npmRepo.

Definition npmInstChain : Npm.Inst :=
  Npm.MkInst npmChainRepo
    (((npmA, 1), npmDepB) :: ((npmB, 1), Npm.MkDep npmD npmD (npmEq 1) false (Some 4))
       :: nil)
    (((npmB, 1), npmPeerC) :: ((npmD, 1), npmPeerC) :: nil) nil (npmA, 1).

Example npm_peer_local_computes :
  Npm.Reduced.VSet.elements
    (Npm.Reduction.versions npmInstChain (Npm.Name.Intermediate kB 1 kC))
  = nil.
Proof. reflexivity. Qed.

Example npm_chain_computes :
  npmDeps npmInstChain (Npm.Name.Link kB 1 kD 1 npmC, Npm.Version.Orig 2)
  = (Npm.Name.Sight kB 1 npmC, Npm.Version.Orig 2 :: nil)
    :: (Npm.Name.Sight kD 1 npmC, Npm.Version.Orig 2 :: Npm.Version.Free :: nil)
    :: nil.
Proof. reflexivity. Qed.

(* B@1 depends on D@1, which peers on B: B offers itself. *)
Definition npmInstSelf : Npm.Inst :=
  Npm.MkInst npmChainRepo
    (((npmA, 1), npmDepB) :: ((npmB, 1), Npm.MkDep npmD npmD (npmEq 1) false (Some 4))
       :: nil)
    (((npmD, 1), Npm.MkPeer npmB (npmBetween 1 3) false true) :: nil) nil (npmA, 1).

Example npm_self_versions_computes :
  Npm.Reduced.VSet.elements
    (Npm.Reduction.versions npmInstSelf (Npm.Name.Link kB 1 kD 1 npmB))
  = Npm.Version.Orig 1 :: nil.
Proof. reflexivity. Qed.

Example npm_self_computes :
  npmDeps npmInstSelf (Npm.Name.Link kB 1 kD 1 npmB, Npm.Version.Orig 1)
  = (Npm.Name.Sight kD 1 npmB, Npm.Version.Orig 1 :: Npm.Version.Free :: nil) :: nil.
Proof. reflexivity. Qed.

(* B@1 depends on D@1, which peers on C: B, not the root, neither holds
   nor peers on C, so it offers D's peer nothing, and no copy of C is put
   into B for it. *)
Definition npmInstSkip : Npm.Inst :=
  Npm.MkInst npmChainRepo
    (((npmA, 1), npmDepB) :: ((npmB, 1), Npm.MkDep npmD npmD (npmEq 1) false (Some 4))
       :: nil)
    (((npmD, 1), npmPeerC) :: nil) nil (npmA, 1).

Example npm_skip_computes :
  Npm.Reduced.VSet.elements
    (Npm.Reduction.versions npmInstSkip (Npm.Name.Link kB 1 kD 1 npmC))
  = nil.
Proof. reflexivity. Qed.

Example npm_skip_versions_computes :
  Npm.Reduced.VSet.elements
    (Npm.Reduction.versions npmInstSkip (Npm.Name.Intermediate kB 1 kC))
  = nil.
Proof. reflexivity. Qed.

Example npm_root_peer_computes :
  npmDeps npmInstRootPeer (Npm.Name.Granular kA 1, Npm.Version.Orig 1)
  = (Npm.Name.Intermediate kA 1 kC, Npm.Version.Orig 1 :: Npm.Version.Orig 2 :: nil)
    :: (Npm.Name.Intermediate kA 1 kC,
        Npm.Version.Orig 2 :: Npm.Version.Orig 3 :: nil) :: nil.
Proof. reflexivity. Qed.

Example npm_root_peer_optional_computes :
  npmDeps npmInstRootPeerOpt (Npm.Name.Granular kA 1, Npm.Version.Orig 1)
  = npmDeps npmInstRootPeer (Npm.Name.Granular kA 1, Npm.Version.Orig 1).
Proof. reflexivity. Qed.

Example npm_root_peer_optional_bare_computes :
  npmDeps npmInstRootPeerOptBare (Npm.Name.Granular kA 1, Npm.Version.Orig 1)
  = (Npm.Name.Intermediate kA 1 kB, Npm.Version.Orig 1 :: nil) :: nil.
Proof. reflexivity. Qed.

Example npm_alias_computes :
  npmDeps npmInstAlias (Npm.Name.Granular kA 1, Npm.Version.Orig 1)
  = (Npm.Name.Intermediate kA 1 kC,
     Npm.Version.Orig 2 :: Npm.Version.Orig 3 :: nil)
    :: (Npm.Name.Intermediate kA 1 kX, Npm.Version.Orig 1 :: nil) :: nil.
Proof. reflexivity. Qed.

(* B@1 depends on C in [2,4) and peers on C in [1,3) (a peer with
   default): the root's link may offer C 2, both ranges' meet, or Bot, and
   B's directory holds nothing where it is offered one and its own copy
   where it is not. *)
Definition npmInstDp : Npm.Inst :=
  Npm.MkInst npmRepo
    (((npmA, 1), npmDepB) :: ((npmB, 1), npmDepC) :: nil)
    (((npmB, 1), npmPeerC) :: nil) nil (npmA, 1).

Example npm_dp_link_computes :
  Npm.Reduced.VSet.elements
    (Npm.Reduction.versions npmInstDp (Npm.Name.Link kA 1 kB 1 npmC))
  = Npm.Version.Orig 2 :: Npm.Version.Bot :: nil.
Proof. reflexivity. Qed.

Example npm_dp_offered_computes :
  npmDeps npmInstDp (Npm.Name.Link kA 1 kB 1 npmC, Npm.Version.Orig 2)
  = (Npm.Name.Intermediate kA 1 kC, Npm.Version.Orig 2 :: nil)
    :: (Npm.Name.Intermediate kB 1 kC, Npm.Version.Bot :: nil)
    :: (Npm.Name.Sight kB 1 npmC, Npm.Version.Orig 2 :: Npm.Version.Free :: nil)
    :: nil.
Proof. reflexivity. Qed.

Example npm_dp_own_computes :
  npmDeps npmInstDp (Npm.Name.Link kA 1 kB 1 npmC, Npm.Version.Bot)
  = (Npm.Name.Intermediate kA 1 kC, Npm.Version.Bot :: nil)
    :: (Npm.Name.Intermediate kB 1 kC,
        Npm.Version.Orig 2 :: Npm.Version.Orig 3 :: nil)
    :: (Npm.Name.Sight kB 1 npmC,
        Npm.Version.Orig 2 :: Npm.Version.Orig 3 :: Npm.Version.Free :: nil)
    :: nil.
Proof. reflexivity. Qed.

Example npm_override_computes :
  npmDeps npmInstOvr (Npm.Name.Granular kA 1, Npm.Version.Orig 1)
  = (Npm.Name.Intermediate kA 1 kC, Npm.Version.Orig 3 :: nil) :: nil.
Proof. reflexivity. Qed.

Definition npmInstOvrAlias (o : list (nat * Npm.Range)) : Npm.Inst :=
  Npm.MkInst (Npm.RealPackageSet.add (npmX, 1) npmRepo)
    (((npmA, 1), npmDepAlias) :: nil) nil o (npmA, 1).

Example npm_override_key_computes :
  npmDeps (npmInstOvrAlias ((npmX, npmEq 1) :: nil))
    (Npm.Name.Granular kA 1, Npm.Version.Orig 1)
  = (Npm.Name.Intermediate kA 1 (npmX, npmX), Npm.Version.Orig 1 :: nil) :: nil.
Proof. reflexivity. Qed.

Example npm_override_target_computes :
  npmDeps (npmInstOvrAlias ((npmC, npmEq 3) :: nil))
    (Npm.Name.Granular kA 1, Npm.Version.Orig 1)
  = (Npm.Name.Intermediate kA 1 kX, Npm.Version.Orig 1 :: nil) :: nil.
Proof. reflexivity. Qed.

Module NpmPrereleaseSemverMatch <: SemverMatch Nat_as_OT.
  Definition isPre (v : nat) : bool := Nat.odd v.
  Definition sameCore (a b : nat) : bool :=
    Nat.eqb (Nat.div a 2) (Nat.div b 2).
End NpmPrereleaseSemverMatch.

Module NpmPrerelease := PackageCalculus.Npm.Npm Nat_as_OT Nat_as_OT NpmPrereleaseSemverMatch.

Definition npmPreRepo : NpmPrerelease.RealPackageSet.t :=
  fold_right NpmPrerelease.RealPackageSet.add NpmPrerelease.RealPackageSet.empty
    ((npmC, 4) :: (npmC, 5) :: (npmC, 6) :: (npmC, 7) :: nil).

Example npm_prerelease_excluded :
  NpmPrerelease.VSet.elements
    (NpmPrerelease.rangeEval ((NpmPrerelease.COp OpGe 4 :: NpmPrerelease.COp OpLt 8 :: nil) :: nil)
       (NpmPrerelease.realVersions npmPreRepo npmC)) = 4 :: 6 :: nil.
Proof. reflexivity. Qed.

Example npm_prerelease_admitted :
  NpmPrerelease.VSet.elements
    (NpmPrerelease.rangeEval ((NpmPrerelease.COp OpGe 5 :: NpmPrerelease.COp OpLt 8 :: nil) :: nil)
       (NpmPrerelease.realVersions npmPreRepo npmC)) = 5 :: 6 :: nil.
Proof. reflexivity. Qed.

Module NpmPlacement := NpmPlacement Nat_as_OT Nat_as_OT NpmSemverMatch.

(* The project depends on key 4 aliasing package 2 and on 3 optionally;
   no version of 3 is in range, so that edge may find nothing. *)
Definition nplInst : NpmPlacement.Inst :=
  NpmPlacement.MkInst
    (fold_right NpmPlacement.RealPackageSet.add NpmPlacement.RealPackageSet.empty
       ((npmB, 1) :: (npmC, 1) :: nil))
    nil nil nil npmA
    (NpmPlacement.MkDep npmX npmB ((NpmPlacement.COp OpEq 1 :: nil) :: nil) false false
     :: NpmPlacement.MkDep npmC npmC ((NpmPlacement.COp OpEq 2 :: nil) :: nil) false true
     :: nil)
    nil.

Example npl_edges :
  List.map (fun e => (NpmPlacement.e_dir e, NpmPlacement.e_name e, NpmPlacement.e_optional e))
    (NpmPlacement.edgesOf nplInst NpmPlacement.Occupant.Proj) =
  (npmX, npmB, false) :: (npmC, npmC, true) :: nil.
Proof. reflexivity. Qed.

Example npl_key :
  NpmPlacement.Placement.VSet.elements
    (NpmPlacement.Placement.Source.versions (NpmPlacement.Reduction.placeRepo nplInst) npmX) =
  NpmPlacement.Occupant.Reg npmB 1 :: nil.
Proof. reflexivity. Qed.

Definition nplInstOvr (o : list (nat * NpmPlacement.Range)) : NpmPlacement.Inst :=
  NpmPlacement.MkInst
    (fold_right NpmPlacement.RealPackageSet.add NpmPlacement.RealPackageSet.empty
       ((npmB, 1) :: (npmB, 2) :: (npmX, 1) :: nil))
    nil nil o npmA
    (NpmPlacement.MkDep npmX npmB ((NpmPlacement.COp OpEq 2 :: nil) :: nil) false false :: nil)
    nil.

Definition nplAccepts (I : NpmPlacement.Inst) : list (list NpmPlacement.Occupant.t) :=
  List.map (fun e => NpmPlacement.Placement.VSet.elements (NpmPlacement.Reduction.accepts I e))
    (NpmPlacement.edgesOf I NpmPlacement.Occupant.Proj).

Example npl_override_key :
  nplAccepts (nplInstOvr ((npmX, (NpmPlacement.COp OpEq 1 :: nil) :: nil) :: nil)) =
  (NpmPlacement.Occupant.Reg npmX 1 :: nil) :: nil.
Proof. reflexivity. Qed.

Example npl_override_target :
  nplAccepts (nplInstOvr ((npmB, (NpmPlacement.COp OpEq 1 :: nil) :: nil) :: nil)) =
  (NpmPlacement.Occupant.Reg npmB 2 :: nil) :: nil.
Proof. reflexivity. Qed.
