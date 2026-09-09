From Stdlib Require Import MSets Bool.
From PackageCalculus Require Import Prelude Core Versions Semver Feature
  FeatureConcurrent.

Create HintDb cmp_cargo.
Create Rewrite HintDb cmp_cargo.

(* Cargo: crates resolve with at most one version per semver-compatibility
   class (the granularity g), feature unification per crate version,
   optional dependencies activated by features, weak (dep?/feat) feature
   edges, and native-library mutual exclusion via the links key.  The
   calculus is a source record over honest manifest data plus a verified
   translation into a FeatureConcurrent instance; composing with that
   functor's proved reduction reaches Core.  Caret/tilde/wildcard
   requirements, implicit features of optional dependencies, and the
   dep: suppression rule are frontend desugarings into the carried
   range/feature-table data. *)
Module Cargo (N V L F G CfgS Src : UsualOrderedType) (PM : SemverMatch V).
  Module C := Core N V.
  Module Pkg := C.Pkg.
  Module PkgSet := C.PkgSet.
  Module VSet := C.VSet.

  (* cargo requirements are the shared semver language: a comma-separated
     conjunction is one comparator set, and the prerelease rule the
     semver crate applies over a whole VersionReq is that set's csAdmits.
     Included under their own names rather than qualified. *)
  Module Sv := Semver V VSet PM.
  Include Sv.

  Module FSet := FSetUOT F.
  Module Featured := PairUOT Pkg FSet.AsUOT.
  Module FeaturedSet := FSetUOT Featured.
  Module PkgF := PairUOT Pkg F.
  Module SupportSet := FSetUOT PkgF.

  Module NFPair := PairUOT N F.
  Module NFF := UOTCompareFacts NFPair.
  Module NF := UOTCompareFacts N.
  Module FF := UOTCompareFacts F.
  #[local] Hint Rewrite NFF.compare_eq_iff NF.compare_eq_iff
    FF.compare_eq_iff : cmp_cargo.
  #[local] Hint Extern 1 => cmp_by NFF.compare_antisym : cmp_cargo.
  #[local] Hint Extern 1 => cmp_by NF.compare_antisym : cmp_cargo.
  #[local] Hint Extern 1 => cmp_by FF.compare_antisym : cmp_cargo.
  #[local] Hint Extern 1 => cmp_by NFF.compare_lt_trans : cmp_cargo.
  #[local] Hint Extern 1 => cmp_by NF.compare_lt_trans : cmp_cargo.
  #[local] Hint Extern 1 => cmp_by FF.compare_lt_trans : cmp_cargo.

  (* One entry of a crate feature's enable list: another feature of the
     same crate, activation of an optional dependency slot (dep:a), a
     strong dependency feature (a/feat), or a weak one (a?/feat). *)
  Module FEntry.
    Inductive fentry : Type :=
    | EFeat (f : F.t)
    | EDep (a : N.t)
    | EDepFeat (a : N.t) (feat : F.t)
    | EWeakFeat (a : N.t) (feat : F.t).
    Definition t := fentry.

    Definition rank (e : t) : nat :=
      match e with
      | EFeat _ => 0 | EDep _ => 1 | EDepFeat _ _ => 2 | EWeakFeat _ _ => 3
      end.

    Definition compare (x y : t) : comparison :=
      match Nat.compare (rank x) (rank y) with
      | Eq =>
          match x, y with
          | EFeat f1, EFeat f2 => F.compare f1 f2
          | EDep a1, EDep a2 => N.compare a1 a2
          | EDepFeat a1 f1, EDepFeat a2 f2 =>
              NFPair.compare (a1, f1) (a2, f2)
          | EWeakFeat a1 f1, EWeakFeat a2 f2 =>
              NFPair.compare (a1, f1) (a2, f2)
          | _, _ => Eq
          end
      | c => c
      end.

    Lemma compare_eq_iff : forall x y, compare x y = Eq <-> x = y.
    Proof. cmp_eq_iff cmp_cargo. Qed.

    Lemma compare_antisym : forall x y, compare y x = CompOpp (compare x y).
    Proof. cmp_antisym cmp_cargo. Qed.

    Lemma compare_lt_trans : forall x y z,
        compare x y = Lt -> compare y z = Lt -> compare x z = Lt.
    Proof. cmp_lt_trans cmp_cargo. Qed.
  End FEntry.
  Module FEntryOT := UOTFromCompare FEntry.

  Module FDefElt := PairUOT PkgF FEntryOT.
  Module FDefRel := FSetUOT FDefElt.

  (* Dependency kinds; dev dependencies participate only at the root. *)
  Module Kind.
    Inductive kind : Type := KNormal | KBuild | KDev.
    Definition t := kind.

    Definition rank (k : t) : nat :=
      match k with KNormal => 0 | KBuild => 1 | KDev => 2 end.

    Definition compare (x y : t) : comparison :=
      Nat.compare (rank x) (rank y).

    Lemma compare_eq_iff : forall x y, compare x y = Eq <-> x = y.
    Proof. cmp_eq_iff cmp_cargo. Qed.

    Lemma compare_antisym : forall x y, compare y x = CompOpp (compare x y).
    Proof. cmp_antisym cmp_cargo. Qed.

    Lemma compare_lt_trans : forall x y z,
        compare x y = Lt -> compare y z = Lt -> compare x z = Lt.
    Proof. cmp_lt_trans cmp_cargo. Qed.
  End Kind.
  Module KindOT := UOTFromCompare Kind.

  (* A dependency slot: manifest alias (the identity dep:/a/feat entries
     reference, and the rename key), real target crate, requirement
     formula, kind, optionality, default-features opt-out, requested
     features, and carried cfg predicate and source identity. *)
  Module SDCfg := PairUOT CfgS Src.
  Module SDReq := PairUOT FSet.AsUOT SDCfg.
  Module SDDflt := PairUOT BoolOT SDReq.
  Module SDOpt := PairUOT BoolOT SDDflt.
  Module SDKind := PairUOT KindOT SDOpt.
  Module SDForm := PairUOT RangeOT SDKind.
  Module SDTgt := PairUOT N SDForm.
  Module SlotData := PairUOT N SDTgt.
  Module SlotElt := PairUOT Pkg SlotData.
  Module SlotRel := FSetUOT SlotElt.

  Definition sAlias (d : SlotData.t) : N.t := fst d.
  Definition sTarget (d : SlotData.t) : N.t := fst (snd d).
  Definition sReq (d : SlotData.t) : Range := fst (snd (snd d)).
  Definition sKind (d : SlotData.t) : Kind.t := fst (snd (snd (snd d))).
  Definition sOptional (d : SlotData.t) : bool :=
    fst (snd (snd (snd (snd d)))).
  Definition sDefault (d : SlotData.t) : bool :=
    fst (snd (snd (snd (snd (snd d))))).
  Definition sReqFeats (d : SlotData.t) : FSet.t :=
    fst (snd (snd (snd (snd (snd (snd d)))))).
  Definition sCfg (d : SlotData.t) : CfgS.t :=
    fst (snd (snd (snd (snd (snd (snd (snd d))))))).
  Definition sSrc (d : SlotData.t) : Src.t :=
    snd (snd (snd (snd (snd (snd (snd (snd d))))))).

  Module LinkElt := PairUOT Pkg L.
  Module LinkRel := FSetUOT LinkElt.

  Module NAPair := PairUOT Pkg N.
  Module SelElt := PairUOT NAPair V.
  Module SelRel := FSetUOT SelElt.

  (* Whether a slot participates in resolution: cfg-active, and dev
     dependencies only from the root crate.  Build dependencies resolve
     in the shared graph (the resolver-v1 reading; the v2 build/normal
     feature split is carried by sKind but not separated here). *)
  Definition slotActive (cfgActive : CfgS.t -> bool) (rc p : Pkg.t)
      (d : SlotData.t) : bool :=
    andb (cfgActive (sCfg d))
      (match sKind d with
       | Kind.KDev => if Pkg.eq_dec p rc then true else false
       | _ => true
       end).

  (* An optional slot is activated when some enabled feature of its
     owner lists it via dep:a or a strong a/feat entry; a?/feat entries
     never activate. *)
  Definition Activated (FDefs : FDefRel.t) (fs : FSet.t) (p : Pkg.t)
      (a : N.t) : Prop :=
    exists f, FSet.In f fs /\
      (FDefRel.In ((p, f), FEntry.EDep a) FDefs \/
       exists feat, FDefRel.In ((p, f), FEntry.EDepFeat a feat) FDefs).

  Definition slotRequests (d : SlotData.t) (dflt : F.t) : FSet.t :=
    if sDefault d then FSet.add dflt (sReqFeats d) else sReqFeats d.

  (* The record quantifies feature sets through FeaturedSet membership;
     fs_functional makes the projection well defined. *)
  Record IsResolution
      (R : PkgSet.t) (support : SupportSet.t) (FDefs : FDefRel.t)
      (Slots : SlotRel.t) (Links : LinkRel.t)
      (g : V.t -> G.t) (cfgActive : CfgS.t -> bool) (dflt : F.t)
      (rc : Pkg.t) (rootFeats : FSet.t)
      (S : PkgSet.t) (FS : FeaturedSet.t) (sel : SelRel.t) : Prop :=
    { res_subset : PkgSet.Subset S R
    ; res_root_mem : PkgSet.In rc S
    ; res_root_feats :
        forall fs, FeaturedSet.In (rc, fs) FS -> FSet.Subset rootFeats fs
    ; res_fs_dom : forall p fs, FeaturedSet.In (p, fs) FS -> PkgSet.In p S
    ; res_fs_total : forall p, PkgSet.In p S ->
        exists fs, FeaturedSet.In (p, fs) FS
    ; res_fs_functional :
        forall p fs fs', FeaturedSet.In (p, fs) FS ->
        FeaturedSet.In (p, fs') FS -> fs = fs'
    ; res_class_unique :
        forall n v v', PkgSet.In (n, v) S -> PkgSet.In (n, v') S ->
        v <> v' -> g v <> g v'
    ; res_support_mem :
        forall p fs f, FeaturedSet.In (p, fs) FS -> FSet.In f fs ->
        SupportSet.In (p, f) support
    ; res_sel_functional :
        forall p a u u', SelRel.In ((p, a), u) sel ->
        SelRel.In ((p, a), u') sel -> u = u'
    ; res_slot_closure :
        forall p fs, PkgSet.In p S -> FeaturedSet.In (p, fs) FS ->
        forall d, SlotRel.In (p, d) Slots ->
        slotActive cfgActive rc p d = true ->
        (sOptional d = false \/ Activated FDefs fs p (sAlias d)) ->
        exists u, SelRel.In ((p, sAlias d), u) sel /\
          rgHolds (sReq d) u = true /\ PkgSet.In (sTarget d, u) S /\
          forall fs', FeaturedSet.In ((sTarget d, u), fs') FS ->
          FSet.Subset (slotRequests d dflt) fs'
    ; res_feat_closure_same :
        forall p fs f f', FeaturedSet.In (p, fs) FS -> FSet.In f fs ->
        FDefRel.In ((p, f), FEntry.EFeat f') FDefs -> FSet.In f' fs
    ; res_feat_closure_dep :
        forall p fs f a feat, FeaturedSet.In (p, fs) FS -> FSet.In f fs ->
        (FDefRel.In ((p, f), FEntry.EDepFeat a feat) FDefs \/
         (FDefRel.In ((p, f), FEntry.EWeakFeat a feat) FDefs /\
          Activated FDefs fs p a)) ->
        forall d u, SlotRel.In (p, d) Slots -> sAlias d = a ->
        SelRel.In ((p, a), u) sel ->
        forall fs', FeaturedSet.In ((sTarget d, u), fs') FS ->
        FSet.In feat fs'
    ; res_links_unique :
        forall p q l, PkgSet.In p S -> PkgSet.In q S ->
        LinkRel.In (p, l) Links -> LinkRel.In (q, l) Links -> p = q }.

  Module LF := UOTCompareFacts L.
  Module GF := UOTCompareFacts G.
  Module VF := UOTCompareFacts V.
  Module PkgFct := UOTCompareFacts Pkg.
  Module SlotName := TripleUOT N V N.
  Module SlotNameF := UOTCompareFacts SlotName.
  Module FDTail := TripleUOT F N F.
  Module DecName := TripleUOT N V FDTail.
  Module DecNameF := UOTCompareFacts DecName.
  #[local] Hint Rewrite LF.compare_eq_iff GF.compare_eq_iff
    VF.compare_eq_iff PkgFct.compare_eq_iff SlotNameF.compare_eq_iff
    DecNameF.compare_eq_iff : cmp_cargo.
  #[local] Hint Extern 1 => cmp_by LF.compare_antisym : cmp_cargo.
  #[local] Hint Extern 1 => cmp_by GF.compare_antisym : cmp_cargo.
  #[local] Hint Extern 1 => cmp_by VF.compare_antisym : cmp_cargo.
  #[local] Hint Extern 1 => cmp_by PkgFct.compare_antisym : cmp_cargo.
  #[local] Hint Extern 1 => cmp_by SlotNameF.compare_antisym : cmp_cargo.
  #[local] Hint Extern 1 => cmp_by DecNameF.compare_antisym : cmp_cargo.
  #[local] Hint Extern 1 => cmp_by LF.compare_lt_trans : cmp_cargo.
  #[local] Hint Extern 1 => cmp_by GF.compare_lt_trans : cmp_cargo.
  #[local] Hint Extern 1 => cmp_by VF.compare_lt_trans : cmp_cargo.
  #[local] Hint Extern 1 => cmp_by PkgFct.compare_lt_trans : cmp_cargo.
  #[local] Hint Extern 1 => cmp_by SlotNameF.compare_lt_trans : cmp_cargo.
  #[local] Hint Extern 1 => cmp_by DecNameF.compare_lt_trans : cmp_cargo.

  (* Encoded names: Root is the synthetic root (Cargo's root crate has
     features, which res_no_root_support forbids of the FC root); Slot is
     the per-dependency-edge choice node, whose single granule makes each
     edge resolve to one version even across compatibility classes and
     under renames; DecisionN delivers a/feat and a?/feat entries, firing
     only when its FWit feature is enabled by the entry's owner. *)
  Module NPlus.
    Inductive name : Type :=
    | Root
    | Crate (n : N.t)
    | LinkN (l : L.t)
    | SlotN (n : N.t) (v : V.t) (a : N.t)
    | DecisionN (n : N.t) (v : V.t) (f : F.t) (a : N.t) (feat : F.t).
    Definition t := name.

    Definition rank (x : t) : nat :=
      match x with
      | Root => 0 | Crate _ => 1 | LinkN _ => 2
      | SlotN _ _ _ => 3 | DecisionN _ _ _ _ _ => 4
      end.

    Definition compare (x y : t) : comparison :=
      match Nat.compare (rank x) (rank y) with
      | Eq =>
          match x, y with
          | Crate n1, Crate n2 => N.compare n1 n2
          | LinkN l1, LinkN l2 => L.compare l1 l2
          | SlotN n1 v1 a1, SlotN n2 v2 a2 =>
              SlotName.compare (n1, (v1, a1)) (n2, (v2, a2))
          | DecisionN n1 v1 f1 a1 t1, DecisionN n2 v2 f2 a2 t2 =>
              DecName.compare (n1, (v1, (f1, (a1, t1))))
                (n2, (v2, (f2, (a2, t2))))
          | _, _ => Eq
          end
      | c => c
      end.

    Lemma compare_eq_iff : forall x y, compare x y = Eq <-> x = y.
    Proof. cmp_eq_iff cmp_cargo. Qed.

    Lemma compare_antisym : forall x y, compare y x = CompOpp (compare x y).
    Proof. cmp_antisym cmp_cargo. Qed.

    Lemma compare_lt_trans : forall x y z,
        compare x y = Lt -> compare y z = Lt -> compare x z = Lt.
    Proof. cmp_lt_trans cmp_cargo. Qed.
  End NPlus.
  Module NPOT := UOTFromCompare NPlus.

  Module VPlus.
    Inductive version : Type :=
    | VOrig (v : V.t)
    | VChoice (v : V.t)
    | VFire (v : V.t)
    | VOff
    | VMember (p : Pkg.t)
    | VUnit.
    Definition t := version.

    Definition rank (x : t) : nat :=
      match x with
      | VOrig _ => 0 | VChoice _ => 1 | VFire _ => 2
      | VOff => 3 | VMember _ => 4 | VUnit => 5
      end.

    Definition compare (x y : t) : comparison :=
      match Nat.compare (rank x) (rank y) with
      | Eq =>
          match x, y with
          | VOrig v1, VOrig v2 => V.compare v1 v2
          | VChoice v1, VChoice v2 => V.compare v1 v2
          | VFire v1, VFire v2 => V.compare v1 v2
          | VMember p1, VMember p2 => Pkg.compare p1 p2
          | _, _ => Eq
          end
      | c => c
      end.

    Lemma compare_eq_iff : forall x y, compare x y = Eq <-> x = y.
    Proof. cmp_eq_iff cmp_cargo. Qed.

    Lemma compare_antisym : forall x y, compare y x = CompOpp (compare x y).
    Proof. cmp_antisym cmp_cargo. Qed.

    Lemma compare_lt_trans : forall x y z,
        compare x y = Lt -> compare y z = Lt -> compare x z = Lt.
    Proof. cmp_lt_trans cmp_cargo. Qed.
  End VPlus.
  Module VPOT := UOTFromCompare VPlus.

  Module GPlus.
    Inductive granule : Type :=
    | GOrig (w : G.t)
    | GChoice
    | GDecide
    | GLink
    | GUnit.
    Definition t := granule.

    Definition rank (x : t) : nat :=
      match x with
      | GOrig _ => 0 | GChoice => 1 | GDecide => 2 | GLink => 3 | GUnit => 4
      end.

    Definition compare (x y : t) : comparison :=
      match Nat.compare (rank x) (rank y) with
      | Eq =>
          match x, y with
          | GOrig w1, GOrig w2 => G.compare w1 w2
          | _, _ => Eq
          end
      | c => c
      end.

    Lemma compare_eq_iff : forall x y, compare x y = Eq <-> x = y.
    Proof. cmp_eq_iff cmp_cargo. Qed.

    Lemma compare_antisym : forall x y, compare y x = CompOpp (compare x y).
    Proof. cmp_antisym cmp_cargo. Qed.

    Lemma compare_lt_trans : forall x y z,
        compare x y = Lt -> compare y z = Lt -> compare x z = Lt.
    Proof. cmp_lt_trans cmp_cargo. Qed.
  End GPlus.
  Module GPOT := UOTFromCompare GPlus.

  Module FPlusComp <: ComparableType.
    Inductive fplus : Type :=
    | FOrigF (f : F.t)
    | FWit.
    Definition t := fplus.

    Definition compare (x y : t) : comparison :=
      match x, y with
      | FOrigF f1, FOrigF f2 => F.compare f1 f2
      | FOrigF _, FWit => Lt
      | FWit, FOrigF _ => Gt
      | FWit, FWit => Eq
      end.

    Lemma compare_eq_iff : forall x y, compare x y = Eq <-> x = y.
    Proof. cmp_eq_iff cmp_cargo. Qed.

    Lemma compare_antisym : forall x y, compare y x = CompOpp (compare x y).
    Proof. cmp_antisym cmp_cargo. Qed.

    Lemma compare_lt_trans : forall x y z,
        compare x y = Lt -> compare y z = Lt -> compare x z = Lt.
    Proof. cmp_lt_trans cmp_cargo. Qed.
  End FPlusComp.
  Module FPlus := UOTFromCompare FPlusComp.

  Module FC := FeatureConcurrent NPOT VPOT FPlus GPOT.

  Definition gPlus (g : V.t -> G.t) (x : VPlus.t) : GPlus.t :=
    match x with
    | VPlus.VOrig v => GPlus.GOrig (g v)
    | VPlus.VChoice _ => GPlus.GChoice
    | VPlus.VFire _ => GPlus.GDecide
    | VPlus.VOff => GPlus.GDecide
    | VPlus.VMember _ => GPlus.GLink
    | VPlus.VUnit => GPlus.GUnit
    end.

  Module NEqb := UOTEqb N.
  Module LEqb := UOTEqb L.
  Module PkgEqb := UOTEqb Pkg.

  Module SOpv := SetOps Pkg V PkgSet VSet.
  Definition evalReq (R : PkgSet.t) (m : N.t) (rg : Range) : VSet.t :=
    SOpv.filterMap (fun '(n, u) =>
        if NEqb.eqb n m then if rgHolds rg u then Some u else None
        else None)
      R.

  Lemma mem_evalReq : forall R m rg u,
      VSet.In u (evalReq R m rg) <->
      PkgSet.In (m, u) R /\ rgHolds rg u = true.
  Proof.
    intros R m rg u; unfold evalReq; rewrite SOpv.mem_filterMap.
    split.
    - intros [[n w] [HR He]]; cbn beta iota in He.
      destruct (NEqb.eqb n m) eqn:En; [| discriminate].
      apply NEqb.eqb_true_iff in En; subst n.
      destruct (rgHolds rg w) eqn:Ev; [| discriminate].
      injection He as ->; split; assumption.
    - intros [HR Hv]; exists (m, u); split; [exact HR | cbn beta iota].
      rewrite NEqb.eqb_refl, Hv; reflexivity.
  Qed.

  (* The versions of a crate name in the repository; encoders consult R
     only through an oracle Vq of this shape, so slice reuse below is
     oracle agreement (the lookup lemmas).  This is not evalReq at some
     top range: no range admits a prerelease it does not name, so none
     denotes the whole repository. *)
  Definition srcVersions (R : PkgSet.t) (n : N.t) : VSet.t :=
    SOpv.filterMap (fun '(m, u) => if NEqb.eqb m n then Some u else None) R.

  Lemma mem_srcVersions : forall R n v,
      VSet.In v (srcVersions R n) <-> PkgSet.In (n, v) R.
  Proof.
    intros R n v; unfold srcVersions; rewrite SOpv.mem_filterMap.
    split.
    - intros [[m w] [HR He]]; cbn beta iota in He.
      destruct (NEqb.eqb m n) eqn:En; [| discriminate].
      apply NEqb.eqb_true_iff in En; subst m.
      injection He as ->; exact HR.
    - intro HR; exists (n, v); split; [exact HR | cbn beta iota].
      rewrite NEqb.eqb_refl; reflexivity.
  Qed.

  Definition transRoot : FC.Pkg.t := (NPlus.Root, VPlus.VUnit).

  Module SOff := SetOps F FPlus FSet FC.Feat.FSet.
  Definition embedFS (fs : FSet.t) : FC.Feat.FSet.t :=
    SOff.map FPlusComp.FOrigF fs.

  Lemma mem_embedFS : forall fs x,
      FC.Feat.FSet.In x (embedFS fs) <->
      exists f, FSet.In f fs /\ x = FPlusComp.FOrigF f.
  Proof.
    intros fs x; unfold embedFS; rewrite SOff.mem_map; reflexivity.
  Qed.

  Lemma embedFS_mono : forall A B,
      FSet.Subset A B -> FC.Feat.FSet.Subset (embedFS A) (embedFS B).
  Proof.
    intros A B H; unfold embedFS; apply SOff.map_mono;
      [exact H | intro; reflexivity].
  Qed.

  Module SOvv := SetOps V VPOT VSet FC.VSet.
  Definition choicesOf (R : PkgSet.t) (d : SlotData.t) : FC.VSet.t :=
    SOvv.map VPlus.VChoice (evalReq R (sTarget d) (sReq d)).

  Definition firesOf (R : PkgSet.t) (d : SlotData.t) : FC.VSet.t :=
    SOvv.map VPlus.VFire (evalReq R (sTarget d) (sReq d)).

  (* Slots of p under alias a that participate in resolution. *)
  Definition slotsAt (Slots : SlotRel.t) (cfgActive : CfgS.t -> bool)
      (rc : Pkg.t) (p : Pkg.t) (a : N.t) : SlotRel.t :=
    SlotRel.filter (fun '(q, d) =>
        andb (if Pkg.eq_dec q p then true else false)
          (andb (NEqb.eqb (sAlias d) a) (slotActive cfgActive rc q d)))
      Slots.

  Lemma mem_slotsAt : forall Slots cfgActive rc p a q d,
      SlotRel.In (q, d) (slotsAt Slots cfgActive rc p a) <->
      SlotRel.In (q, d) Slots /\ q = p /\ sAlias d = a /\
      slotActive cfgActive rc q d = true.
  Proof.
    intros Slots cfgActive rc p a q d; unfold slotsAt.
    rewrite SlotRel.filter_spec'.
    split.
    - intros [Hin Hb].
      apply andb_true_iff in Hb; destruct Hb as [Hq Hb].
      destruct (Pkg.eq_dec q p) as [-> | NE]; [| discriminate].
      apply andb_true_iff in Hb; destruct Hb as [Ha Hact].
      apply NEqb.eqb_true_iff in Ha.
      repeat split; assumption.
    - intros [Hin [-> [Ha Hact]]]; split; [exact Hin |].
      destruct (Pkg.eq_dec p p) as [_ | NE];
        [| contradiction NE; reflexivity].
      subst a; rewrite NEqb.eqb_refl, Hact; reflexivity.
  Qed.

  (* Feature-table entries that create a decision gadget, with the feat they
     deliver; weak entries never activate, strong ones do. *)
  Definition entryFeatD (e : FEntry.t) : option (N.t * F.t) :=
    match e with
    | FEntry.EDepFeat a feat => Some (a, feat)
    | FEntry.EWeakFeat a feat => Some (a, feat)
    | _ => None
    end.

  Definition entryActivates (e : FEntry.t) : option N.t :=
    match e with
    | FEntry.EDep a => Some a
    | FEntry.EDepFeat a _ => Some a
    | _ => None
    end.

  Module SOsp := SetOps SlotElt FC.Pkg SlotRel FC.PkgSet.
  Module SOvp := SetOps V FC.Pkg VSet FC.PkgSet.
  Module SOfp := SetOps FDefElt FC.Pkg FDefRel FC.PkgSet.
  Module SOpp := SetOps Pkg FC.Pkg PkgSet FC.PkgSet.
  Module SOlp := SetOps LinkElt FC.Pkg LinkRel FC.PkgSet.

  Definition realBlock (R : PkgSet.t) : FC.PkgSet.t :=
    SOpp.map (fun '(n, v) => (NPlus.Crate n, VPlus.VOrig v)) R.

  Definition slotBlock (R : PkgSet.t) (Slots : SlotRel.t)
      (cfgActive : CfgS.t -> bool) (rc : Pkg.t) : FC.PkgSet.t :=
    SOsp.unionMap (fun '((n, v), d) =>
        if slotActive cfgActive rc (n, v) d
        then SOvp.map (fun u => (NPlus.SlotN n v (sAlias d), VPlus.VChoice u))
               (evalReq R (sTarget d) (sReq d))
        else FC.PkgSet.empty)
      Slots.

  Definition featdBlock (R : PkgSet.t) (FDefs : FDefRel.t)
      (Slots : SlotRel.t) (cfgActive : CfgS.t -> bool)
      (rc : Pkg.t) : FC.PkgSet.t :=
    SOfp.unionMap (fun '(((n, v), f), e) =>
        match entryFeatD e with
        | Some (a, feat) =>
            SOsp.unionMap (fun '(_, d) =>
                FC.PkgSet.add
                  (NPlus.DecisionN n v f a feat, VPlus.VOff)
                  (SOvp.map
                     (fun u => (NPlus.DecisionN n v f a feat, VPlus.VFire u))
                     (evalReq R (sTarget d) (sReq d))))
              (slotsAt Slots cfgActive rc (n, v) a)
        | None => FC.PkgSet.empty
        end)
      FDefs.

  Definition linkBlock (R : PkgSet.t) (Links : LinkRel.t) : FC.PkgSet.t :=
    SOlp.filterMap (fun '(p, l) =>
        if PkgSet.mem p R
        then Some (NPlus.LinkN l, VPlus.VMember p)
        else None)
      Links.

  (* -- lookup-primary layer: the per-name and per-crate queries are the
     definitions; the global translation is their aggregation, defined
     after them. -- *)

  Definition ownSlots (Slots : SlotRel.t) (p : Pkg.t) : SlotRel.t :=
    SlotRel.filter (fun '(q, _) => PkgEqb.eqb q p) Slots.

  Lemma mem_ownSlots : forall Slots p q d,
      SlotRel.In (q, d) (ownSlots Slots p) <->
      SlotRel.In (q, d) Slots /\ q = p.
  Proof.
    intros Slots p q d; unfold ownSlots; rewrite SlotRel.filter_spec'.
    rewrite PkgEqb.eqb_true_iff; tauto.
  Qed.

  Definition ownFDefs (FDefs : FDefRel.t) (p : Pkg.t) : FDefRel.t :=
    FDefRel.filter (fun '((q, _), _) => PkgEqb.eqb q p) FDefs.

  Lemma mem_ownFDefs : forall FDefs p q f e,
      FDefRel.In ((q, f), e) (ownFDefs FDefs p) <->
      FDefRel.In ((q, f), e) FDefs /\ q = p.
  Proof.
    intros FDefs p q f e; unfold ownFDefs; rewrite FDefRel.filter_spec'.
    rewrite PkgEqb.eqb_true_iff; tauto.
  Qed.

  Definition ownLinks (Links : LinkRel.t) (p : Pkg.t) : LinkRel.t :=
    LinkRel.filter (fun '(q, _) => PkgEqb.eqb q p) Links.

  Lemma mem_ownLinks : forall Links p q l,
      LinkRel.In (q, l) (ownLinks Links p) <->
      LinkRel.In (q, l) Links /\ q = p.
  Proof.
    intros Links p q l; unfold ownLinks; rewrite LinkRel.filter_spec'.
    rewrite PkgEqb.eqb_true_iff; tauto.
  Qed.

  Definition ownSupport (support : SupportSet.t) (p : Pkg.t)
    : SupportSet.t :=
    SupportSet.filter (fun '(q, _) => PkgEqb.eqb q p) support.

  Lemma mem_ownSupport : forall support p q f,
      SupportSet.In (q, f) (ownSupport support p) <->
      SupportSet.In (q, f) support /\ q = p.
  Proof.
    intros support p q f; unfold ownSupport.
    rewrite SupportSet.filter_spec', PkgEqb.eqb_true_iff; tauto.
  Qed.

  Module SOso := SetOps SlotElt Pkg SlotRel PkgSet.
  Definition slotOwners (Slots : SlotRel.t) : PkgSet.t :=
    SOso.map fst Slots.

  Module SOfo := SetOps FDefElt Pkg FDefRel PkgSet.
  Definition fdefOwners (FDefs : FDefRel.t) : PkgSet.t :=
    SOfo.map (fun r => fst (fst r)) FDefs.

  Module SOlo := SetOps LinkElt Pkg LinkRel PkgSet.
  Definition linkOwners (Links : LinkRel.t) : PkgSet.t :=
    SOlo.map fst Links.

  Module SOso2 := SetOps PkgF Pkg SupportSet PkgSet.
  Definition supportOwners (support : SupportSet.t) : PkgSet.t :=
    SOso2.map fst support.

  (* Whether some feature entry of (p, f) delivers (a, feat); weak and
     strong entries mint the same decision gadget. *)
  Definition fdEntryb (FDefs : FDefRel.t) (p : Pkg.t) (f : F.t)
      (a : N.t) (feat : F.t) : bool :=
    orb (FDefRel.mem ((p, f), FEntry.EDepFeat a feat) FDefs)
      (FDefRel.mem ((p, f), FEntry.EWeakFeat a feat) FDefs).

  Lemma fdEntryb_iff : forall FDefs p f a feat,
      fdEntryb FDefs p f a feat = true <->
      exists e, FDefRel.In ((p, f), e) FDefs /\
        entryFeatD e = Some (a, feat).
  Proof.
    intros FDefs p f a feat; unfold fdEntryb; rewrite orb_true_iff.
    rewrite !FDefRel.mem_spec.
    split.
    - intros [H | H]; eexists; split; try exact H; reflexivity.
    - intros [e [He Hd]].
      destruct e; simpl in Hd; try discriminate;
        injection Hd as -> ->; [left | right]; exact He.
  Qed.

  Module NPSet := FSetUOT NPOT.
  Module SOpn := SetOps Pkg NPOT PkgSet NPSet.
  Module SOsn := SetOps SlotElt NPOT SlotRel NPSet.
  Module SOfn := SetOps FDefElt NPOT FDefRel NPSet.
  Module SOln := SetOps LinkElt NPOT LinkRel NPSet.

  (* Names the instance can mint; over-minting is harmless because the
     per-name versions below come out empty for inert names. *)
  Definition targetNames (R : PkgSet.t) (FDefs : FDefRel.t)
      (Slots : SlotRel.t) (Links : LinkRel.t) : NPSet.t :=
    NPSet.add NPlus.Root
      (NPSet.union (SOpn.map (fun '(n, _) => NPlus.Crate n) R)
         (NPSet.union
            (SOsn.map (fun '((n, v), d) =>
                 NPlus.SlotN n v (sAlias d)) Slots)
            (NPSet.union
               (SOfn.filterMap (fun '(((n, v), f), e) =>
                    match entryFeatD e with
                    | Some (a, feat) =>
                        Some (NPlus.DecisionN n v f a feat)
                    | None => None
                    end) FDefs)
               (SOln.map (fun '(_, l) => NPlus.LinkN l) Links)))).

  Module SOsv := SetOps SlotElt VPOT SlotRel FC.VSet.
  Module SOlv := SetOps LinkElt VPOT LinkRel FC.VSet.

  (* THE per-name lookup: the target versions of a synthetic name, from
     the rows that mint it. *)
  Definition versions (R : PkgSet.t) (FDefs : FDefRel.t)
      (Slots : SlotRel.t) (Links : LinkRel.t)
      (cfgActive : CfgS.t -> bool) (rc : Pkg.t) (np : NPlus.t)
    : FC.VSet.t :=
    match np with
    | NPlus.Root => FC.VSet.singleton VPlus.VUnit
    | NPlus.Crate n => SOvv.map VPlus.VOrig (srcVersions R n)
    | NPlus.SlotN n v a =>
        SOsv.unionMap (fun '(_, d) =>
            SOvv.map VPlus.VChoice (evalReq R (sTarget d) (sReq d)))
          (slotsAt Slots cfgActive rc (n, v) a)
    | NPlus.DecisionN n v f a feat =>
        if fdEntryb FDefs (n, v) f a feat
        then SOsv.unionMap (fun '(_, d) =>
               FC.VSet.add VPlus.VOff
                 (SOvv.map VPlus.VFire
                    (evalReq R (sTarget d) (sReq d))))
             (slotsAt Slots cfgActive rc (n, v) a)
        else FC.VSet.empty
    | NPlus.LinkN l =>
        SOlv.filterMap (fun '(q, l') =>
            if andb (LEqb.eqb l' l) (PkgSet.mem q R)
            then Some (VPlus.VMember q) else None)
          Links
    end.

  Module SOnp := SetOps NPOT FC.Pkg NPSet FC.PkgSet.
  Module SOvp2 := SetOps VPOT FC.Pkg FC.VSet FC.PkgSet.

  Definition transReal (R : PkgSet.t) (FDefs : FDefRel.t)
      (Slots : SlotRel.t) (Links : LinkRel.t)
      (cfgActive : CfgS.t -> bool) (rc : Pkg.t) : FC.PkgSet.t :=
    SOnp.unionMap (fun np =>
        SOvp2.map (fun w => (np, w))
          (versions R FDefs Slots Links cfgActive rc np))
      (targetNames R FDefs Slots Links).

  Module SOss := SetOps PkgF FC.Feat.PkgF SupportSet FC.Feat.SupportSet.
  Module SOfs := SetOps FDefElt FC.Feat.PkgF FDefRel FC.Feat.SupportSet.
  Module SOss2 := SetOps SlotElt FC.Feat.PkgF SlotRel FC.Feat.SupportSet.
  Module SOvs := SetOps V FC.Feat.PkgF VSet FC.Feat.SupportSet.

  (* THE per-crate support lookup: a crate-version's support rows and
     the wit support of its own decision gadgets. *)
  Definition supportAt (R : PkgSet.t) (support : SupportSet.t)
      (FDefs : FDefRel.t) (Slots : SlotRel.t)
      (cfgActive : CfgS.t -> bool) (rc : Pkg.t) (p : Pkg.t)
    : FC.Feat.SupportSet.t :=
    FC.Feat.SupportSet.union
      (SOss.map (fun '((n, v), f) =>
           ((NPlus.Crate n, VPlus.VOrig v), FPlusComp.FOrigF f))
         (ownSupport support p))
      (SOfs.unionMap (fun '(((n, v), f), e) =>
           match entryFeatD e with
           | Some (a, feat) =>
               SOss2.unionMap (fun '(_, d) =>
                   FC.Feat.SupportSet.add
                     ((NPlus.DecisionN n v f a feat, VPlus.VOff),
                      FPlusComp.FWit)
                     (SOvs.map (fun u =>
                          ((NPlus.DecisionN n v f a feat, VPlus.VFire u),
                           FPlusComp.FWit))
                        (evalReq R (sTarget d) (sReq d))))
                 (slotsAt Slots cfgActive rc (n, v) a)
           | None => FC.Feat.SupportSet.empty
           end)
         (ownFDefs FDefs p)).

  Module SOos := SetOps Pkg FC.Feat.PkgF PkgSet FC.Feat.SupportSet.
  Definition transSupport (R : PkgSet.t) (support : SupportSet.t)
      (FDefs : FDefRel.t) (Slots : SlotRel.t)
      (cfgActive : CfgS.t -> bool) (rc : Pkg.t) : FC.Feat.SupportSet.t :=
    SOos.unionMap (supportAt R support FDefs Slots cfgActive rc)
      (PkgSet.union (supportOwners support) (fdefOwners FDefs)).

  Module SOsd := SetOps SlotElt FC.Feat.FeatDepElt SlotRel
    FC.Feat.FeatDepRel.
  Module SOvd := SetOps V FC.Feat.FeatDepElt VSet FC.Feat.FeatDepRel.
  Module SOld := SetOps LinkElt FC.Feat.FeatDepElt LinkRel
    FC.Feat.FeatDepRel.
  Module SOfd := SetOps FDefElt FC.Feat.FeatDepElt FDefRel
    FC.Feat.FeatDepRel.

  Definition rootEdge (rc : Pkg.t) (rootFeats : FSet.t) :
      FC.Feat.FeatDepRel.t :=
    FC.Feat.FeatDepRel.singleton
      (transRoot,
       (NPlus.Crate (fst rc),
        (FC.VSet.singleton (VPlus.VOrig (snd rc)), embedFS rootFeats))).

  Definition slotHop1 (R : PkgSet.t) (Slots : SlotRel.t)
      (cfgActive : CfgS.t -> bool) (rc : Pkg.t) : FC.Feat.FeatDepRel.t :=
    SOsd.filterMap (fun '((n, v), d) =>
        if andb (slotActive cfgActive rc (n, v) d) (negb (sOptional d))
        then Some ((NPlus.Crate n, VPlus.VOrig v),
                   (NPlus.SlotN n v (sAlias d),
                    (choicesOf R d, FC.Feat.FSet.empty)))
        else None)
      Slots.

  Definition slotHop2 (R : PkgSet.t) (Slots : SlotRel.t)
      (cfgActive : CfgS.t -> bool) (dflt : F.t)
      (rc : Pkg.t) : FC.Feat.FeatDepRel.t :=
    SOsd.unionMap (fun '((n, v), d) =>
        if slotActive cfgActive rc (n, v) d
        then SOvd.map (fun u =>
                 ((NPlus.SlotN n v (sAlias d), VPlus.VChoice u),
                  (NPlus.Crate (sTarget d),
                   (FC.VSet.singleton (VPlus.VOrig u),
                    embedFS (slotRequests d dflt)))))
               (evalReq R (sTarget d) (sReq d))
        else FC.Feat.FeatDepRel.empty)
      Slots.

  Definition linkEdges (R : PkgSet.t) (Links : LinkRel.t) :
      FC.Feat.FeatDepRel.t :=
    SOld.filterMap (fun '((n, v), l) =>
        if PkgSet.mem (n, v) R
        then Some ((NPlus.Crate n, VPlus.VOrig v),
                   (NPlus.LinkN l,
                    (FC.VSet.singleton (VPlus.VMember (n, v)),
                     FC.Feat.FSet.empty)))
        else None)
      Links.

  Definition decisionEdges (R : PkgSet.t) (FDefs : FDefRel.t)
      (Slots : SlotRel.t) (cfgActive : CfgS.t -> bool)
      (rc : Pkg.t) : FC.Feat.FeatDepRel.t :=
    SOfd.unionMap (fun '(((n, v), f), e) =>
        match entryFeatD e with
        | Some (a, feat) =>
            SOsd.unionMap (fun '(_, d) =>
                SOvd.map (fun u =>
                    ((NPlus.SlotN n v a, VPlus.VChoice u),
                     (NPlus.DecisionN n v f a feat,
                      (FC.VSet.singleton (VPlus.VFire u),
                       FC.Feat.FSet.empty))))
                  (evalReq R (sTarget d) (sReq d)))
              (slotsAt Slots cfgActive rc (n, v) a)
        | None => FC.Feat.FeatDepRel.empty
        end)
      FDefs.

  (* THE per-crate dependency lookup: the feature-graph edges minted by
     a crate-version's own slot, link, and feature rows.  Slots is
     passed whole to decisionEdges because slotsAt already keys by the
     owning crate. *)
  Definition dependees (R : PkgSet.t) (FDefs : FDefRel.t)
      (Slots : SlotRel.t) (Links : LinkRel.t)
      (cfgActive : CfgS.t -> bool) (dflt : F.t)
      (rc : Pkg.t) (p : Pkg.t) : FC.Feat.FeatDepRel.t :=
    FC.Feat.FeatDepRel.union
      (slotHop1 R (ownSlots Slots p) cfgActive rc)
      (FC.Feat.FeatDepRel.union
         (slotHop2 R (ownSlots Slots p) cfgActive dflt rc)
         (FC.Feat.FeatDepRel.union (linkEdges R (ownLinks Links p))
            (decisionEdges R (ownFDefs FDefs p) Slots cfgActive rc))).

  Definition dfOwners (Slots : SlotRel.t) (Links : LinkRel.t)
      (FDefs : FDefRel.t) : PkgSet.t :=
    PkgSet.union (slotOwners Slots)
      (PkgSet.union (linkOwners Links) (fdefOwners FDefs)).

  Module SOod := SetOps Pkg FC.Feat.FeatDepElt PkgSet FC.Feat.FeatDepRel.
  Definition transDf (R : PkgSet.t) (FDefs : FDefRel.t)
      (Slots : SlotRel.t) (Links : LinkRel.t)
      (cfgActive : CfgS.t -> bool) (dflt : F.t)
      (rc : Pkg.t) (rootFeats : FSet.t) : FC.Feat.FeatDepRel.t :=
    FC.Feat.FeatDepRel.union (rootEdge rc rootFeats)
      (SOod.unionMap (dependees R FDefs Slots Links cfgActive dflt rc)
         (dfOwners Slots Links FDefs)).

  Module SOfa := SetOps FDefElt FC.Feat.AddlDepElt FDefRel
    FC.Feat.AddlDepRel.
  Module SOsa := SetOps SlotElt FC.Feat.AddlDepElt SlotRel
    FC.Feat.AddlDepRel.
  Module SOva := SetOps V FC.Feat.AddlDepElt VSet FC.Feat.AddlDepRel.

  Definition sameFeatEdges (FDefs : FDefRel.t) : FC.Feat.AddlDepRel.t :=
    SOfa.filterMap (fun '(((n, v), f), e) =>
        match e with
        | FEntry.EFeat f' =>
            Some (((NPlus.Crate n, VPlus.VOrig v), FPlusComp.FOrigF f),
                  (NPlus.Crate n,
                   (FC.VSet.singleton (VPlus.VOrig v),
                    FC.Feat.FSet.singleton (FPlusComp.FOrigF f'))))
        | _ => None
        end)
      FDefs.

  Definition activationEdges (R : PkgSet.t) (FDefs : FDefRel.t)
      (Slots : SlotRel.t) (cfgActive : CfgS.t -> bool)
      (rc : Pkg.t) : FC.Feat.AddlDepRel.t :=
    SOfa.unionMap (fun '(((n, v), f), e) =>
        match entryActivates e with
        | Some a =>
            SOsa.map (fun '(_, d) =>
                (((NPlus.Crate n, VPlus.VOrig v), FPlusComp.FOrigF f),
                 (NPlus.SlotN n v a,
                  (choicesOf R d, FC.Feat.FSet.empty))))
              (slotsAt Slots cfgActive rc (n, v) a)
        | None => FC.Feat.AddlDepRel.empty
        end)
      FDefs.

  Definition witEnableEdges (R : PkgSet.t) (FDefs : FDefRel.t)
      (Slots : SlotRel.t) (cfgActive : CfgS.t -> bool)
      (rc : Pkg.t) : FC.Feat.AddlDepRel.t :=
    SOfa.unionMap (fun '(((n, v), f), e) =>
        match entryFeatD e with
        | Some (a, feat) =>
            SOsa.map (fun '(_, d) =>
                (((NPlus.Crate n, VPlus.VOrig v), FPlusComp.FOrigF f),
                 (NPlus.DecisionN n v f a feat,
                  (FC.VSet.add VPlus.VOff (firesOf R d),
                   FC.Feat.FSet.singleton FPlusComp.FWit))))
              (slotsAt Slots cfgActive rc (n, v) a)
        | None => FC.Feat.AddlDepRel.empty
        end)
      FDefs.

  Definition witDeliverEdges (R : PkgSet.t) (FDefs : FDefRel.t)
      (Slots : SlotRel.t) (cfgActive : CfgS.t -> bool)
      (rc : Pkg.t) : FC.Feat.AddlDepRel.t :=
    SOfa.unionMap (fun '(((n, v), f), e) =>
        match entryFeatD e with
        | Some (a, feat) =>
            SOsa.unionMap (fun '(_, d) =>
                SOva.map (fun u =>
                    (((NPlus.DecisionN n v f a feat, VPlus.VFire u),
                      FPlusComp.FWit),
                     (NPlus.Crate (sTarget d),
                      (FC.VSet.singleton (VPlus.VOrig u),
                       FC.Feat.FSet.singleton (FPlusComp.FOrigF feat)))))
                  (evalReq R (sTarget d) (sReq d)))
              (slotsAt Slots cfgActive rc (n, v) a)
        | None => FC.Feat.AddlDepRel.empty
        end)
      FDefs.

  (* THE per-crate feature-edge lookup: the feature-level edges minted
     by a crate-version's own feature rows. *)
  Definition addlDependees (R : PkgSet.t) (FDefs : FDefRel.t)
      (Slots : SlotRel.t) (cfgActive : CfgS.t -> bool)
      (rc : Pkg.t) (p : Pkg.t) : FC.Feat.AddlDepRel.t :=
    FC.Feat.AddlDepRel.union (sameFeatEdges (ownFDefs FDefs p))
      (FC.Feat.AddlDepRel.union
         (activationEdges R (ownFDefs FDefs p) Slots cfgActive rc)
         (FC.Feat.AddlDepRel.union
            (witEnableEdges R (ownFDefs FDefs p) Slots cfgActive rc)
            (witDeliverEdges R (ownFDefs FDefs p) Slots cfgActive rc))).

  Module SOoa := SetOps Pkg FC.Feat.AddlDepElt PkgSet FC.Feat.AddlDepRel.
  Definition transDa (R : PkgSet.t) (FDefs : FDefRel.t)
      (Slots : SlotRel.t) (cfgActive : CfgS.t -> bool)
      (rc : Pkg.t) : FC.Feat.AddlDepRel.t :=
    SOoa.unionMap (addlDependees R FDefs Slots cfgActive rc)
      (fdefOwners FDefs).

  Lemma mem_realBlock : forall R x,
      FC.PkgSet.In x (realBlock R) <->
      exists n v, PkgSet.In (n, v) R /\
        x = (NPlus.Crate n, VPlus.VOrig v).
  Proof.
    intros R x; unfold realBlock; rewrite SOpp.mem_map.
    split.
    - intros [[n v] [HR ->]]; exists n, v; split; [exact HR | reflexivity].
    - intros [n [v [HR ->]]]; exists (n, v); split;
        [exact HR | reflexivity].
  Qed.

  Lemma mem_slotBlock : forall R Slots cfgActive rc x,
      FC.PkgSet.In x (slotBlock R Slots cfgActive rc) <->
      exists n v d u, SlotRel.In ((n, v), d) Slots /\
        slotActive cfgActive rc (n, v) d = true /\
        VSet.In u (evalReq R (sTarget d) (sReq d)) /\
        x = (NPlus.SlotN n v (sAlias d), VPlus.VChoice u).
  Proof.
    intros R Slots cfgActive rc x; unfold slotBlock.
    rewrite SOsp.mem_unionMap.
    split.
    - intros [[[n v] d] [Hs Hx]]; cbn beta iota in Hx.
      destruct (slotActive cfgActive rc (n, v) d) eqn:Ha;
        [| exfalso; exact (SOvp.empty_in _ Hx)].
      apply SOvp.mem_map in Hx; destruct Hx as [u [Hu ->]].
      exists n, v, d, u; repeat split; assumption.
    - intros [n [v [d [u [Hs [Ha [Hu ->]]]]]]].
      exists ((n, v), d); split; [exact Hs | cbn beta iota].
      rewrite Ha; apply SOvp.mem_map; exists u; split;
        [exact Hu | reflexivity].
  Qed.

  Lemma mem_featdBlock : forall R FDefs Slots cfgActive rc x,
      FC.PkgSet.In x (featdBlock R FDefs Slots cfgActive rc) <->
      exists n v f e a feat d,
        FDefRel.In (((n, v), f), e) FDefs /\
        entryFeatD e = Some (a, feat) /\
        SlotRel.In ((n, v), d) Slots /\ sAlias d = a /\
        slotActive cfgActive rc (n, v) d = true /\
        (x = (NPlus.DecisionN n v f a feat, VPlus.VOff) \/
         exists u, VSet.In u (evalReq R (sTarget d) (sReq d)) /\
           x = (NPlus.DecisionN n v f a feat, VPlus.VFire u)).
  Proof.
    intros R FDefs Slots cfgActive rc x; unfold featdBlock.
    rewrite SOfp.mem_unionMap.
    split.
    - intros [[[[n v] f] e] [He Hx]]; cbn beta iota in Hx.
      destruct (entryFeatD e) as [[a feat] |] eqn:Ee;
        [| exfalso; exact (SOsp.empty_in _ Hx)].
      apply SOsp.mem_unionMap in Hx; destruct Hx as [[q d] [Hq Hx]];
        cbn beta iota in Hx.
      apply mem_slotsAt in Hq; destruct Hq as [Hs [-> [Ha Hact]]].
      apply FC.PkgSet.add_spec in Hx.
      exists n, v, f, e, a, feat, d.
      repeat split; try assumption.
      destruct Hx as [-> | Hx]; [left; reflexivity | right].
      apply SOvp.mem_map in Hx; destruct Hx as [u [Hu ->]].
      exists u; split; [exact Hu | reflexivity].
    - intros [n [v [f [e [a [feat [d [He [Ee [Hs [Ha [Hact Hx]]]]]]]]]]]].
      exists (((n, v), f), e); split; [exact He | cbn beta iota].
      rewrite Ee.
      apply SOsp.mem_unionMap; exists ((n, v), d); split.
      + apply mem_slotsAt; repeat split; assumption.
      + cbn beta iota; apply FC.PkgSet.add_spec.
        destruct Hx as [-> | [u [Hu ->]]]; [left; reflexivity | right].
        apply SOvp.mem_map; exists u; split; [exact Hu | reflexivity].
  Qed.

  Lemma mem_linkBlock : forall R Links x,
      FC.PkgSet.In x (linkBlock R Links) <->
      exists n v l, LinkRel.In ((n, v), l) Links /\
        PkgSet.In (n, v) R /\
        x = (NPlus.LinkN l, VPlus.VMember (n, v)).
  Proof.
    intros R Links x; unfold linkBlock; rewrite SOlp.mem_filterMap.
    split.
    - intros [[[n v] l] [Hl Hx]]; cbn beta iota in Hx.
      destruct (PkgSet.mem (n, v) R) eqn:Hm; [| discriminate].
      apply PkgSet.mem_spec in Hm.
      injection Hx as <-.
      exists n, v, l; repeat split; assumption.
    - intros [n [v [l [Hl [HR ->]]]]].
      exists ((n, v), l); split; [exact Hl | cbn beta iota].
      apply PkgSet.mem_spec in HR; rewrite HR; reflexivity.
  Qed.

  Lemma mem_targetNames : forall R FDefs Slots Links np,
      NPSet.In np (targetNames R FDefs Slots Links) <->
      np = NPlus.Root \/
      (exists n v, PkgSet.In (n, v) R /\ np = NPlus.Crate n) \/
      (exists n v d, SlotRel.In ((n, v), d) Slots /\
         np = NPlus.SlotN n v (sAlias d)) \/
      (exists n v f e a feat, FDefRel.In (((n, v), f), e) FDefs /\
         entryFeatD e = Some (a, feat) /\
         np = NPlus.DecisionN n v f a feat) \/
      (exists q l, LinkRel.In (q, l) Links /\ np = NPlus.LinkN l).
  Proof.
    intros R FDefs Slots Links np; unfold targetNames.
    rewrite NPSet.add_spec, !NPSet.union_spec.
    rewrite SOpn.mem_map, SOsn.mem_map, SOfn.mem_filterMap,
      SOln.mem_map.
    split.
    - intros [-> | [H | [H | [H | H]]]].
      + left; reflexivity.
      + destruct H as [[n v] [HR ->]]; right; left; eauto.
      + destruct H as [[[n v] d] [Hs ->]]; right; right; left; eauto 6.
      + destruct H as [[[[n v] f] e] [Hf He]]; cbn beta iota in He.
        destruct (entryFeatD e) as [[a feat] |] eqn:Hd; [| discriminate].
        injection He as <-.
        right; right; right; left; exists n, v, f, e, a, feat; auto.
      + destruct H as [[q l] [Hl ->]]; right; right; right; right; eauto.
    - intros [-> | [H | [H | [H | H]]]].
      + left; reflexivity.
      + destruct H as [n [v [HR ->]]]; right; left; exists (n, v); auto.
      + destruct H as [n [v [d [Hs ->]]]]; right; right; left.
        exists ((n, v), d); auto.
      + destruct H as [n [v [f [e [a [feat [Hf [He ->]]]]]]]].
        right; right; right; left; exists (((n, v), f), e).
        split; [exact Hf | cbn beta iota; rewrite He; reflexivity].
      + destruct H as [q [l [Hl ->]]]; right; right; right; right.
        exists (q, l); auto.
  Qed.

  Lemma mem_transReal : forall R FDefs Slots Links cfgActive rc x,
      FC.PkgSet.In x (transReal R FDefs Slots Links cfgActive rc) <->
      x = transRoot \/
      FC.PkgSet.In x (realBlock R) \/
      FC.PkgSet.In x (slotBlock R Slots cfgActive rc) \/
      FC.PkgSet.In x (featdBlock R FDefs Slots cfgActive rc) \/
      FC.PkgSet.In x (linkBlock R Links).
  Proof.
    intros R FDefs Slots Links cfgActive rc x; unfold transReal.
    rewrite SOnp.mem_unionMap.
    split.
    - intros [np [Hnp Hx]].
      apply SOvp2.mem_map in Hx; destruct Hx as [w [Hw ->]].
      apply mem_targetNames in Hnp.
      destruct Hnp as [-> | [H | [H | [H | H]]]].
      + apply FC.VSet.singleton_spec in Hw; subst w; left; reflexivity.
      + destruct H as [n [v [HR ->]]]; simpl in Hw.
        apply SOvv.mem_map in Hw; destruct Hw as [u [Hu ->]].
        apply mem_srcVersions in Hu.
        right; left; apply mem_realBlock; eauto.
      + destruct H as [n [v [d [Hs ->]]]]; simpl in Hw.
        apply SOsv.mem_unionMap in Hw.
        destruct Hw as [[q d'] [Hq Hw]]; cbn beta iota in Hw.
        apply mem_slotsAt in Hq; destruct Hq as [Hq [-> [Ha Hact]]].
        apply SOvv.mem_map in Hw; destruct Hw as [u [Hu ->]].
        right; right; left; apply mem_slotBlock.
        exists n, v, d', u; rewrite Ha; repeat split; assumption.
      + destruct H as [n [v [f [e0 [a [feat [Hf0 [He0 ->]]]]]]]].
        simpl in Hw.
        destruct (fdEntryb FDefs (n, v) f a feat) eqn:Hb;
          [| apply FC.VSet.empty_spec in Hw; destruct Hw].
        apply fdEntryb_iff in Hb; destruct Hb as [e [Hfe Hde]].
        apply SOsv.mem_unionMap in Hw.
        destruct Hw as [[q d] [Hq Hw]]; cbn beta iota in Hw.
        apply mem_slotsAt in Hq; destruct Hq as [Hq [-> [Ha Hact]]].
        apply FC.VSet.add_spec in Hw.
        right; right; right; left; apply mem_featdBlock.
        exists n, v, f, e, a, feat, d.
        repeat split; try assumption.
        destruct Hw as [-> | Hw]; [left; reflexivity |].
        apply SOvv.mem_map in Hw; destruct Hw as [u [Hu ->]].
        right; exists u; split; [exact Hu | reflexivity].
      + destruct H as [q0 [l [Hl0 ->]]]; simpl in Hw.
        apply SOlv.mem_filterMap in Hw.
        destruct Hw as [[q l'] [Hq He]]; cbn beta iota in He.
        destruct (andb (LEqb.eqb l' l) (PkgSet.mem q R)) eqn:Hg;
          [| discriminate].
        apply andb_true_iff in Hg; destruct Hg as [Hle HqR].
        apply LEqb.eqb_true_iff in Hle; subst l'.
        apply PkgSet.mem_spec in HqR.
        injection He as <-.
        destruct q as [n v].
        right; right; right; right; apply mem_linkBlock; eauto 6.
    - intros [-> | [H | [H | [H | H]]]].
      + exists NPlus.Root; split;
          [apply mem_targetNames; left; reflexivity |].
        apply SOvp2.mem_map; exists VPlus.VUnit; split;
          [apply FC.VSet.singleton_spec |]; reflexivity.
      + apply mem_realBlock in H; destruct H as [n [v [HR ->]]].
        exists (NPlus.Crate n); split;
          [apply mem_targetNames; right; left; eauto |].
        apply SOvp2.mem_map; exists (VPlus.VOrig v); split;
          [| reflexivity].
        simpl; apply SOvv.mem_map; exists v; split;
          [apply mem_srcVersions; exact HR | reflexivity].
      + apply mem_slotBlock in H.
        destruct H as [n [v [d [u [Hs [Hact [Hu ->]]]]]]].
        exists (NPlus.SlotN n v (sAlias d)); split;
          [apply mem_targetNames; right; right; left; eauto 6 |].
        apply SOvp2.mem_map; exists (VPlus.VChoice u); split;
          [| reflexivity].
        simpl; apply SOsv.mem_unionMap; exists ((n, v), d); split.
        * apply mem_slotsAt; repeat split; assumption.
        * cbn beta iota; apply SOvv.mem_map; exists u; split;
            [exact Hu | reflexivity].
      + apply mem_featdBlock in H.
        destruct H
          as [n [v [f [e [a [feat [d [Hf [He [Hs [Ha [Hact Hw]]]]]]]]]]]].
        exists (NPlus.DecisionN n v f a feat); split;
          [apply mem_targetNames; right; right; right; left;
           exists n, v, f, e, a, feat; auto |].
        apply SOvp2.mem_map.
        assert (Hb : fdEntryb FDefs (n, v) f a feat = true)
          by (apply fdEntryb_iff; eauto).
        destruct Hw as [-> | [u [Hu ->]]].
        * exists VPlus.VOff; split; [| reflexivity].
          simpl; rewrite Hb.
          apply SOsv.mem_unionMap; exists ((n, v), d); split.
          { apply mem_slotsAt; repeat split; assumption. }
          cbn beta iota; apply FC.VSet.add_spec; left; reflexivity.
        * exists (VPlus.VFire u); split; [| reflexivity].
          simpl; rewrite Hb.
          apply SOsv.mem_unionMap; exists ((n, v), d); split.
          { apply mem_slotsAt; repeat split; assumption. }
          cbn beta iota; apply FC.VSet.add_spec; right.
          apply SOvv.mem_map; exists u; split; [exact Hu | reflexivity].
      + apply mem_linkBlock in H; destruct H as [n [v [l [Hl [HR ->]]]]].
        exists (NPlus.LinkN l); split;
          [apply mem_targetNames; right; right; right; right; eauto |].
        apply SOvp2.mem_map; exists (VPlus.VMember (n, v)); split;
          [| reflexivity].
        simpl; apply SOlv.mem_filterMap; exists ((n, v), l); split;
          [exact Hl | cbn beta iota].
        rewrite LEqb.eqb_refl; simpl.
        assert (Hm : PkgSet.mem (n, v) R = true)
          by (apply PkgSet.mem_spec; exact HR).
        rewrite Hm; reflexivity.
  Qed.

  Lemma mem_transSupport : forall R support FDefs Slots cfgActive rc y,
      FC.Feat.SupportSet.In y
        (transSupport R support FDefs Slots cfgActive rc) <->
      (exists n v f, SupportSet.In ((n, v), f) support /\
         y = ((NPlus.Crate n, VPlus.VOrig v), FPlusComp.FOrigF f)) \/
      (exists n v f e a feat d,
         FDefRel.In (((n, v), f), e) FDefs /\
         entryFeatD e = Some (a, feat) /\
         SlotRel.In ((n, v), d) Slots /\ sAlias d = a /\
         slotActive cfgActive rc (n, v) d = true /\
         (y = ((NPlus.DecisionN n v f a feat, VPlus.VOff),
               FPlusComp.FWit) \/
          exists u, VSet.In u (evalReq R (sTarget d) (sReq d)) /\
            y = ((NPlus.DecisionN n v f a feat, VPlus.VFire u),
                 FPlusComp.FWit))).
  Proof.
    intros R support FDefs Slots cfgActive rc y; unfold transSupport.
    rewrite SOos.mem_unionMap.
    split.
    - intros [p [_ Hy]]; unfold supportAt in Hy.
      apply FC.Feat.SupportSet.union_spec in Hy.
      rewrite SOss.mem_map, SOfs.mem_unionMap in Hy.
      destruct Hy as [[[[n v] f] [Hs ->]] | [[[[n v] f] e] [He Hy]]].
      + apply mem_ownSupport in Hs; destruct Hs as [Hs _].
        left; exists n, v, f; split; [exact Hs | reflexivity].
      + apply mem_ownFDefs in He; destruct He as [He _].
        right; cbn beta iota in Hy.
        destruct (entryFeatD e) as [[a feat] |] eqn:Ee;
          [| exfalso; exact (SOss2.empty_in _ Hy)].
        apply SOss2.mem_unionMap in Hy; destruct Hy as [[q d] [Hq Hy]];
          cbn beta iota in Hy.
        apply mem_slotsAt in Hq; destruct Hq as [Hs [-> [Ha Hact]]].
        apply FC.Feat.SupportSet.add_spec in Hy.
        exists n, v, f, e, a, feat, d.
        repeat split; try assumption.
        destruct Hy as [-> | Hy]; [left; reflexivity | right].
        apply SOvs.mem_map in Hy; destruct Hy as [u [Hu ->]].
        exists u; split; [exact Hu | reflexivity].
    - intros [[n [v [f [Hs ->]]]]
             | [n [v [f [e [a [feat [d [He [Ee [Hs [Ha [Hact Hy]]]]]]]]]]]]].
      + exists (n, v); split.
        { apply PkgSet.union_spec; left; unfold supportOwners.
          apply SOso2.mem_map; exists ((n, v), f); split;
            [exact Hs | reflexivity]. }
        unfold supportAt; apply FC.Feat.SupportSet.union_spec; left.
        apply SOss.mem_map; exists ((n, v), f); split; [| reflexivity].
        apply mem_ownSupport; split; [exact Hs | reflexivity].
      + exists (n, v); split.
        { apply PkgSet.union_spec; right; unfold fdefOwners.
          apply SOfo.mem_map; exists (((n, v), f), e); split;
            [exact He | reflexivity]. }
        unfold supportAt; apply FC.Feat.SupportSet.union_spec; right.
        apply SOfs.mem_unionMap; exists (((n, v), f), e); split.
        { apply mem_ownFDefs; split; [exact He | reflexivity]. }
        cbn beta iota; rewrite Ee.
        apply SOss2.mem_unionMap; exists ((n, v), d); split.
        * apply mem_slotsAt; repeat split; assumption.
        * cbn beta iota; apply FC.Feat.SupportSet.add_spec.
          destruct Hy as [-> | [u [Hu ->]]]; [left; reflexivity | right].
          apply SOvs.mem_map; exists u; split; [exact Hu | reflexivity].
  Qed.

  Lemma mem_rootEdge : forall rc rootFeats e,
      FC.Feat.FeatDepRel.In e (rootEdge rc rootFeats) <->
      e = (transRoot,
           (NPlus.Crate (fst rc),
            (FC.VSet.singleton (VPlus.VOrig (snd rc)),
             embedFS rootFeats))).
  Proof.
    intros rc rootFeats e; unfold rootEdge.
    rewrite FC.Feat.FeatDepRel.singleton_spec; split; intro H; subst e;
      reflexivity.
  Qed.

  Lemma mem_slotHop1 : forall R Slots cfgActive rc e,
      FC.Feat.FeatDepRel.In e (slotHop1 R Slots cfgActive rc) <->
      exists n v d, SlotRel.In ((n, v), d) Slots /\
        slotActive cfgActive rc (n, v) d = true /\
        sOptional d = false /\
        e = ((NPlus.Crate n, VPlus.VOrig v),
             (NPlus.SlotN n v (sAlias d),
              (choicesOf R d, FC.Feat.FSet.empty))).
  Proof.
    intros R Slots cfgActive rc e; unfold slotHop1.
    rewrite SOsd.mem_filterMap.
    split.
    - intros [[[n v] d] [Hs He]]; cbn beta iota in He.
      destruct (andb (slotActive cfgActive rc (n, v) d)
                  (negb (sOptional d))) eqn:Hb; [| discriminate].
      apply andb_true_iff in Hb; destruct Hb as [Hact Hopt].
      apply negb_true_iff in Hopt.
      injection He as <-.
      exists n, v, d; repeat split; assumption.
    - intros [n [v [d [Hs [Hact [Hopt ->]]]]]].
      exists ((n, v), d); split; [exact Hs | cbn beta iota].
      rewrite Hact, Hopt; reflexivity.
  Qed.

  Lemma mem_slotHop2 : forall R Slots cfgActive dflt rc e,
      FC.Feat.FeatDepRel.In e (slotHop2 R Slots cfgActive dflt rc) <->
      exists n v d u, SlotRel.In ((n, v), d) Slots /\
        slotActive cfgActive rc (n, v) d = true /\
        VSet.In u (evalReq R (sTarget d) (sReq d)) /\
        e = ((NPlus.SlotN n v (sAlias d), VPlus.VChoice u),
             (NPlus.Crate (sTarget d),
              (FC.VSet.singleton (VPlus.VOrig u),
               embedFS (slotRequests d dflt)))).
  Proof.
    intros R Slots cfgActive dflt rc e; unfold slotHop2.
    rewrite SOsd.mem_unionMap.
    split.
    - intros [[[n v] d] [Hs He]]; cbn beta iota in He.
      destruct (slotActive cfgActive rc (n, v) d) eqn:Ha;
        [| exfalso; exact (SOvd.empty_in _ He)].
      apply SOvd.mem_map in He; destruct He as [u [Hu ->]].
      exists n, v, d, u; repeat split; assumption.
    - intros [n [v [d [u [Hs [Ha [Hu ->]]]]]]].
      exists ((n, v), d); split; [exact Hs | cbn beta iota].
      rewrite Ha; apply SOvd.mem_map; exists u; split;
        [exact Hu | reflexivity].
  Qed.

  Lemma mem_linkEdges : forall R Links e,
      FC.Feat.FeatDepRel.In e (linkEdges R Links) <->
      exists n v l, LinkRel.In ((n, v), l) Links /\
        PkgSet.In (n, v) R /\
        e = ((NPlus.Crate n, VPlus.VOrig v),
             (NPlus.LinkN l,
              (FC.VSet.singleton (VPlus.VMember (n, v)),
               FC.Feat.FSet.empty))).
  Proof.
    intros R Links e; unfold linkEdges; rewrite SOld.mem_filterMap.
    split.
    - intros [[[n v] l] [Hl He]]; cbn beta iota in He.
      destruct (PkgSet.mem (n, v) R) eqn:Hm; [| discriminate].
      apply PkgSet.mem_spec in Hm.
      injection He as <-.
      exists n, v, l; repeat split; assumption.
    - intros [n [v [l [Hl [HR ->]]]]].
      exists ((n, v), l); split; [exact Hl | cbn beta iota].
      apply PkgSet.mem_spec in HR; rewrite HR; reflexivity.
  Qed.

  Lemma mem_decisionEdges : forall R FDefs Slots cfgActive rc e,
      FC.Feat.FeatDepRel.In e (decisionEdges R FDefs Slots cfgActive rc) <->
      exists n v f e' a feat d u,
        FDefRel.In (((n, v), f), e') FDefs /\
        entryFeatD e' = Some (a, feat) /\
        SlotRel.In ((n, v), d) Slots /\ sAlias d = a /\
        slotActive cfgActive rc (n, v) d = true /\
        VSet.In u (evalReq R (sTarget d) (sReq d)) /\
        e = ((NPlus.SlotN n v a, VPlus.VChoice u),
             (NPlus.DecisionN n v f a feat,
              (FC.VSet.singleton (VPlus.VFire u), FC.Feat.FSet.empty))).
  Proof.
    intros R FDefs Slots cfgActive rc e; unfold decisionEdges.
    rewrite SOfd.mem_unionMap.
    split.
    - intros [[[[n v] f] e'] [He' He]]; cbn beta iota in He.
      destruct (entryFeatD e') as [[a feat] |] eqn:Ee;
        [| exfalso; exact (SOsd.empty_in _ He)].
      apply SOsd.mem_unionMap in He; destruct He as [[q d] [Hq He]];
        cbn beta iota in He.
      apply mem_slotsAt in Hq; destruct Hq as [Hs [-> [Ha Hact]]].
      apply SOvd.mem_map in He; destruct He as [u [Hu ->]].
      exists n, v, f, e', a, feat, d, u; repeat split; assumption.
    - intros [n [v [f [e' [a [feat [d [u
        [He' [Ee [Hs [Ha [Hact [Hu ->]]]]]]]]]]]]]].
      exists (((n, v), f), e'); split; [exact He' | cbn beta iota].
      rewrite Ee.
      apply SOsd.mem_unionMap; exists ((n, v), d); split.
      + apply mem_slotsAt; repeat split; assumption.
      + cbn beta iota; apply SOvd.mem_map; exists u; split;
          [exact Hu | reflexivity].
  Qed.

  Lemma mem_transDf : forall R FDefs Slots Links cfgActive dflt rc
      rootFeats e,
      FC.Feat.FeatDepRel.In e
        (transDf R FDefs Slots Links cfgActive dflt rc rootFeats) <->
      FC.Feat.FeatDepRel.In e (rootEdge rc rootFeats) \/
      FC.Feat.FeatDepRel.In e (slotHop1 R Slots cfgActive rc) \/
      FC.Feat.FeatDepRel.In e (slotHop2 R Slots cfgActive dflt rc) \/
      FC.Feat.FeatDepRel.In e (linkEdges R Links) \/
      FC.Feat.FeatDepRel.In e (decisionEdges R FDefs Slots cfgActive rc).
  Proof.
    intros R FDefs Slots Links cfgActive dflt rc rootFeats e.
    unfold transDf.
    rewrite FC.Feat.FeatDepRel.union_spec, SOod.mem_unionMap.
    split.
    - intros [H | [p [_ H]]]; [left; exact H |].
      unfold dependees in H.
      rewrite !FC.Feat.FeatDepRel.union_spec in H.
      destruct H as [H | [H | [H | H]]].
      + apply mem_slotHop1 in H.
        destruct H as [n [v [d [Hs [Hact [Hopt He]]]]]].
        apply mem_ownSlots in Hs; destruct Hs as [Hs _].
        right; left; apply mem_slotHop1.
        exists n, v, d; repeat split; assumption.
      + apply mem_slotHop2 in H.
        destruct H as [n [v [d [u [Hs [Hact [Hu He]]]]]]].
        apply mem_ownSlots in Hs; destruct Hs as [Hs _].
        right; right; left; apply mem_slotHop2.
        exists n, v, d, u; repeat split; assumption.
      + apply mem_linkEdges in H.
        destruct H as [n [v [l [Hl [HR He]]]]].
        apply mem_ownLinks in Hl; destruct Hl as [Hl _].
        right; right; right; left; apply mem_linkEdges.
        exists n, v, l; repeat split; assumption.
      + apply mem_decisionEdges in H.
        destruct H
          as [n [v [f [e' [a [feat [d [u [Hf [Hd [Hs [Ha [Hact
             [Hu He]]]]]]]]]]]]]].
        apply mem_ownFDefs in Hf; destruct Hf as [Hf _].
        right; right; right; right; apply mem_decisionEdges.
        exists n, v, f, e', a, feat, d, u; repeat split; assumption.
    - intros [H | H]; [left; exact H |].
      right; destruct H as [H | [H | [H | H]]].
      + apply mem_slotHop1 in H.
        destruct H as [n [v [d [Hs [Hact [Hopt He]]]]]].
        exists (n, v); split.
        { apply PkgSet.union_spec; left; unfold slotOwners.
          apply SOso.mem_map; exists ((n, v), d); split;
            [exact Hs | reflexivity]. }
        unfold dependees; rewrite !FC.Feat.FeatDepRel.union_spec.
        left; apply mem_slotHop1; exists n, v, d.
        repeat split; try assumption.
        apply mem_ownSlots; split; [exact Hs | reflexivity].
      + apply mem_slotHop2 in H.
        destruct H as [n [v [d [u [Hs [Hact [Hu He]]]]]]].
        exists (n, v); split.
        { apply PkgSet.union_spec; left; unfold slotOwners.
          apply SOso.mem_map; exists ((n, v), d); split;
            [exact Hs | reflexivity]. }
        unfold dependees; rewrite !FC.Feat.FeatDepRel.union_spec.
        right; left; apply mem_slotHop2; exists n, v, d, u.
        repeat split; try assumption.
        apply mem_ownSlots; split; [exact Hs | reflexivity].
      + apply mem_linkEdges in H.
        destruct H as [n [v [l [Hl [HR He]]]]].
        exists (n, v); split.
        { apply PkgSet.union_spec; right; apply PkgSet.union_spec; left.
          unfold linkOwners; apply SOlo.mem_map.
          exists ((n, v), l); split; [exact Hl | reflexivity]. }
        unfold dependees; rewrite !FC.Feat.FeatDepRel.union_spec.
        right; right; left; apply mem_linkEdges; exists n, v, l.
        repeat split; try assumption.
        apply mem_ownLinks; split; [exact Hl | reflexivity].
      + apply mem_decisionEdges in H.
        destruct H
          as [n [v [f [e' [a [feat [d [u [Hf [Hd [Hs [Ha [Hact
             [Hu He]]]]]]]]]]]]]].
        exists (n, v); split.
        { apply PkgSet.union_spec; right; apply PkgSet.union_spec; right.
          unfold fdefOwners; apply SOfo.mem_map.
          exists (((n, v), f), e'); split; [exact Hf | reflexivity]. }
        unfold dependees; rewrite !FC.Feat.FeatDepRel.union_spec.
        right; right; right; apply mem_decisionEdges.
        exists n, v, f, e', a, feat, d, u.
        repeat split; try assumption.
        apply mem_ownFDefs; split; [exact Hf | reflexivity].
  Qed.

  Lemma mem_sameFeatEdges : forall FDefs e,
      FC.Feat.AddlDepRel.In e (sameFeatEdges FDefs) <->
      exists n v f f',
        FDefRel.In (((n, v), f), FEntry.EFeat f') FDefs /\
        e = (((NPlus.Crate n, VPlus.VOrig v), FPlusComp.FOrigF f),
             (NPlus.Crate n,
              (FC.VSet.singleton (VPlus.VOrig v),
               FC.Feat.FSet.singleton (FPlusComp.FOrigF f')))).
  Proof.
    intros FDefs e; unfold sameFeatEdges; rewrite SOfa.mem_filterMap.
    split.
    - intros [[[[n v] f] e'] [He' He]]; cbn beta iota in He.
      destruct e' as [f' | | |]; try discriminate.
      injection He as <-.
      exists n, v, f, f'; split; [exact He' | reflexivity].
    - intros [n [v [f [f' [He' ->]]]]].
      exists (((n, v), f), FEntry.EFeat f'); split;
        [exact He' | reflexivity].
  Qed.

  Lemma mem_activationEdges : forall R FDefs Slots cfgActive rc e,
      FC.Feat.AddlDepRel.In e
        (activationEdges R FDefs Slots cfgActive rc) <->
      exists n v f e' a d,
        FDefRel.In (((n, v), f), e') FDefs /\
        entryActivates e' = Some a /\
        SlotRel.In ((n, v), d) Slots /\ sAlias d = a /\
        slotActive cfgActive rc (n, v) d = true /\
        e = (((NPlus.Crate n, VPlus.VOrig v), FPlusComp.FOrigF f),
             (NPlus.SlotN n v a, (choicesOf R d, FC.Feat.FSet.empty))).
  Proof.
    intros R FDefs Slots cfgActive rc e; unfold activationEdges.
    rewrite SOfa.mem_unionMap.
    split.
    - intros [[[[n v] f] e'] [He' He]]; cbn beta iota in He.
      destruct (entryActivates e') as [a |] eqn:Ea;
        [| exfalso; exact (SOsa.empty_in _ He)].
      apply SOsa.mem_map in He; destruct He as [[q d] [Hq ->]].
      apply mem_slotsAt in Hq; destruct Hq as [Hs [-> [Ha Hact]]].
      exists n, v, f, e', a, d; repeat split; assumption.
    - intros [n [v [f [e' [a [d [He' [Ea [Hs [Ha Hact]]]]]]]]]].
      destruct Hact as [Hact ->].
      exists (((n, v), f), e'); split; [exact He' | cbn beta iota].
      rewrite Ea.
      apply SOsa.mem_map; exists ((n, v), d); split;
        [apply mem_slotsAt; repeat split; assumption | reflexivity].
  Qed.

  Lemma mem_witEnableEdges : forall R FDefs Slots cfgActive rc e,
      FC.Feat.AddlDepRel.In e
        (witEnableEdges R FDefs Slots cfgActive rc) <->
      exists n v f e' a feat d,
        FDefRel.In (((n, v), f), e') FDefs /\
        entryFeatD e' = Some (a, feat) /\
        SlotRel.In ((n, v), d) Slots /\ sAlias d = a /\
        slotActive cfgActive rc (n, v) d = true /\
        e = (((NPlus.Crate n, VPlus.VOrig v), FPlusComp.FOrigF f),
             (NPlus.DecisionN n v f a feat,
              (FC.VSet.add VPlus.VOff (firesOf R d),
               FC.Feat.FSet.singleton FPlusComp.FWit))).
  Proof.
    intros R FDefs Slots cfgActive rc e; unfold witEnableEdges.
    rewrite SOfa.mem_unionMap.
    split.
    - intros [[[[n v] f] e'] [He' He]]; cbn beta iota in He.
      destruct (entryFeatD e') as [[a feat] |] eqn:Ee;
        [| exfalso; exact (SOsa.empty_in _ He)].
      apply SOsa.mem_map in He; destruct He as [[q d] [Hq ->]].
      apply mem_slotsAt in Hq; destruct Hq as [Hs [-> [Ha Hact]]].
      exists n, v, f, e', a, feat, d; repeat split; assumption.
    - intros [n [v [f [e' [a [feat [d [He' [Ee [Hs [Ha Hact]]]]]]]]]]].
      destruct Hact as [Hact ->].
      exists (((n, v), f), e'); split; [exact He' | cbn beta iota].
      rewrite Ee.
      apply SOsa.mem_map; exists ((n, v), d); split;
        [apply mem_slotsAt; repeat split; assumption | reflexivity].
  Qed.

  Lemma mem_witDeliverEdges : forall R FDefs Slots cfgActive rc e,
      FC.Feat.AddlDepRel.In e
        (witDeliverEdges R FDefs Slots cfgActive rc) <->
      exists n v f e' a feat d u,
        FDefRel.In (((n, v), f), e') FDefs /\
        entryFeatD e' = Some (a, feat) /\
        SlotRel.In ((n, v), d) Slots /\ sAlias d = a /\
        slotActive cfgActive rc (n, v) d = true /\
        VSet.In u (evalReq R (sTarget d) (sReq d)) /\
        e = (((NPlus.DecisionN n v f a feat, VPlus.VFire u), FPlusComp.FWit),
             (NPlus.Crate (sTarget d),
              (FC.VSet.singleton (VPlus.VOrig u),
               FC.Feat.FSet.singleton (FPlusComp.FOrigF feat)))).
  Proof.
    intros R FDefs Slots cfgActive rc e; unfold witDeliverEdges.
    rewrite SOfa.mem_unionMap.
    split.
    - intros [[[[n v] f] e'] [He' He]]; cbn beta iota in He.
      destruct (entryFeatD e') as [[a feat] |] eqn:Ee;
        [| exfalso; exact (SOsa.empty_in _ He)].
      apply SOsa.mem_unionMap in He; destruct He as [[q d] [Hq He]];
        cbn beta iota in He.
      apply mem_slotsAt in Hq; destruct Hq as [Hs [-> [Ha Hact]]].
      apply SOva.mem_map in He; destruct He as [u [Hu ->]].
      exists n, v, f, e', a, feat, d, u; repeat split; assumption.
    - intros [n [v [f [e' [a [feat [d [u
        [He' [Ee [Hs [Ha [Hact [Hu ->]]]]]]]]]]]]]].
      exists (((n, v), f), e'); split; [exact He' | cbn beta iota].
      rewrite Ee.
      apply SOsa.mem_unionMap; exists ((n, v), d); split.
      + apply mem_slotsAt; repeat split; assumption.
      + cbn beta iota; apply SOva.mem_map; exists u; split;
          [exact Hu | reflexivity].
  Qed.

  Lemma mem_transDa : forall R FDefs Slots cfgActive rc e,
      FC.Feat.AddlDepRel.In e (transDa R FDefs Slots cfgActive rc) <->
      FC.Feat.AddlDepRel.In e (sameFeatEdges FDefs) \/
      FC.Feat.AddlDepRel.In e (activationEdges R FDefs Slots cfgActive rc) \/
      FC.Feat.AddlDepRel.In e (witEnableEdges R FDefs Slots cfgActive rc) \/
      FC.Feat.AddlDepRel.In e (witDeliverEdges R FDefs Slots cfgActive rc).
  Proof.
    intros R FDefs Slots cfgActive rc e.
    unfold transDa; rewrite SOoa.mem_unionMap.
    split.
    - intros [p [_ H]]; unfold addlDependees in H.
      rewrite !FC.Feat.AddlDepRel.union_spec in H.
      destruct H as [H | [H | [H | H]]].
      + apply mem_sameFeatEdges in H.
        destruct H as [n [v [f [f' [Hf He]]]]].
        apply mem_ownFDefs in Hf; destruct Hf as [Hf _].
        left; apply mem_sameFeatEdges.
        exists n, v, f, f'; split; assumption.
      + apply mem_activationEdges in H.
        destruct H as [n [v [f [e' [a [d [Hf [Hd [Hs [Ha [Hact He]]]]]]]]]]].
        apply mem_ownFDefs in Hf; destruct Hf as [Hf _].
        right; left; apply mem_activationEdges.
        exists n, v, f, e', a, d; repeat split; assumption.
      + apply mem_witEnableEdges in H.
        destruct H
          as [n [v [f [e' [a [feat [d [Hf [Hd [Hs [Ha [Hact He]]]]]]]]]]]].
        apply mem_ownFDefs in Hf; destruct Hf as [Hf _].
        right; right; left; apply mem_witEnableEdges.
        exists n, v, f, e', a, feat, d; repeat split; assumption.
      + apply mem_witDeliverEdges in H.
        destruct H
          as [n [v [f [e' [a [feat [d [u [Hf [Hd [Hs [Ha [Hact
             [Hu He]]]]]]]]]]]]]].
        apply mem_ownFDefs in Hf; destruct Hf as [Hf _].
        right; right; right; apply mem_witDeliverEdges.
        exists n, v, f, e', a, feat, d, u; repeat split; assumption.
    - intros [H | [H | [H | H]]].
      + apply mem_sameFeatEdges in H.
        destruct H as [n [v [f [f' [Hf He]]]]].
        exists (n, v); split.
        { unfold fdefOwners; apply SOfo.mem_map.
          exists (((n, v), f), FEntry.EFeat f'); split;
            [exact Hf | reflexivity]. }
        unfold addlDependees; rewrite !FC.Feat.AddlDepRel.union_spec.
        left; apply mem_sameFeatEdges; exists n, v, f, f'.
        split; [| assumption].
        apply mem_ownFDefs; split; [exact Hf | reflexivity].
      + apply mem_activationEdges in H.
        destruct H as [n [v [f [e' [a [d [Hf [Hd [Hs [Ha [Hact He]]]]]]]]]]].
        exists (n, v); split.
        { unfold fdefOwners; apply SOfo.mem_map.
          exists (((n, v), f), e'); split; [exact Hf | reflexivity]. }
        unfold addlDependees; rewrite !FC.Feat.AddlDepRel.union_spec.
        right; left; apply mem_activationEdges.
        exists n, v, f, e', a, d; repeat split; try assumption.
        apply mem_ownFDefs; split; [exact Hf | reflexivity].
      + apply mem_witEnableEdges in H.
        destruct H
          as [n [v [f [e' [a [feat [d [Hf [Hd [Hs [Ha [Hact He]]]]]]]]]]]].
        exists (n, v); split.
        { unfold fdefOwners; apply SOfo.mem_map.
          exists (((n, v), f), e'); split; [exact Hf | reflexivity]. }
        unfold addlDependees; rewrite !FC.Feat.AddlDepRel.union_spec.
        right; right; left; apply mem_witEnableEdges.
        exists n, v, f, e', a, feat, d; repeat split; try assumption.
        apply mem_ownFDefs; split; [exact Hf | reflexivity].
      + apply mem_witDeliverEdges in H.
        destruct H
          as [n [v [f [e' [a [feat [d [u [Hf [Hd [Hs [Ha [Hact
             [Hu He]]]]]]]]]]]]]].
        exists (n, v); split.
        { unfold fdefOwners; apply SOfo.mem_map.
          exists (((n, v), f), e'); split; [exact Hf | reflexivity]. }
        unfold addlDependees; rewrite !FC.Feat.AddlDepRel.union_spec.
        right; right; right; apply mem_witDeliverEdges.
        exists n, v, f, e', a, feat, d, u; repeat split; try assumption.
        apply mem_ownFDefs; split; [exact Hf | reflexivity].
  Qed.

  (* Duplicate manifest aliases are rejected by Cargo; the products assume
     that well-formedness because the slot node is keyed by alias. *)
  Definition AliasFunctional (Slots : SlotRel.t) : Prop :=
    forall p d d', SlotRel.In (p, d) Slots -> SlotRel.In (p, d') Slots ->
    sAlias d = sAlias d' -> d = d'.

  Module SOstrip := SetOps FPlus F FC.Feat.FSet FSet.
  Definition stripFS (fs : FC.Feat.FSet.t) : FSet.t :=
    SOstrip.filterMap (fun x =>
        match x with
        | FPlusComp.FOrigF f => Some f
        | FPlusComp.FWit => None
        end)
      fs.

  Lemma mem_stripFS : forall fs f,
      FSet.In f (stripFS fs) <-> FC.Feat.FSet.In (FPlusComp.FOrigF f) fs.
  Proof.
    intros fs f; unfold stripFS; rewrite SOstrip.mem_filterMap.
    split.
    - intros [[f' |] [Hf He]]; [| discriminate].
      injection He as ->; exact Hf.
    - intro Hf; exists (FPlusComp.FOrigF f); split;
        [exact Hf | reflexivity].
  Qed.

  Lemma embedFS_subset_strip : forall A B,
      FC.Feat.FSet.Subset (embedFS A) B -> FSet.Subset A (stripFS B).
  Proof.
    intros A B H f Hf; apply mem_stripFS, H, mem_embedFS.
    exists f; split; [exact Hf | reflexivity].
  Qed.

  Module SOcp := SetOps FC.Feat.Featured Pkg FC.Feat.FeaturedSet PkgSet.
  Definition decodeS (S : FC.Feat.FeaturedSet.t) : PkgSet.t :=
    SOcp.filterMap (fun '((nm, w), _) =>
        match nm, w with
        | NPlus.Crate n, VPlus.VOrig v => Some (n, v)
        | _, _ => None
        end)
      S.

  Lemma mem_decodeS : forall S n v,
      PkgSet.In (n, v) (decodeS S) <->
      exists fs, FC.Feat.FeaturedSet.In
        ((NPlus.Crate n, VPlus.VOrig v), fs) S.
  Proof.
    intros S n v; unfold decodeS; rewrite SOcp.mem_filterMap.
    split.
    - intros [[[nm w] fs] [Hin He]]; cbn beta iota in He.
      destruct nm; try discriminate; destruct w; try discriminate.
      injection He as -> ->; exists fs; exact Hin.
    - intros [fs Hin].
      exists ((NPlus.Crate n, VPlus.VOrig v), fs); split;
        [exact Hin | reflexivity].
  Qed.

  Module SOcf := SetOps FC.Feat.Featured Featured FC.Feat.FeaturedSet
    FeaturedSet.
  Definition decodeFS (S : FC.Feat.FeaturedSet.t) : FeaturedSet.t :=
    SOcf.filterMap (fun '((nm, w), fs) =>
        match nm, w with
        | NPlus.Crate n, VPlus.VOrig v => Some ((n, v), stripFS fs)
        | _, _ => None
        end)
      S.

  Lemma mem_decodeFS : forall S n v fs,
      FeaturedSet.In ((n, v), fs) (decodeFS S) <->
      exists fsP, FC.Feat.FeaturedSet.In
        ((NPlus.Crate n, VPlus.VOrig v), fsP) S /\ fs = stripFS fsP.
  Proof.
    intros S n v fs; unfold decodeFS; rewrite SOcf.mem_filterMap.
    split.
    - intros [[[nm w] fsP] [Hin He]]; cbn beta iota in He.
      destruct nm; try discriminate; destruct w; try discriminate.
      injection He as -> -> <-; exists fsP; split;
        [exact Hin | reflexivity].
    - intros [fsP [Hin ->]].
      exists ((NPlus.Crate n, VPlus.VOrig v), fsP); split;
        [exact Hin | reflexivity].
  Qed.

  Module SOcsel := SetOps FC.Feat.Featured SelElt FC.Feat.FeaturedSet
    SelRel.
  Definition decodeSel (S : FC.Feat.FeaturedSet.t) : SelRel.t :=
    SOcsel.filterMap (fun '((nm, w), _) =>
        match nm, w with
        | NPlus.SlotN n v a, VPlus.VChoice u => Some (((n, v), a), u)
        | _, _ => None
        end)
      S.

  Lemma mem_decodeSel : forall S n v a u,
      SelRel.In (((n, v), a), u) (decodeSel S) <->
      exists fs, FC.Feat.FeaturedSet.In
        ((NPlus.SlotN n v a, VPlus.VChoice u), fs) S.
  Proof.
    intros S n v a u; unfold decodeSel; rewrite SOcsel.mem_filterMap.
    split.
    - intros [[[nm w] fs] [Hin He]]; cbn beta iota in He.
      destruct nm; try discriminate; destruct w; try discriminate.
      injection He as -> -> -> ->; exists fs; exact Hin.
    - intros [fs Hin].
      exists ((NPlus.SlotN n v a, VPlus.VChoice u), fs); split;
        [exact Hin | reflexivity].
  Qed.

  Theorem cargo_soundness :
    forall R support FDefs Slots Links g cfgActive dflt rc rootFeats
           (S_FC : FC.Feat.FeaturedSet.t) (pi : FC.ParentRel.t),
      AliasFunctional Slots ->
      FC.IsResolution (transReal R FDefs Slots Links cfgActive rc)
        (transSupport R support FDefs Slots cfgActive rc)
        (transDf R FDefs Slots Links cfgActive dflt rc rootFeats)
        (transDa R FDefs Slots cfgActive rc)
        (gPlus g) transRoot S_FC pi ->
      IsResolution R support FDefs Slots Links g cfgActive dflt rc
        rootFeats (decodeS S_FC) (decodeFS S_FC) (decodeSel S_FC).
  Proof.
    intros R support FDefs Slots Links g cfgActive dflt rc rootFeats
      S_FC pi Half Hfc.
    destruct rc as [rn rv].
    destruct Hfc as [Hnrs Hsub Hroot Hfu Hpc Hpca Hpif Hvg Hsm].
    assert (A1 : forall n v fs,
        FC.Feat.FeaturedSet.In ((NPlus.Crate n, VPlus.VOrig v), fs) S_FC ->
        PkgSet.In (n, v) R).
    { intros n v fs Hin.
      specialize (Hsub _ _ Hin); apply mem_transReal in Hsub.
      destruct Hsub as [He | [He | [He | [He | He]]]].
      - discriminate He.
      - apply mem_realBlock in He; destruct He as [n' [v' [HR He]]].
        injection He as -> ->; exact HR.
      - apply mem_slotBlock in He;
          destruct He as [? [? [? [? [_ [_ [_ He]]]]]]]; discriminate He.
      - apply mem_featdBlock in He;
          destruct He as
            [? [? [? [? [? [? [? [_ [_ [_ [_ [_ He]]]]]]]]]]]];
          destruct He as [He | [? [_ He]]]; discriminate He.
      - apply mem_linkBlock in He;
          destruct He as [? [? [? [_ [_ He]]]]]; discriminate He. }
    assert (A2 : forall n v a u fs,
        FC.Feat.FeaturedSet.In
          ((NPlus.SlotN n v a, VPlus.VChoice u), fs) S_FC ->
        exists d, SlotRel.In ((n, v), d) Slots /\ sAlias d = a /\
          slotActive cfgActive (rn, rv) (n, v) d = true /\
          VSet.In u (evalReq R (sTarget d) (sReq d))).
    { intros n v a u fs Hin.
      specialize (Hsub _ _ Hin); apply mem_transReal in Hsub.
      destruct Hsub as [He | [He | [He | [He | He]]]].
      - discriminate He.
      - apply mem_realBlock in He; destruct He as [? [? [_ He]]];
          discriminate He.
      - apply mem_slotBlock in He;
          destruct He as [n' [v' [d [u' [Hs [Ha [Hu He]]]]]]].
        injection He as En Ev Ea Eu; subst.
        exists d; repeat split; try assumption; reflexivity.
      - apply mem_featdBlock in He;
          destruct He as
            [? [? [? [? [? [? [? [_ [_ [_ [_ [_ He]]]]]]]]]]]];
          destruct He as [He | [? [_ He]]]; discriminate He.
      - apply mem_linkBlock in He;
          destruct He as [? [? [? [_ [_ He]]]]]; discriminate He. }
    assert (A4 : forall nm x x' fs fs',
        FC.Feat.FeaturedSet.In ((nm, x), fs) S_FC ->
        FC.Feat.FeaturedSet.In ((nm, x'), fs') S_FC ->
        gPlus g x = gPlus g x' -> x = x').
    { intros nm x x' fs fs' Hx Hx' Hg.
      destruct (VPOT.eq_dec x x') as [E | NE]; [exact E |].
      exfalso; exact (Hvg _ _ _ _ _ Hx Hx' NE Hg). }
    constructor.
    - (* res_subset *)
      intros [n v] Hp; apply mem_decodeS in Hp;
        destruct Hp as [fs Hp]; exact (A1 _ _ _ Hp).
    - (* res_root_mem *)
      assert (Hre : FC.Feat.FeatDepRel.In
          (transRoot,
           (NPlus.Crate rn,
            (FC.VSet.singleton (VPlus.VOrig rv), embedFS rootFeats)))
          (transDf R FDefs Slots Links cfgActive dflt (rn, rv)
             rootFeats)).
      { apply mem_transDf; left; apply mem_rootEdge; reflexivity. }
      destruct (Hpc _ _ Hroot _ _ _ Hre)
        as [x [[Hx [[fsx [Hsubx HxS]] Hpix]] _]].
      apply FC.VSet.singleton_spec in Hx; subst x.
      apply mem_decodeS; exists fsx; exact HxS.
    - (* res_root_feats *)
      intros fs Hfs; apply mem_decodeFS in Hfs;
        destruct Hfs as [fsP [HinP ->]].
      assert (Hre : FC.Feat.FeatDepRel.In
          (transRoot,
           (NPlus.Crate rn,
            (FC.VSet.singleton (VPlus.VOrig rv), embedFS rootFeats)))
          (transDf R FDefs Slots Links cfgActive dflt (rn, rv)
             rootFeats)).
      { apply mem_transDf; left; apply mem_rootEdge; reflexivity. }
      destruct (Hpc _ _ Hroot _ _ _ Hre)
        as [x [[Hx [[fsx [Hsubx HxS]] Hpix]] _]].
      apply FC.VSet.singleton_spec in Hx; subst x.
      rewrite (Hfu _ _ _ _ HinP HxS).
      apply embedFS_subset_strip; exact Hsubx.
    - (* res_fs_dom *)
      intros [n v] fs Hfs; apply mem_decodeFS in Hfs;
        destruct Hfs as [fsP [HinP _]].
      apply mem_decodeS; exists fsP; exact HinP.
    - (* res_fs_total *)
      intros [n v] Hp; apply mem_decodeS in Hp; destruct Hp as [fsP Hp].
      exists (stripFS fsP); apply mem_decodeFS; exists fsP; split;
        [exact Hp | reflexivity].
    - (* res_fs_functional *)
      intros [n v] fs fs' Hfs Hfs'.
      apply mem_decodeFS in Hfs; destruct Hfs as [fsP [HinP ->]].
      apply mem_decodeFS in Hfs'; destruct Hfs' as [fsP' [HinP' ->]].
      rewrite (Hfu _ _ _ _ HinP HinP'); reflexivity.
    - (* res_class_unique *)
      intros n v v' Hv Hv' NE Hg.
      apply mem_decodeS in Hv; destruct Hv as [fsP Hv].
      apply mem_decodeS in Hv'; destruct Hv' as [fsP' Hv'].
      assert (Hgp : gPlus g (VPlus.VOrig v) = gPlus g (VPlus.VOrig v'))
        by (cbn; rewrite Hg; reflexivity).
      specialize (A4 _ _ _ _ _ Hv Hv' Hgp).
      injection A4 as ->; contradiction NE; reflexivity.
    - (* res_support_mem *)
      intros [n v] fs f Hfs Hf.
      apply mem_decodeFS in Hfs; destruct Hfs as [fsP [HinP ->]].
      apply mem_stripFS in Hf.
      specialize (Hsm _ _ _ _ HinP Hf).
      apply mem_transSupport in Hsm.
      destruct Hsm as [[n' [v' [f' [Hsp He]]]] | Hbad].
      + injection He as -> -> ->; exact Hsp.
      + destruct Hbad as
          [? [? [? [? [? [? [? [_ [_ [_ [_ [_ He]]]]]]]]]]]];
          destruct He as [He | [? [_ He]]]; discriminate He.
    - (* res_sel_functional *)
      intros [n v] a u u' Hu Hu'.
      apply mem_decodeSel in Hu; destruct Hu as [fs Hu].
      apply mem_decodeSel in Hu'; destruct Hu' as [fs' Hu'].
      assert (Hg : gPlus g (VPlus.VChoice u) = gPlus g (VPlus.VChoice u'))
        by reflexivity.
      specialize (A4 _ _ _ _ _ Hu Hu' Hg).
      injection A4 as ->; reflexivity.
    - (* res_slot_closure *)
      intros [n v] fs Hp Hfs d Hd Hact Hopt.
      apply mem_decodeFS in Hfs; destruct Hfs as [fsP [HinP ->]].
      assert (Achain : forall u fsS,
          VSet.In u (evalReq R (sTarget d) (sReq d)) ->
          FC.Feat.FeaturedSet.In
            ((NPlus.SlotN n v (sAlias d), VPlus.VChoice u), fsS) S_FC ->
          exists u0,
            SelRel.In (((n, v), sAlias d), u0) (decodeSel S_FC) /\
            rgHolds (sReq d) u0 = true /\
            PkgSet.In (sTarget d, u0) (decodeS S_FC) /\
            forall fs', FeaturedSet.In ((sTarget d, u0), fs')
              (decodeFS S_FC) ->
            FSet.Subset (slotRequests d dflt) fs').
      { intros u fsS Hu HinS.
        assert (He2 : FC.Feat.FeatDepRel.In
            ((NPlus.SlotN n v (sAlias d), VPlus.VChoice u),
             (NPlus.Crate (sTarget d),
              (FC.VSet.singleton (VPlus.VOrig u),
               embedFS (slotRequests d dflt))))
            (transDf R FDefs Slots Links cfgActive dflt (rn, rv)
               rootFeats)).
        { apply mem_transDf; right; right; left; apply mem_slotHop2.
          exists n, v, d, u; repeat split; assumption. }
        destruct (Hpc _ _ HinS _ _ _ He2)
          as [y [[Hy [[fsy [Hsuby HyS]] Hpiy]] _]].
        apply FC.VSet.singleton_spec in Hy; subst y.
        exists u; repeat split.
        - apply mem_decodeSel; exists fsS; exact HinS.
        - apply mem_evalReq in Hu; exact (proj2 Hu).
        - apply mem_decodeS; exists fsy; exact HyS.
        - intros fs' Hfs'; apply mem_decodeFS in Hfs';
            destruct Hfs' as [fsP' [HinP' ->]].
          rewrite (Hfu _ _ _ _ HinP' HyS).
          apply embedFS_subset_strip; exact Hsuby. }
      destruct Hopt as [Hno | Hacted].
      + assert (He1 : FC.Feat.FeatDepRel.In
            ((NPlus.Crate n, VPlus.VOrig v),
             (NPlus.SlotN n v (sAlias d),
              (choicesOf R d, FC.Feat.FSet.empty)))
            (transDf R FDefs Slots Links cfgActive dflt (rn, rv)
               rootFeats)).
        { apply mem_transDf; right; left; apply mem_slotHop1.
          exists n, v, d; repeat split; assumption. }
        destruct (Hpc _ _ HinP _ _ _ He1)
          as [x [[Hx [[fsx [Hsubx HxS]] Hpix]] _]].
        unfold choicesOf in Hx; apply SOvv.mem_map in Hx;
          destruct Hx as [u [Hu ->]].
        exact (Achain _ _ Hu HxS).
      + destruct Hacted as [f [Hffs Hent]].
        apply mem_stripFS in Hffs.
        assert (Hea : exists e',
            FDefRel.In (((n, v), f), e') FDefs /\
            entryActivates e' = Some (sAlias d)).
        { destruct Hent as [He | [feat He]].
          - exists (FEntry.EDep (sAlias d)); split;
              [exact He | reflexivity].
          - exists (FEntry.EDepFeat (sAlias d) feat); split;
              [exact He | reflexivity]. }
        destruct Hea as [e' [He' Ea]].
        assert (Hga : FC.Feat.AddlDepRel.In
            (((NPlus.Crate n, VPlus.VOrig v), FPlusComp.FOrigF f),
             (NPlus.SlotN n v (sAlias d),
              (choicesOf R d, FC.Feat.FSet.empty)))
            (transDa R FDefs Slots cfgActive (rn, rv))).
        { apply mem_transDa; right; left; apply mem_activationEdges.
          exists n, v, f, e', (sAlias d), d; repeat split; assumption. }
        destruct (Hpca _ _ HinP _ Hffs _ _ _ Hga)
          as [x [[Hx [[fsx [Hsubx HxS]] Hpix]] _]].
        unfold choicesOf in Hx; apply SOvv.mem_map in Hx;
          destruct Hx as [u [Hu ->]].
        exact (Achain _ _ Hu HxS).
    - (* res_feat_closure_same *)
      intros [n v] fs f f' Hfs Hf He.
      apply mem_decodeFS in Hfs; destruct Hfs as [fsP [HinP ->]].
      apply mem_stripFS in Hf.
      assert (Hg : FC.Feat.AddlDepRel.In
          (((NPlus.Crate n, VPlus.VOrig v), FPlusComp.FOrigF f),
           (NPlus.Crate n,
            (FC.VSet.singleton (VPlus.VOrig v),
             FC.Feat.FSet.singleton (FPlusComp.FOrigF f'))))
          (transDa R FDefs Slots cfgActive (rn, rv))).
      { apply mem_transDa; left; apply mem_sameFeatEdges.
        exists n, v, f, f'; split; [exact He | reflexivity]. }
      destruct (Hpca _ _ HinP _ Hf _ _ _ Hg)
        as [x [[Hx [[fsx [Hsubx HxS]] Hpix]] _]].
      apply FC.VSet.singleton_spec in Hx; subst x.
      rewrite (Hfu _ _ _ _ HinP HxS).
      apply mem_stripFS, Hsubx, FC.Feat.FSet.singleton_spec; reflexivity.
    - (* res_feat_closure_dep *)
      intros [n v] fs f a feat Hfs Hf Hent d u Hd Halias Hsel fs' Hfs'.
      apply mem_decodeFS in Hfs; destruct Hfs as [fsP [HinP ->]].
      apply mem_stripFS in Hf.
      assert (He' : exists e', FDefRel.In (((n, v), f), e') FDefs /\
          entryFeatD e' = Some (a, feat)).
      { destruct Hent as [He | [He _]].
        - exists (FEntry.EDepFeat a feat); split; [exact He | reflexivity].
        - exists (FEntry.EWeakFeat a feat); split;
            [exact He | reflexivity]. }
      destruct He' as [e' [He' Ee]].
      apply mem_decodeSel in Hsel; destruct Hsel as [fsS HinS].
      destruct (A2 _ _ _ _ _ HinS) as [d0 [Hd0 [Ha0 [Hact0 Hu0]]]].
      assert (d0 = d) by (apply (Half (n, v)); congruence); subst d0.
      subst a.
      assert (Hwe : FC.Feat.AddlDepRel.In
          (((NPlus.Crate n, VPlus.VOrig v), FPlusComp.FOrigF f),
           (NPlus.DecisionN n v f (sAlias d) feat,
            (FC.VSet.add VPlus.VOff (firesOf R d),
             FC.Feat.FSet.singleton FPlusComp.FWit)))
          (transDa R FDefs Slots cfgActive (rn, rv))).
      { apply mem_transDa; right; right; left; apply mem_witEnableEdges.
        exists n, v, f, e', (sAlias d), feat, d; repeat split;
          assumption. }
      destruct (Hpca _ _ HinP _ Hf _ _ _ Hwe)
        as [w [[Hw [[fsw [Hsubw HwS]] Hpiw]] _]].
      assert (Hde : FC.Feat.FeatDepRel.In
          ((NPlus.SlotN n v (sAlias d), VPlus.VChoice u),
           (NPlus.DecisionN n v f (sAlias d) feat,
            (FC.VSet.singleton (VPlus.VFire u), FC.Feat.FSet.empty)))
          (transDf R FDefs Slots Links cfgActive dflt (rn, rv)
             rootFeats)).
      { apply mem_transDf; right; right; right; right;
          apply mem_decisionEdges.
        exists n, v, f, e', (sAlias d), feat, d, u; repeat split;
          assumption. }
      destruct (Hpc _ _ HinS _ _ _ Hde)
        as [y [[Hy [[fsy [Hsuby HyS]] Hpiy]] _]].
      apply FC.VSet.singleton_spec in Hy; subst y.
      assert (Hwg : gPlus g w = gPlus g (VPlus.VFire u)).
      { apply FC.VSet.add_spec in Hw.
        destruct Hw as [-> | Hw]; [reflexivity |].
        unfold firesOf in Hw; apply SOvv.mem_map in Hw;
          destruct Hw as [u' [_ ->]]; reflexivity. }
      specialize (A4 _ _ _ _ _ HwS HyS Hwg); subst w.
      assert (Hwd : FC.Feat.AddlDepRel.In
          (((NPlus.DecisionN n v f (sAlias d) feat, VPlus.VFire u),
            FPlusComp.FWit),
           (NPlus.Crate (sTarget d),
            (FC.VSet.singleton (VPlus.VOrig u),
             FC.Feat.FSet.singleton (FPlusComp.FOrigF feat))))
          (transDa R FDefs Slots cfgActive (rn, rv))).
      { apply mem_transDa; right; right; right;
          apply mem_witDeliverEdges.
        exists n, v, f, e', (sAlias d), feat, d, u; repeat split;
          assumption. }
      assert (HwitIn : FC.Feat.FSet.In FPlusComp.FWit fsw).
      { apply Hsubw, FC.Feat.FSet.singleton_spec; reflexivity. }
      destruct (Hpca _ _ HwS _ HwitIn _ _ _ Hwd)
        as [z [[Hz [[fsz [Hsubz HzS]] Hpiz]] _]].
      apply FC.VSet.singleton_spec in Hz; subst z.
      apply mem_decodeFS in Hfs'; destruct Hfs' as [fsP' [HinP' ->]].
      rewrite (Hfu _ _ _ _ HinP' HzS).
      apply mem_stripFS, Hsubz, FC.Feat.FSet.singleton_spec; reflexivity.
    - (* res_links_unique *)
      intros p q l Hp Hq Hlp Hlq.
      destruct p as [pn pv]; destruct q as [qn qv].
      apply mem_decodeS in Hp; destruct Hp as [fsp Hp].
      apply mem_decodeS in Hq; destruct Hq as [fsq Hq].
      assert (Hep : FC.Feat.FeatDepRel.In
          ((NPlus.Crate pn, VPlus.VOrig pv),
           (NPlus.LinkN l,
            (FC.VSet.singleton (VPlus.VMember (pn, pv)),
             FC.Feat.FSet.empty)))
          (transDf R FDefs Slots Links cfgActive dflt (rn, rv)
             rootFeats)).
      { apply mem_transDf; right; right; right; left; apply mem_linkEdges.
        exists pn, pv, l; repeat split;
          [exact Hlp | exact (A1 _ _ _ Hp)]. }
      assert (Heq : FC.Feat.FeatDepRel.In
          ((NPlus.Crate qn, VPlus.VOrig qv),
           (NPlus.LinkN l,
            (FC.VSet.singleton (VPlus.VMember (qn, qv)),
             FC.Feat.FSet.empty)))
          (transDf R FDefs Slots Links cfgActive dflt (rn, rv)
             rootFeats)).
      { apply mem_transDf; right; right; right; left; apply mem_linkEdges.
        exists qn, qv, l; repeat split;
          [exact Hlq | exact (A1 _ _ _ Hq)]. }
      destruct (Hpc _ _ Hp _ _ _ Hep)
        as [x [[Hx [[fsx [_ HxS]] _]] _]].
      destruct (Hpc _ _ Hq _ _ _ Heq)
        as [y [[Hy [[fsy [_ HyS]] _]] _]].
      apply FC.VSet.singleton_spec in Hx; subst x.
      apply FC.VSet.singleton_spec in Hy; subst y.
      assert (Hg : gPlus g (VPlus.VMember (pn, pv)) =
                   gPlus g (VPlus.VMember (qn, qv))) by reflexivity.
      specialize (A4 _ _ _ _ _ HxS HyS Hg).
      injection A4 as -> ->; reflexivity.
  Qed.

  Definition activatedb (FDefs : FDefRel.t) (fs : FSet.t) (p : Pkg.t)
      (a : N.t) : bool :=
    FDefRel.exists_ (fun '((q, f), e) =>
        andb (PkgEqb.eqb q p)
          (andb (FSet.mem f fs)
             (match entryActivates e with
              | Some a' => NEqb.eqb a' a
              | None => false
              end)))
      FDefs.

  Lemma activatedb_iff : forall FDefs fs p a,
      activatedb FDefs fs p a = true <-> Activated FDefs fs p a.
  Proof.
    intros FDefs fs p a; unfold activatedb, Activated.
    rewrite FDefRel.exists_spec'.
    split.
    - intros [[[q f] e] [He Hb]]; cbn beta iota in Hb.
      apply andb_true_iff in Hb; destruct Hb as [Hq Hb].
      apply andb_true_iff in Hb; destruct Hb as [Hf Ha].
      apply PkgEqb.eqb_true_iff in Hq; subst q.
      apply FSet.mem_spec in Hf.
      destruct e; cbn in Ha; try discriminate;
        apply NEqb.eqb_true_iff in Ha; subst a.
      + exists f; split; [exact Hf | left; exact He].
      + exists f; split; [exact Hf | right; eexists; exact He].
    - intros [f [Hf [He | [feat He]]]].
      + exists ((p, f), FEntry.EDep a); split; [exact He |].
        cbn beta iota; rewrite PkgEqb.eqb_refl; cbn.
        apply FSet.mem_spec in Hf; rewrite Hf; cbn.
        rewrite NEqb.eqb_refl; reflexivity.
      + exists ((p, f), FEntry.EDepFeat a feat); split; [exact He |].
        cbn beta iota; rewrite PkgEqb.eqb_refl; cbn.
        apply FSet.mem_spec in Hf; rewrite Hf; cbn.
        rewrite NEqb.eqb_refl; reflexivity.
  Qed.

  Definition requiredb (FDefs : FDefRel.t) (fs : FSet.t) (p : Pkg.t)
      (d : SlotData.t) : bool :=
    orb (negb (sOptional d)) (activatedb FDefs fs p (sAlias d)).

  Lemma requiredb_iff : forall FDefs fs p d,
      requiredb FDefs fs p d = true <->
      sOptional d = false \/ Activated FDefs fs p (sAlias d).
  Proof.
    intros FDefs fs p d; unfold requiredb.
    rewrite orb_true_iff, negb_true_iff, activatedb_iff; tauto.
  Qed.

  (* The unique feature set FS assigns to p; total via a default so the
     witness stays computable, pinned by fs_functional in proofs. *)
  Definition fsAt (FS : FeaturedSet.t) (p : Pkg.t) : FSet.t :=
    match FeaturedSet.choose
            (FeaturedSet.filter (fun '(q, _) => PkgEqb.eqb q p) FS)
    with
    | Some (_, fs) => fs
    | None => FSet.empty
    end.

  Lemma fsAt_in : forall FS p fs,
      (forall q fs1 fs2, FeaturedSet.In (q, fs1) FS ->
         FeaturedSet.In (q, fs2) FS -> fs1 = fs2) ->
      FeaturedSet.In (p, fs) FS -> fsAt FS p = fs.
  Proof.
    intros FS p fs Hfun Hin; unfold fsAt.
    destruct (FeaturedSet.choose
                (FeaturedSet.filter (fun '(q, _) => PkgEqb.eqb q p) FS))
      as [[q fs'] |] eqn:Hc.
    - apply FeaturedSet.choose_spec1 in Hc.
      apply FeaturedSet.filter_spec' in Hc; destruct Hc as [Hc Hq].
      apply PkgEqb.eqb_true_iff in Hq; subst q.
      exact (Hfun _ _ _ Hc Hin).
    - exfalso; apply FeaturedSet.choose_spec2 in Hc.
      apply (Hc (p, fs)).
      apply FeaturedSet.filter_spec'; split;
        [exact Hin | apply PkgEqb.eqb_refl].
  Qed.

  (* Whether the choice node at (q, a) is selected: q resolved and some
     active slot under alias a is required (non-optional or activated). *)
  Definition selectsb (FDefs : FDefRel.t) (Slots : SlotRel.t)
      (cfgActive : CfgS.t -> bool) (rc : Pkg.t)
      (S : PkgSet.t) (FS : FeaturedSet.t) (q : Pkg.t) (a : N.t) : bool :=
    andb (PkgSet.mem q S)
      (SlotRel.exists_ (fun '(q', d) =>
           andb (PkgEqb.eqb q' q)
             (andb (NEqb.eqb (sAlias d) a)
                (andb (slotActive cfgActive rc q' d)
                   (requiredb FDefs (fsAt FS q) q d))))
         Slots).

  Lemma selectsb_iff : forall FDefs Slots cfgActive rc S FS q a,
      selectsb FDefs Slots cfgActive rc S FS q a = true <->
      PkgSet.In q S /\
      exists d, SlotRel.In (q, d) Slots /\ sAlias d = a /\
        slotActive cfgActive rc q d = true /\
        (sOptional d = false \/
         Activated FDefs (fsAt FS q) q (sAlias d)).
  Proof.
    intros FDefs Slots cfgActive rc S FS q a; unfold selectsb.
    rewrite andb_true_iff, PkgSet.mem_spec, SlotRel.exists_spec'.
    split.
    - intros [HS [[q' d] [Hd Hb]]]; cbn beta iota in Hb.
      apply andb_true_iff in Hb; destruct Hb as [Hq Hb].
      apply andb_true_iff in Hb; destruct Hb as [Ha Hb].
      apply andb_true_iff in Hb; destruct Hb as [Hact Hreq].
      apply PkgEqb.eqb_true_iff in Hq; subst q'.
      apply NEqb.eqb_true_iff in Ha.
      apply requiredb_iff in Hreq.
      rewrite Ha in Hreq.
      split; [exact HS |].
      exists d; repeat split; try assumption.
      rewrite <- Ha in Hreq; exact Hreq.
    - intros [HS [d [Hd [Ha [Hact Hreq]]]]].
      split; [exact HS |].
      exists (q, d); split; [exact Hd | cbn beta iota].
      rewrite PkgEqb.eqb_refl; cbn.
      subst a; rewrite NEqb.eqb_refl; cbn.
      rewrite Hact; cbn.
      apply requiredb_iff in Hreq; rewrite Hreq; reflexivity.
  Qed.

  Definition hasActiveSlotb (Slots : SlotRel.t)
      (cfgActive : CfgS.t -> bool) (rc : Pkg.t) (q : Pkg.t) (a : N.t)
    : bool :=
    SlotRel.exists_ (fun '(q', d) =>
        andb (PkgEqb.eqb q' q)
          (andb (NEqb.eqb (sAlias d) a)
             (slotActive cfgActive rc q' d)))
      Slots.

  Lemma hasActiveSlotb_iff : forall Slots cfgActive rc q a,
      hasActiveSlotb Slots cfgActive rc q a = true <->
      exists d, SlotRel.In (q, d) Slots /\ sAlias d = a /\
        slotActive cfgActive rc q d = true.
  Proof.
    intros Slots cfgActive rc q a; unfold hasActiveSlotb.
    rewrite SlotRel.exists_spec'.
    split.
    - intros [[q' d] [Hd Hb]]; cbn beta iota in Hb.
      apply andb_true_iff in Hb; destruct Hb as [Hq Hb].
      apply andb_true_iff in Hb; destruct Hb as [Ha Hact].
      apply PkgEqb.eqb_true_iff in Hq; subst q'.
      apply NEqb.eqb_true_iff in Ha.
      exists d; repeat split; assumption.
    - intros [d [Hd [Ha Hact]]].
      exists (q, d); split; [exact Hd | cbn beta iota].
      rewrite PkgEqb.eqb_refl; cbn.
      subst a; rewrite NEqb.eqb_refl; cbn; exact Hact.
  Qed.

  (* -- the completeness witness: the FC featured resolution and parent
     relation a Cargo resolution induces -- *)

  Module SOfw := SetOps Featured FC.Feat.Featured FeaturedSet
    FC.Feat.FeaturedSet.
  Definition wCrates (FS : FeaturedSet.t) : FC.Feat.FeaturedSet.t :=
    SOfw.map (fun '((n, v), fs) =>
        ((NPlus.Crate n, VPlus.VOrig v), embedFS fs)) FS.

  Module SOselw := SetOps SelElt FC.Feat.Featured SelRel
    FC.Feat.FeaturedSet.
  Definition wChoices (FDefs : FDefRel.t) (Slots : SlotRel.t)
      (cfgActive : CfgS.t -> bool) (rc : Pkg.t) (S : PkgSet.t)
      (FS : FeaturedSet.t) (sel : SelRel.t) : FC.Feat.FeaturedSet.t :=
    SOselw.filterMap (fun '(((n, v), a), u) =>
        if selectsb FDefs Slots cfgActive rc S FS (n, v) a
        then Some ((NPlus.SlotN n v a, VPlus.VChoice u),
                   FC.Feat.FSet.empty)
        else None)
      sel.

  Module SOfdw := SetOps FDefElt FC.Feat.Featured FDefRel
    FC.Feat.FeaturedSet.
  Definition wFires (FDefs : FDefRel.t) (Slots : SlotRel.t)
      (cfgActive : CfgS.t -> bool) (rc : Pkg.t) (S : PkgSet.t)
      (FS : FeaturedSet.t) (sel : SelRel.t) : FC.Feat.FeaturedSet.t :=
    SOselw.unionMap (fun '(((n, v), a), u) =>
        if selectsb FDefs Slots cfgActive rc S FS (n, v) a
        then SOfdw.filterMap (fun '((q, f), e) =>
               match entryFeatD e with
               | Some (a', feat) =>
                   if andb (PkgEqb.eqb q (n, v)) (NEqb.eqb a' a)
                   then Some
                          ((NPlus.DecisionN n v f a' feat, VPlus.VFire u),
                           if FSet.mem f (fsAt FS (n, v))
                           then FC.Feat.FSet.singleton FPlusComp.FWit
                           else FC.Feat.FSet.empty)
                   else None
               | None => None
               end)
             FDefs
        else FC.Feat.FeaturedSet.empty)
      sel.

  Definition wOffs (FDefs : FDefRel.t) (Slots : SlotRel.t)
      (cfgActive : CfgS.t -> bool) (rc : Pkg.t) (S : PkgSet.t)
      (FS : FeaturedSet.t) : FC.Feat.FeaturedSet.t :=
    SOfdw.filterMap (fun '(((n0, v0), f), e) =>
        match entryFeatD e with
        | Some (a, feat) =>
            if andb (PkgSet.mem (n0, v0) S)
                 (andb (FSet.mem f (fsAt FS (n0, v0)))
                    (andb (hasActiveSlotb Slots cfgActive rc (n0, v0) a)
                       (negb (selectsb FDefs Slots cfgActive rc S FS
                                (n0, v0) a))))
            then Some ((NPlus.DecisionN n0 v0 f a feat, VPlus.VOff),
                       FC.Feat.FSet.singleton FPlusComp.FWit)
            else None
        | None => None
        end)
      FDefs.

  Module SOlw := SetOps LinkElt FC.Feat.Featured LinkRel
    FC.Feat.FeaturedSet.
  Definition wLinks (S : PkgSet.t) (Links : LinkRel.t)
    : FC.Feat.FeaturedSet.t :=
    SOlw.filterMap (fun '(p, l) =>
        if PkgSet.mem p S
        then Some ((NPlus.LinkN l, VPlus.VMember p), FC.Feat.FSet.empty)
        else None)
      Links.

  Definition fcResolution (FDefs : FDefRel.t) (Slots : SlotRel.t)
      (Links : LinkRel.t) (cfgActive : CfgS.t -> bool) (rc : Pkg.t)
      (S : PkgSet.t) (FS : FeaturedSet.t) (sel : SelRel.t)
    : FC.Feat.FeaturedSet.t :=
    FC.Feat.FeaturedSet.add (transRoot, FC.Feat.FSet.empty)
      (FC.Feat.FeaturedSet.union (wCrates FS)
         (FC.Feat.FeaturedSet.union
            (wChoices FDefs Slots cfgActive rc S FS sel)
            (FC.Feat.FeaturedSet.union
               (wFires FDefs Slots cfgActive rc S FS sel)
               (FC.Feat.FeaturedSet.union
                  (wOffs FDefs Slots cfgActive rc S FS)
                  (wLinks S Links))))).

  Lemma mem_wCrates : forall FS y,
      FC.Feat.FeaturedSet.In y (wCrates FS) <->
      exists n v fs, FeaturedSet.In ((n, v), fs) FS /\
        y = ((NPlus.Crate n, VPlus.VOrig v), embedFS fs).
  Proof.
    intros FS y; unfold wCrates; rewrite SOfw.mem_map.
    split.
    - intros [[[n v] fs] [Hin ->]]; eauto 6.
    - intros [n [v [fs [Hin ->]]]]; exists ((n, v), fs); auto.
  Qed.

  Lemma mem_wChoices : forall FDefs Slots cfgActive rc S FS sel y,
      FC.Feat.FeaturedSet.In y
        (wChoices FDefs Slots cfgActive rc S FS sel) <->
      exists n v a u, SelRel.In (((n, v), a), u) sel /\
        selectsb FDefs Slots cfgActive rc S FS (n, v) a = true /\
        y = ((NPlus.SlotN n v a, VPlus.VChoice u), FC.Feat.FSet.empty).
  Proof.
    intros FDefs Slots cfgActive rc S FS sel y; unfold wChoices.
    rewrite SOselw.mem_filterMap.
    split.
    - intros [[[[n v] a] u] [Hin He]]; cbn beta iota in He.
      destruct (selectsb FDefs Slots cfgActive rc S FS (n, v) a)
        eqn:Hsel; [| discriminate].
      injection He as <-.
      exists n, v, a, u; repeat split; assumption.
    - intros [n [v [a [u [Hin [Hsel ->]]]]]].
      exists (((n, v), a), u); split; [exact Hin | cbn beta iota].
      rewrite Hsel; reflexivity.
  Qed.

  Lemma mem_wFires : forall FDefs Slots cfgActive rc S FS sel y,
      FC.Feat.FeaturedSet.In y
        (wFires FDefs Slots cfgActive rc S FS sel) <->
      exists n v a u f e feat,
        SelRel.In (((n, v), a), u) sel /\
        selectsb FDefs Slots cfgActive rc S FS (n, v) a = true /\
        FDefRel.In (((n, v), f), e) FDefs /\
        entryFeatD e = Some (a, feat) /\
        y = ((NPlus.DecisionN n v f a feat, VPlus.VFire u),
             if FSet.mem f (fsAt FS (n, v))
             then FC.Feat.FSet.singleton FPlusComp.FWit
             else FC.Feat.FSet.empty).
  Proof.
    intros FDefs Slots cfgActive rc S FS sel y; unfold wFires.
    rewrite SOselw.mem_unionMap.
    split.
    - intros [[[[n v] a] u] [Hin Hy]]; cbn beta iota in Hy.
      destruct (selectsb FDefs Slots cfgActive rc S FS (n, v) a)
        eqn:Hsel; [| exfalso; exact (SOfdw.empty_in _ Hy)].
      apply SOfdw.mem_filterMap in Hy.
      destruct Hy as [[[q f] e] [Hf He]]; cbn beta iota in He.
      destruct (entryFeatD e) as [[a' feat] |] eqn:Hd; [| discriminate].
      destruct (andb (PkgEqb.eqb q (n, v)) (NEqb.eqb a' a)) eqn:Hg;
        [| discriminate].
      apply andb_true_iff in Hg; destruct Hg as [Hq Ha].
      apply PkgEqb.eqb_true_iff in Hq; subst q.
      apply NEqb.eqb_true_iff in Ha; subst a'.
      injection He as <-.
      exists n, v, a, u, f, e, feat; repeat split; assumption.
    - intros [n [v [a [u [f [e [feat [Hin [Hsel [Hf [Hd ->]]]]]]]]]]].
      exists (((n, v), a), u); split; [exact Hin | cbn beta iota].
      rewrite Hsel.
      apply SOfdw.mem_filterMap; exists (((n, v), f), e).
      split; [exact Hf | cbn beta iota].
      rewrite Hd, PkgEqb.eqb_refl, NEqb.eqb_refl; reflexivity.
  Qed.

  Lemma mem_wOffs : forall FDefs Slots cfgActive rc S FS y,
      FC.Feat.FeaturedSet.In y (wOffs FDefs Slots cfgActive rc S FS) <->
      exists n0 v0 f e a feat,
        FDefRel.In (((n0, v0), f), e) FDefs /\
        entryFeatD e = Some (a, feat) /\
        PkgSet.In (n0, v0) S /\
        FSet.In f (fsAt FS (n0, v0)) /\
        hasActiveSlotb Slots cfgActive rc (n0, v0) a = true /\
        selectsb FDefs Slots cfgActive rc S FS (n0, v0) a = false /\
        y = ((NPlus.DecisionN n0 v0 f a feat, VPlus.VOff),
             FC.Feat.FSet.singleton FPlusComp.FWit).
  Proof.
    intros FDefs Slots cfgActive rc S FS y; unfold wOffs.
    rewrite SOfdw.mem_filterMap.
    split.
    - intros [[[[n0 v0] f] e] [Hf He]]; cbn beta iota in He.
      destruct (entryFeatD e) as [[a feat] |] eqn:Hd; [| discriminate].
      destruct (andb (PkgSet.mem (n0, v0) S) _) eqn:Hg in He;
        [| discriminate].
      injection He as <-.
      apply andb_true_iff in Hg; destruct Hg as [HS Hg].
      apply andb_true_iff in Hg; destruct Hg as [Hfs Hg].
      apply andb_true_iff in Hg; destruct Hg as [Hslot Hns].
      apply negb_true_iff in Hns.
      apply PkgSet.mem_spec in HS.
      apply FSet.mem_spec in Hfs.
      exists n0, v0, f, e, a, feat; repeat split; assumption.
    - intros [n0 [v0 [f [e [a [feat
        [Hf [Hd [HS [Hfs [Hslot [Hns ->]]]]]]]]]]]].
      exists (((n0, v0), f), e); split; [exact Hf | cbn beta iota].
      rewrite Hd.
      apply PkgSet.mem_spec in HS; rewrite HS.
      apply FSet.mem_spec in Hfs; rewrite Hfs.
      rewrite Hslot, Hns; reflexivity.
  Qed.

  Lemma mem_wLinks : forall S Links y,
      FC.Feat.FeaturedSet.In y (wLinks S Links) <->
      exists p l, LinkRel.In (p, l) Links /\ PkgSet.In p S /\
        y = ((NPlus.LinkN l, VPlus.VMember p), FC.Feat.FSet.empty).
  Proof.
    intros S Links y; unfold wLinks; rewrite SOlw.mem_filterMap.
    split.
    - intros [[p l] [Hin He]]; cbn beta iota in He.
      destruct (PkgSet.mem p S) eqn:HS; [| discriminate].
      injection He as <-.
      apply PkgSet.mem_spec in HS.
      exists p, l; repeat split; assumption.
    - intros [p [l [Hin [HS ->]]]].
      exists (p, l); split; [exact Hin | cbn beta iota].
      apply PkgSet.mem_spec in HS; rewrite HS; reflexivity.
  Qed.

  Lemma mem_fcResolution : forall FDefs Slots Links cfgActive rc S FS sel y,
      FC.Feat.FeaturedSet.In y
        (fcResolution FDefs Slots Links cfgActive rc S FS sel) <->
      y = (transRoot, FC.Feat.FSet.empty) \/
      FC.Feat.FeaturedSet.In y (wCrates FS) \/
      FC.Feat.FeaturedSet.In y
        (wChoices FDefs Slots cfgActive rc S FS sel) \/
      FC.Feat.FeaturedSet.In y
        (wFires FDefs Slots cfgActive rc S FS sel) \/
      FC.Feat.FeaturedSet.In y (wOffs FDefs Slots cfgActive rc S FS) \/
      FC.Feat.FeaturedSet.In y (wLinks S Links).
  Proof.
    intros; unfold fcResolution.
    rewrite FC.Feat.FeaturedSet.add_spec,
      !FC.Feat.FeaturedSet.union_spec; tauto.
  Qed.

  Module SOselr := SetOps SelElt FC.ParentElt SelRel FC.ParentRel.
  Module SOslr := SetOps SlotElt FC.ParentElt SlotRel FC.ParentRel.
  Module SOfdr := SetOps FDefElt FC.ParentElt FDefRel FC.ParentRel.
  Module SOlr := SetOps LinkElt FC.ParentElt LinkRel FC.ParentRel.
  Module SOpr := SetOps Pkg FC.ParentElt PkgSet FC.ParentRel.

  Definition piChoices (FDefs : FDefRel.t) (Slots : SlotRel.t)
      (cfgActive : CfgS.t -> bool) (rc : Pkg.t) (S : PkgSet.t)
      (FS : FeaturedSet.t) (sel : SelRel.t) : FC.ParentRel.t :=
    SOselr.filterMap (fun '(((n, v), a), u) =>
        if selectsb FDefs Slots cfgActive rc S FS (n, v) a
        then Some ((NPlus.SlotN n v a, VPlus.VChoice u),
                   (NPlus.Crate n, VPlus.VOrig v))
        else None)
      sel.

  Definition piHops (FDefs : FDefRel.t) (Slots : SlotRel.t)
      (cfgActive : CfgS.t -> bool) (rc : Pkg.t) (S : PkgSet.t)
      (FS : FeaturedSet.t) (sel : SelRel.t) : FC.ParentRel.t :=
    SOselr.unionMap (fun '(((n, v), a), u) =>
        if selectsb FDefs Slots cfgActive rc S FS (n, v) a
        then SOslr.filterMap (fun '(q', d) =>
               if andb (PkgEqb.eqb q' (n, v))
                    (andb (NEqb.eqb (sAlias d) a)
                       (slotActive cfgActive rc q' d))
               then Some ((NPlus.Crate (sTarget d), VPlus.VOrig u),
                          (NPlus.SlotN n v a, VPlus.VChoice u))
               else None)
             Slots
        else FC.ParentRel.empty)
      sel.

  Definition piDecides (FDefs : FDefRel.t) (Slots : SlotRel.t)
      (cfgActive : CfgS.t -> bool) (rc : Pkg.t) (S : PkgSet.t)
      (FS : FeaturedSet.t) (sel : SelRel.t) : FC.ParentRel.t :=
    SOselr.unionMap (fun '(((n, v), a), u) =>
        if selectsb FDefs Slots cfgActive rc S FS (n, v) a
        then SOfdr.filterMap (fun '((q, f), e) =>
               match entryFeatD e with
               | Some (a', feat) =>
                   if andb (PkgEqb.eqb q (n, v)) (NEqb.eqb a' a)
                   then Some
                          ((NPlus.DecisionN n v f a' feat, VPlus.VFire u),
                           (NPlus.SlotN n v a, VPlus.VChoice u))
                   else None
               | None => None
               end)
             FDefs
        else FC.ParentRel.empty)
      sel.

  Definition piEnablesF (FDefs : FDefRel.t) (Slots : SlotRel.t)
      (cfgActive : CfgS.t -> bool) (rc : Pkg.t) (S : PkgSet.t)
      (FS : FeaturedSet.t) (sel : SelRel.t) : FC.ParentRel.t :=
    SOselr.unionMap (fun '(((n, v), a), u) =>
        if selectsb FDefs Slots cfgActive rc S FS (n, v) a
        then SOfdr.filterMap (fun '((q, f), e) =>
               match entryFeatD e with
               | Some (a', feat) =>
                   if andb (PkgEqb.eqb q (n, v)) (NEqb.eqb a' a)
                   then Some
                          ((NPlus.DecisionN n v f a' feat, VPlus.VFire u),
                           (NPlus.Crate n, VPlus.VOrig v))
                   else None
               | None => None
               end)
             FDefs
        else FC.ParentRel.empty)
      sel.

  Definition piEnablesN (FDefs : FDefRel.t) (Slots : SlotRel.t)
      (cfgActive : CfgS.t -> bool) (rc : Pkg.t) (S : PkgSet.t)
      (FS : FeaturedSet.t) : FC.ParentRel.t :=
    SOfdr.filterMap (fun '(((n0, v0), f), e) =>
        match entryFeatD e with
        | Some (a, feat) =>
            if andb (PkgSet.mem (n0, v0) S)
                 (andb (FSet.mem f (fsAt FS (n0, v0)))
                    (andb (hasActiveSlotb Slots cfgActive rc (n0, v0) a)
                       (negb (selectsb FDefs Slots cfgActive rc S FS
                                (n0, v0) a))))
            then Some ((NPlus.DecisionN n0 v0 f a feat, VPlus.VOff),
                       (NPlus.Crate n0, VPlus.VOrig v0))
            else None
        | None => None
        end)
      FDefs.

  Definition piDelivers (FDefs : FDefRel.t) (Slots : SlotRel.t)
      (cfgActive : CfgS.t -> bool) (rc : Pkg.t) (S : PkgSet.t)
      (FS : FeaturedSet.t) (sel : SelRel.t) : FC.ParentRel.t :=
    SOselr.unionMap (fun '(((n, v), a), u) =>
        if selectsb FDefs Slots cfgActive rc S FS (n, v) a
        then SOfdr.unionMap (fun '((q, f), e) =>
               match entryFeatD e with
               | Some (a', feat) =>
                   if andb (PkgEqb.eqb q (n, v)) (NEqb.eqb a' a)
                   then SOslr.filterMap (fun '(q', d) =>
                          if andb (PkgEqb.eqb q' (n, v))
                               (andb (NEqb.eqb (sAlias d) a)
                                  (slotActive cfgActive rc q' d))
                          then Some
                                 ((NPlus.Crate (sTarget d),
                                   VPlus.VOrig u),
                                  (NPlus.DecisionN n v f a' feat,
                                   VPlus.VFire u))
                          else None)
                        Slots
                   else FC.ParentRel.empty
               | None => FC.ParentRel.empty
               end)
             FDefs
        else FC.ParentRel.empty)
      sel.

  Definition piLinks (S : PkgSet.t) (Links : LinkRel.t)
    : FC.ParentRel.t :=
    SOlr.filterMap (fun '(p, l) =>
        if PkgSet.mem p S
        then Some ((NPlus.LinkN l, VPlus.VMember p),
                   (NPlus.Crate (fst p), VPlus.VOrig (snd p)))
        else None)
      Links.

  Definition piSelves (S : PkgSet.t) : FC.ParentRel.t :=
    SOpr.map (fun '(n, v) =>
        ((NPlus.Crate n, VPlus.VOrig v), (NPlus.Crate n, VPlus.VOrig v)))
      S.

  Lemma mem_piChoices : forall FDefs Slots cfgActive rc S FS sel y,
      FC.ParentRel.In y (piChoices FDefs Slots cfgActive rc S FS sel) <->
      exists n v a u, SelRel.In (((n, v), a), u) sel /\
        selectsb FDefs Slots cfgActive rc S FS (n, v) a = true /\
        y = ((NPlus.SlotN n v a, VPlus.VChoice u),
             (NPlus.Crate n, VPlus.VOrig v)).
  Proof.
    intros FDefs Slots cfgActive rc S FS sel y; unfold piChoices.
    rewrite SOselr.mem_filterMap.
    split.
    - intros [[[[n v] a] u] [Hin He]]; cbn beta iota in He.
      destruct (selectsb FDefs Slots cfgActive rc S FS (n, v) a)
        eqn:Hsel; [| discriminate].
      injection He as <-.
      exists n, v, a, u; repeat split; assumption.
    - intros [n [v [a [u [Hin [Hsel ->]]]]]].
      exists (((n, v), a), u); split; [exact Hin | cbn beta iota].
      rewrite Hsel; reflexivity.
  Qed.

  Lemma mem_piHops : forall FDefs Slots cfgActive rc S FS sel y,
      FC.ParentRel.In y (piHops FDefs Slots cfgActive rc S FS sel) <->
      exists n v a u d, SelRel.In (((n, v), a), u) sel /\
        selectsb FDefs Slots cfgActive rc S FS (n, v) a = true /\
        SlotRel.In ((n, v), d) Slots /\ sAlias d = a /\
        slotActive cfgActive rc (n, v) d = true /\
        y = ((NPlus.Crate (sTarget d), VPlus.VOrig u),
             (NPlus.SlotN n v a, VPlus.VChoice u)).
  Proof.
    intros FDefs Slots cfgActive rc S FS sel y; unfold piHops.
    rewrite SOselr.mem_unionMap.
    split.
    - intros [[[[n v] a] u] [Hin Hy]]; cbn beta iota in Hy.
      destruct (selectsb FDefs Slots cfgActive rc S FS (n, v) a)
        eqn:Hsel; [| exfalso; exact (SOslr.empty_in _ Hy)].
      apply SOslr.mem_filterMap in Hy.
      destruct Hy as [[q' d] [Hd He]]; cbn beta iota in He.
      destruct (andb (PkgEqb.eqb q' (n, v)) _) eqn:Hg in He;
        [| discriminate].
      injection He as <-.
      apply andb_true_iff in Hg; destruct Hg as [Hq Hg].
      apply andb_true_iff in Hg; destruct Hg as [Ha Hact].
      apply PkgEqb.eqb_true_iff in Hq; subst q'.
      apply NEqb.eqb_true_iff in Ha.
      exists n, v, a, u, d; repeat split; assumption.
    - intros [n [v [a [u [d [Hin [Hsel [Hd [Ha [Hact ->]]]]]]]]]].
      exists (((n, v), a), u); split; [exact Hin | cbn beta iota].
      rewrite Hsel.
      apply SOslr.mem_filterMap; exists ((n, v), d).
      split; [exact Hd | cbn beta iota].
      rewrite PkgEqb.eqb_refl; cbn.
      subst a; rewrite NEqb.eqb_refl; cbn.
      rewrite Hact; reflexivity.
  Qed.

  Lemma mem_piDecides : forall FDefs Slots cfgActive rc S FS sel y,
      FC.ParentRel.In y (piDecides FDefs Slots cfgActive rc S FS sel) <->
      exists n v a u f e feat,
        SelRel.In (((n, v), a), u) sel /\
        selectsb FDefs Slots cfgActive rc S FS (n, v) a = true /\
        FDefRel.In (((n, v), f), e) FDefs /\
        entryFeatD e = Some (a, feat) /\
        y = ((NPlus.DecisionN n v f a feat, VPlus.VFire u),
             (NPlus.SlotN n v a, VPlus.VChoice u)).
  Proof.
    intros FDefs Slots cfgActive rc S FS sel y; unfold piDecides.
    rewrite SOselr.mem_unionMap.
    split.
    - intros [[[[n v] a] u] [Hin Hy]]; cbn beta iota in Hy.
      destruct (selectsb FDefs Slots cfgActive rc S FS (n, v) a)
        eqn:Hsel; [| exfalso; exact (SOfdr.empty_in _ Hy)].
      apply SOfdr.mem_filterMap in Hy.
      destruct Hy as [[[q f] e] [Hf He]]; cbn beta iota in He.
      destruct (entryFeatD e) as [[a' feat] |] eqn:Hd; [| discriminate].
      destruct (andb (PkgEqb.eqb q (n, v)) (NEqb.eqb a' a)) eqn:Hg;
        [| discriminate].
      apply andb_true_iff in Hg; destruct Hg as [Hq Ha].
      apply PkgEqb.eqb_true_iff in Hq; subst q.
      apply NEqb.eqb_true_iff in Ha; subst a'.
      injection He as <-.
      exists n, v, a, u, f, e, feat; repeat split; assumption.
    - intros [n [v [a [u [f [e [feat [Hin [Hsel [Hf [Hd ->]]]]]]]]]]].
      exists (((n, v), a), u); split; [exact Hin | cbn beta iota].
      rewrite Hsel.
      apply SOfdr.mem_filterMap; exists (((n, v), f), e).
      split; [exact Hf | cbn beta iota].
      rewrite Hd, PkgEqb.eqb_refl, NEqb.eqb_refl; reflexivity.
  Qed.

  Lemma mem_piEnablesF : forall FDefs Slots cfgActive rc S FS sel y,
      FC.ParentRel.In y (piEnablesF FDefs Slots cfgActive rc S FS sel) <->
      exists n v a u f e feat,
        SelRel.In (((n, v), a), u) sel /\
        selectsb FDefs Slots cfgActive rc S FS (n, v) a = true /\
        FDefRel.In (((n, v), f), e) FDefs /\
        entryFeatD e = Some (a, feat) /\
        y = ((NPlus.DecisionN n v f a feat, VPlus.VFire u),
             (NPlus.Crate n, VPlus.VOrig v)).
  Proof.
    intros FDefs Slots cfgActive rc S FS sel y; unfold piEnablesF.
    rewrite SOselr.mem_unionMap.
    split.
    - intros [[[[n v] a] u] [Hin Hy]]; cbn beta iota in Hy.
      destruct (selectsb FDefs Slots cfgActive rc S FS (n, v) a)
        eqn:Hsel; [| exfalso; exact (SOfdr.empty_in _ Hy)].
      apply SOfdr.mem_filterMap in Hy.
      destruct Hy as [[[q f] e] [Hf He]]; cbn beta iota in He.
      destruct (entryFeatD e) as [[a' feat] |] eqn:Hd; [| discriminate].
      destruct (andb (PkgEqb.eqb q (n, v)) (NEqb.eqb a' a)) eqn:Hg;
        [| discriminate].
      apply andb_true_iff in Hg; destruct Hg as [Hq Ha].
      apply PkgEqb.eqb_true_iff in Hq; subst q.
      apply NEqb.eqb_true_iff in Ha; subst a'.
      injection He as <-.
      exists n, v, a, u, f, e, feat; repeat split; assumption.
    - intros [n [v [a [u [f [e [feat [Hin [Hsel [Hf [Hd ->]]]]]]]]]]].
      exists (((n, v), a), u); split; [exact Hin | cbn beta iota].
      rewrite Hsel.
      apply SOfdr.mem_filterMap; exists (((n, v), f), e).
      split; [exact Hf | cbn beta iota].
      rewrite Hd, PkgEqb.eqb_refl, NEqb.eqb_refl; reflexivity.
  Qed.

  Lemma mem_piEnablesN : forall FDefs Slots cfgActive rc S FS y,
      FC.ParentRel.In y (piEnablesN FDefs Slots cfgActive rc S FS) <->
      exists n0 v0 f e a feat,
        FDefRel.In (((n0, v0), f), e) FDefs /\
        entryFeatD e = Some (a, feat) /\
        PkgSet.In (n0, v0) S /\
        FSet.In f (fsAt FS (n0, v0)) /\
        hasActiveSlotb Slots cfgActive rc (n0, v0) a = true /\
        selectsb FDefs Slots cfgActive rc S FS (n0, v0) a = false /\
        y = ((NPlus.DecisionN n0 v0 f a feat, VPlus.VOff),
             (NPlus.Crate n0, VPlus.VOrig v0)).
  Proof.
    intros FDefs Slots cfgActive rc S FS y; unfold piEnablesN.
    rewrite SOfdr.mem_filterMap.
    split.
    - intros [[[[n0 v0] f] e] [Hf He]]; cbn beta iota in He.
      destruct (entryFeatD e) as [[a feat] |] eqn:Hd; [| discriminate].
      destruct (andb (PkgSet.mem (n0, v0) S) _) eqn:Hg in He;
        [| discriminate].
      injection He as <-.
      apply andb_true_iff in Hg; destruct Hg as [HS Hg].
      apply andb_true_iff in Hg; destruct Hg as [Hfs Hg].
      apply andb_true_iff in Hg; destruct Hg as [Hslot Hns].
      apply negb_true_iff in Hns.
      apply PkgSet.mem_spec in HS.
      apply FSet.mem_spec in Hfs.
      exists n0, v0, f, e, a, feat; repeat split; assumption.
    - intros [n0 [v0 [f [e [a [feat
        [Hf [Hd [HS [Hfs [Hslot [Hns ->]]]]]]]]]]]].
      exists (((n0, v0), f), e); split; [exact Hf | cbn beta iota].
      rewrite Hd.
      apply PkgSet.mem_spec in HS; rewrite HS.
      apply FSet.mem_spec in Hfs; rewrite Hfs.
      rewrite Hslot, Hns; reflexivity.
  Qed.

  Lemma mem_piDelivers : forall FDefs Slots cfgActive rc S FS sel y,
      FC.ParentRel.In y (piDelivers FDefs Slots cfgActive rc S FS sel) <->
      exists n v a u f e feat d,
        SelRel.In (((n, v), a), u) sel /\
        selectsb FDefs Slots cfgActive rc S FS (n, v) a = true /\
        FDefRel.In (((n, v), f), e) FDefs /\
        entryFeatD e = Some (a, feat) /\
        SlotRel.In ((n, v), d) Slots /\ sAlias d = a /\
        slotActive cfgActive rc (n, v) d = true /\
        y = ((NPlus.Crate (sTarget d), VPlus.VOrig u),
             (NPlus.DecisionN n v f a feat, VPlus.VFire u)).
  Proof.
    intros FDefs Slots cfgActive rc S FS sel y; unfold piDelivers.
    rewrite SOselr.mem_unionMap.
    split.
    - intros [[[[n v] a] u] [Hin Hy]]; cbn beta iota in Hy.
      destruct (selectsb FDefs Slots cfgActive rc S FS (n, v) a)
        eqn:Hsel; [| exfalso; exact (SOfdr.empty_in _ Hy)].
      apply SOfdr.mem_unionMap in Hy.
      destruct Hy as [[[q f] e] [Hf Hy]]; cbn beta iota in Hy.
      destruct (entryFeatD e) as [[a' feat] |] eqn:Hd;
        [| exfalso; exact (SOslr.empty_in _ Hy)].
      destruct (andb (PkgEqb.eqb q (n, v)) (NEqb.eqb a' a)) eqn:Hg;
        [| exfalso; exact (SOslr.empty_in _ Hy)].
      apply andb_true_iff in Hg; destruct Hg as [Hq Ha].
      apply PkgEqb.eqb_true_iff in Hq; subst q.
      apply NEqb.eqb_true_iff in Ha; subst a'.
      apply SOslr.mem_filterMap in Hy.
      destruct Hy as [[q' d] [Hdd He]]; cbn beta iota in He.
      destruct (andb (PkgEqb.eqb q' (n, v)) _) eqn:Hg2 in He;
        [| discriminate].
      injection He as <-.
      apply andb_true_iff in Hg2; destruct Hg2 as [Hq2 Hg2].
      apply andb_true_iff in Hg2; destruct Hg2 as [Ha2 Hact].
      apply PkgEqb.eqb_true_iff in Hq2; subst q'.
      apply NEqb.eqb_true_iff in Ha2.
      exists n, v, a, u, f, e, feat, d; repeat split; assumption.
    - intros [n [v [a [u [f [e [feat [d
        [Hin [Hsel [Hf [Hd [Hdd [Ha [Hact ->]]]]]]]]]]]]]]].
      exists (((n, v), a), u); split; [exact Hin | cbn beta iota].
      rewrite Hsel.
      apply SOfdr.mem_unionMap; exists (((n, v), f), e).
      split; [exact Hf | cbn beta iota].
      rewrite Hd, PkgEqb.eqb_refl, NEqb.eqb_refl; cbn.
      apply SOslr.mem_filterMap; exists ((n, v), d).
      split; [exact Hdd | cbn beta iota].
      rewrite PkgEqb.eqb_refl; cbn.
      subst a; rewrite NEqb.eqb_refl; cbn.
      rewrite Hact; reflexivity.
  Qed.

  Lemma mem_piLinks : forall S Links y,
      FC.ParentRel.In y (piLinks S Links) <->
      exists p l, LinkRel.In (p, l) Links /\ PkgSet.In p S /\
        y = ((NPlus.LinkN l, VPlus.VMember p),
             (NPlus.Crate (fst p), VPlus.VOrig (snd p))).
  Proof.
    intros S Links y; unfold piLinks; rewrite SOlr.mem_filterMap.
    split.
    - intros [[p l] [Hin He]]; cbn beta iota in He.
      destruct (PkgSet.mem p S) eqn:HS; [| discriminate].
      injection He as <-.
      apply PkgSet.mem_spec in HS.
      exists p, l; repeat split; assumption.
    - intros [p [l [Hin [HS ->]]]].
      exists (p, l); split; [exact Hin | cbn beta iota].
      apply PkgSet.mem_spec in HS; rewrite HS; reflexivity.
  Qed.

  Lemma mem_piSelves : forall S y,
      FC.ParentRel.In y (piSelves S) <->
      exists n v, PkgSet.In (n, v) S /\
        y = ((NPlus.Crate n, VPlus.VOrig v),
             (NPlus.Crate n, VPlus.VOrig v)).
  Proof.
    intros S y; unfold piSelves; rewrite SOpr.mem_map.
    split.
    - intros [[n v] [Hin ->]]; eauto.
    - intros [n [v [Hin ->]]]; exists (n, v); auto.
  Qed.

  Definition fcParents (FDefs : FDefRel.t) (Slots : SlotRel.t)
      (Links : LinkRel.t) (cfgActive : CfgS.t -> bool) (rc : Pkg.t)
      (S : PkgSet.t) (FS : FeaturedSet.t) (sel : SelRel.t)
    : FC.ParentRel.t :=
    FC.ParentRel.add
      ((NPlus.Crate (fst rc), VPlus.VOrig (snd rc)), transRoot)
      (FC.ParentRel.union (piChoices FDefs Slots cfgActive rc S FS sel)
         (FC.ParentRel.union (piHops FDefs Slots cfgActive rc S FS sel)
            (FC.ParentRel.union
               (piDecides FDefs Slots cfgActive rc S FS sel)
               (FC.ParentRel.union
                  (piEnablesF FDefs Slots cfgActive rc S FS sel)
                  (FC.ParentRel.union
                     (piEnablesN FDefs Slots cfgActive rc S FS)
                     (FC.ParentRel.union
                        (piDelivers FDefs Slots cfgActive rc S FS sel)
                        (FC.ParentRel.union (piLinks S Links)
                           (piSelves S)))))))).

  Lemma mem_fcParents : forall FDefs Slots Links cfgActive rc S FS sel y,
      FC.ParentRel.In y
        (fcParents FDefs Slots Links cfgActive rc S FS sel) <->
      y = ((NPlus.Crate (fst rc), VPlus.VOrig (snd rc)), transRoot) \/
      FC.ParentRel.In y (piChoices FDefs Slots cfgActive rc S FS sel) \/
      FC.ParentRel.In y (piHops FDefs Slots cfgActive rc S FS sel) \/
      FC.ParentRel.In y (piDecides FDefs Slots cfgActive rc S FS sel) \/
      FC.ParentRel.In y (piEnablesF FDefs Slots cfgActive rc S FS sel) \/
      FC.ParentRel.In y (piEnablesN FDefs Slots cfgActive rc S FS) \/
      FC.ParentRel.In y (piDelivers FDefs Slots cfgActive rc S FS sel) \/
      FC.ParentRel.In y (piLinks S Links) \/
      FC.ParentRel.In y (piSelves S).
  Proof.
    intros; unfold fcParents.
    rewrite FC.ParentRel.add_spec, !FC.ParentRel.union_spec; tauto.
  Qed.

  (* Weak feature entries may only reference optional slots -- Cargo
     itself rejects dep?/feat on a non-optional dependency, and the
     decision gadget hard-codes that reading: a non-optional slot's
     choice is always selected, which would fire a weak delivery the
     source semantics does not demand. *)
  Definition WeakOptional (FDefs : FDefRel.t) (Slots : SlotRel.t)
    : Prop :=
    forall p f a feat,
      FDefRel.In ((p, f), FEntry.EWeakFeat a feat) FDefs ->
      forall d, SlotRel.In (p, d) Slots -> sAlias d = a ->
      sOptional d = true.

  (* The synthetic root carries no support entries whatever the source
     resolution does: transSupport only ever names crates and gadgets. *)
  Lemma fc_no_root_support : forall R support FDefs Slots cfgActive rc f,
      ~ FC.Feat.SupportSet.In (transRoot, f)
          (transSupport R support FDefs Slots cfgActive rc).
  Proof.
    intros R support FDefs Slots cfgActive rc f Hy.
    apply mem_transSupport in Hy.
    destruct Hy as [[n [v [f0 [Hs He]]]] | Hy].
    - discriminate He.
    - destruct Hy
        as [n [v [f0 [e [a [feat [d [_ [_ [_ [_ [_ Hy]]]]]]]]]]]].
      destruct Hy as [He | [u [_ He]]]; discriminate He.
  Qed.

  Lemma fc_root_mem : forall FDefs Slots Links cfgActive rc S FS sel,
      FC.Feat.FeaturedSet.In (transRoot, FC.Feat.FSet.empty)
        (fcResolution FDefs Slots Links cfgActive rc S FS sel).
  Proof.
    intros; apply mem_fcResolution; left; reflexivity.
  Qed.

  (* Everything a selected choice key pins down, given a resolution:
     the unique slot behind it, and the selected version's facts. *)
  Lemma selects_sound :
    forall R support FDefs Slots Links g cfgActive dflt rc rootFeats
           S FS sel n v a u,
      AliasFunctional Slots ->
      IsResolution R support FDefs Slots Links g cfgActive dflt rc
        rootFeats S FS sel ->
      SelRel.In (((n, v), a), u) sel ->
      selectsb FDefs Slots cfgActive rc S FS (n, v) a = true ->
      exists d, SlotRel.In ((n, v), d) Slots /\ sAlias d = a /\
        slotActive cfgActive rc (n, v) d = true /\
        VSet.In u (evalReq R (sTarget d) (sReq d)) /\
        PkgSet.In (sTarget d, u) S /\
        (forall fs', FeaturedSet.In ((sTarget d, u), fs') FS ->
           FSet.Subset (slotRequests d dflt) fs') /\
        (forall d0, SlotRel.In ((n, v), d0) Slots -> sAlias d0 = a ->
           d0 = d).
  Proof.
    intros R support FDefs Slots Links g cfgActive dflt rc rootFeats
      S FS sel n v a u Half Hres Hin Hsel.
    destruct Hres.
    apply selectsb_iff in Hsel.
    destruct Hsel as [HS [d [Hd [Ha [Hact Hreq]]]]].
    destruct (res_fs_total0 (n, v) HS) as [fs Hfs].
    rewrite (fsAt_in FS (n, v) fs res_fs_functional0 Hfs) in Hreq.
    rewrite Ha in Hreq.
    destruct (res_slot_closure0 (n, v) fs HS Hfs d Hd Hact) as
      [u' [Hsel' [Hvf [HtS Hsub]]]].
    { rewrite Ha; exact Hreq. }
    rewrite Ha in Hsel'.
    pose proof (res_sel_functional0 (n, v) a u' u Hsel' Hin); subst u'.
    exists d; repeat split; try assumption.
    - apply mem_evalReq; split; [| exact Hvf].
      apply res_subset0; exact HtS.
    - intros d0 Hd0 Ha0; apply (Half (n, v) d0 d Hd0 Hd).
      rewrite Ha0, Ha; reflexivity.
  Qed.

  Lemma fc_subset :
    forall R support FDefs Slots Links g cfgActive dflt rc rootFeats
           S FS sel,
      AliasFunctional Slots ->
      IsResolution R support FDefs Slots Links g cfgActive dflt rc
        rootFeats S FS sel ->
      forall p fs,
        FC.Feat.FeaturedSet.In (p, fs)
          (fcResolution FDefs Slots Links cfgActive rc S FS sel) ->
        FC.PkgSet.In p (transReal R FDefs Slots Links cfgActive rc).
  Proof.
    intros R support FDefs Slots Links g cfgActive dflt rc rootFeats
      S FS sel Half Hres p fs Hy.
    pose proof Hres as Hres0; destruct Hres0.
    apply mem_fcResolution in Hy.
    destruct Hy as [Hy | [Hy | [Hy | [Hy | [Hy | Hy]]]]].
    - injection Hy as -> ->.
      apply mem_transReal; left; reflexivity.
    - apply mem_wCrates in Hy; destruct Hy as [n [v [fs0 [Hfs He]]]].
      injection He as -> ->.
      apply mem_transReal; right; left; apply mem_realBlock.
      exists n, v; split; [| reflexivity].
      apply res_subset0, (res_fs_dom0 _ _ Hfs).
    - apply mem_wChoices in Hy.
      destruct Hy as [n [v [a [u [Hin [Hsel He]]]]]].
      injection He as -> ->.
      destruct (selects_sound R support FDefs Slots Links g cfgActive
                  dflt rc rootFeats S FS sel n v a u Half Hres Hin Hsel)
        as [d [Hd [Ha [Hact [Hu _]]]]].
      apply mem_transReal; right; right; left; apply mem_slotBlock.
      exists n, v, d, u; subst a; repeat split; assumption.
    - apply mem_wFires in Hy.
      destruct Hy as [n [v [a [u [f [e [feat
        [Hin [Hsel [Hf [Hd He]]]]]]]]]]].
      injection He as -> ->.
      destruct (selects_sound R support FDefs Slots Links g cfgActive
                  dflt rc rootFeats S FS sel n v a u Half Hres Hin Hsel)
        as [d [Hdd [Ha [Hact [Hu _]]]]].
      apply mem_transReal; right; right; right; left.
      apply mem_featdBlock.
      exists n, v, f, e, a, feat, d.
      repeat split; try assumption.
      right; exists u; split; [exact Hu | reflexivity].
    - apply mem_wOffs in Hy.
      destruct Hy as [n0 [v0 [f [e [a [feat
        [Hf [Hd [HS [Hfs [Hslot [Hns He]]]]]]]]]]]].
      injection He as -> ->.
      apply hasActiveSlotb_iff in Hslot.
      destruct Hslot as [d [Hdd [Ha Hact]]].
      apply mem_transReal; right; right; right; left.
      apply mem_featdBlock.
      exists n0, v0, f, e, a, feat, d.
      repeat split; try assumption.
      left; reflexivity.
    - apply mem_wLinks in Hy.
      destruct Hy as [q [l [Hl [HS He]]]].
      injection He as -> ->.
      destruct q as [qn qv].
      apply mem_transReal; right; right; right; right.
      apply mem_linkBlock.
      exists qn, qv, l; repeat split; try assumption.
      apply res_subset0; exact HS.
  Qed.

  Lemma fc_support_mem :
    forall R support FDefs Slots Links g cfgActive dflt rc rootFeats
           S FS sel,
      AliasFunctional Slots ->
      IsResolution R support FDefs Slots Links g cfgActive dflt rc
        rootFeats S FS sel ->
      forall n v fs f,
        FC.Feat.FeaturedSet.In ((n, v), fs)
          (fcResolution FDefs Slots Links cfgActive rc S FS sel) ->
        FC.Feat.FSet.In f fs ->
        FC.Feat.SupportSet.In ((n, v), f)
          (transSupport R support FDefs Slots cfgActive rc).
  Proof.
    intros R support FDefs Slots Links g cfgActive dflt rc rootFeats
      S FS sel Half Hres n v fs f Hy Hf.
    pose proof Hres as Hres0; destruct Hres0.
    apply mem_fcResolution in Hy.
    destruct Hy as [Hy | [Hy | [Hy | [Hy | [Hy | Hy]]]]].
    - injection Hy as -> -> ->.
      exfalso; exact (FC.Feat.FSet.empty_spec Hf).
    - apply mem_wCrates in Hy.
      destruct Hy as [n1 [v1 [fs0 [Hfs He]]]].
      injection He as -> -> ->.
      apply mem_embedFS in Hf; destruct Hf as [f0 [Hf0 ->]].
      apply mem_transSupport; left.
      exists n1, v1, f0; split; [| reflexivity].
      apply (res_support_mem0 _ _ _ Hfs Hf0).
    - apply mem_wChoices in Hy.
      destruct Hy as [n1 [v1 [a [u [Hin [Hsel He]]]]]].
      injection He as -> -> ->.
      exfalso; exact (FC.Feat.FSet.empty_spec Hf).
    - apply mem_wFires in Hy.
      destruct Hy as [n1 [v1 [a [u [f0 [e [feat
        [Hin [Hsel [Hfd [Hd He]]]]]]]]]]].
      injection He as -> -> ->.
      destruct (FSet.mem f0 (fsAt FS (n1, v1))).
      2:{ exfalso; exact (FC.Feat.FSet.empty_spec Hf). }
      apply FC.Feat.FSet.singleton_spec in Hf; subst f.
      destruct (selects_sound R support FDefs Slots Links g cfgActive
                  dflt rc rootFeats S FS sel n1 v1 a u Half Hres Hin
                  Hsel)
        as [d [Hdd [Ha [Hact [Hu _]]]]].
      apply mem_transSupport; right.
      exists n1, v1, f0, e, a, feat, d.
      repeat split; try assumption.
      right; exists u; split; [exact Hu | reflexivity].
    - apply mem_wOffs in Hy.
      destruct Hy as [n0 [v0 [f0 [e [a [feat
        [Hfd [Hd [HS [Hfs [Hslot [Hns He]]]]]]]]]]]].
      injection He as -> -> ->.
      apply FC.Feat.FSet.singleton_spec in Hf; subst f.
      apply hasActiveSlotb_iff in Hslot.
      destruct Hslot as [d [Hdd [Ha Hact]]].
      apply mem_transSupport; right.
      exists n0, v0, f0, e, a, feat, d.
      repeat split; try assumption.
      left; reflexivity.
    - apply mem_wLinks in Hy.
      destruct Hy as [q [l [Hl [HS He]]]].
      injection He as -> -> ->.
      exfalso; exact (FC.Feat.FSet.empty_spec Hf).
  Qed.

  (* One destruct arm per witness family, leaving the equations raw so
     congruence can discharge every cross-family pairing. *)
  Ltac fc_node_cases H :=
    apply mem_fcResolution in H;
    destruct H as [H | [H | [H | [H | [H | H]]]]];
    [ unfold transRoot in H
    | apply mem_wCrates in H;
      let n := fresh "cn" in let v := fresh "cv" in
      let fs := fresh "cfs" in
      destruct H as [n [v [fs [?Hfs ?He]]]]
    | apply mem_wChoices in H;
      destruct H as [?n [?v [?a [?u [?Hin [?Hsel ?He]]]]]]
    | apply mem_wFires in H;
      destruct H
        as [?n [?v [?a [?u [?f [?e [?feat
           [?Hin [?Hsel [?Hfd [?Hd ?He]]]]]]]]]]]
    | apply mem_wOffs in H;
      destruct H
        as [?n [?v [?f [?e [?a [?feat
           [?Hfd [?Hd [?HS [?Hfs [?Hslot [?Hns ?He]]]]]]]]]]]]
    | apply mem_wLinks in H;
      destruct H as [?q [?l [?Hl [?HS ?He]]]] ].

  Lemma fc_version_granularity :
    forall R support FDefs Slots Links g cfgActive dflt rc rootFeats
           S FS sel,
      IsResolution R support FDefs Slots Links g cfgActive dflt rc
        rootFeats S FS sel ->
      forall nm x x' fs fs',
        FC.Feat.FeaturedSet.In ((nm, x), fs)
          (fcResolution FDefs Slots Links cfgActive rc S FS sel) ->
        FC.Feat.FeaturedSet.In ((nm, x'), fs')
          (fcResolution FDefs Slots Links cfgActive rc S FS sel) ->
        x <> x' -> gPlus g x <> gPlus g x'.
  Proof.
    intros R support FDefs Slots Links g cfgActive dflt rc rootFeats
      S FS sel Hres nm x x' fs fs' H1 H2 Hneq.
    pose proof Hres as H0; destruct H0.
    fc_node_cases H1; fc_node_cases H2; try congruence.
    - (* crate x crate *)
      assert (En : cn = cn0) by congruence.
      assert (Ev : cv <> cv0) by congruence.
      subst cn0.
      assert (Hx : x = VPlus.VOrig cv) by congruence.
      assert (Hx' : x' = VPlus.VOrig cv0) by congruence.
      subst x x'; cbn.
      intro HG; injection HG as HG.
      exact (res_class_unique0 cn cv cv0
               (res_fs_dom0 _ _ Hfs) (res_fs_dom0 _ _ Hfs0) Ev HG).
    - (* choice x choice *) exfalso.
      assert (En : n = n0) by congruence.
      assert (Ev : v = v0) by congruence.
      assert (Ea : a = a0) by congruence.
      subst n0 v0 a0.
      pose proof (res_sel_functional0 (n, v) a u u0 Hin Hin0).
      congruence.
    - (* fires x fires *) exfalso.
      assert (En : n = n0) by congruence.
      assert (Ev : v = v0) by congruence.
      assert (Ea : a = a0) by congruence.
      subst n0 v0 a0.
      pose proof (res_sel_functional0 (n, v) a u u0 Hin Hin0).
      congruence.
    - (* links x links *) exfalso.
      assert (El : l = l0) by congruence.
      subst l0.
      pose proof (res_links_unique0 q q0 l HS HS0 Hl Hl0).
      congruence.
  Qed.

  Lemma fc_feature_unification :
    forall R support FDefs Slots Links g cfgActive dflt rc rootFeats
           S FS sel,
      IsResolution R support FDefs Slots Links g cfgActive dflt rc
        rootFeats S FS sel ->
      forall nm x fs fs',
        FC.Feat.FeaturedSet.In ((nm, x), fs)
          (fcResolution FDefs Slots Links cfgActive rc S FS sel) ->
        FC.Feat.FeaturedSet.In ((nm, x), fs')
          (fcResolution FDefs Slots Links cfgActive rc S FS sel) ->
        fs = fs'.
  Proof.
    intros R support FDefs Slots Links g cfgActive dflt rc rootFeats
      S FS sel Hres nm x fs fs' H1 H2.
    pose proof Hres as H0; destruct H0.
    fc_node_cases H1; fc_node_cases H2; try congruence.
    - (* crate x crate *)
      assert (En : cn = cn0) by congruence.
      assert (Ev : cv = cv0) by congruence.
      subst cn0 cv0.
      pose proof (res_fs_functional0 (cn, cv) cfs cfs0 Hfs Hfs0).
      congruence.
    - (* fires x fires *)
      assert (En : n = n0) by congruence.
      assert (Ev : v = v0) by congruence.
      assert (Ef : f = f0) by congruence.
      subst n0 v0 f0.
      congruence.
  Qed.

  Ltac fc_pi_cases H :=
    apply mem_fcParents in H;
    destruct H as [H | [H | [H | [H | [H | [H | [H | [H | H]]]]]]]];
    [ unfold transRoot in H
    | apply mem_piChoices in H;
      destruct H as [?n [?v [?a [?u [?Hin [?Hsel ?He]]]]]]
    | apply mem_piHops in H;
      destruct H
        as [?n [?v [?a [?u [?d [?Hin [?Hsel [?Hd [?Ha [?Hact ?He]]]]]]]]]]
    | apply mem_piDecides in H;
      destruct H
        as [?n [?v [?a [?u [?f [?e [?feat
           [?Hin [?Hsel [?Hfd [?Hdd ?He]]]]]]]]]]]
    | apply mem_piEnablesF in H;
      destruct H
        as [?n [?v [?a [?u [?f [?e [?feat
           [?Hin [?Hsel [?Hfd [?Hdd ?He]]]]]]]]]]]
    | apply mem_piEnablesN in H;
      destruct H
        as [?n [?v [?f [?e [?a [?feat
           [?Hfd [?Hdd [?HS [?Hfs [?Hslot [?Hns ?He]]]]]]]]]]]]
    | apply mem_piDelivers in H;
      destruct H
        as [?n [?v [?a [?u [?f [?e [?feat [?d
           [?Hin [?Hsel [?Hfd [?Hdd [?Hsd [?Ha [?Hact ?He]]]]]]]]]]]]]]]
    | apply mem_piLinks in H;
      let q := fresh "lq" in
      destruct H as [q [?l [?Hl [?HS ?He]]]];
      destruct q as [?qn ?qv]
    | apply mem_piSelves in H;
      destruct H as [?n [?v [?HS ?He]]] ].

  Lemma fc_pi_functional :
    forall R support FDefs Slots Links g cfgActive dflt rc rootFeats
           S FS sel,
      IsResolution R support FDefs Slots Links g cfgActive dflt rc
        rootFeats S FS sel ->
      forall nm x x' pp,
        FC.ParentRel.In ((nm, x), pp)
          (fcParents FDefs Slots Links cfgActive rc S FS sel) ->
        FC.ParentRel.In ((nm, x'), pp)
          (fcParents FDefs Slots Links cfgActive rc S FS sel) ->
        x = x'.
  Proof.
    intros R support FDefs Slots Links g cfgActive dflt rc rootFeats
      S FS sel Hres nm x x' pp H1 H2.
    pose proof Hres as H0; destruct H0.
    fc_pi_cases H1; fc_pi_cases H2; try congruence.
    - (* choices x choices *)
      assert (En : n = n0) by congruence.
      assert (Ev : v = v0) by congruence.
      assert (Ea : a = a0) by congruence.
      subst n0 v0 a0.
      pose proof (res_sel_functional0 (n, v) a u u0 Hin Hin0).
      congruence.
    - (* enablesF x enablesF *)
      assert (En : n = n0) by congruence.
      assert (Ev : v = v0) by congruence.
      assert (Ea : a = a0) by congruence.
      subst n0 v0 a0.
      pose proof (res_sel_functional0 (n, v) a u u0 Hin Hin0).
      congruence.
    - (* links x links *)
      cbn [fst snd] in He, He0.
      congruence.
  Qed.

  (* Uniqueness is one fact in every closure branch: a rival version
     sits under the edge's target name with the same parent, and the
     witness parent relation is functional there. *)
  Ltac fc_closure_unique Hres Hpi :=
    let x := fresh "x" in
    let Hu := fresh "Hu" in
    intros x [_ [_ Hu]];
    eapply fc_pi_functional; [exact Hres | exact Hpi | exact Hu].

  Lemma fc_parent_closure :
    forall R support FDefs Slots Links g cfgActive dflt rc rootFeats
           S FS sel,
      AliasFunctional Slots ->
      IsResolution R support FDefs Slots Links g cfgActive dflt rc
        rootFeats S FS sel ->
      forall p fs_p,
        FC.Feat.FeaturedSet.In (p, fs_p)
          (fcResolution FDefs Slots Links cfgActive rc S FS sel) ->
        forall nm vs fs,
          FC.Feat.FeatDepRel.In (p, (nm, (vs, fs)))
            (transDf R FDefs Slots Links cfgActive dflt rc rootFeats) ->
          exists! x, FC.VSet.In x vs /\
            (exists fs', FC.Feat.FSet.Subset fs fs' /\
               FC.Feat.FeaturedSet.In ((nm, x), fs')
                 (fcResolution FDefs Slots Links cfgActive rc S FS sel)) /\
            FC.ParentRel.In ((nm, x), p)
              (fcParents FDefs Slots Links cfgActive rc S FS sel).
  Proof.
    intros R support FDefs Slots Links g cfgActive dflt rc rootFeats
      S FS sel Half Hres p fs_p Hp nm vs fs Hed.
    destruct rc as [rn rv].
    pose proof Hres as Hres0; destruct Hres0.
    apply mem_transDf in Hed.
    destruct Hed as [Hed | [Hed | [Hed | [Hed | Hed]]]].
    - (* the root edge, discharged by the root crate and its feats *)
      apply mem_rootEdge in Hed; cbn [fst snd] in Hed.
      injection Hed as -> -> -> ->.
      destruct (res_fs_total0 (rn, rv) res_root_mem0) as [fs0 Hfs0].
      assert (Hpi : FC.ParentRel.In
          ((NPlus.Crate rn, VPlus.VOrig rv), transRoot)
          (fcParents FDefs Slots Links cfgActive (rn, rv) S FS sel)).
      { apply mem_fcParents; left; cbn [fst snd]; reflexivity. }
      exists (VPlus.VOrig rv); split.
      + split; [| split].
        * apply FC.VSet.singleton_spec; reflexivity.
        * exists (embedFS fs0); split.
          -- apply embedFS_mono; exact (res_root_feats0 _ Hfs0).
          -- apply mem_fcResolution; right; left; apply mem_wCrates.
             exists rn, rv, fs0; split; [exact Hfs0 | reflexivity].
        * exact Hpi.
      + fc_closure_unique Hres Hpi.
    - (* a non-optional slot, discharged by its choice node *)
      apply mem_slotHop1 in Hed.
      destruct Hed as [n [v [d [Hd [Hact [Hopt Heq]]]]]].
      injection Heq as -> -> -> ->.
      fc_node_cases Hp; try congruence.
      assert (En : cn = n) by congruence.
      assert (Ev : cv = v) by congruence.
      subst cn cv.
      assert (HS : PkgSet.In (n, v) S) by exact (res_fs_dom0 _ _ Hfs).
      destruct (res_slot_closure0 (n, v) cfs HS Hfs d Hd Hact
                  (or_introl Hopt)) as [u [Hsu [Hvf [HtS Hsub]]]].
      assert (Hu : VSet.In u (evalReq R (sTarget d) (sReq d))).
      { apply mem_evalReq; split;
          [apply res_subset0; exact HtS | exact Hvf]. }
      assert (Hsel : selectsb FDefs Slots cfgActive (rn, rv) S FS (n, v)
                       (sAlias d) = true).
      { apply selectsb_iff; split; [exact HS |].
        exists d; repeat split; try assumption.
        left; exact Hopt. }
      assert (Hpi : FC.ParentRel.In
          ((NPlus.SlotN n v (sAlias d), VPlus.VChoice u),
           (NPlus.Crate n, VPlus.VOrig v))
          (fcParents FDefs Slots Links cfgActive (rn, rv) S FS sel)).
      { apply mem_fcParents; right; left; apply mem_piChoices.
        exists n, v, (sAlias d), u; repeat split; try assumption. }
      exists (VPlus.VChoice u); split.
      + split; [| split].
        * unfold choicesOf; apply SOvv.mem_map; exists u; split;
            [exact Hu | reflexivity].
        * exists FC.Feat.FSet.empty; split.
          -- apply FC.Feat.FSet.empty_subset.
          -- apply mem_fcResolution; right; right; left;
               apply mem_wChoices.
             exists n, v, (sAlias d), u; repeat split; try assumption.
        * exact Hpi.
      + fc_closure_unique Hres Hpi.
    - (* the second slot hop, discharged by the selected crate *)
      apply mem_slotHop2 in Hed.
      destruct Hed as [n [v [d [u [Hd [Hact [Hu Heq]]]]]]].
      injection Heq as -> -> -> ->.
      fc_node_cases Hp; try congruence.
      assert (En : n0 = n) by congruence.
      assert (Ev : v0 = v) by congruence.
      assert (Ea : a = sAlias d) by congruence.
      assert (Eu : u0 = u) by congruence.
      subst n0 v0 a u0.
      destruct (selects_sound R support FDefs Slots Links g cfgActive
                  dflt (rn, rv) rootFeats S FS sel n v (sAlias d) u Half
                  Hres Hin Hsel)
        as [d0 [Hd0 [Ha0 [Hact0 [Hu0 [HtS [Hsub Huniq]]]]]]].
      pose proof (Huniq d Hd eq_refl) as Ed; subst d0.
      destruct (res_fs_total0 (sTarget d, u) HtS) as [fsT HfsT].
      assert (Hpi : FC.ParentRel.In
          ((NPlus.Crate (sTarget d), VPlus.VOrig u),
           (NPlus.SlotN n v (sAlias d), VPlus.VChoice u))
          (fcParents FDefs Slots Links cfgActive (rn, rv) S FS sel)).
      { apply mem_fcParents; right; right; left; apply mem_piHops.
        exists n, v, (sAlias d), u, d; repeat split; try assumption. }
      exists (VPlus.VOrig u); split.
      + split; [| split].
        * apply FC.VSet.singleton_spec; reflexivity.
        * exists (embedFS fsT); split.
          -- apply embedFS_mono; exact (Hsub _ HfsT).
          -- apply mem_fcResolution; right; left; apply mem_wCrates.
             exists (sTarget d), u, fsT; split;
               [exact HfsT | reflexivity].
        * exact Hpi.
      + fc_closure_unique Hres Hpi.
    - (* the links edge, discharged by the crate's own link node *)
      apply mem_linkEdges in Hed.
      destruct Hed as [n [v [l [Hl [HR Heq]]]]].
      injection Heq as -> -> -> ->.
      fc_node_cases Hp; try congruence.
      assert (En : cn = n) by congruence.
      assert (Ev : cv = v) by congruence.
      subst cn cv.
      assert (HS : PkgSet.In (n, v) S) by exact (res_fs_dom0 _ _ Hfs).
      assert (Hpi : FC.ParentRel.In
          ((NPlus.LinkN l, VPlus.VMember (n, v)),
           (NPlus.Crate n, VPlus.VOrig v))
          (fcParents FDefs Slots Links cfgActive (rn, rv) S FS sel)).
      { apply mem_fcParents; do 7 right; left; apply mem_piLinks.
        exists (n, v), l; repeat split; try assumption. }
      exists (VPlus.VMember (n, v)); split.
      + split; [| split].
        * apply FC.VSet.singleton_spec; reflexivity.
        * exists FC.Feat.FSet.empty; split.
          -- apply FC.Feat.FSet.empty_subset.
          -- apply mem_fcResolution; do 5 right; apply mem_wLinks.
             exists (n, v), l; repeat split; try assumption.
        * exact Hpi.
      + fc_closure_unique Hres Hpi.
    - (* the decision edge, discharged by the gadget's firing node *)
      apply mem_decisionEdges in Hed.
      destruct Hed as [n [v [f [e [a [feat [d [u
        [Hfd [Hen [Hd [Ha [Hact [Hu Heq]]]]]]]]]]]]]].
      injection Heq as -> -> -> ->.
      fc_node_cases Hp; try congruence.
      assert (En : n0 = n) by congruence.
      assert (Ev : v0 = v) by congruence.
      assert (Ea : a0 = a) by congruence.
      assert (Eu : u0 = u) by congruence.
      subst n0 v0 a0 u0.
      assert (Hpi : FC.ParentRel.In
          ((NPlus.DecisionN n v f a feat, VPlus.VFire u),
           (NPlus.SlotN n v a, VPlus.VChoice u))
          (fcParents FDefs Slots Links cfgActive (rn, rv) S FS sel)).
      { apply mem_fcParents; do 3 right; left; apply mem_piDecides.
        exists n, v, a, u, f, e, feat; repeat split; try assumption. }
      exists (VPlus.VFire u); split.
      + split; [| split].
        * apply FC.VSet.singleton_spec; reflexivity.
        * exists (if FSet.mem f (fsAt FS (n, v))
                  then FC.Feat.FSet.singleton FPlusComp.FWit
                  else FC.Feat.FSet.empty); split.
          -- apply FC.Feat.FSet.empty_subset.
          -- apply mem_fcResolution; do 3 right; left; apply mem_wFires.
             exists n, v, a, u, f, e, feat; repeat split; try assumption.
        * exact Hpi.
      + fc_closure_unique Hres Hpi.
  Qed.

  Lemma fc_parent_closure_addl :
    forall R support FDefs Slots Links g cfgActive dflt rc rootFeats
           S FS sel,
      AliasFunctional Slots ->
      WeakOptional FDefs Slots ->
      IsResolution R support FDefs Slots Links g cfgActive dflt rc
        rootFeats S FS sel ->
      forall p fs_p,
        FC.Feat.FeaturedSet.In (p, fs_p)
          (fcResolution FDefs Slots Links cfgActive rc S FS sel) ->
        forall ft, FC.Feat.FSet.In ft fs_p ->
        forall nm vs fs,
          FC.Feat.AddlDepRel.In ((p, ft), (nm, (vs, fs)))
            (transDa R FDefs Slots cfgActive rc) ->
          exists! x, FC.VSet.In x vs /\
            (exists fs', FC.Feat.FSet.Subset fs fs' /\
               FC.Feat.FeaturedSet.In ((nm, x), fs')
                 (fcResolution FDefs Slots Links cfgActive rc S FS sel)) /\
            FC.ParentRel.In ((nm, x), p)
              (fcParents FDefs Slots Links cfgActive rc S FS sel).
  Proof.
    intros R support FDefs Slots Links g cfgActive dflt rc rootFeats
      S FS sel Half Hwo Hres p fs_p Hp ft Hft nm vs fs Hed.
    destruct rc as [rn rv].
    pose proof Hres as Hres0; destruct Hres0.
    apply mem_transDa in Hed.
    destruct Hed as [Hed | [Hed | [Hed | Hed]]].
    - (* a sibling feature, discharged by the crate's own node *)
      apply mem_sameFeatEdges in Hed.
      destruct Hed as [n [v [f [f' [Hfd Heq]]]]].
      injection Heq as -> -> -> -> ->.
      fc_node_cases Hp; try congruence.
      assert (En : cn = n) by congruence.
      assert (Ev : cv = v) by congruence.
      subst cn cv.
      assert (Efs : fs_p = embedFS cfs) by congruence.
      subst fs_p.
      apply mem_embedFS in Hft; destruct Hft as [f1 [Hf0 Ef]].
      injection Ef as <-.
      assert (HS : PkgSet.In (n, v) S) by exact (res_fs_dom0 _ _ Hfs).
      assert (Hf' : FSet.In f' cfs)
        by exact (res_feat_closure_same0 (n, v) cfs f f' Hfs Hf0 Hfd).
      assert (Hpi : FC.ParentRel.In
          ((NPlus.Crate n, VPlus.VOrig v),
           (NPlus.Crate n, VPlus.VOrig v))
          (fcParents FDefs Slots Links cfgActive (rn, rv) S FS sel)).
      { apply mem_fcParents; do 8 right; apply mem_piSelves.
        exists n, v; split; [exact HS | reflexivity]. }
      exists (VPlus.VOrig v); split.
      + split; [| split].
        * apply FC.VSet.singleton_spec; reflexivity.
        * exists (embedFS cfs); split.
          -- intros y Hy; apply FC.Feat.FSet.singleton_spec in Hy.
             subst y; apply mem_embedFS; exists f'; split;
               [exact Hf' | reflexivity].
          -- apply mem_fcResolution; right; left; apply mem_wCrates.
             exists n, v, cfs; split; [exact Hfs | reflexivity].
        * exact Hpi.
      + fc_closure_unique Hres Hpi.
    - (* an activating entry, discharged by the slot's choice node *)
      apply mem_activationEdges in Hed.
      destruct Hed
        as [n [v [f [e [a [d [Hfd [Hea [Hd [Ha [Hact Heq]]]]]]]]]]].
      injection Heq as -> -> -> -> ->.
      fc_node_cases Hp; try congruence.
      assert (En : cn = n) by congruence.
      assert (Ev : cv = v) by congruence.
      subst cn cv.
      assert (Efs : fs_p = embedFS cfs) by congruence.
      subst fs_p.
      apply mem_embedFS in Hft; destruct Hft as [f1 [Hf0 Ef]].
      injection Ef as <-.
      assert (HS : PkgSet.In (n, v) S) by exact (res_fs_dom0 _ _ Hfs).
      assert (Hfsa : fsAt FS (n, v) = cfs)
        by exact (fsAt_in FS (n, v) cfs res_fs_functional0 Hfs).
      assert (Hacted : Activated FDefs cfs (n, v) a).
      { exists f; split; [exact Hf0 |].
        destruct e as [f2 | a2 | a2 feat | a2 feat]; cbn in Hea;
          try discriminate; injection Hea as ->.
        - left; exact Hfd.
        - right; exists feat; exact Hfd. }
      assert (Hreq : sOptional d = false \/
                     Activated FDefs cfs (n, v) (sAlias d))
        by (right; rewrite Ha; exact Hacted).
      destruct (res_slot_closure0 (n, v) cfs HS Hfs d Hd Hact Hreq)
        as [u [Hsu [Hvf [HtS Hsub]]]].
      rewrite Ha in Hsu.
      assert (Hu : VSet.In u (evalReq R (sTarget d) (sReq d))).
      { apply mem_evalReq; split;
          [apply res_subset0; exact HtS | exact Hvf]. }
      assert (Hsel : selectsb FDefs Slots cfgActive (rn, rv) S FS (n, v)
                       a = true).
      { apply selectsb_iff; split; [exact HS |].
        exists d; repeat split; try assumption.
        right; rewrite Hfsa, Ha; exact Hacted. }
      assert (Hpi : FC.ParentRel.In
          ((NPlus.SlotN n v a, VPlus.VChoice u),
           (NPlus.Crate n, VPlus.VOrig v))
          (fcParents FDefs Slots Links cfgActive (rn, rv) S FS sel)).
      { apply mem_fcParents; right; left; apply mem_piChoices.
        exists n, v, a, u; repeat split; try assumption. }
      exists (VPlus.VChoice u); split.
      + split; [| split].
        * unfold choicesOf; apply SOvv.mem_map; exists u; split;
            [exact Hu | reflexivity].
        * exists FC.Feat.FSet.empty; split.
          -- apply FC.Feat.FSet.empty_subset.
          -- apply mem_fcResolution; right; right; left;
               apply mem_wChoices.
             exists n, v, a, u; repeat split; try assumption.
        * exact Hpi.
      + fc_closure_unique Hres Hpi.
    - (* a delivering entry enabling its gadget's witness feature *)
      apply mem_witEnableEdges in Hed.
      destruct Hed as [n [v [f [e [a [feat [d
        [Hfd [Hen [Hd [Ha [Hact Heq]]]]]]]]]]]].
      injection Heq as -> -> -> -> ->.
      fc_node_cases Hp; try congruence.
      assert (En : cn = n) by congruence.
      assert (Ev : cv = v) by congruence.
      subst cn cv.
      assert (Efs : fs_p = embedFS cfs) by congruence.
      subst fs_p.
      apply mem_embedFS in Hft; destruct Hft as [f1 [Hf0 Ef]].
      injection Ef as <-.
      assert (HS : PkgSet.In (n, v) S) by exact (res_fs_dom0 _ _ Hfs).
      assert (Hfsa : fsAt FS (n, v) = cfs)
        by exact (fsAt_in FS (n, v) cfs res_fs_functional0 Hfs).
      assert (Hfm : FSet.In f (fsAt FS (n, v)))
        by (rewrite Hfsa; exact Hf0).
      assert (Hfmb : FSet.mem f (fsAt FS (n, v)) = true)
        by (apply FSet.mem_spec; exact Hfm).
      destruct (selectsb FDefs Slots cfgActive (rn, rv) S FS (n, v) a)
        eqn:Hsel.
      + (* the slot's choice is taken, so the gadget fires *)
        pose proof Hsel as Hsb; apply selectsb_iff in Hsb.
        destruct Hsb as [_ [d0 [Hd0 [Ha0 [Hact0 Hreq0]]]]].
        assert (Ea0 : sAlias d0 = sAlias d) by congruence.
        pose proof (Half (n, v) d0 d Hd0 Hd Ea0) as Ed; subst d0.
        rewrite Hfsa in Hreq0.
        destruct (res_slot_closure0 (n, v) cfs HS Hfs d Hd Hact Hreq0)
          as [u [Hsu [Hvf [HtS Hsub]]]].
        rewrite Ha in Hsu.
        assert (Hu : VSet.In u (evalReq R (sTarget d) (sReq d))).
        { apply mem_evalReq; split;
            [apply res_subset0; exact HtS | exact Hvf]. }
        assert (Hpi : FC.ParentRel.In
            ((NPlus.DecisionN n v f a feat, VPlus.VFire u),
             (NPlus.Crate n, VPlus.VOrig v))
            (fcParents FDefs Slots Links cfgActive (rn, rv) S FS sel)).
        { apply mem_fcParents; do 4 right; left; apply mem_piEnablesF.
          exists n, v, a, u, f, e, feat; repeat split; try assumption. }
        exists (VPlus.VFire u); split.
        * split; [| split].
          -- apply FC.VSet.add_spec; right; unfold firesOf.
             apply SOvv.mem_map; exists u; split;
               [exact Hu | reflexivity].
          -- exists (FC.Feat.FSet.singleton FPlusComp.FWit); split;
               [intros y Hy; exact Hy |].
             apply mem_fcResolution; do 3 right; left; apply mem_wFires.
             exists n, v, a, u, f, e, feat; repeat split;
               try assumption.
             rewrite Hfmb; reflexivity.
          -- exact Hpi.
        * fc_closure_unique Hres Hpi.
      + (* no choice is taken, so the gadget takes its off version *)
        assert (Hslot : hasActiveSlotb Slots cfgActive (rn, rv) (n, v) a
                        = true).
        { apply hasActiveSlotb_iff; exists d; repeat split;
            try assumption. }
        assert (Hpi : FC.ParentRel.In
            ((NPlus.DecisionN n v f a feat, VPlus.VOff),
             (NPlus.Crate n, VPlus.VOrig v))
            (fcParents FDefs Slots Links cfgActive (rn, rv) S FS sel)).
        { apply mem_fcParents; do 5 right; left; apply mem_piEnablesN.
          exists n, v, f, e, a, feat; repeat split; try assumption. }
        exists VPlus.VOff; split.
        * split; [| split].
          -- apply FC.VSet.add_spec; left; reflexivity.
          -- exists (FC.Feat.FSet.singleton FPlusComp.FWit); split;
               [intros y Hy; exact Hy |].
             apply mem_fcResolution; do 4 right; left;
               apply mem_wOffs.
             exists n, v, f, e, a, feat; repeat split; try assumption.
          -- exact Hpi.
        * fc_closure_unique Hres Hpi.
    - (* a gadget delivering feat to the crate its slot selected *)
      apply mem_witDeliverEdges in Hed.
      destruct Hed as [n [v [f [e [a [feat [d [u
        [Hfd [Hen [Hd [Ha [Hact [Hu Heq]]]]]]]]]]]]]].
      injection Heq as -> -> -> -> ->.
      fc_node_cases Hp; try congruence.
      assert (En : n0 = n) by congruence.
      assert (Ev : v0 = v) by congruence.
      assert (Ea : a0 = a) by congruence.
      assert (Eu : u0 = u) by congruence.
      assert (Ef : f0 = f) by congruence.
      assert (Eft : feat0 = feat) by congruence.
      subst n0 v0 a0 u0 f0 feat0.
      assert (Efs : fs_p = if FSet.mem f (fsAt FS (n, v))
                           then FC.Feat.FSet.singleton FPlusComp.FWit
                           else FC.Feat.FSet.empty) by congruence.
      subst fs_p.
      destruct (FSet.mem f (fsAt FS (n, v))) eqn:Hfmb.
      2:{ exfalso; exact (FC.Feat.FSet.empty_spec Hft). }
      assert (Hfm : FSet.In f (fsAt FS (n, v)))
        by (apply FSet.mem_spec; exact Hfmb).
      pose proof Hsel as Hsb; apply selectsb_iff in Hsb.
      destruct Hsb as [HS [d1 [Hd1 [Ha1 [Hact1 Hreq1]]]]].
      assert (Ea1 : sAlias d1 = sAlias d) by congruence.
      pose proof (Half (n, v) d1 d Hd1 Hd Ea1) as Ed1; subst d1.
      destruct (res_fs_total0 (n, v) HS) as [fs1 Hfs1].
      assert (Hfsa : fsAt FS (n, v) = fs1)
        by exact (fsAt_in FS (n, v) fs1 res_fs_functional0 Hfs1).
      rewrite Hfsa in Hfm, Hreq1.
      (* a?/feat only ever names an optional slot, so a taken choice
         means the entry's alias really was activated *)
      assert (Hent :
          FDefRel.In (((n, v), f), FEntry.EDepFeat a feat) FDefs \/
          (FDefRel.In (((n, v), f), FEntry.EWeakFeat a feat) FDefs /\
           Activated FDefs fs1 (n, v) a)).
      { destruct e as [f2 | a2 | a2 feat2 | a2 feat2]; cbn in Hen;
          try discriminate; injection Hen as -> ->.
        - left; exact Hfd.
        - right; split; [exact Hfd |].
          pose proof (Hwo (n, v) f a feat Hfd d Hd Ha) as Hopt.
          destruct Hreq1 as [Hbad | Hacted]; [congruence |].
          rewrite Ha in Hacted; exact Hacted. }
      destruct (selects_sound R support FDefs Slots Links g cfgActive
                  dflt (rn, rv) rootFeats S FS sel n v a u Half Hres Hin
                  Hsel)
        as [d2 [Hd2 [Ha2 [Hact2 [Hu2 [HtS [Hsub Huniq]]]]]]].
      assert (Ea2 : sAlias d2 = sAlias d) by congruence.
      pose proof (Half (n, v) d2 d Hd2 Hd Ea2) as Ed2; subst d2.
      destruct (res_fs_total0 (sTarget d, u) HtS) as [fsT HfsT].
      assert (Hfeat : FSet.In feat fsT)
        by exact (res_feat_closure_dep0 (n, v) fs1 f a feat Hfs1 Hfm
                    Hent d u Hd Ha Hin fsT HfsT).
      assert (Hpi : FC.ParentRel.In
          ((NPlus.Crate (sTarget d), VPlus.VOrig u),
           (NPlus.DecisionN n v f a feat, VPlus.VFire u))
          (fcParents FDefs Slots Links cfgActive (rn, rv) S FS sel)).
      { apply mem_fcParents; do 6 right; left; apply mem_piDelivers.
        exists n, v, a, u, f, e, feat, d; repeat split;
          try assumption. }
      exists (VPlus.VOrig u); split.
      + split; [| split].
        * apply FC.VSet.singleton_spec; reflexivity.
        * exists (embedFS fsT); split.
          -- intros y Hy; apply FC.Feat.FSet.singleton_spec in Hy.
             subst y; apply mem_embedFS; exists feat; split;
               [exact Hfeat | reflexivity].
          -- apply mem_fcResolution; right; left; apply mem_wCrates.
             exists (sTarget d), u, fsT; split;
               [exact HfsT | reflexivity].
        * exact Hpi.
      + fc_closure_unique Hres Hpi.
  Qed.

  Theorem cargo_completeness :
    forall R support FDefs Slots Links g cfgActive dflt rc rootFeats
           S FS sel,
      AliasFunctional Slots ->
      WeakOptional FDefs Slots ->
      IsResolution R support FDefs Slots Links g cfgActive dflt rc
        rootFeats S FS sel ->
      FC.IsResolution (transReal R FDefs Slots Links cfgActive rc)
        (transSupport R support FDefs Slots cfgActive rc)
        (transDf R FDefs Slots Links cfgActive dflt rc rootFeats)
        (transDa R FDefs Slots cfgActive rc)
        (gPlus g) transRoot
        (fcResolution FDefs Slots Links cfgActive rc S FS sel)
        (fcParents FDefs Slots Links cfgActive rc S FS sel).
  Proof.
    intros R support FDefs Slots Links g cfgActive dflt rc rootFeats
      S FS sel Half Hwo Hres.
    constructor.
    - intro f; apply fc_no_root_support.
    - intros q fs Hq.
      exact (fc_subset R support FDefs Slots Links g cfgActive dflt rc
               rootFeats S FS sel Half Hres q fs Hq).
    - apply fc_root_mem.
    - intros nm x fs fs' H1 H2.
      exact (fc_feature_unification R support FDefs Slots Links g
               cfgActive dflt rc rootFeats S FS sel Hres nm x fs fs'
               H1 H2).
    - intros q fs_q Hq nm vs fs Hed.
      exact (fc_parent_closure R support FDefs Slots Links g cfgActive
               dflt rc rootFeats S FS sel Half Hres q fs_q Hq nm vs fs
               Hed).
    - intros q fs_q Hq ft Hft nm vs fs Hed.
      exact (fc_parent_closure_addl R support FDefs Slots Links g
               cfgActive dflt rc rootFeats S FS sel Half Hwo Hres q fs_q
               Hq ft Hft nm vs fs Hed).
    - intros nm x x' pp H1 H2.
      exact (fc_pi_functional R support FDefs Slots Links g cfgActive
               dflt rc rootFeats S FS sel Hres nm x x' pp H1 H2).
    - intros nm x x' fs fs' H1 H2 Hne.
      exact (fc_version_granularity R support FDefs Slots Links g
               cfgActive dflt rc rootFeats S FS sel Hres nm x x' fs fs'
               H1 H2 Hne).
    - intros nm x fs f Hq Hf.
      exact (fc_support_mem R support FDefs Slots Links g cfgActive dflt
               rc rootFeats S FS sel Half Hres nm x fs f Hq Hf).
  Qed.

  Module Lookup.
    Module NSet := FSetUOT N.
    Module PkgPreimage := PreimageOfKeys N Pkg NSet PkgSet.

    Definition realPreimage (R : PkgSet.t) (ns : NSet.t) : PkgSet.t :=
      PkgPreimage.ofKeys fst ns R.

    Module SOsn2 := SetOps SlotElt N SlotRel NSet.
    (* The names a crate-version's rows read: its own name (for the link
       guard) and its slots' targets. *)
    Definition crateReads (Slots : SlotRel.t) (p : Pkg.t) : NSet.t :=
      NSet.add (fst p)
        (SOsn2.map (fun '(_, d) => sTarget d) (ownSlots Slots p)).

    Lemma mem_crateReads_target : forall Slots p d,
        SlotRel.In (p, d) Slots ->
        NSet.In (sTarget d) (crateReads Slots p).
    Proof.
      intros Slots p d Hs; apply NSet.add_spec; right.
      apply SOsn2.mem_map; exists (p, d); split; [| reflexivity].
      apply mem_ownSlots; split; [exact Hs | reflexivity].
    Qed.

    Lemma evalReq_preimage : forall R ns m rg,
        NSet.In m ns ->
        evalReq (realPreimage R ns) m rg = evalReq R m rg.
    Proof.
      intros R ns m rg Hm; apply VSet.ext; intro u.
      rewrite !mem_evalReq; unfold realPreimage.
      rewrite PkgPreimage.mem_ofKeys; simpl; tauto.
    Qed.

    Lemma srcVersions_preimage : forall R ns m,
        NSet.In m ns ->
        srcVersions (realPreimage R ns) m = srcVersions R m.
    Proof.
      intros R ns m Hm; apply VSet.ext; intro u.
      rewrite !mem_srcVersions; unfold realPreimage.
      rewrite PkgPreimage.mem_ofKeys; simpl; tauto.
    Qed.

    Lemma mem_preimage : forall R ns p,
        NSet.In (fst p) ns ->
        (PkgSet.In p (realPreimage R ns) <-> PkgSet.In p R).
    Proof.
      intros R ns p Hn; unfold realPreimage.
      rewrite PkgPreimage.mem_ofKeys; tauto.
    Qed.

    Lemma choicesOf_preimage : forall R ns d,
        NSet.In (sTarget d) ns ->
        choicesOf (realPreimage R ns) d = choicesOf R d.
    Proof.
      intros R ns d Hm; unfold choicesOf.
      rewrite evalReq_preimage; [reflexivity | exact Hm].
    Qed.

    Lemma firesOf_preimage : forall R ns d,
        NSet.In (sTarget d) ns ->
        firesOf (realPreimage R ns) d = firesOf R d.
    Proof.
      intros R ns d Hm; unfold firesOf.
      rewrite evalReq_preimage; [reflexivity | exact Hm].
    Qed.

    Lemma ownSlots_idem : forall Slots p,
        ownSlots (ownSlots Slots p) p = ownSlots Slots p.
    Proof.
      intros Slots p; apply SlotRel.ext; intros [q d].
      rewrite !mem_ownSlots; tauto.
    Qed.

    Lemma ownFDefs_idem : forall FDefs p,
        ownFDefs (ownFDefs FDefs p) p = ownFDefs FDefs p.
    Proof.
      intros FDefs p; apply FDefRel.ext; intros [[q f] e].
      rewrite !mem_ownFDefs; tauto.
    Qed.

    Lemma ownLinks_idem : forall Links p,
        ownLinks (ownLinks Links p) p = ownLinks Links p.
    Proof.
      intros Links p; apply LinkRel.ext; intros [q l].
      rewrite !mem_ownLinks; tauto.
    Qed.

    Lemma slotsAt_own : forall Slots cfgActive rc p a,
        slotsAt (ownSlots Slots p) cfgActive rc p a =
        slotsAt Slots cfgActive rc p a.
    Proof.
      intros Slots cfgActive rc p a; apply SlotRel.ext; intros [q d].
      rewrite !mem_slotsAt, mem_ownSlots; tauto.
    Qed.

    Theorem versions_lookupCrate : forall R FDefs Slots Links cfgActive rc n,
        versions (realPreimage R (NSet.singleton n)) FDefs Slots Links
          cfgActive rc (NPlus.Crate n) =
        versions R FDefs Slots Links cfgActive rc (NPlus.Crate n).
    Proof.
      intros; simpl.
      rewrite srcVersions_preimage; [reflexivity |].
      apply NSet.singleton_spec; reflexivity.
    Qed.

    (* The names a slot or decision query reads: the targets of the owner's
       active slots at the queried alias, and nothing else.  crateReads,
       which the driver hands these two queries, is wider -- it adds the
       owner's own name (the link guard's read) and the targets of its
       slots at every other alias. *)
    Definition aliasReads (Slots : SlotRel.t) (cfgActive : CfgS.t -> bool)
        (rc p : Pkg.t) (a : N.t) : NSet.t :=
      SOsn2.map (fun '(_, d) => sTarget d) (slotsAt Slots cfgActive rc p a).

    Lemma mem_aliasReads : forall Slots cfgActive rc p a q d,
        SlotRel.In (q, d) (slotsAt Slots cfgActive rc p a) ->
        NSet.In (sTarget d) (aliasReads Slots cfgActive rc p a).
    Proof.
      intros Slots cfgActive rc p a q d Hd; apply SOsn2.mem_map.
      exists (q, d); split; [exact Hd | reflexivity].
    Qed.

    Lemma aliasReads_crateReads : forall Slots cfgActive rc p a,
        NSet.Subset (aliasReads Slots cfgActive rc p a) (crateReads Slots p).
    Proof.
      intros Slots cfgActive rc p a m Hm.
      apply SOsn2.mem_map in Hm; destruct Hm as [[q d] [Hq Hm]].
      cbn beta iota in Hm; subst m.
      apply mem_slotsAt in Hq; destruct Hq as [HqS [-> _]].
      exact (mem_crateReads_target Slots p d HqS).
    Qed.

    (* A slot name's versions are the choices its owner's active slots at
       that alias admit: the feature and link tables are never consulted,
       the slot table only through slotsAt, and the repository only at the
       targets of those slots. *)
    Lemma versions_slotN_agree :
      forall R R' FDefs FDefs' Slots Slots' Links Links' cfgActive rc n v a,
        slotsAt Slots' cfgActive rc (n, v) a =
          slotsAt Slots cfgActive rc (n, v) a ->
        (forall q d,
            SlotRel.In (q, d) (slotsAt Slots cfgActive rc (n, v) a) ->
            evalReq R' (sTarget d) (sReq d) =
              evalReq R (sTarget d) (sReq d)) ->
        versions R' FDefs' Slots' Links' cfgActive rc (NPlus.SlotN n v a) =
        versions R FDefs Slots Links cfgActive rc (NPlus.SlotN n v a).
    Proof.
      intros R R' FDefs FDefs' Slots Slots' Links Links' cfgActive rc n v a
        Hs Hr; cbn [versions]; rewrite Hs.
      apply FC.VSet.ext; intro w; rewrite !SOsv.mem_unionMap.
      split; intros [[q d] [Hq Hw]]; exists (q, d); split; try exact Hq;
        cbn beta iota in Hw |- *;
        [rewrite <- (Hr q d Hq) | rewrite (Hr q d Hq)]; exact Hw.
    Qed.

    Theorem versions_lookupSlot :
      forall R FDefs FDefs' Slots Links Links' cfgActive rc n v a,
        versions (realPreimage R (crateReads Slots (n, v))) FDefs'
          (ownSlots Slots (n, v)) Links' cfgActive rc (NPlus.SlotN n v a) =
        versions R FDefs Slots Links cfgActive rc (NPlus.SlotN n v a).
    Proof.
      intros R FDefs FDefs' Slots Links Links' cfgActive rc n v a.
      apply versions_slotN_agree; [apply slotsAt_own |].
      intros q d Hq; apply evalReq_preimage.
      apply (aliasReads_crateReads Slots cfgActive rc (n, v) a).
      exact (mem_aliasReads Slots cfgActive rc (n, v) a q d Hq).
    Qed.

    Lemma fdEntryb_own : forall FDefs p f a feat,
        fdEntryb (ownFDefs FDefs p) p f a feat = fdEntryb FDefs p f a feat.
    Proof.
      intros FDefs p f a feat; unfold fdEntryb.
      assert (H : forall e, FDefRel.mem ((p, f), e) (ownFDefs FDefs p) =
                            FDefRel.mem ((p, f), e) FDefs).
      { intro e; apply FDefRel.mem_restrict.
        - intros [[q g] e'] Hx.
          exact (proj1 (proj1 (mem_ownFDefs FDefs p q g e') Hx)).
        - intro Hx; apply mem_ownFDefs; split; [exact Hx | reflexivity]. }
      rewrite !H; reflexivity.
    Qed.

    (* A decision name's versions add VOff to the fires of the same slots
       the slot name reads, gated by the owner's own feature entry: the
       link table is never consulted, the feature table only at the
       owner's rows, and the repository only at those slots' targets. *)
    Lemma versions_decisionN_agree :
      forall R R' FDefs FDefs' Slots Slots' Links Links' cfgActive rc
             n v f a feat,
        fdEntryb FDefs' (n, v) f a feat = fdEntryb FDefs (n, v) f a feat ->
        slotsAt Slots' cfgActive rc (n, v) a =
          slotsAt Slots cfgActive rc (n, v) a ->
        (forall q d,
            SlotRel.In (q, d) (slotsAt Slots cfgActive rc (n, v) a) ->
            evalReq R' (sTarget d) (sReq d) =
              evalReq R (sTarget d) (sReq d)) ->
        versions R' FDefs' Slots' Links' cfgActive rc
          (NPlus.DecisionN n v f a feat) =
        versions R FDefs Slots Links cfgActive rc
          (NPlus.DecisionN n v f a feat).
    Proof.
      intros R R' FDefs FDefs' Slots Slots' Links Links' cfgActive rc
        n v f a feat Hf Hs Hr; cbn [versions]; rewrite Hf, Hs.
      destruct (fdEntryb FDefs (n, v) f a feat); [| reflexivity].
      apply FC.VSet.ext; intro w; rewrite !SOsv.mem_unionMap.
      split; intros [[q d] [Hq Hw]]; exists (q, d); split; try exact Hq;
        cbn beta iota in Hw |- *;
        [rewrite <- (Hr q d Hq) | rewrite (Hr q d Hq)]; exact Hw.
    Qed.

    Theorem versions_lookupDecision :
      forall R FDefs Slots Links Links' cfgActive rc n v f a feat,
        versions (realPreimage R (crateReads Slots (n, v)))
          (ownFDefs FDefs (n, v)) (ownSlots Slots (n, v)) Links' cfgActive rc
          (NPlus.DecisionN n v f a feat) =
        versions R FDefs Slots Links cfgActive rc
          (NPlus.DecisionN n v f a feat).
    Proof.
      intros R FDefs Slots Links Links' cfgActive rc n v f a feat.
      apply versions_decisionN_agree;
        [apply fdEntryb_own | apply slotsAt_own |].
      intros q d Hq; apply evalReq_preimage.
      apply (aliasReads_crateReads Slots cfgActive rc (n, v) a).
      exact (mem_aliasReads Slots cfgActive rc (n, v) a q d Hq).
    Qed.

    Definition linksAt (Links : LinkRel.t) (l : L.t) : LinkRel.t :=
      LinkRel.filter (fun '(_, l') => LEqb.eqb l' l) Links.

    Lemma mem_linksAt : forall Links l q l',
        LinkRel.In (q, l') (linksAt Links l) <->
        LinkRel.In (q, l') Links /\ l' = l.
    Proof.
      intros Links l q l'; unfold linksAt; rewrite LinkRel.filter_spec'.
      rewrite LEqb.eqb_true_iff; tauto.
    Qed.

    (* The crates declaring a link: the only packages a link query's
       membership test can reach. *)
    Definition linkPkgs (Links : LinkRel.t) (l : L.t) : PkgSet.t :=
      linkOwners (linksAt Links l).

    Lemma mem_linkPkgs : forall Links l q,
        PkgSet.In q (linkPkgs Links l) <-> LinkRel.In (q, l) Links.
    Proof.
      intros Links l q; unfold linkPkgs, linkOwners; rewrite SOlo.mem_map.
      split.
      - intros [[q' l'] [Hq Hm]]; cbn [fst] in Hm; subst q'.
        apply mem_linksAt in Hq; destruct Hq as [Hq ->]; exact Hq.
      - intro Hq; exists (q, l); split; [| reflexivity].
        apply mem_linksAt; split; [exact Hq | reflexivity].
    Qed.

    Lemma versions_linkN_agree :
      forall R R' FDefs FDefs' Slots Slots' Links Links' cfgActive rc l,
        (forall q, LinkRel.In (q, l) Links' <-> LinkRel.In (q, l) Links) ->
        (forall q, LinkRel.In (q, l) Links ->
           PkgSet.mem q R' = PkgSet.mem q R) ->
        versions R' FDefs' Slots' Links' cfgActive rc (NPlus.LinkN l) =
        versions R FDefs Slots Links cfgActive rc (NPlus.LinkN l).
    Proof.
      intros R R' FDefs FDefs' Slots Slots' Links Links' cfgActive rc l HL HR.
      cbn [versions]; apply FC.VSet.ext; intro w.
      rewrite !SOlv.mem_filterMap; split.
      - intros [[q l'] [Hq Hw]]; cbn beta iota in Hw.
        destruct (andb (LEqb.eqb l' l) (PkgSet.mem q R')) eqn:Eb;
          [| discriminate].
        apply andb_true_iff in Eb; destruct Eb as [El Em].
        apply LEqb.eqb_true_iff in El; subst l'.
        injection Hw as <-.
        assert (HqL : LinkRel.In (q, l) Links) by (apply HL; exact Hq).
        exists (q, l); split; [exact HqL | cbn beta iota].
        rewrite LEqb.eqb_refl, <- (HR q HqL), Em; reflexivity.
      - intros [[q l'] [Hq Hw]]; cbn beta iota in Hw.
        destruct (andb (LEqb.eqb l' l) (PkgSet.mem q R)) eqn:Eb;
          [| discriminate].
        apply andb_true_iff in Eb; destruct Eb as [El Em].
        apply LEqb.eqb_true_iff in El; subst l'.
        injection Hw as <-.
        exists (q, l); split; [apply HL; exact Hq | cbn beta iota].
        rewrite LEqb.eqb_refl, (HR q Hq), Em; reflexivity.
    Qed.

    (* A link name's versions are its declarers that the repository has, so
       the slice keeps the intersection: dropping it would answer for a
       declarer the repository does not carry, and no hypothesis here says
       there is none. *)
    Theorem versions_lookupLink :
      forall R FDefs FDefs' Slots Slots' Links cfgActive rc l,
        versions (PkgSet.inter R (linkPkgs Links l)) FDefs' Slots'
          (linksAt Links l) cfgActive rc (NPlus.LinkN l) =
        versions R FDefs Slots Links cfgActive rc (NPlus.LinkN l).
    Proof.
      intros R FDefs FDefs' Slots Slots' Links cfgActive rc l.
      apply versions_linkN_agree.
      - intro q; rewrite mem_linksAt; tauto.
      - intros q Hq; apply PkgSet.mem_restrict.
        + intros x Hx; apply PkgSet.inter_spec in Hx; tauto.
        + intro Hx; apply PkgSet.inter_spec; split;
            [exact Hx | apply mem_linkPkgs; exact Hq].
    Qed.

    Theorem dependees_lookupCrate :
      forall R FDefs Slots Links cfgActive dflt rc p,
        dependees (realPreimage R (crateReads Slots p))
          (ownFDefs FDefs p) (ownSlots Slots p) (ownLinks Links p)
          cfgActive dflt rc p =
        dependees R FDefs Slots Links cfgActive dflt rc p.
    Proof.
      intros R FDefs Slots Links cfgActive dflt rc p; unfold dependees.
      rewrite ownSlots_idem, ownFDefs_idem, ownLinks_idem.
      apply FC.Feat.FeatDepRel.ext; intro e.
      rewrite !FC.Feat.FeatDepRel.union_spec.
      apply Morphisms_Prop.or_iff_morphism.
      { split; intro H; apply mem_slotHop1 in H;
          destruct H as [n [v [d [Hs [Hact [Hopt He]]]]]];
          apply mem_slotHop1; exists n, v, d;
          assert (Hp : (n, v) = p)
            by (apply (proj1 (mem_ownSlots Slots p (n, v) d)) in Hs;
                tauto);
          assert (Hs' : SlotRel.In ((n, v), d) Slots)
            by (apply (proj1 (mem_ownSlots Slots p (n, v) d)) in Hs;
                tauto);
          (rewrite choicesOf_preimage in He
           + rewrite <- (choicesOf_preimage R (crateReads Slots p) d)
               in He);
          try (subst p; apply (mem_crateReads_target Slots (n, v) d);
               exact Hs');
          repeat split; assumption. }
      apply Morphisms_Prop.or_iff_morphism.
      { split; intro H; apply mem_slotHop2 in H;
          destruct H as [n [v [d [u [Hs [Hact [Hu He]]]]]]];
          apply mem_slotHop2; exists n, v, d, u;
          assert (Hp : (n, v) = p)
            by (apply (proj1 (mem_ownSlots Slots p (n, v) d)) in Hs;
                tauto);
          assert (Hs' : SlotRel.In ((n, v), d) Slots)
            by (apply (proj1 (mem_ownSlots Slots p (n, v) d)) in Hs;
                tauto);
          (rewrite evalReq_preimage in Hu
           + rewrite <- (evalReq_preimage R (crateReads Slots p)
                           (sTarget d) (sReq d)) in Hu);
          try (subst p; apply (mem_crateReads_target Slots (n, v) d);
               exact Hs');
          repeat split; assumption. }
      apply Morphisms_Prop.or_iff_morphism.
      { split; intro H; apply mem_linkEdges in H;
          destruct H as [n [v [l [Hl [HR He]]]]];
          apply mem_linkEdges; exists n, v, l;
          assert (Hp : (n, v) = p)
            by (apply (proj1 (mem_ownLinks Links p (n, v) l)) in Hl;
                tauto);
          (rewrite (mem_preimage R (crateReads Slots p) (n, v)) in HR
           + rewrite <- (mem_preimage R (crateReads Slots p) (n, v))
               in HR);
          try (rewrite Hp; apply NSet.add_spec; left; reflexivity);
          repeat split; assumption. }
      { split; intro H; apply mem_decisionEdges in H;
          destruct H
            as [n [v [f [e' [a [feat [d [u [Hf [Hd [Hs [Ha [Hact
               [Hu He]]]]]]]]]]]]]].
        - assert (Hp : (n, v) = p)
            by (apply (proj1 (mem_ownFDefs FDefs p (n, v) f e')) in Hf;
                tauto).
          subst p.
          apply (proj1 (mem_ownSlots Slots (n, v) (n, v) d)) in Hs;
            destruct Hs as [Hs _].
          rewrite evalReq_preimage in Hu;
            [| apply (mem_crateReads_target Slots (n, v) d); exact Hs].
          apply mem_decisionEdges; exists n, v, f, e', a, feat, d, u.
          repeat split; assumption.
        - assert (Hp : (n, v) = p)
            by (apply (proj1 (mem_ownFDefs FDefs p (n, v) f e')) in Hf;
                tauto).
          subst p.
          rewrite <- (evalReq_preimage R (crateReads Slots (n, v))
                        (sTarget d) (sReq d)) in Hu;
            [| apply (mem_crateReads_target Slots (n, v) d); exact Hs].
          apply mem_decisionEdges; exists n, v, f, e', a, feat, d, u.
          repeat split; try assumption.
          apply mem_ownSlots; split; [exact Hs | reflexivity]. }
    Qed.

    Theorem addlDependees_lookupCrate :
      forall R FDefs Slots cfgActive rc p,
        addlDependees (realPreimage R (crateReads Slots p))
          (ownFDefs FDefs p) (ownSlots Slots p) cfgActive rc p =
        addlDependees R FDefs Slots cfgActive rc p.
    Proof.
      intros R FDefs Slots cfgActive rc p; unfold addlDependees.
      rewrite ownFDefs_idem.
      apply FC.Feat.AddlDepRel.ext; intro e.
      rewrite !FC.Feat.AddlDepRel.union_spec.
      apply Morphisms_Prop.or_iff_morphism; [reflexivity |].
      apply Morphisms_Prop.or_iff_morphism.
      { split; intro H; apply mem_activationEdges in H;
          destruct H as [n [v [f [e' [a [d [Hf [Hd [Hs [Ha [Hact
             He]]]]]]]]]]].
        - assert (Hp : (n, v) = p)
            by (apply (proj1 (mem_ownFDefs FDefs p (n, v) f e')) in Hf;
                tauto).
          subst p.
          apply (proj1 (mem_ownSlots Slots (n, v) (n, v) d)) in Hs;
            destruct Hs as [Hs _].
          rewrite choicesOf_preimage in He;
            [| apply (mem_crateReads_target Slots (n, v) d); exact Hs].
          apply mem_activationEdges; exists n, v, f, e', a, d.
          repeat split; assumption.
        - assert (Hp : (n, v) = p)
            by (apply (proj1 (mem_ownFDefs FDefs p (n, v) f e')) in Hf;
                tauto).
          subst p.
          rewrite <- (choicesOf_preimage R (crateReads Slots (n, v)) d)
            in He;
            [| apply (mem_crateReads_target Slots (n, v) d); exact Hs].
          apply mem_activationEdges; exists n, v, f, e', a, d.
          repeat split; try assumption.
          apply mem_ownSlots; split; [exact Hs | reflexivity]. }
      apply Morphisms_Prop.or_iff_morphism.
      { split; intro H; apply mem_witEnableEdges in H;
          destruct H
            as [n [v [f [e' [a [feat [d [Hf [Hd [Hs [Ha [Hact
               He]]]]]]]]]]]].
        - assert (Hp : (n, v) = p)
            by (apply (proj1 (mem_ownFDefs FDefs p (n, v) f e')) in Hf;
                tauto).
          subst p.
          apply (proj1 (mem_ownSlots Slots (n, v) (n, v) d)) in Hs;
            destruct Hs as [Hs _].
          rewrite firesOf_preimage in He;
            [| apply (mem_crateReads_target Slots (n, v) d); exact Hs].
          apply mem_witEnableEdges; exists n, v, f, e', a, feat, d.
          repeat split; assumption.
        - assert (Hp : (n, v) = p)
            by (apply (proj1 (mem_ownFDefs FDefs p (n, v) f e')) in Hf;
                tauto).
          subst p.
          rewrite <- (firesOf_preimage R (crateReads Slots (n, v)) d)
            in He;
            [| apply (mem_crateReads_target Slots (n, v) d); exact Hs].
          apply mem_witEnableEdges; exists n, v, f, e', a, feat, d.
          repeat split; try assumption.
          apply mem_ownSlots; split; [exact Hs | reflexivity]. }
      { split; intro H; apply mem_witDeliverEdges in H;
          destruct H
            as [n [v [f [e' [a [feat [d [u [Hf [Hd [Hs [Ha [Hact
               [Hu He]]]]]]]]]]]]]].
        - assert (Hp : (n, v) = p)
            by (apply (proj1 (mem_ownFDefs FDefs p (n, v) f e')) in Hf;
                tauto).
          subst p.
          apply (proj1 (mem_ownSlots Slots (n, v) (n, v) d)) in Hs;
            destruct Hs as [Hs _].
          rewrite evalReq_preimage in Hu;
            [| apply (mem_crateReads_target Slots (n, v) d); exact Hs].
          apply mem_witDeliverEdges; exists n, v, f, e', a, feat, d, u.
          repeat split; assumption.
        - assert (Hp : (n, v) = p)
            by (apply (proj1 (mem_ownFDefs FDefs p (n, v) f e')) in Hf;
                tauto).
          subst p.
          rewrite <- (evalReq_preimage R (crateReads Slots (n, v))
                        (sTarget d) (sReq d)) in Hu;
            [| apply (mem_crateReads_target Slots (n, v) d); exact Hs].
          apply mem_witDeliverEdges; exists n, v, f, e', a, feat, d, u.
          repeat split; try assumption.
          apply mem_ownSlots; split; [exact Hs | reflexivity]. }
    Qed.

    Lemma ownSupport_idem : forall support p,
        ownSupport (ownSupport support p) p = ownSupport support p.
    Proof.
      intros support p; apply SupportSet.ext; intros [q f].
      rewrite !mem_ownSupport; tauto.
    Qed.

    Theorem supportAt_lookupCrate :
      forall R support FDefs Slots cfgActive rc p,
        supportAt (realPreimage R (crateReads Slots p))
          (ownSupport support p) (ownFDefs FDefs p) (ownSlots Slots p)
          cfgActive rc p =
        supportAt R support FDefs Slots cfgActive rc p.
    Proof.
      intros R support FDefs Slots cfgActive rc p; unfold supportAt.
      rewrite ownSupport_idem, ownFDefs_idem.
      apply FC.Feat.SupportSet.ext; intro y.
      rewrite !FC.Feat.SupportSet.union_spec.
      apply Morphisms_Prop.or_iff_morphism; [reflexivity |].
      rewrite !SOfs.mem_unionMap.
      split; intros [[[[n v] f] e] [Hf Hy]]; cbn beta iota in Hy.
      - assert (Hp : (n, v) = p)
          by (apply (proj1 (mem_ownFDefs FDefs p (n, v) f e)) in Hf;
              tauto).
        subst p.
        exists (((n, v), f), e); split; [exact Hf |]; cbn beta iota.
        destruct (entryFeatD e) as [[a feat] |] eqn:Ee;
          [| exfalso; exact (SOss2.empty_in _ Hy)].
        apply SOss2.mem_unionMap in Hy; destruct Hy as [[q d] [Hq Hy]];
          cbn beta iota in Hy.
        rewrite slotsAt_own in Hq.
        apply mem_slotsAt in Hq; destruct Hq as [HqS [-> [Ha2 Hact]]].
        rewrite evalReq_preimage in Hy;
          [| apply (mem_crateReads_target Slots (n, v) d); exact HqS].
        apply SOss2.mem_unionMap; exists ((n, v), d); split.
        { apply mem_slotsAt; repeat split; assumption. }
        cbn beta iota; exact Hy.
      - assert (Hp : (n, v) = p)
          by (apply (proj1 (mem_ownFDefs FDefs p (n, v) f e)) in Hf;
              tauto).
        subst p.
        exists (((n, v), f), e); split; [exact Hf |]; cbn beta iota.
        destruct (entryFeatD e) as [[a feat] |] eqn:Ee;
          [| exfalso; exact (SOss2.empty_in _ Hy)].
        apply SOss2.mem_unionMap in Hy; destruct Hy as [[q d] [Hq Hy]];
          cbn beta iota in Hy.
        apply mem_slotsAt in Hq; destruct Hq as [HqS [-> [Ha2 Hact]]].
        rewrite <- (evalReq_preimage R (crateReads Slots (n, v))
                      (sTarget d) (sReq d)) in Hy;
          [| apply (mem_crateReads_target Slots (n, v) d); exact HqS].
        apply SOss2.mem_unionMap; exists ((n, v), d); split.
        { rewrite slotsAt_own; apply mem_slotsAt; repeat split;
            assumption. }
        cbn beta iota; exact Hy.
    Qed.
  End Lookup.
End Cargo.
