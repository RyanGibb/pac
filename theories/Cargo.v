From Stdlib Require Import MSets Bool.
From PackageCalculus Require Import Prelude Core Semver ConflictClass.

Create HintDb cmp_cargo.
Create Rewrite HintDb cmp_cargo.

Module Cargo (N V F G CfgS Src : UsualOrderedType) (PM : SemverMatch V).
  Module C := Core N V.
  Module Pkg := C.Pkg.
  Module PkgSet := C.PkgSet.
  Module VSet := C.VSet.

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

  Module SKTail := PairUOT KindOT CfgS.
  Module SlotKey := PairUOT N SKTail.
  Definition sKey (d : SlotData.t) : SlotKey.t :=
    (sAlias d, (sKind d, sCfg d)).
  Definition kAlias (k : SlotKey.t) : N.t := fst k.

  Module LinkElt := PairUOT Pkg N.
  Module LinkRel := FSetUOT LinkElt.

  Module NAPair := PairUOT Pkg SlotKey.
  Module ParentElt := PairUOT NAPair V.
  Module ParentRel := FSetUOT ParentElt.

  Definition slotActive (rc p : Pkg.t) (d : SlotData.t) : bool :=
    match sKind d with
    | Kind.KDev => if Pkg.eq_dec p rc then true else false
    | _ => true
    end.

  Definition Activated (FDefs : FDefRel.t) (fs : FSet.t) (p : Pkg.t)
      (a : N.t) : Prop :=
    exists f, FSet.In f fs /\
      (FDefRel.In ((p, f), FEntry.EDep a) FDefs \/
       (exists feat, FDefRel.In ((p, f), FEntry.EDepFeat a feat) FDefs) \/
       (exists feat, FDefRel.In ((p, f), FEntry.EWeakFeat a feat) FDefs)).

  Definition slotRequests (d : SlotData.t) (dflt : F.t) : FSet.t :=
    if sDefault d then FSet.add dflt (sReqFeats d) else sReqFeats d.

  #[local] Set Implicit Arguments.
  Record IsResolution
      (R : PkgSet.t) (support : SupportSet.t) (FDefs : FDefRel.t)
      (Slots : SlotRel.t) (Links : LinkRel.t)
      (g : V.t -> G.t) (dflt : F.t)
      (rc : Pkg.t) (rootFeats : FSet.t)
      (S : PkgSet.t) (FS : FeaturedSet.t) (pi : ParentRel.t) : Prop :=
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
    ; res_gran_unique :
        forall m v v', PkgSet.In (m, v) S -> PkgSet.In (m, v') S ->
        v <> v' -> g v <> g v'
    ; res_support_mem :
        forall p fs f, FeaturedSet.In (p, fs) FS -> FSet.In f fs ->
        SupportSet.In (p, f) support
    ; res_pi_functional :
        forall p k u u', ParentRel.In ((p, k), u) pi ->
        ParentRel.In ((p, k), u') pi -> u = u'
    ; res_pi_dom :
        forall p k u, ParentRel.In ((p, k), u) pi ->
        exists fs d, FeaturedSet.In (p, fs) FS /\ SlotRel.In (p, d) Slots /\
          sKey d = k /\ slotActive rc p d = true /\
          (sOptional d = false \/ Activated FDefs fs p (sAlias d))
    ; res_slot_closure :
        forall p fs, PkgSet.In p S -> FeaturedSet.In (p, fs) FS ->
        forall d, SlotRel.In (p, d) Slots ->
        slotActive rc p d = true ->
        (sOptional d = false \/ Activated FDefs fs p (sAlias d)) ->
        exists u, ParentRel.In ((p, sKey d), u) pi /\
          rgHolds (sReq d) u = true /\ PkgSet.In (sTarget d, u) S /\
          forall fs', FeaturedSet.In ((sTarget d, u), fs') FS ->
          FSet.Subset (slotRequests d dflt) fs'
    ; res_feat_closure_same :
        forall p fs f f', FeaturedSet.In (p, fs) FS -> FSet.In f fs ->
        FDefRel.In ((p, f), FEntry.EFeat f') FDefs -> FSet.In f' fs
    ; res_feat_closure_dep :
        forall p fs f a feat, FeaturedSet.In (p, fs) FS -> FSet.In f fs ->
        (FDefRel.In ((p, f), FEntry.EDepFeat a feat) FDefs \/
         FDefRel.In ((p, f), FEntry.EWeakFeat a feat) FDefs) ->
        forall d u, SlotRel.In (p, d) Slots -> sAlias d = a ->
        ParentRel.In ((p, sKey d), u) pi ->
        forall fs', FeaturedSet.In ((sTarget d, u), fs') FS ->
        FSet.In feat fs'
    ; res_links_unique :
        forall p q l, PkgSet.In p S -> PkgSet.In q S ->
        LinkRel.In (p, l) Links -> LinkRel.In (q, l) Links -> p = q }.
  #[local] Unset Implicit Arguments.

  Module GF := UOTCompareFacts G.
  Module VF := UOTCompareFacts V.
  Module SlotName := TripleUOT N G SlotData.
  Module SlotNameF := UOTCompareFacts SlotName.
  Module FDTail := TripleUOT F SlotData F.
  Module DecName := TripleUOT N G FDTail.
  Module DecNameF := UOTCompareFacts DecName.
  #[local] Hint Rewrite GF.compare_eq_iff VF.compare_eq_iff
    SlotNameF.compare_eq_iff DecNameF.compare_eq_iff : cmp_cargo.
  #[local] Hint Extern 1 => cmp_by GF.compare_antisym : cmp_cargo.
  #[local] Hint Extern 1 => cmp_by VF.compare_antisym : cmp_cargo.
  #[local] Hint Extern 1 => cmp_by SlotNameF.compare_antisym : cmp_cargo.
  #[local] Hint Extern 1 => cmp_by DecNameF.compare_antisym : cmp_cargo.
  #[local] Hint Extern 1 => cmp_by GF.compare_lt_trans : cmp_cargo.
  #[local] Hint Extern 1 => cmp_by VF.compare_lt_trans : cmp_cargo.
  #[local] Hint Extern 1 => cmp_by SlotNameF.compare_lt_trans : cmp_cargo.
  #[local] Hint Extern 1 => cmp_by DecNameF.compare_lt_trans : cmp_cargo.

  Module NEqb := UOTEqb N.
  Module PkgEqb := UOTEqb Pkg.
  Module SKEqb := UOTEqb SlotKey.

  Module SOpv := SetOps Pkg V PkgSet VSet.
  Definition evalReq (R : PkgSet.t) (m : N.t) (rg : Range) : VSet.t :=
    SOpv.filterMap (fun '(o, u) =>
        if NEqb.eqb o m then if rgHolds rg u then Some u else None
        else None)
      R.

  Lemma mem_evalReq : forall R m rg u,
      VSet.In u (evalReq R m rg) <->
      PkgSet.In (m, u) R /\ rgHolds rg u = true.
  Proof.
    intros R m rg u; unfold evalReq; rewrite SOpv.mem_filterMap.
    split.
    - intros [[o w] [HR He]]; cbn beta iota in He.
      destruct (NEqb.eqb o m) eqn:En; [| discriminate].
      apply NEqb.eqb_true_iff in En; subst o.
      rewrite if_some_iff in He; destruct He as [Hv <-]; split; assumption.
    - intros [HR Hv]; exists (m, u); split; [exact HR | cbn beta iota].
      rewrite NEqb.eqb_refl, Hv; reflexivity.
  Qed.

  Definition slotsAt (Slots : SlotRel.t)
      (rc : Pkg.t) (p : Pkg.t) (a : N.t) : SlotRel.t :=
    SlotRel.filter (fun '(q, d) =>
        andb (if Pkg.eq_dec q p then true else false)
          (andb (NEqb.eqb (sAlias d) a) (slotActive rc q d)))
      Slots.

  Lemma mem_slotsAt : forall Slots rc p a q d,
      SlotRel.In (q, d) (slotsAt Slots rc p a) <->
      SlotRel.In (q, d) Slots /\ q = p /\ sAlias d = a /\
      slotActive rc q d = true.
  Proof.
    intros Slots rc p a q d; unfold slotsAt.
    rewrite SlotRel.filter_spec'; cbn beta iota.
    rewrite !andb_true_iff, NEqb.eqb_true_iff.
    destruct (Pkg.eq_dec q p); intuition congruence.
  Qed.

  Definition slotsAtKey (Slots : SlotRel.t)
      (rc : Pkg.t) (p : Pkg.t) (k : SlotKey.t) : SlotRel.t :=
    SlotRel.filter (fun '(q, d) =>
        andb (if Pkg.eq_dec q p then true else false)
          (andb (SKEqb.eqb (sKey d) k) (slotActive rc q d)))
      Slots.

  Lemma mem_slotsAtKey : forall Slots rc p k q d,
      SlotRel.In (q, d) (slotsAtKey Slots rc p k) <->
      SlotRel.In (q, d) Slots /\ q = p /\ sKey d = k /\
      slotActive rc q d = true.
  Proof.
    intros Slots rc p k q d; unfold slotsAtKey.
    rewrite SlotRel.filter_spec'; cbn beta iota.
    rewrite !andb_true_iff, SKEqb.eqb_true_iff.
    destruct (Pkg.eq_dec q p); intuition congruence.
  Qed.

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
    | FEntry.EWeakFeat a _ => Some a
    | _ => None
    end.

  Definition SiteFunctional (Slots : SlotRel.t) : Prop :=
    forall p d d', SlotRel.In (p, d) Slots -> SlotRel.In (p, d') Slots ->
    sKey d = sKey d' -> d = d'.

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
      rewrite !andb_true_iff, PkgEqb.eqb_true_iff, FSet.mem_spec in Hb.
      destruct Hb as [-> [Hf Ha]]; exists f; split; [exact Hf |].
      destruct e; cbn in Ha; try discriminate;
        apply NEqb.eqb_true_iff in Ha; subst a; eauto.
    - intros [f [Hf He]]; apply FSet.mem_spec in Hf.
      destruct He as [He | [[feat He] | [feat He]]];
        (eexists; split; [exact He |]);
        cbn [entryActivates]; rewrite PkgEqb.eqb_refl, Hf, NEqb.eqb_refl;
        reflexivity.
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
     result stays computable, pinned by res_fs_functional in proofs. *)
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

  Definition parentsb (FDefs : FDefRel.t) (Slots : SlotRel.t)
      (rc : Pkg.t)
      (S : PkgSet.t) (FS : FeaturedSet.t) (q : Pkg.t) (k : SlotKey.t)
    : bool :=
    andb (PkgSet.mem q S)
      (SlotRel.exists_ (fun '(q', d) =>
           andb (PkgEqb.eqb q' q)
             (andb (SKEqb.eqb (sKey d) k)
                (andb (slotActive rc q' d)
                   (requiredb FDefs (fsAt FS q) q d))))
         Slots).

  Lemma parentsb_iff : forall FDefs Slots rc S FS q k,
      parentsb FDefs Slots rc S FS q k = true <->
      PkgSet.In q S /\
      exists d, SlotRel.In (q, d) Slots /\ sKey d = k /\
        slotActive rc q d = true /\
        (sOptional d = false \/
         Activated FDefs (fsAt FS q) q (sAlias d)).
  Proof.
    intros FDefs Slots rc S FS q k; unfold parentsb.
    rewrite andb_true_iff, PkgSet.mem_spec, SlotRel.exists_spec'.
    split.
    - intros [HS [[q' d] [Hd Hb]]]; cbn beta iota in Hb.
      rewrite !andb_true_iff, PkgEqb.eqb_true_iff, SKEqb.eqb_true_iff,
        requiredb_iff in Hb.
      destruct Hb as [-> Hb]; split; [exact HS |]; exists d; tauto.
    - intros [HS [d [Hd [<- [Hact Hreq]]]]]; split; [exact HS |].
      exists (q, d); split; [exact Hd | cbn beta iota].
      apply requiredb_iff in Hreq.
      rewrite PkgEqb.eqb_refl, SKEqb.eqb_refl, Hact, Hreq; reflexivity.
  Qed.

  Module NGPair := PairUOT N G.
  Module NFGTrip := TripleUOT N F G.
  Module NGF := UOTCompareFacts NGPair.
  Module NFGF := UOTCompareFacts NFGTrip.
  Module GEqb := UOTEqb G.
  Module FEqb := UOTEqb F.
  #[local] Hint Rewrite NGF.compare_eq_iff NFGF.compare_eq_iff : cmp_cargo.
  #[local] Hint Extern 1 => cmp_by NGF.compare_antisym : cmp_cargo.
  #[local] Hint Extern 1 => cmp_by NFGF.compare_antisym : cmp_cargo.
  #[local] Hint Extern 1 => cmp_by NGF.compare_lt_trans : cmp_cargo.
  #[local] Hint Extern 1 => cmp_by NFGF.compare_lt_trans : cmp_cargo.

  Module NPlus.
    Inductive name : Type :=
    | CRoot
    | CCrate (m : N.t) (gr : G.t)
    | CFeatP (m : N.t) (f : F.t) (gr : G.t)
    | CSlot (m : N.t) (gr : G.t) (d : SlotData.t)
    | CDec (m : N.t) (gr : G.t) (f : F.t) (d : SlotData.t) (feat : F.t)
    | CLink (l : N.t).
    Definition t := name.

    Definition rank (x : t) : nat :=
      match x with
      | CRoot => 0 | CCrate _ _ => 1 | CFeatP _ _ _ => 2
      | CSlot _ _ _ => 3 | CDec _ _ _ _ _ => 4 | CLink _ => 5
      end.

    Definition compare (x y : t) : comparison :=
      match Nat.compare (rank x) (rank y) with
      | Eq =>
          match x, y with
          | CCrate n1 g1, CCrate n2 g2 => NGPair.compare (n1, g1) (n2, g2)
          | CFeatP n1 f1 g1, CFeatP n2 f2 g2 =>
              NFGTrip.compare (n1, (f1, g1)) (n2, (f2, g2))
          | CSlot n1 v1 a1, CSlot n2 v2 a2 =>
              SlotName.compare (n1, (v1, a1)) (n2, (v2, a2))
          | CDec n1 v1 f1 a1 t1, CDec n2 v2 f2 a2 t2 =>
              DecName.compare (n1, (v1, (f1, (a1, t1))))
                (n2, (v2, (f2, (a2, t2))))
          | CLink l1, CLink l2 => N.compare l1 l2
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
  Module NPOTF := UOTCompareFacts NPOT.
  #[local] Hint Rewrite NPOTF.compare_eq_iff : cmp_cargo.
  #[local] Hint Extern 1 => cmp_by NPOTF.compare_antisym : cmp_cargo.
  #[local] Hint Extern 1 => cmp_by NPOTF.compare_lt_trans : cmp_cargo.

  Module VPlus.
    Inductive version : Type :=
    | WUnit
    | WOrig (v : V.t)
    | WClass (gr : G.t)
    | WName (n : NPlus.t).
    Definition t := version.

    Definition rank (x : t) : nat :=
      match x with
      | WUnit => 0 | WOrig _ => 1 | WClass _ => 2 | WName _ => 3
      end.

    Definition compare (x y : t) : comparison :=
      match Nat.compare (rank x) (rank y) with
      | Eq =>
          match x, y with
          | WOrig v1, WOrig v2 => V.compare v1 v2
          | WClass g1, WClass g2 => G.compare g1 g2
          | WName n1, WName n2 => NPOT.compare n1 n2
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

  (* Its core shared, so that the conflict class package calculus at the core's own
     sorts states its lookups over this T. *)
  Module ClsT := ConflictClass NPOT VPOT.
  Module T := ClsT.C.

  Module SOvp := SetOps V T.Pkg VSet T.PkgSet.
  Module SOpp := SetOps Pkg T.Pkg PkgSet T.PkgSet.
  Module SOsp := SetOps PkgF T.Pkg SupportSet T.PkgSet.
  Module SOslp := SetOps SlotElt T.Pkg SlotRel T.PkgSet.
  Module SOfp := SetOps FDefElt T.Pkg FDefRel T.PkgSet.
  Module SOlp := SetOps LinkElt T.Pkg LinkRel T.PkgSet.
  Module SOvv := SetOps V VPOT VSet T.VSet.

  Definition gransOf (g : V.t -> G.t) (vs : VSet.t) : T.VSet.t :=
    SOvv.map (fun u => VPlus.WClass (g u)) vs.

  Definition inGran (g : V.t -> G.t) (gr : G.t) (vs : VSet.t) : T.VSet.t :=
    SOvv.filterMap
      (fun u => if GEqb.eqb (g u) gr then Some (VPlus.WOrig u) else None) vs.

  Definition granMet (g : V.t -> G.t) (gr : G.t) (vs : VSet.t) : bool :=
    VSet.exists_ (fun u => GEqb.eqb (g u) gr) vs.

  Definition SlotOwned (g : V.t -> G.t) (Slots : SlotRel.t) (rc : Pkg.t)
      (m : N.t) (gr : G.t) (d : SlotData.t) : Prop :=
    exists v, g v = gr /\ SlotRel.In ((m, v), d) Slots /\
      slotActive rc (m, v) d = true.

  Definition DecOwned (g : V.t -> G.t) (FDefs : FDefRel.t) (Slots : SlotRel.t)
      (rc : Pkg.t) (m : N.t) (gr : G.t) (f : F.t) (d : SlotData.t)
      (feat : F.t) : Prop :=
    exists v e, g v = gr /\ FDefRel.In (((m, v), f), e) FDefs /\
      entryFeatD e = Some (sAlias d, feat) /\
      SlotRel.In ((m, v), d) Slots /\ slotActive rc (m, v) d = true.

  Module SDEqb := UOTEqb SlotData.

  Definition slotOwnedb (g : V.t -> G.t) (Slots : SlotRel.t) (rc : Pkg.t)
      (m : N.t) (gr : G.t) (d : SlotData.t) : bool :=
    SlotRel.exists_ (fun '((m', v), d') =>
        andb (NEqb.eqb m' m)
          (andb (GEqb.eqb (g v) gr)
             (andb (SDEqb.eqb d' d) (slotActive rc (m', v) d'))))
      Slots.

  Lemma slotOwnedb_iff : forall g Slots rc m gr d,
      slotOwnedb g Slots rc m gr d = true <-> SlotOwned g Slots rc m gr d.
  Proof.
    intros g Slots rc m gr d; unfold slotOwnedb, SlotOwned.
    rewrite SlotRel.exists_spec'; split.
    - intros [[[m' v] d'] [Hs Hb]]; cbn beta iota in Hb.
      rewrite !andb_true_iff, NEqb.eqb_true_iff, GEqb.eqb_true_iff,
        SDEqb.eqb_true_iff in Hb.
      destruct Hb as [-> [Hg [-> Hact]]]; exists v; repeat split; assumption.
    - intros [v [<- [Hs Hact]]].
      exists ((m, v), d); split; [exact Hs | cbn beta iota].
      rewrite NEqb.eqb_refl, GEqb.eqb_refl, SDEqb.eqb_refl, Hact;
        reflexivity.
  Qed.

  Definition decOwnedb (g : V.t -> G.t) (FDefs : FDefRel.t) (Slots : SlotRel.t)
      (rc : Pkg.t) (m : N.t) (gr : G.t) (f : F.t) (d : SlotData.t)
      (feat : F.t) : bool :=
    FDefRel.exists_ (fun '(((m', v), f'), e) =>
        andb (andb (NEqb.eqb m' m) (GEqb.eqb (g v) gr))
          (andb (FEqb.eqb f' f)
             (andb (match entryFeatD e with
                    | Some (a, t) => andb (NEqb.eqb a (sAlias d)) (FEqb.eqb t feat)
                    | None => false
                    end)
                (andb (SlotRel.mem ((m', v), d) Slots)
                   (slotActive rc (m', v) d)))))
      FDefs.

  Lemma decOwnedb_iff : forall g FDefs Slots rc m gr f d feat,
      decOwnedb g FDefs Slots rc m gr f d feat = true <->
      DecOwned g FDefs Slots rc m gr f d feat.
  Proof.
    intros g FDefs Slots rc m gr f d feat; unfold decOwnedb, DecOwned.
    rewrite FDefRel.exists_spec'; split.
    - intros [[[[m' v] f'] e] [He Hb]]; cbn beta iota in Hb.
      rewrite !andb_true_iff, NEqb.eqb_true_iff, GEqb.eqb_true_iff,
        FEqb.eqb_true_iff, SlotRel.mem_spec in Hb.
      destruct Hb as [[-> Hg] [-> [Hee [Hs Hact]]]].
      destruct (entryFeatD e) as [[a t] |] eqn:Ee; [| discriminate Hee].
      apply andb_true_iff in Hee; destruct Hee as [Ha Ht].
      apply NEqb.eqb_true_iff in Ha; apply FEqb.eqb_true_iff in Ht; subst a t.
      exists v, e; repeat split; assumption.
    - intros [v [e [<- [He [Ee [Hs Hact]]]]]].
      exists (((m, v), f), e); split; [exact He | cbn beta iota].
      rewrite Ee, GEqb.eqb_refl, (proj2 (SlotRel.mem_spec _ _) Hs), Hact,
        !NEqb.eqb_refl, !FEqb.eqb_refl; reflexivity.
  Qed.

  Definition rootPkg : T.Pkg.t := (NPlus.CRoot, VPlus.WUnit).

  Definition crateReal (g : V.t -> G.t) (R : PkgSet.t) : T.PkgSet.t :=
    SOpp.map (fun '(m, v) => (NPlus.CCrate m (g v), VPlus.WOrig v)) R.

  Definition featReal (g : V.t -> G.t) (support : SupportSet.t)
    : T.PkgSet.t :=
    SOsp.map (fun '((m, v), f) => (NPlus.CFeatP m f (g v), VPlus.WOrig v)) support.

  Definition slotReal (g : V.t -> G.t) (R : PkgSet.t) (Slots : SlotRel.t)
      (rc : Pkg.t) : T.PkgSet.t :=
    SOslp.unionMap (fun '((m, v), d) =>
        if slotActive rc (m, v) d
        then SOvp.map (fun u => (NPlus.CSlot m (g v) d, VPlus.WClass (g u)))
               (evalReq R (sTarget d) (sReq d))
        else T.PkgSet.empty)
      Slots.

  Definition decReal (g : V.t -> G.t) (R : PkgSet.t) (FDefs : FDefRel.t)
      (Slots : SlotRel.t) (rc : Pkg.t)
    : T.PkgSet.t :=
    SOfp.unionMap (fun '(((m, v), f), e) =>
        match entryFeatD e with
        | Some (a, feat) =>
            SOslp.unionMap (fun '(_, d) =>
                SOvp.map (fun u =>
                    (NPlus.CDec m (g v) f d feat, VPlus.WClass (g u)))
                  (evalReq R (sTarget d) (sReq d)))
              (slotsAt Slots rc (m, v) a)
        | None => T.PkgSet.empty
        end)
      FDefs.

  Definition linkReal (g : V.t -> G.t) (R : PkgSet.t) (Links : LinkRel.t)
    : T.PkgSet.t :=
    SOlp.filterMap (fun '((m, v), l) =>
        if PkgSet.mem (m, v) R
        then Some (NPlus.CLink l, VPlus.WName (NPlus.CCrate m (g v)))
        else None)
      Links.

  Definition reduceReal (g : V.t -> G.t) (R : PkgSet.t)
      (support : SupportSet.t) (FDefs : FDefRel.t) (Slots : SlotRel.t)
      (Links : LinkRel.t) (rc : Pkg.t)
    : T.PkgSet.t :=
    T.PkgSet.union (T.PkgSet.singleton rootPkg)
      (T.PkgSet.union (crateReal g R)
         (T.PkgSet.union (featReal g support)
            (T.PkgSet.union (slotReal g R Slots rc)
               (T.PkgSet.union (decReal g R FDefs Slots rc)
                  (linkReal g R Links))))).

  Module SOlc := SetOps LinkElt ClsT.InClassElt LinkRel ClsT.InClassRel.
  Definition linkRel (g : V.t -> G.t) (Links : LinkRel.t)
    : ClsT.InClassRel.t :=
    SOlc.map (fun '((m, v), l) =>
        ((NPlus.CCrate m (g v), VPlus.WOrig v), NPlus.CLink l))
      Links.

  Module SOlv := SetOps LinkElt VPOT LinkRel T.VSet.
  Module SOpv2 := SetOps Pkg VPOT PkgSet T.VSet.
  Module SOspv := SetOps PkgF VPOT SupportSet T.VSet.
  Module SOsh := SetOps SlotElt T.Dependees SlotRel T.DependeesSet.
  Module SOfh := SetOps FDefElt T.Dependees FDefRel T.DependeesSet.
  Module SOlh := SetOps LinkElt T.Dependees LinkRel T.DependeesSet.
  Module SOfsh := SetOps F T.Dependees FSet T.DependeesSet.

  Definition versions (g : V.t -> G.t) (R : PkgSet.t)
      (support : SupportSet.t) (FDefs : FDefRel.t) (Slots : SlotRel.t)
      (Links : LinkRel.t) (rc : Pkg.t)
      (n : NPlus.t) : T.VSet.t :=
    match n with
    | NPlus.CRoot => T.VSet.singleton VPlus.WUnit
    | NPlus.CCrate m gr =>
        SOpv2.filterMap (fun '(n', v) =>
            if andb (NEqb.eqb n' m) (GEqb.eqb (g v) gr)
            then Some (VPlus.WOrig v) else None)
          R
    | NPlus.CFeatP m f gr =>
        SOspv.filterMap (fun '((n', v), f') =>
            if andb (andb (NEqb.eqb n' m) (FEqb.eqb f' f))
                 (GEqb.eqb (g v) gr)
            then Some (VPlus.WOrig v) else None)
          support
    | NPlus.CSlot m gr d =>
        if slotOwnedb g Slots rc m gr d
        then gransOf g (evalReq R (sTarget d) (sReq d))
        else T.VSet.empty
    | NPlus.CDec m gr f d feat =>
        if decOwnedb g FDefs Slots rc m gr f d feat
        then gransOf g (evalReq R (sTarget d) (sReq d))
        else T.VSet.empty
    | NPlus.CLink l =>
        SOlv.filterMap (fun '((m, v), l') =>
            if andb (NEqb.eqb l' l) (PkgSet.mem (m, v) R)
            then Some (VPlus.WName (NPlus.CCrate m (g v))) else None)
          Links
    end.

  Definition dependees (g : V.t -> G.t) (R : PkgSet.t)
      (support : SupportSet.t) (FDefs : FDefRel.t) (Slots : SlotRel.t)
      (Links : LinkRel.t) (dflt : F.t)
      (rc : Pkg.t) (rootFeats : FSet.t) (p : T.Pkg.t)
    : T.DependeesSet.t :=
    match p with
    | (NPlus.CRoot, VPlus.WUnit) =>
        let '(m, v) := rc in
        T.DependeesSet.add
          (NPlus.CCrate m (g v), T.VSet.singleton (VPlus.WOrig v))
          (SOfsh.map (fun f =>
               (NPlus.CFeatP m f (g v), T.VSet.singleton (VPlus.WOrig v)))
             rootFeats)
    | (NPlus.CCrate m gr, VPlus.WOrig v) =>
        if negb (andb (GEqb.eqb (g v) gr) (PkgSet.mem (m, v) R))
        then T.DependeesSet.empty else
        T.DependeesSet.union
          (SOsh.filterMap (fun '(q, d) =>
               if andb (PkgEqb.eqb q (m, v))
                    (andb (slotActive rc (m, v) d)
                       (negb (sOptional d)))
               then Some (NPlus.CSlot m (g v) d,
                          gransOf g (evalReq R (sTarget d) (sReq d)))
               else None)
             Slots)
          (SOlh.filterMap (fun '(q, l) =>
               if PkgEqb.eqb q (m, v)
               then Some (NPlus.CLink l,
                          T.VSet.singleton (VPlus.WName (NPlus.CCrate m gr)))
               else None)
             Links)
    | (NPlus.CFeatP m f gr, VPlus.WOrig v) =>
        if negb (GEqb.eqb (g v) gr) then T.DependeesSet.empty else
        if negb (SupportSet.mem ((m, v), f) support)
        then T.DependeesSet.empty else
        T.DependeesSet.add
          (NPlus.CCrate m (g v), T.VSet.singleton (VPlus.WOrig v))
          (SOfh.unionMap (fun '(((n', v'), f'), e) =>
               if negb (andb (PkgEqb.eqb (n', v') (m, v)) (FEqb.eqb f' f))
               then T.DependeesSet.empty
               else
                 T.DependeesSet.union
                   (match e with
                    | FEntry.EFeat f2 =>
                        T.DependeesSet.singleton
                          (NPlus.CFeatP m f2 (g v),
                           T.VSet.singleton (VPlus.WOrig v))
                    | _ => T.DependeesSet.empty
                    end)
                   (T.DependeesSet.union
                      (match entryActivates e with
                       | Some a =>
                           SOsh.map (fun '(_, d) =>
                               (NPlus.CSlot m (g v) d,
                                gransOf g
                                  (evalReq R (sTarget d) (sReq d))))
                             (slotsAt Slots rc (m, v) a)
                       | None => T.DependeesSet.empty
                       end)
                      (match entryFeatD e with
                       | Some (a, feat) =>
                           SOsh.map (fun '(_, d) =>
                               (NPlus.CDec m (g v) f d feat,
                                gransOf g
                                  (evalReq R (sTarget d) (sReq d))))
                             (slotsAt Slots rc (m, v) a)
                       | None => T.DependeesSet.empty
                       end)))
             FDefs)
    | (NPlus.CSlot m gr0 d, VPlus.WClass gr) =>
        if negb (andb (slotOwnedb g Slots rc m gr0 d)
                   (granMet g gr (evalReq R (sTarget d) (sReq d))))
        then T.DependeesSet.empty else
        T.DependeesSet.add
          (NPlus.CCrate (sTarget d) gr,
           inGran g gr (evalReq R (sTarget d) (sReq d)))
          (SOfsh.map (fun f =>
               (NPlus.CFeatP (sTarget d) f gr,
                inGran g gr (evalReq R (sTarget d) (sReq d))))
             (slotRequests d dflt))
    | (NPlus.CDec m gr0 f d feat, VPlus.WClass gr) =>
        if negb (andb (decOwnedb g FDefs Slots rc m gr0 f d feat)
                   (granMet g gr (evalReq R (sTarget d) (sReq d))))
        then T.DependeesSet.empty else
        T.DependeesSet.add
          (NPlus.CSlot m gr0 d, T.VSet.singleton (VPlus.WClass gr))
          (T.DependeesSet.singleton
             (NPlus.CFeatP (sTarget d) feat gr,
              inGran g gr (evalReq R (sTarget d) (sReq d))))
    | _ => T.DependeesSet.empty
    end.

  Module SOhe := SetOps T.Dependees T.DepElt T.DependeesSet T.DepRel.
  Definition depEdges (p : T.Pkg.t) (hs : T.DependeesSet.t) : T.DepRel.t :=
    SOhe.map (fun h => (p, h)) hs.

  Module SOpe := SetOps T.Pkg T.DepElt T.PkgSet T.DepRel.
  Definition reduceDeps (g : V.t -> G.t) (R : PkgSet.t)
      (support : SupportSet.t) (FDefs : FDefRel.t) (Slots : SlotRel.t)
      (Links : LinkRel.t) (dflt : F.t)
      (rc : Pkg.t) (rootFeats : FSet.t) : T.DepRel.t :=
    SOpe.unionMap (fun p =>
        depEdges p
          (dependees g R support FDefs Slots Links dflt rc
             rootFeats p))
      (reduceReal g R support FDefs Slots Links rc).

  Lemma mem_gransOf : forall g vs w,
      T.VSet.In w (gransOf g vs) <->
      exists u, VSet.In u vs /\ w = VPlus.WClass (g u).
  Proof.
    intros g vs w; unfold gransOf; rewrite SOvv.mem_map; reflexivity.
  Qed.

  Lemma mem_inGran : forall g gr vs w,
      T.VSet.In w (inGran g gr vs) <->
      exists u, VSet.In u vs /\ g u = gr /\ w = VPlus.WOrig u.
  Proof.
    intros g gr vs w; unfold inGran; rewrite SOvv.mem_filterMap_if.
    cbn beta; setoid_rewrite GEqb.eqb_true_iff; reflexivity.
  Qed.

  Lemma granMet_iff : forall g gr vs,
      granMet g gr vs = true <-> exists u, VSet.In u vs /\ g u = gr.
  Proof.
    intros g gr vs; unfold granMet; rewrite VSet.exists_spec'.
    cbn beta; setoid_rewrite GEqb.eqb_true_iff; reflexivity.
  Qed.

  Lemma mem_crateReal : forall g R x,
      T.PkgSet.In x (crateReal g R) <->
      exists m v, PkgSet.In (m, v) R /\
        x = (NPlus.CCrate m (g v), VPlus.WOrig v).
  Proof.
    intros g R x; unfold crateReal; rewrite SOpp.mem_map; split.
    - intros [[m v] [HR He]]; cbn beta iota in He.
      exists m, v; split; assumption.
    - intros [m [v [HR ->]]]; exists (m, v); split;
        [exact HR | reflexivity].
  Qed.

  Lemma mem_featReal : forall g support x,
      T.PkgSet.In x (featReal g support) <->
      exists m v f, SupportSet.In ((m, v), f) support /\
        x = (NPlus.CFeatP m f (g v), VPlus.WOrig v).
  Proof.
    intros g support x; unfold featReal; rewrite SOsp.mem_map; split.
    - intros [[[m v] f] [HR He]]; cbn beta iota in He.
      exists m, v, f; split; assumption.
    - intros [m [v [f [HR ->]]]]; exists ((m, v), f); split;
        [exact HR | reflexivity].
  Qed.

  Lemma mem_slotReal : forall g R Slots rc x,
      T.PkgSet.In x (slotReal g R Slots rc) <->
      exists m v d u, SlotRel.In ((m, v), d) Slots /\
        slotActive rc (m, v) d = true /\
        VSet.In u (evalReq R (sTarget d) (sReq d)) /\
        x = (NPlus.CSlot m (g v) d, VPlus.WClass (g u)).
  Proof.
    intros g R Slots rc x; unfold slotReal.
    rewrite SOslp.mem_unionMap; split.
    - intros [[[m v] d] [Hs Hx]]; cbn beta iota in Hx.
      apply SOslp.in_if_empty in Hx as [Ha Hx].
      apply SOvp.mem_map in Hx; destruct Hx as [u [Hu ->]].
      exists m, v, d, u; repeat split; assumption.
    - intros [m [v [d [u [Hs [Ha [Hu ->]]]]]]].
      exists ((m, v), d); split; [exact Hs | cbn beta iota].
      rewrite Ha; apply SOvp.mem_map; exists u; split;
        [exact Hu | reflexivity].
  Qed.

  Lemma mem_decReal : forall g R FDefs Slots rc x,
      T.PkgSet.In x (decReal g R FDefs Slots rc) <->
      exists m v f e a feat d u,
        FDefRel.In (((m, v), f), e) FDefs /\
        entryFeatD e = Some (a, feat) /\
        SlotRel.In ((m, v), d) Slots /\ sAlias d = a /\
        slotActive rc (m, v) d = true /\
        VSet.In u (evalReq R (sTarget d) (sReq d)) /\
        x = (NPlus.CDec m (g v) f d feat, VPlus.WClass (g u)).
  Proof.
    intros g R FDefs Slots rc x; unfold decReal.
    rewrite SOfp.mem_unionMap; split.
    - intros [[[[m v] f] e] [Hf Hx]]; cbn beta iota in Hx.
      destruct (entryFeatD e) as [[a feat] |] eqn:Ee;
        [| exfalso; exact (SOslp.empty_in _ Hx)].
      apply SOslp.mem_unionMap in Hx; destruct Hx as [[q d] [Hq Hx]];
        cbn beta iota in Hx.
      apply mem_slotsAt in Hq; destruct Hq as [Hs [-> [Ha Hact]]].
      apply SOvp.mem_map in Hx; destruct Hx as [u [Hu ->]].
      exists m, v, f, e, a, feat, d, u; repeat split; assumption.
    - intros [m [v [f [e [a [feat [d [u
        [Hf [Ee [Hs [Ha [Hact [Hu ->]]]]]]]]]]]]]].
      exists (((m, v), f), e); split; [exact Hf | cbn beta iota].
      rewrite Ee; apply SOslp.mem_unionMap; exists ((m, v), d); split.
      { apply mem_slotsAt; repeat split; assumption. }
      cbn beta iota; apply SOvp.mem_map; exists u; split;
        [exact Hu | reflexivity].
  Qed.

  Lemma mem_linkReal : forall g R Links x,
      T.PkgSet.In x (linkReal g R Links) <->
      exists m v l, LinkRel.In ((m, v), l) Links /\ PkgSet.In (m, v) R /\
        x = (NPlus.CLink l, VPlus.WName (NPlus.CCrate m (g v))).
  Proof.
    intros g R Links x; unfold linkReal; rewrite SOlp.mem_filterMap; split.
    - intros [[[m v] l] [Hl He]]; cbn beta iota in He.
      rewrite if_some_iff, PkgSet.mem_spec in He; destruct He as [HR <-].
      exists m, v, l; auto.
    - intros [m [v [l [Hl [HR ->]]]]]; exists ((m, v), l); split;
        [exact Hl | cbn beta iota].
      rewrite (proj2 (PkgSet.mem_spec _ _) HR); reflexivity.
  Qed.

  Lemma mem_linkRel : forall g Links q k,
      ClsT.InClassRel.In (q, k) (linkRel g Links) <->
      exists m v l, LinkRel.In ((m, v), l) Links /\
        q = (NPlus.CCrate m (g v), VPlus.WOrig v) /\ k = NPlus.CLink l.
  Proof.
    intros g Links q k; unfold linkRel; rewrite SOlc.mem_map; split.
    - intros [[[m v] l] [Hl He]]; cbn beta iota in He.
      injection He as -> ->; exists m, v, l; repeat split; exact Hl.
    - intros [m [v [l [Hl [-> ->]]]]]; exists ((m, v), l); split;
        [exact Hl | reflexivity].
  Qed.

  Lemma mem_reduceReal :
    forall g R support FDefs Slots Links rc x,
      T.PkgSet.In x
        (reduceReal g R support FDefs Slots Links rc) <->
      x = rootPkg \/ T.PkgSet.In x (crateReal g R) \/
      T.PkgSet.In x (featReal g support) \/
      T.PkgSet.In x (slotReal g R Slots rc) \/
      T.PkgSet.In x (decReal g R FDefs Slots rc) \/
      T.PkgSet.In x (linkReal g R Links).
  Proof.
    intros; unfold reduceReal; rewrite !T.PkgSet.union_spec.
    rewrite T.PkgSet.singleton_spec; reflexivity.
  Qed.

  Lemma real_shape :
    forall g R support FDefs Slots Links rc n w,
      T.PkgSet.In (n, w) (reduceReal g R support FDefs Slots Links rc) <->
      match n with
      | NPlus.CRoot => w = VPlus.WUnit
      | NPlus.CCrate m gr =>
          exists v, w = VPlus.WOrig v /\ PkgSet.In (m, v) R /\ gr = g v
      | NPlus.CFeatP m f gr =>
          exists v, w = VPlus.WOrig v /\
            SupportSet.In ((m, v), f) support /\ gr = g v
      | NPlus.CSlot m gr d =>
          SlotOwned g Slots rc m gr d /\
          exists u, VSet.In u (evalReq R (sTarget d) (sReq d)) /\
            w = VPlus.WClass (g u)
      | NPlus.CDec m gr f d feat =>
          DecOwned g FDefs Slots rc m gr f d feat /\
          exists u, VSet.In u (evalReq R (sTarget d) (sReq d)) /\
            w = VPlus.WClass (g u)
      | NPlus.CLink l =>
          exists m v, w = VPlus.WName (NPlus.CCrate m (g v)) /\
            LinkRel.In ((m, v), l) Links /\ PkgSet.In (m, v) R
      end.
  Proof.
    intros g R support FDefs Slots Links rc n w.
    rewrite mem_reduceReal, mem_crateReal, mem_featReal, mem_slotReal,
      mem_decReal, mem_linkReal; unfold rootPkg, SlotOwned, DecOwned.
    split.
    - intros [He | [He | [He | [He | [He | He]]]]]; mem_destruct; eauto 20.
    - destruct n as [| m gr | m f gr | m gr d | m gr f d feat | l];
        cbn beta iota.
      + intros ->; left; reflexivity.
      + intros [v [-> [HR ->]]]; right; left; exists m, v; auto.
      + intros [v [-> [Hs ->]]]; right; right; left; exists m, v, f; auto.
      + intros [[v [<- [Hs Hact]]] [u [Hu ->]]].
        right; right; right; left; exists m, v, d, u; auto.
      + intros [[v [e [<- [Hf [Ee [Hs Hact]]]]]] [u [Hu ->]]].
        right; right; right; right; left.
        exists m, v, f, e, (sAlias d), feat, d, u; repeat split; assumption.
      + intros [m [v [-> [Hl HR]]]]; right; right; right; right; right.
        exists m, v, l; auto.
  Qed.

  Lemma mem_versions_link : forall g R support FDefs Slots Links rc l w,
      T.VSet.In w (versions g R support FDefs Slots Links rc (NPlus.CLink l))
      <-> exists m v, w = VPlus.WName (NPlus.CCrate m (g v)) /\
        LinkRel.In ((m, v), l) Links /\ PkgSet.In (m, v) R.
  Proof.
    intros; cbn [versions]; rewrite SOlv.mem_filterMap; split.
    - intros [[[m v] l'] [Hl He]]; cbn beta iota in He.
      rewrite if_some_iff, andb_true_iff, NEqb.eqb_true_iff, PkgSet.mem_spec
        in He.
      destruct He as [[-> HR] <-]; exists m, v; auto.
    - intros [m [v [-> [Hl HR]]]]; exists ((m, v), l); split;
        [exact Hl | cbn beta iota].
      rewrite NEqb.eqb_refl, (proj2 (PkgSet.mem_spec _ _) HR); reflexivity.
  Qed.

  Lemma versions_link_reduceReal :
    forall g R support FDefs Slots Links rc l w,
      T.VSet.In w
        (versions g R support FDefs Slots Links rc (NPlus.CLink l)) <->
      exists n, w = VPlus.WName n /\
        ClsT.Reduction.T.VSet.In (ClsT.Reduction.Version.Name n)
          (ClsT.Reduction.T.versions
             (ClsT.Reduction.reduceReal (crateReal g R) (linkRel g Links))
             (ClsT.Reduction.Name.Cls (NPlus.CLink l))).
  Proof.
    intros; rewrite mem_versions_link, ClsT.Reduction.Lookup.versions_cls.
    split.
    - intros [m [v [-> [Hl Em]]]].
      exists (NPlus.CCrate m (g v)); split; [reflexivity |].
      apply ClsT.Reduction.Lookup.SOpv.mem_map.
      exists (NPlus.CCrate m (g v), VPlus.WOrig v); split; [| reflexivity].
      apply ClsT.Reduction.Lookup.mem_inClass; split.
      + apply mem_crateReal; exists m, v; split; [exact Em | reflexivity].
      + apply mem_linkRel; exists m, v, l; repeat split; exact Hl.
    - intros [n [-> Hn]]; apply ClsT.Reduction.Lookup.SOpv.mem_map in Hn.
      destruct Hn as [q [Hq E]]; injection E as ->.
      apply ClsT.Reduction.Lookup.mem_inClass in Hq; destruct Hq as [Hq Hc].
      apply mem_linkRel in Hc; destruct Hc as [m [v [l' [Hl [-> Ek]]]]].
      injection Ek as <-.
      apply mem_crateReal in Hq; destruct Hq as [m' [v' [HR E]]].
      injection E as E1 _ E3; subst m' v'.
      exists m, v; auto.
  Qed.

  Lemma mem_reduceDeps :
    forall g R support FDefs Slots Links dflt rc rootFeats
           (p : T.Pkg.t) (h : T.Dependees.t),
      T.DepRel.In (p, h)
        (reduceDeps g R support FDefs Slots Links dflt rc
           rootFeats) <->
      T.PkgSet.In p
        (reduceReal g R support FDefs Slots Links rc) /\
      T.DependeesSet.In h
        (dependees g R support FDefs Slots Links dflt rc
           rootFeats p).
  Proof.
    intros g R support FDefs Slots Links dflt rc rootFeats p
      [n vs]; unfold reduceDeps; rewrite SOpe.mem_unionMap.
    split.
    - intros [q [Hq Hy]]; cbn beta iota in Hy.
      unfold depEdges in Hy; apply SOhe.mem_map in Hy.
      mem_destruct; split; assumption.
    - intros [Hp Hh].
      exists p; split; [exact Hp | cbn beta iota].
      unfold depEdges; apply SOhe.mem_map.
      exists (n, vs); split; [exact Hh | reflexivity].
  Qed.

  Definition Inert (p : T.Pkg.t) : Prop :=
    match p with
    | (NPlus.CRoot, VPlus.WUnit) => False
    | (NPlus.CCrate _ _, VPlus.WOrig _) => False
    | (NPlus.CFeatP _ _ _, VPlus.WOrig _) => False
    | (NPlus.CSlot _ _ _, VPlus.WClass _) => False
    | (NPlus.CDec _ _ _ _ _, VPlus.WClass _) => False
    | _ => True
    end.

  Lemma dep_inert :
    forall g R support FDefs Slots Links dflt rc rootFeats p,
      Inert p ->
      dependees g R support FDefs Slots Links dflt rc
        rootFeats p = T.DependeesSet.empty.
  Proof.
    intros g R support FDefs Slots Links dflt rc rootFeats
      [n w] Hi; destruct n; destruct w; try (exfalso; exact Hi);
      reflexivity.
  Qed.

  Lemma mem_dep_root :
    forall g R support FDefs Slots Links dflt rn rv rootFeats h,
      T.DependeesSet.In h
        (dependees g R support FDefs Slots Links dflt (rn, rv)
           rootFeats rootPkg) <->
      h = (NPlus.CCrate rn (g rv), T.VSet.singleton (VPlus.WOrig rv)) \/
      exists f, FSet.In f rootFeats /\
        h = (NPlus.CFeatP rn f (g rv), T.VSet.singleton (VPlus.WOrig rv)).
  Proof.
    intros; cbn [dependees rootPkg].
    rewrite T.DependeesSet.add_spec, SOfsh.mem_map.
    split; (intros [Hx | [f [Hf Hx]]];
            [left; exact Hx
             | right; exists f; split; [exact Hf | exact Hx]]).
  Qed.

  Lemma mem_dep_crate :
    forall g R support FDefs Slots Links dflt rc rootFeats
           m gr v h,
      T.DependeesSet.In h
        (dependees g R support FDefs Slots Links dflt rc
           rootFeats (NPlus.CCrate m gr, VPlus.WOrig v)) <->
      g v = gr /\ PkgSet.In (m, v) R /\
      ((exists d, SlotRel.In ((m, v), d) Slots /\
          slotActive rc (m, v) d = true /\
          sOptional d = false /\
          h = (NPlus.CSlot m (g v) d,
               gransOf g (evalReq R (sTarget d) (sReq d)))) \/
       (exists l, LinkRel.In ((m, v), l) Links /\
          h = (NPlus.CLink l,
               T.VSet.singleton (VPlus.WName (NPlus.CCrate m gr))))).
  Proof.
    intros; cbn [dependees].
    destruct (andb (GEqb.eqb (g v) gr) (PkgSet.mem (m, v) R)) eqn:Eb;
      cbn [negb].
    2:{ split; [intro Hc; destruct (T.DependeesSet.empty_spec Hc) |].
        intros [<- [Em _]].
        rewrite GEqb.eqb_refl, (proj2 (PkgSet.mem_spec _ _) Em) in Eb.
        discriminate Eb. }
    rewrite andb_true_iff, GEqb.eqb_true_iff, PkgSet.mem_spec in Eb.
    destruct Eb as [<- Em].
    rewrite T.DependeesSet.union_spec, SOsh.mem_filterMap,
      SOlh.mem_filterMap.
    split.
    - intros [[[q d] [Hs He]] | [[q l] [Hl He]]]; cbn beta iota in He;
        rewrite if_some_iff in He; (split; [reflexivity | split; [exact Em |]]).
      + rewrite !andb_true_iff, PkgEqb.eqb_true_iff, negb_true_iff in He.
        destruct He as [[-> [Ha Ho]] <-]; left; exists d; auto.
      + rewrite PkgEqb.eqb_true_iff in He; destruct He as [-> <-].
        right; exists l; auto.
    - intros [_ [_ [[d [Hs [Ha [Ho ->]]]] | [l [Hl ->]]]]].
      + left; exists ((m, v), d); split; [exact Hs | cbn beta iota].
        rewrite PkgEqb.eqb_refl, Ha, Ho; reflexivity.
      + right; exists ((m, v), l); split; [exact Hl | cbn beta iota].
        rewrite PkgEqb.eqb_refl; reflexivity.
  Qed.

  Lemma mem_dep_featP :
    forall g R support FDefs Slots Links dflt rc rootFeats
           m f gr v h,
      T.DependeesSet.In h
        (dependees g R support FDefs Slots Links dflt rc
           rootFeats (NPlus.CFeatP m f gr, VPlus.WOrig v)) <->
      g v = gr /\ SupportSet.In ((m, v), f) support /\
      (h = (NPlus.CCrate m (g v), T.VSet.singleton (VPlus.WOrig v)) \/
       exists e0, FDefRel.In (((m, v), f), e0) FDefs /\
         ((exists f', e0 = FEntry.EFeat f' /\
             h = (NPlus.CFeatP m f' (g v),
                  T.VSet.singleton (VPlus.WOrig v))) \/
          (exists a d, entryActivates e0 = Some a /\
             SlotRel.In ((m, v), d) Slots /\ sAlias d = a /\
             slotActive rc (m, v) d = true /\
             h = (NPlus.CSlot m (g v) d,
                  gransOf g (evalReq R (sTarget d) (sReq d)))) \/
          (exists a feat d, entryFeatD e0 = Some (a, feat) /\
             SlotRel.In ((m, v), d) Slots /\ sAlias d = a /\
             slotActive rc (m, v) d = true /\
             h = (NPlus.CDec m (g v) f d feat,
                  gransOf g (evalReq R (sTarget d) (sReq d)))))).
  Proof.
    intros; cbn [dependees].
    destruct (GEqb.eqb (g v) gr) eqn:Eg; cbn [negb].
    2:{ split; [intro Hc; exfalso; exact (T.DependeesSet.empty_spec Hc) |].
        intros [Hg _]; exfalso;
          rewrite (proj2 (GEqb.eqb_true_iff _ _) Hg) in Eg;
          discriminate Eg. }
    apply GEqb.eqb_true_iff in Eg.
    destruct (SupportSet.mem ((m, v), f) support) eqn:Em; cbn [negb].
    2:{ split; [intro Hc; exfalso; exact (T.DependeesSet.empty_spec Hc) |].
        intros [_ [Hsp _]]; exfalso;
          rewrite (proj2 (SupportSet.mem_spec _ _) Hsp) in Em;
          discriminate Em. }
    apply SupportSet.mem_spec in Em.
    rewrite T.DependeesSet.add_spec, SOfh.mem_unionMap.
    split.
    - intros [Hh | [[[[n' v'] f'] e0] [Hfd Hh]]].
      + split; [exact Eg | split; [exact Em | left; exact Hh]].
      + cbn beta iota in Hh.
        destruct (negb (andb (PkgEqb.eqb (n', v') (m, v))
                         (FEqb.eqb f' f))) eqn:Ek;
          [exfalso; exact (T.DependeesSet.empty_spec Hh) |].
        rewrite negb_false_iff, andb_true_iff, PkgEqb.eqb_true_iff,
          FEqb.eqb_true_iff in Ek; destruct Ek as [[= -> ->] ->].
        rewrite !T.DependeesSet.union_spec in Hh.
        split; [exact Eg | split; [exact Em | right]].
        exists e0; split; [exact Hfd |].
        destruct Hh as [Hh | [Hh | Hh]].
        * destruct e0 as [f2 | a0 | a0 feat0 | a0 feat0];
            try (exfalso; exact (T.DependeesSet.empty_spec Hh)).
          apply T.DependeesSet.singleton_spec in Hh; subst h.
          left; exists f2; split; reflexivity.
        * destruct (entryActivates e0) as [a |] eqn:Ea;
            [| exfalso; exact (T.DependeesSet.empty_spec Hh)].
          apply SOsh.mem_map in Hh; destruct Hh as [[q d] [Hq ->]].
          apply mem_slotsAt in Hq; destruct Hq as [Hs [-> [Ha Hact]]].
          right; left; exists a, d; repeat split; assumption.
        * destruct (entryFeatD e0) as [[a feat] |] eqn:Ea;
            [| exfalso; exact (T.DependeesSet.empty_spec Hh)].
          apply SOsh.mem_map in Hh; destruct Hh as [[q d] [Hq ->]].
          apply mem_slotsAt in Hq; destruct Hq as [Hs [-> [Ha Hact]]].
          right; right; exists a, feat, d; repeat split; assumption.
    - intros [_ [_ [Hh | [e0 [Hfd Hcase]]]]]; [left; exact Hh | right].
      exists (((m, v), f), e0); split; [exact Hfd | cbn beta iota].
      rewrite PkgEqb.eqb_refl, FEqb.eqb_refl; cbn [andb negb].
      rewrite !T.DependeesSet.union_spec.
      destruct Hcase as [[f2 [-> ->]] | [Hc | Hc]].
      + left; cbn [entryActivates entryFeatD].
        apply T.DependeesSet.singleton_spec; reflexivity.
      + destruct Hc as [a [d [Ea [Hs [Ha [Hact ->]]]]]].
        right; left; rewrite Ea; apply SOsh.mem_map.
        exists ((m, v), d); split; [| reflexivity].
        apply mem_slotsAt; repeat split; assumption.
      + destruct Hc as [a [feat [d [Ea [Hs [Ha [Hact ->]]]]]]].
        right; right; rewrite Ea; apply SOsh.mem_map.
        exists ((m, v), d); split; [| reflexivity].
        apply mem_slotsAt; repeat split; assumption.
  Qed.

  Lemma mem_dep_slot :
    forall g R support FDefs Slots Links dflt rc rootFeats
           m gr0 d gr h,
      T.DependeesSet.In h
        (dependees g R support FDefs Slots Links dflt rc
           rootFeats (NPlus.CSlot m gr0 d, VPlus.WClass gr)) <->
      SlotOwned g Slots rc m gr0 d /\
      exists u, VSet.In u (evalReq R (sTarget d) (sReq d)) /\ g u = gr /\
        (h = (NPlus.CCrate (sTarget d) gr,
              inGran g gr (evalReq R (sTarget d) (sReq d))) \/
         exists f, FSet.In f (slotRequests d dflt) /\
           h = (NPlus.CFeatP (sTarget d) f gr,
                inGran g gr (evalReq R (sTarget d) (sReq d)))).
  Proof.
    intros; cbn [dependees].
    destruct (slotOwnedb g Slots rc m gr0 d) eqn:Eo; cbn [andb].
    2:{ split; [intro Hc; cbn [negb] in Hc;
                exfalso; exact (T.DependeesSet.empty_spec Hc) |].
        intros [Ho _]; apply slotOwnedb_iff in Ho; congruence. }
    apply slotOwnedb_iff in Eo.
    split.
    - intro Hh; split; [exact Eo |].
      destruct (granMet g gr (evalReq R (sTarget d) (sReq d))) eqn:Ec;
        cbn [negb] in Hh;
        [| exfalso; exact (T.DependeesSet.empty_spec Hh)].
      apply granMet_iff in Ec; destruct Ec as [u [Hu Hgu]].
      exists u; split; [exact Hu | split; [exact Hgu |]].
      rewrite T.DependeesSet.add_spec, SOfsh.mem_map in Hh.
      destruct Hh as [Hh | [f [Hf Hh]]];
        [left; exact Hh | right; exists f; split; [exact Hf | exact Hh]].
    - intros [_ [u [Hu [Hgu Hh]]]].
      rewrite (proj2 (granMet_iff _ _ _) (ex_intro _ u (conj Hu Hgu)));
        cbn [negb].
      rewrite T.DependeesSet.add_spec, SOfsh.mem_map.
      destruct Hh as [Hh | [f [Hf Hh]]];
        [left; exact Hh | right; exists f; split; [exact Hf | exact Hh]].
  Qed.

  Lemma mem_dep_dec :
    forall g R support FDefs Slots Links dflt rc rootFeats
           m gr0 f d feat gr h,
      T.DependeesSet.In h
        (dependees g R support FDefs Slots Links dflt rc
           rootFeats (NPlus.CDec m gr0 f d feat, VPlus.WClass gr)) <->
      DecOwned g FDefs Slots rc m gr0 f d feat /\
      exists u, VSet.In u (evalReq R (sTarget d) (sReq d)) /\ g u = gr /\
        (h = (NPlus.CSlot m gr0 d, T.VSet.singleton (VPlus.WClass gr)) \/
         h = (NPlus.CFeatP (sTarget d) feat gr,
              inGran g gr (evalReq R (sTarget d) (sReq d)))).
  Proof.
    intros; cbn [dependees].
    destruct (decOwnedb g FDefs Slots rc m gr0 f d feat) eqn:Eo; cbn [andb].
    2:{ split; [intro Hc; cbn [negb] in Hc;
                exfalso; exact (T.DependeesSet.empty_spec Hc) |].
        intros [Ho _]; apply decOwnedb_iff in Ho; congruence. }
    apply decOwnedb_iff in Eo.
    split.
    - intro Hh; split; [exact Eo |].
      destruct (granMet g gr (evalReq R (sTarget d) (sReq d))) eqn:Ec;
        cbn [negb] in Hh;
        [| exfalso; exact (T.DependeesSet.empty_spec Hh)].
      apply granMet_iff in Ec; destruct Ec as [u [Hu Hgu]].
      exists u; split; [exact Hu | split; [exact Hgu |]].
      rewrite T.DependeesSet.add_spec, T.DependeesSet.singleton_spec
        in Hh; exact Hh.
    - intros [_ [u [Hu [Hgu Hh]]]].
      rewrite (proj2 (granMet_iff _ _ _) (ex_intro _ u (conj Hu Hgu)));
        cbn [negb].
      rewrite T.DependeesSet.add_spec, T.DependeesSet.singleton_spec.
      exact Hh.
  Qed.
  Lemma dep_real :
    forall g R support FDefs Slots Links dflt rc rootFeats p h,
      T.DependeesSet.In h
        (dependees g R support FDefs Slots Links dflt rc
           rootFeats p) ->
      T.PkgSet.In p
        (reduceReal g R support FDefs Slots Links rc).
  Proof.
    intros g R support FDefs Slots Links dflt rc rootFeats
      [n w] h Hh; apply real_shape.
    destruct n as [ | m gr | m f gr | m gr0 d | m gr0 f d feat | l ];
      destruct w as [ | u | gr' | q ];
      try (rewrite dep_inert in Hh by exact I;
           exfalso; exact (T.DependeesSet.empty_spec Hh)).
    - reflexivity.
    - apply mem_dep_crate in Hh; destruct Hh as [<- [HR _]].
      exists u; auto.
    - apply mem_dep_featP in Hh; destruct Hh as [<- [Hsp _]].
      exists u; auto.
    - apply mem_dep_slot in Hh; destruct Hh as [Ho [u [Hu [<- _]]]].
      split; [exact Ho | exists u; auto].
    - apply mem_dep_dec in Hh; destruct Hh as [Ho [u [Hu [<- _]]]].
      split; [exact Ho | exists u; auto].
  Qed.
  Module SOtp := SetOps T.Pkg Pkg T.PkgSet PkgSet.
  Definition cargoResolution (S : T.PkgSet.t) : PkgSet.t :=
    SOtp.filterMap (fun '(n, w) =>
        match n, w with
        | NPlus.CCrate m _, VPlus.WOrig v => Some (m, v)
        | _, _ => None
        end)
      S.

  Lemma mem_cargoResolution : forall S m v,
      PkgSet.In (m, v) (cargoResolution S) <->
      exists gr, T.PkgSet.In (NPlus.CCrate m gr, VPlus.WOrig v) S.
  Proof.
    intros S m v; unfold cargoResolution; rewrite SOtp.mem_filterMap; split.
    - intros [[n w] [Hin He]]; cbn beta iota in He.
      destruct n; try discriminate; destruct w; try discriminate.
      injection He as -> ->; exists gr; exact Hin.
    - intros [gr Hin]; exists (NPlus.CCrate m gr, VPlus.WOrig v); split;
        [exact Hin | reflexivity].
  Qed.

  Module SOtf := SetOps T.Pkg F T.PkgSet FSet.
  Definition featsAt (S : T.PkgSet.t) (p : Pkg.t) : FSet.t :=
    SOtf.filterMap (fun '(n, w) =>
        match n, w with
        | NPlus.CFeatP m f _, VPlus.WOrig v =>
            if PkgEqb.eqb (m, v) p then Some f else None
        | _, _ => None
        end)
      S.

  Lemma mem_featsAt : forall S m v f,
      FSet.In f (featsAt S (m, v)) <->
      exists gr, T.PkgSet.In (NPlus.CFeatP m f gr, VPlus.WOrig v) S.
  Proof.
    intros S m v f; unfold featsAt; rewrite SOtf.mem_filterMap; split.
    - intros [[n w] [Hin He]]; cbn beta iota in He.
      destruct n; try discriminate; destruct w; try discriminate.
      rewrite if_some_iff, PkgEqb.eqb_true_iff in He.
      destruct He as [[= -> ->] ->]; exists gr; exact Hin.
    - intros [gr Hin]; exists (NPlus.CFeatP m f gr, VPlus.WOrig v); split;
        [exact Hin | cbn beta iota].
      rewrite PkgEqb.eqb_refl; reflexivity.
  Qed.

  Module SOpf := SetOps Pkg Featured PkgSet FeaturedSet.
  Definition decodeFS (S : T.PkgSet.t) : FeaturedSet.t :=
    SOpf.map (fun p => (p, featsAt S p)) (cargoResolution S).

  Lemma mem_decodeFS : forall S p fs,
      FeaturedSet.In (p, fs) (decodeFS S) <->
      PkgSet.In p (cargoResolution S) /\ fs = featsAt S p.
  Proof.
    intros S p fs; unfold decodeFS; rewrite SOpf.mem_map; split.
    - intros [q [Hq He]]; injection He as -> ->; split;
        [exact Hq | reflexivity].
    - intros [Hp ->]; exists p; split; [exact Hp | reflexivity].
  Qed.

  Module SOtv2 := SetOps T.Pkg V T.PkgSet VSet.
  Definition targets (S : T.PkgSet.t) (m : N.t) (gr : G.t) : VSet.t :=
    SOtv2.filterMap (fun '(n, w) =>
        match n, w with
        | NPlus.CCrate m' gr', VPlus.WOrig u =>
            if andb (NEqb.eqb m' m) (GEqb.eqb gr' gr) then Some u else None
        | _, _ => None
        end)
      S.

  Lemma mem_targets : forall S m gr u,
      VSet.In u (targets S m gr) <->
      T.PkgSet.In (NPlus.CCrate m gr, VPlus.WOrig u) S.
  Proof.
    intros S m gr u; unfold targets; rewrite SOtv2.mem_filterMap; split.
    - intros [[n w] [Hin He]]; cbn beta iota in He.
      destruct n; try discriminate; destruct w; try discriminate.
      rewrite if_some_iff, andb_true_iff, NEqb.eqb_true_iff, GEqb.eqb_true_iff
        in He.
      destruct He as [[-> ->] ->]; exact Hin.
    - intro Hin; exists (NPlus.CCrate m gr, VPlus.WOrig u); split;
        [exact Hin | cbn beta iota].
      rewrite NEqb.eqb_refl, GEqb.eqb_refl; reflexivity.
  Qed.

  Module SOtpar := SetOps T.Pkg ParentElt T.PkgSet ParentRel.
  Module SOvpar := SetOps V ParentElt VSet ParentRel.
  Definition decodeParents (FDefs : FDefRel.t) (Slots : SlotRel.t)
      (rc : Pkg.t) (S : T.PkgSet.t) : ParentRel.t :=
    SOtpar.unionMap (fun '(n, w) =>
        match n, w with
        | NPlus.CSlot m gr d, VPlus.WClass gr' =>
            SOvpar.unionMap (fun v =>
                if andb (SlotRel.mem ((m, v), d) Slots)
                     (andb (slotActive rc (m, v) d)
                        (orb (negb (sOptional d))
                           (activatedb FDefs (featsAt S (m, v)) (m, v)
                              (sAlias d))))
                then SOvpar.map (fun u => (((m, v), sKey d), u))
                       (targets S (sTarget d) gr')
                else ParentRel.empty)
              (targets S m gr)
        | _, _ => ParentRel.empty
        end)
      S.

  Lemma mem_decodeParents : forall FDefs Slots rc S m v k u,
      ParentRel.In (((m, v), k), u) (decodeParents FDefs Slots rc S) <->
      exists gr gr' d, T.PkgSet.In (NPlus.CSlot m gr d, VPlus.WClass gr') S /\
        T.PkgSet.In (NPlus.CCrate m gr, VPlus.WOrig v) S /\
        SlotRel.In ((m, v), d) Slots /\ sKey d = k /\
        slotActive rc (m, v) d = true /\
        (sOptional d = false \/
         Activated FDefs (featsAt S (m, v)) (m, v) (sAlias d)) /\
        T.PkgSet.In (NPlus.CCrate (sTarget d) gr', VPlus.WOrig u) S.
  Proof.
    intros FDefs Slots rc S m v k u; unfold decodeParents.
    rewrite SOtpar.mem_unionMap; split.
    - intros [[n w] [Hin Hy]]; cbn beta iota in Hy.
      destruct n; try (exfalso; exact (SOvpar.empty_in _ Hy));
        destruct w; try (exfalso; exact (SOvpar.empty_in _ Hy)).
      rewrite SOvpar.mem_unionMap_if in Hy; cbn beta in Hy.
      destruct Hy as [v0 [Hv0 [Eb Hy]]].
      rewrite !andb_true_iff, SlotRel.mem_spec in Eb.
      destruct Eb as [Hs [Hact Ereq]].
      change (requiredb FDefs (featsAt S (m0, v0)) (m0, v0) d = true)
        in Ereq.
      apply requiredb_iff in Ereq.
      apply SOvpar.mem_map in Hy; destruct Hy as [u' [Hu' He]].
      injection He as -> -> -> ->.
      exists gr, gr0, d; repeat split; try assumption.
      + apply mem_targets; exact Hv0.
      + apply mem_targets; exact Hu'.
    - intros [gr [gr' [d [Hslot [Hown [Hs [Ha [Hact [Hreq Hcr]]]]]]]]].
      exists (NPlus.CSlot m gr d, VPlus.WClass gr'); split;
        [exact Hslot | cbn beta iota].
      apply SOvpar.mem_unionMap; exists v; split;
        [apply mem_targets; exact Hown | cbn beta iota].
      rewrite (proj2 (SlotRel.mem_spec _ _) Hs), Hact.
      apply requiredb_iff in Hreq; unfold requiredb in Hreq; rewrite Hreq.
      cbn [andb].
      apply SOvpar.mem_map; exists u; split;
        [apply mem_targets; exact Hcr | rewrite Ha; reflexivity].
  Qed.

  Theorem cargo_soundness :
    forall R support FDefs Slots Links g dflt rc rootFeats
           (S : T.PkgSet.t),
      SiteFunctional Slots ->
      T.IsResolution
        (reduceReal g R support FDefs Slots Links rc)
        (reduceDeps g R support FDefs Slots Links dflt rc
           rootFeats) rootPkg S ->
      IsResolution R support FDefs Slots Links g dflt rc
        rootFeats (cargoResolution S) (decodeFS S)
        (decodeParents FDefs Slots rc S).
  Proof.
    intros R support FDefs Slots Links g dflt rc rootFeats S
      Hsite Hres.
    destruct rc as [rn rv].
    destruct Hres as [Hsub Hroot Hdep Huniq].
    assert (A1 : forall m gr v,
        T.PkgSet.In (NPlus.CCrate m gr, VPlus.WOrig v) S ->
        PkgSet.In (m, v) R /\ gr = g v).
    { intros m gr v Hin; apply Hsub, real_shape in Hin.
      destruct Hin as [v' [E [HR ->]]]; injection E as <-; auto. }
    assert (A2 : forall m f gr v,
        T.PkgSet.In (NPlus.CFeatP m f gr, VPlus.WOrig v) S ->
        SupportSet.In ((m, v), f) support /\ gr = g v).
    { intros m f gr v Hin; apply Hsub, real_shape in Hin.
      destruct Hin as [v' [E [Hsp ->]]]; injection E as <-; auto. }
    assert (A3 : forall m gr d gr',
        T.PkgSet.In (NPlus.CSlot m gr d, VPlus.WClass gr') S ->
        exists u, VSet.In u (evalReq R (sTarget d) (sReq d)) /\ g u = gr').
    { intros m gr d gr' Hin; apply Hsub, real_shape in Hin.
      destruct Hin as [_ [u [Hu E]]]; injection E as ->; eauto. }
    assert (A5 : forall m f gr u u',
        T.PkgSet.In (NPlus.CFeatP m f gr, VPlus.WOrig u') S ->
        T.PkgSet.In (NPlus.CCrate m gr, VPlus.WOrig u) S -> u' = u).
    { intros m f gr u u' Hf Hc.
      destruct (A2 _ _ _ _ Hf) as [Hsp Egr]; subst gr.
      assert (Hed : T.DepRel.In
          ((NPlus.CFeatP m f (g u'), VPlus.WOrig u'),
           (NPlus.CCrate m (g u'), T.VSet.singleton (VPlus.WOrig u')))
          (reduceDeps g R support FDefs Slots Links dflt
             (rn, rv) rootFeats)).
      { apply mem_reduceDeps; split; [exact (Hsub _ Hf) |].
        apply mem_dep_featP; split; [reflexivity |].
        split; [exact Hsp | left; reflexivity]. }
      destruct (Hdep _ Hf _ _ Hed) as [w [Hw HwS]].
      apply T.VSet.singleton_spec in Hw; subst w.
      assert (E := Huniq _ _ _ HwS Hc); injection E as E; exact E. }
    constructor.
    - intros [m v] Hp; apply mem_cargoResolution in Hp; destruct Hp as [gr Hp].
      exact (proj1 (A1 _ _ _ Hp)).
    - assert (Hed : T.DepRel.In
          (rootPkg, (NPlus.CCrate rn (g rv), T.VSet.singleton (VPlus.WOrig rv)))
          (reduceDeps g R support FDefs Slots Links dflt
             (rn, rv) rootFeats)).
      { apply mem_reduceDeps; split; [exact (Hsub _ Hroot) |].
        apply mem_dep_root; left; reflexivity. }
      destruct (Hdep _ Hroot _ _ Hed) as [w [Hw HwS]].
      apply T.VSet.singleton_spec in Hw; subst w.
      apply mem_cargoResolution; exists (g rv); exact HwS.
    - intros fs Hfs; apply mem_decodeFS in Hfs;
        destruct Hfs as [_ ->]; intros f Hf.
      assert (Hed : T.DepRel.In
          (rootPkg, (NPlus.CFeatP rn f (g rv),
                   T.VSet.singleton (VPlus.WOrig rv)))
          (reduceDeps g R support FDefs Slots Links dflt
             (rn, rv) rootFeats)).
      { apply mem_reduceDeps; split; [exact (Hsub _ Hroot) |].
        apply mem_dep_root; right; exists f; split;
          [exact Hf | reflexivity]. }
      destruct (Hdep _ Hroot _ _ Hed) as [w [Hw HwS]].
      apply T.VSet.singleton_spec in Hw; subst w.
      apply mem_featsAt; exists (g rv); exact HwS.
    - intros p fs Hfs; apply mem_decodeFS in Hfs; exact (proj1 Hfs).
    - intros p Hp; exists (featsAt S p); apply mem_decodeFS; split;
        [exact Hp | reflexivity].
    - intros p fs fs' Hfs Hfs'.
      apply mem_decodeFS in Hfs; destruct Hfs as [_ ->].
      apply mem_decodeFS in Hfs'; destruct Hfs' as [_ ->]; reflexivity.
    - intros m v v' Hv Hv' NE Hg.
      apply mem_cargoResolution in Hv; destruct Hv as [gr Hv].
      apply mem_cargoResolution in Hv'; destruct Hv' as [gr' Hv'].
      destruct (A1 _ _ _ Hv) as [_ Egr]; subst gr.
      destruct (A1 _ _ _ Hv') as [_ Egr']; subst gr'.
      rewrite <- Hg in Hv'.
      assert (E := Huniq _ _ _ Hv Hv'); injection E as E.
      contradiction NE.
    - intros [m v] fs f Hfs Hf.
      apply mem_decodeFS in Hfs; destruct Hfs as [_ ->].
      apply mem_featsAt in Hf; destruct Hf as [gr Hf].
      exact (proj1 (A2 _ _ _ _ Hf)).
    - intros [m v] a u u' Hu Hu'.
      apply mem_decodeParents in Hu;
        destruct Hu as [gr [gr1 [d [Hslot [Hown [Hs [Ha [Hact [_ Hcr]]]]]]]]].
      apply mem_decodeParents in Hu';
        destruct Hu' as [gr' [gr1' [d' [Hslot' [Hown' [Hs' [Ha' [Hact'
          [_ Hcr']]]]]]]]].
      assert (d' = d)
        by exact (Hsite (m, v) d' d Hs' Hs (eq_trans Ha' (eq_sym Ha))).
      subst d'.
      destruct (A1 _ _ _ Hown) as [_ ->].
      destruct (A1 _ _ _ Hown') as [_ ->].
      assert (E := Huniq _ _ _ Hslot Hslot'); injection E as E; subst gr1'.
      assert (E2 := Huniq _ _ _ Hcr Hcr'); injection E2 as E2; exact E2.
    - intros [m v] k u Hu.
      apply mem_decodeParents in Hu;
        destruct Hu as [gr [gr1 [d [_ [Hown [Hs [Ha [Hact [Hreq _]]]]]]]]].
      exists (featsAt S (m, v)), d; repeat split; try assumption.
      apply mem_decodeFS; split; [| reflexivity].
      apply mem_cargoResolution; exists gr; exact Hown.
    - intros [m v] fs Hp Hfs d Hd Hact Hopt.
      apply mem_decodeFS in Hfs; destruct Hfs as [_ ->].
      apply mem_cargoResolution in Hp; destruct Hp as [gr0 Hp].
      destruct (A1 _ _ _ Hp) as [_ Egr0]; subst gr0.
      assert (Achain : forall gr,
          T.PkgSet.In (NPlus.CSlot m (g v) d, VPlus.WClass gr) S ->
          exists u, ParentRel.In (((m, v), sKey d), u)
                      (decodeParents FDefs Slots (rn, rv) S) /\
            rgHolds (sReq d) u = true /\
            PkgSet.In (sTarget d, u) (cargoResolution S) /\
            forall fs', FeaturedSet.In ((sTarget d, u), fs')
              (decodeFS S) ->
            FSet.Subset (slotRequests d dflt) fs').
      { intros gr Hslot.
        destruct (A3 _ _ _ _ Hslot) as [u0 [Hu0 Egr]].
        subst gr.
        assert (Ho := proj1 (proj1 (real_shape _ _ _ _ _ _ _ _ _)
                               (Hsub _ Hslot))).
        assert (Hed : T.DepRel.In
            ((NPlus.CSlot m (g v) d, VPlus.WClass (g u0)),
             (NPlus.CCrate (sTarget d) (g u0),
              inGran g (g u0) (evalReq R (sTarget d) (sReq d))))
            (reduceDeps g R support FDefs Slots Links dflt
               (rn, rv) rootFeats)).
        { apply mem_reduceDeps; split; [exact (Hsub _ Hslot) |].
          apply mem_dep_slot; split; [exact Ho |].
          exists u0; split; [exact Hu0 |].
          split; [reflexivity | left; reflexivity]. }
        destruct (Hdep _ Hslot _ _ Hed) as [w [Hw HwS]].
        apply mem_inGran in Hw; destruct Hw as [u [Hu [Hgu ->]]].
        exists u; repeat split.
        - apply mem_decodeParents; exists (g v), (g u0), d.
          split; [exact Hslot |].
          split; [exact Hp |].
          split; [exact Hd |].
          split; [reflexivity |].
          split; [exact Hact |].
          split; [exact Hopt | exact HwS].
        - apply mem_evalReq in Hu; exact (proj2 Hu).
        - apply mem_cargoResolution; exists (g u0); exact HwS.
        - intros fs' Hfs'; apply mem_decodeFS in Hfs';
            destruct Hfs' as [_ ->]; intros f Hf.
          assert (Hef : T.DepRel.In
              ((NPlus.CSlot m (g v) d, VPlus.WClass (g u0)),
               (NPlus.CFeatP (sTarget d) f (g u0),
                inGran g (g u0) (evalReq R (sTarget d) (sReq d))))
              (reduceDeps g R support FDefs Slots Links dflt
                 (rn, rv) rootFeats)).
          { apply mem_reduceDeps; split; [exact (Hsub _ Hslot) |].
            apply mem_dep_slot; split; [exact Ho |].
            exists u0; split; [exact Hu0 |].
            split; [reflexivity |].
            right; exists f; split; [exact Hf | reflexivity]. }
          destruct (Hdep _ Hslot _ _ Hef) as [w' [Hw' Hw'S]].
          apply mem_inGran in Hw'; destruct Hw' as [u' [Hu' [Hgu' ->]]].
          assert (u' = u) by (apply (A5 (sTarget d) f (g u0));
                              assumption).
          subst u'.
          apply mem_featsAt; exists (g u0); exact Hw'S. }
      destruct Hopt as [Hno | Hacted].
      + assert (Hed : T.DepRel.In
            ((NPlus.CCrate m (g v), VPlus.WOrig v),
             (NPlus.CSlot m (g v) d,
              gransOf g (evalReq R (sTarget d) (sReq d))))
            (reduceDeps g R support FDefs Slots Links dflt
               (rn, rv) rootFeats)).
        { apply mem_reduceDeps; split; [exact (Hsub _ Hp) |].
          apply mem_dep_crate; split; [reflexivity |].
          split; [exact (proj1 (A1 _ _ _ Hp)) |].
          left; exists d; repeat split; assumption. }
        destruct (Hdep _ Hp _ _ Hed) as [w [Hw HwS]].
        apply mem_gransOf in Hw; destruct Hw as [u1 [Hu1 ->]].
        exact (Achain _ HwS).
      + destruct Hacted as [f [Hffs Hent]].
        apply mem_featsAt in Hffs; destruct Hffs as [gr1 Hffs].
        destruct (A2 _ _ _ _ Hffs) as [_ Egr1]; subst gr1.
        assert (Hea : exists e', FDefRel.In (((m, v), f), e') FDefs /\
            entryActivates e' = Some (sAlias d)).
        { destruct Hent as [He | [[feat He] | [feat He]]].
          - exists (FEntry.EDep (sAlias d)); split;
              [exact He | reflexivity].
          - exists (FEntry.EDepFeat (sAlias d) feat); split;
              [exact He | reflexivity].
          - exists (FEntry.EWeakFeat (sAlias d) feat); split;
              [exact He | reflexivity]. }
        destruct Hea as [e' [He' Ea]].
        assert (Hed : T.DepRel.In
            ((NPlus.CFeatP m f (g v), VPlus.WOrig v),
             (NPlus.CSlot m (g v) d,
              gransOf g (evalReq R (sTarget d) (sReq d))))
            (reduceDeps g R support FDefs Slots Links dflt
               (rn, rv) rootFeats)).
        { apply mem_reduceDeps; split; [exact (Hsub _ Hffs) |].
          apply mem_dep_featP; split; [reflexivity |].
          split; [exact (proj1 (A2 _ _ _ _ Hffs)) |].
          right; exists e'; split; [exact He' |].
          right; left; exists (sAlias d), d; repeat split; assumption. }
        destruct (Hdep _ Hffs _ _ Hed) as [w [Hw HwS]].
        apply mem_gransOf in Hw; destruct Hw as [u1 [Hu1 ->]].
        exact (Achain _ HwS).
    - intros [m v] fs f f' Hfs Hf He.
      apply mem_decodeFS in Hfs; destruct Hfs as [_ ->].
      apply mem_featsAt in Hf; destruct Hf as [gr Hf].
      destruct (A2 _ _ _ _ Hf) as [_ Egr]; subst gr.
      assert (Hed : T.DepRel.In
          ((NPlus.CFeatP m f (g v), VPlus.WOrig v),
           (NPlus.CFeatP m f' (g v), T.VSet.singleton (VPlus.WOrig v)))
          (reduceDeps g R support FDefs Slots Links dflt
             (rn, rv) rootFeats)).
      { apply mem_reduceDeps; split; [exact (Hsub _ Hf) |].
        apply mem_dep_featP; split; [reflexivity |].
        split; [exact (proj1 (A2 _ _ _ _ Hf)) |].
        right; exists (FEntry.EFeat f'); split; [exact He |].
        left; exists f'; split; reflexivity. }
      destruct (Hdep _ Hf _ _ Hed) as [w [Hw HwS]].
      apply T.VSet.singleton_spec in Hw; subst w.
      apply mem_featsAt; exists (g v); exact HwS.
    - intros [m v] fs f a feat Hfs Hf Hent d u Hd Halias Hpi fs' Hfs'.
      apply mem_decodeFS in Hfs; destruct Hfs as [_ ->].
      apply mem_featsAt in Hf; destruct Hf as [gr Hf].
      destruct (A2 _ _ _ _ Hf) as [_ Egr]; subst gr.
      subst a.
      assert (He' : exists e', FDefRel.In (((m, v), f), e') FDefs /\
          entryFeatD e' = Some (sAlias d, feat)).
      { destruct Hent as [He | He].
        - exists (FEntry.EDepFeat (sAlias d) feat); split;
            [exact He | reflexivity].
        - exists (FEntry.EWeakFeat (sAlias d) feat); split;
            [exact He | reflexivity]. }
      destruct He' as [e' [He' Ee]].
      apply mem_decodeParents in Hpi;
        destruct Hpi as [gr2 [gr2' [d2 [Hslot2 [Hcr2 [Hs2 [Ha2 [Hact2
          [_ Hcr2t]]]]]]]]].
      assert (d2 = d) by exact (Hsite (m, v) d2 d Hs2 Hd Ha2); subst d2.
      destruct (A1 _ _ _ Hcr2) as [_ ->].
      assert (Hed : T.DepRel.In
          ((NPlus.CFeatP m f (g v), VPlus.WOrig v),
           (NPlus.CDec m (g v) f d feat,
            gransOf g (evalReq R (sTarget d) (sReq d))))
          (reduceDeps g R support FDefs Slots Links dflt
             (rn, rv) rootFeats)).
      { apply mem_reduceDeps; split; [exact (Hsub _ Hf) |].
        apply mem_dep_featP; split; [reflexivity |].
        split; [exact (proj1 (A2 _ _ _ _ Hf)) |].
        right; exists e'; split; [exact He' |].
        right; right; exists (sAlias d), feat, d; repeat split;
          assumption. }
      destruct (Hdep _ Hf _ _ Hed) as [w [Hw HwS]].
      apply mem_gransOf in Hw; destruct Hw as [u1 [Hu1 ->]].
      assert (Hdo := proj1 (proj1 (real_shape _ _ _ _ _ _ _ _ _)
                              (Hsub _ HwS))).
      assert (Hpin : T.DepRel.In
          ((NPlus.CDec m (g v) f d feat, VPlus.WClass (g u1)),
           (NPlus.CSlot m (g v) d,
            T.VSet.singleton (VPlus.WClass (g u1))))
          (reduceDeps g R support FDefs Slots Links dflt
             (rn, rv) rootFeats)).
      { apply mem_reduceDeps; split; [exact (Hsub _ HwS) |].
        apply mem_dep_dec; split; [exact Hdo |].
        exists u1; split; [exact Hu1 |].
        split; [reflexivity | left; reflexivity]. }
      destruct (Hdep _ HwS _ _ Hpin) as [x [Hx HxS]].
      apply T.VSet.singleton_spec in Hx; subst x.
      assert (Hdel : T.DepRel.In
          ((NPlus.CDec m (g v) f d feat, VPlus.WClass (g u1)),
           (NPlus.CFeatP (sTarget d) feat (g u1),
            inGran g (g u1) (evalReq R (sTarget d) (sReq d))))
          (reduceDeps g R support FDefs Slots Links dflt
             (rn, rv) rootFeats)).
      { apply mem_reduceDeps; split; [exact (Hsub _ HwS) |].
        apply mem_dep_dec; split; [exact Hdo |].
        exists u1; split; [exact Hu1 |].
        split; [reflexivity | right; reflexivity]. }
      destruct (Hdep _ HwS _ _ Hdel) as [y [Hy HyS]].
      apply mem_inGran in Hy; destruct Hy as [u2 [Hu2 [Hgu2 ->]]].
      assert (Egr : VPlus.WClass gr2' = VPlus.WClass (g u1))
        by exact (Huniq _ _ _ Hslot2 HxS).
      injection Egr as Egr; subst gr2'.
      assert (u2 = u) by (apply (A5 (sTarget d) feat (g u1)); assumption).
      subst u2.
      apply mem_decodeFS in Hfs'; destruct Hfs' as [_ ->].
      apply mem_featsAt; exists (g u1); exact HyS.
    - intros p q l Hp Hq Hlp Hlq.
      destruct p as [pn pv]; destruct q as [qn qv].
      apply mem_cargoResolution in Hp; destruct Hp as [grp Hp].
      apply mem_cargoResolution in Hq; destruct Hq as [grq Hq].
      destruct (A1 _ _ _ Hp) as [HpR Egp]; subst grp.
      destruct (A1 _ _ _ Hq) as [HqR Egq]; subst grq.
      assert (Hep : T.DepRel.In
          ((NPlus.CCrate pn (g pv), VPlus.WOrig pv),
           (NPlus.CLink l,
            T.VSet.singleton (VPlus.WName (NPlus.CCrate pn (g pv)))))
          (reduceDeps g R support FDefs Slots Links dflt
             (rn, rv) rootFeats)).
      { apply mem_reduceDeps; split; [exact (Hsub _ Hp) |].
        apply mem_dep_crate; split; [reflexivity |].
        split; [exact HpR | right; exists l; split;
                            [exact Hlp | reflexivity]]. }
      assert (Heq : T.DepRel.In
          ((NPlus.CCrate qn (g qv), VPlus.WOrig qv),
           (NPlus.CLink l,
            T.VSet.singleton (VPlus.WName (NPlus.CCrate qn (g qv)))))
          (reduceDeps g R support FDefs Slots Links dflt
             (rn, rv) rootFeats)).
      { apply mem_reduceDeps; split; [exact (Hsub _ Hq) |].
        apply mem_dep_crate; split; [reflexivity |].
        split; [exact HqR | right; exists l; split;
                            [exact Hlq | reflexivity]]. }
      destruct (Hdep _ Hp _ _ Hep) as [x [Hx HxS]].
      destruct (Hdep _ Hq _ _ Heq) as [y [Hy HyS]].
      apply T.VSet.singleton_spec in Hx; subst x.
      apply T.VSet.singleton_spec in Hy; subst y.
      assert (E := Huniq _ _ _ HxS HyS); injection E as E1 E2.
      subst qn; rewrite <- E2 in Hq.
      assert (E' := Huniq _ _ _ Hp Hq); injection E' as E'.
      rewrite E'; reflexivity.
  Qed.

  Module SOfw2 := SetOps Featured T.Pkg FeaturedSet T.PkgSet.
  Module SOfsp := SetOps F T.Pkg FSet T.PkgSet.
  Module SOparp := SetOps ParentElt T.Pkg ParentRel T.PkgSet.

  Definition wFeats (g : V.t -> G.t) (FS : FeaturedSet.t) : T.PkgSet.t :=
    SOfw2.unionMap (fun '((m, v), fs) =>
        SOfsp.map (fun f => (NPlus.CFeatP m f (g v), VPlus.WOrig v)) fs)
      FS.

  Lemma mem_wFeats : forall g FS x,
      T.PkgSet.In x (wFeats g FS) <->
      exists m v fs f, FeaturedSet.In ((m, v), fs) FS /\ FSet.In f fs /\
        x = (NPlus.CFeatP m f (g v), VPlus.WOrig v).
  Proof.
    intros g FS x; unfold wFeats; rewrite SOfw2.mem_unionMap; split.
    - intros [[[m v] fs] [Hin Hx]]; cbn beta iota in Hx.
      apply SOfsp.mem_map in Hx; destruct Hx as [f [Hf ->]].
      exists m, v, fs, f; repeat split; assumption.
    - intros [m [v [fs [f [Hin [Hf ->]]]]]].
      exists ((m, v), fs); split; [exact Hin | cbn beta iota].
      apply SOfsp.mem_map; exists f; split; [exact Hf | reflexivity].
  Qed.

  Definition wSlots (g : V.t -> G.t) (FDefs : FDefRel.t)
      (Slots : SlotRel.t) (rc : Pkg.t)
      (S : PkgSet.t) (FS : FeaturedSet.t) (pi : ParentRel.t) : T.PkgSet.t :=
    SOparp.unionMap (fun '(((m, v), k), u) =>
        if parentsb FDefs Slots rc S FS (m, v) k
        then SOslp.map (fun '(_, d) =>
                 (NPlus.CSlot m (g v) d, VPlus.WClass (g u)))
               (slotsAtKey Slots rc (m, v) k)
        else T.PkgSet.empty)
      pi.

  Lemma mem_wSlots : forall g FDefs Slots rc S FS pi x,
      T.PkgSet.In x (wSlots g FDefs Slots rc S FS pi) <->
      exists m v k u d, ParentRel.In (((m, v), k), u) pi /\
        parentsb FDefs Slots rc S FS (m, v) k = true /\
        SlotRel.In ((m, v), d) Slots /\ sKey d = k /\
        slotActive rc (m, v) d = true /\
        x = (NPlus.CSlot m (g v) d, VPlus.WClass (g u)).
  Proof.
    intros g FDefs Slots rc S FS pi x; unfold wSlots.
    rewrite SOparp.mem_unionMap; split.
    - intros [[[[m v] k] u] [Hin Hx]]; cbn beta iota in Hx.
      apply SOslp.in_if_empty in Hx as [Eb Hx].
      apply SOslp.mem_map in Hx; destruct Hx as [[q d] [Hq ->]].
      apply mem_slotsAtKey in Hq; destruct Hq as [Hs [-> [Ha Hact]]].
      exists m, v, k, u, d; repeat split; assumption.
    - intros [m [v [k [u [d [Hin [Eb [Hs [Ha [Hact ->]]]]]]]]]].
      exists (((m, v), k), u); split; [exact Hin | cbn beta iota].
      rewrite Eb; apply SOslp.mem_map; exists ((m, v), d); split;
        [apply mem_slotsAtKey; repeat split; assumption | reflexivity].
  Qed.

  Definition wDecs (g : V.t -> G.t) (FDefs : FDefRel.t)
      (Slots : SlotRel.t) (rc : Pkg.t)
      (S : PkgSet.t) (FS : FeaturedSet.t) (pi : ParentRel.t) : T.PkgSet.t :=
    SOparp.unionMap (fun '(((m, v), k), u) =>
        if parentsb FDefs Slots rc S FS (m, v) k
        then SOfp.unionMap (fun '((q, f), e) =>
               match entryFeatD e with
               | Some (a', feat) =>
                   if andb (andb (PkgEqb.eqb q (m, v))
                              (NEqb.eqb a' (kAlias k)))
                        (FSet.mem f (fsAt FS (m, v)))
                   then SOslp.map (fun '(_, d) =>
                            (NPlus.CDec m (g v) f d feat, VPlus.WClass (g u)))
                          (slotsAtKey Slots rc (m, v) k)
                   else T.PkgSet.empty
               | None => T.PkgSet.empty
               end)
             FDefs
        else T.PkgSet.empty)
      pi.

  Lemma mem_wDecs : forall g FDefs Slots rc S FS pi x,
      T.PkgSet.In x (wDecs g FDefs Slots rc S FS pi) <->
      exists m v k u f e feat d, ParentRel.In (((m, v), k), u) pi /\
        parentsb FDefs Slots rc S FS (m, v) k = true /\
        FDefRel.In (((m, v), f), e) FDefs /\
        entryFeatD e = Some (kAlias k, feat) /\
        FSet.In f (fsAt FS (m, v)) /\
        SlotRel.In ((m, v), d) Slots /\ sKey d = k /\
        slotActive rc (m, v) d = true /\
        x = (NPlus.CDec m (g v) f d feat, VPlus.WClass (g u)).
  Proof.
    intros g FDefs Slots rc S FS pi x; unfold wDecs.
    rewrite SOparp.mem_unionMap; split.
    - intros [[[[m v] k] u] [Hin Hx]]; cbn beta iota in Hx.
      apply SOslp.in_if_empty in Hx as [Eb Hx].
      apply SOfp.mem_unionMap in Hx; destruct Hx as [[[q f] e] [Hf Hx]].
      cbn beta iota in Hx.
      destruct (entryFeatD e) as [[a' feat] |] eqn:Ee;
        [| exfalso; exact (SOslp.empty_in _ Hx)].
      rewrite SOslp.in_if_empty, !andb_true_iff, PkgEqb.eqb_true_iff,
        NEqb.eqb_true_iff, FSet.mem_spec in Hx.
      destruct Hx as [[[-> ->] Em] Hx].
      apply SOslp.mem_map in Hx; destruct Hx as [[q d] [Hq ->]].
      apply mem_slotsAtKey in Hq; destruct Hq as [Hs [-> [Ha Hact]]].
      exists m, v, k, u, f, e, feat, d; repeat split; assumption.
    - intros [m [v [k [u [f [e [feat [d
        [Hin [Eb [Hf [Ee [Em [Hs [Ha [Hact ->]]]]]]]]]]]]]]]].
      exists (((m, v), k), u); split; [exact Hin | cbn beta iota].
      rewrite Eb; apply SOfp.mem_unionMap.
      exists (((m, v), f), e); split; [exact Hf | cbn beta iota].
      rewrite Ee, PkgEqb.eqb_refl, NEqb.eqb_refl,
        (proj2 (FSet.mem_spec _ _) Em); cbn [andb].
      apply SOslp.mem_map; exists ((m, v), d); split;
        [apply mem_slotsAtKey; repeat split; assumption | reflexivity].
  Qed.

  Definition coreResolution (g : V.t -> G.t) (FDefs : FDefRel.t)
      (Slots : SlotRel.t) (Links : LinkRel.t)
      (rc : Pkg.t) (S : PkgSet.t)
      (FS : FeaturedSet.t) (pi : ParentRel.t) : T.PkgSet.t :=
    T.PkgSet.add rootPkg
      (T.PkgSet.union (crateReal g S)
         (T.PkgSet.union (wFeats g FS)
            (T.PkgSet.union
               (wSlots g FDefs Slots rc S FS pi)
               (T.PkgSet.union
                  (wDecs g FDefs Slots rc S FS pi)
                  (linkReal g S Links))))).

  Lemma mem_coreResolution :
    forall g FDefs Slots Links rc S FS pi x,
      T.PkgSet.In x
        (coreResolution g FDefs Slots Links rc S FS pi) <->
      x = rootPkg \/ T.PkgSet.In x (crateReal g S) \/
      T.PkgSet.In x (wFeats g FS) \/
      T.PkgSet.In x (wSlots g FDefs Slots rc S FS pi) \/
      T.PkgSet.In x (wDecs g FDefs Slots rc S FS pi) \/
      T.PkgSet.In x (linkReal g S Links).
  Proof.
    intros; unfold coreResolution.
    rewrite T.PkgSet.add_spec, !T.PkgSet.union_spec; reflexivity.
  Qed.

  Lemma core_shape :
    forall g FDefs Slots Links rc S FS pi n w,
      T.PkgSet.In (n, w)
        (coreResolution g FDefs Slots Links rc S FS pi) <->
      match n with
      | NPlus.CRoot => w = VPlus.WUnit
      | NPlus.CCrate m gr =>
          exists v, w = VPlus.WOrig v /\ PkgSet.In (m, v) S /\ gr = g v
      | NPlus.CFeatP m f gr =>
          exists v fs, w = VPlus.WOrig v /\ FeaturedSet.In ((m, v), fs) FS /\
            FSet.In f fs /\ gr = g v
      | NPlus.CSlot m gr d =>
          exists v u, w = VPlus.WClass (g u) /\ gr = g v /\
            ParentRel.In (((m, v), sKey d), u) pi /\
            parentsb FDefs Slots rc S FS (m, v) (sKey d) = true /\
            SlotRel.In ((m, v), d) Slots /\ slotActive rc (m, v) d = true
      | NPlus.CDec m gr f d feat =>
          exists v u e, w = VPlus.WClass (g u) /\ gr = g v /\
            ParentRel.In (((m, v), sKey d), u) pi /\
            parentsb FDefs Slots rc S FS (m, v) (sKey d) = true /\
            SlotRel.In ((m, v), d) Slots /\ slotActive rc (m, v) d = true /\
            FDefRel.In (((m, v), f), e) FDefs /\
            entryFeatD e = Some (sAlias d, feat) /\
            FSet.In f (fsAt FS (m, v))
      | NPlus.CLink l =>
          exists m v, w = VPlus.WName (NPlus.CCrate m (g v)) /\
            LinkRel.In ((m, v), l) Links /\ PkgSet.In (m, v) S
      end.
  Proof.
    intros g FDefs Slots Links rc S FS pi n w.
    rewrite mem_coreResolution, mem_crateReal, mem_wFeats, mem_wSlots,
      mem_wDecs, mem_linkReal; unfold rootPkg; split.
    - intros [He | [He | [He | [He | [He | He]]]]]; mem_destruct; eauto 20.
    - destruct n as [| m gr | m f gr | m gr d | m gr f d feat | l];
        cbn beta iota.
      + intros ->; left; reflexivity.
      + intros [v [-> [HS ->]]]; right; left; exists m, v; auto.
      + intros [v [fs [-> [Hfs [Hf ->]]]]].
        right; right; left; exists m, v, fs, f; auto.
      + intros [v [u [-> [-> [Hpi [Eb [Hs Hact]]]]]]].
        right; right; right; left; exists m, v, (sKey d), u, d.
        repeat split; assumption.
      + intros [v [u [e [-> [-> [Hpi [Eb [Hs [Hact [Hf [Ee Hfs]]]]]]]]]]].
        right; right; right; right; left.
        exists m, v, (sKey d), u, f, e, feat, d; repeat split; assumption.
      + intros [m [v [-> [Hl HS]]]]; right; right; right; right; right.
        exists m, v, l; auto.
  Qed.

  Lemma fsAt_mem
      {R support FDefs Slots Links g dflt rc rootFeats S FS pi} :
      IsResolution R support FDefs Slots Links g dflt rc
        rootFeats S FS pi ->
      forall p, PkgSet.In p S -> FeaturedSet.In (p, fsAt FS p) FS.
  Proof.
    intros Hres p Hp; destruct (res_fs_total Hres Hp) as [fs Hfs].
    rewrite (fsAt_in FS p fs (res_fs_functional Hres) Hfs); exact Hfs.
  Qed.

  Lemma parent_pick
      {R support FDefs Slots Links g dflt rc rootFeats S FS pi} :
      IsResolution R support FDefs Slots Links g dflt rc
        rootFeats S FS pi ->
      forall m v d, PkgSet.In (m, v) S ->
      SlotRel.In ((m, v), d) Slots ->
      slotActive rc (m, v) d = true ->
      (sOptional d = false \/
       Activated FDefs (fsAt FS (m, v)) (m, v) (sAlias d)) ->
      exists u, ParentRel.In (((m, v), sKey d), u) pi /\
        parentsb FDefs Slots rc S FS (m, v) (sKey d) = true /\
        VSet.In u (evalReq R (sTarget d) (sReq d)) /\
        PkgSet.In (sTarget d, u) S /\
        FSet.Subset (slotRequests d dflt) (fsAt FS (sTarget d, u)).
  Proof.
    intros Hres m v d HS Hd Hact Hopt.
    destruct (res_slot_closure Hres HS (fsAt_mem Hres _ HS) Hd Hact Hopt)
      as [u [Hpi [Hrg [Htgt Hsub]]]].
    exists u; repeat split; try assumption.
    - apply parentsb_iff; split; [exact HS |].
      exists d; repeat split; assumption.
    - apply mem_evalReq; split; [exact (res_subset Hres Htgt) | exact Hrg].
    - exact (Hsub _ (fsAt_mem Hres _ Htgt)).
  Qed.

  Lemma parent_slot
      {R support FDefs Slots Links g dflt rc rootFeats S FS pi} :
      SiteFunctional Slots ->
      IsResolution R support FDefs Slots Links g dflt rc
        rootFeats S FS pi ->
      forall m v k u, ParentRel.In (((m, v), k), u) pi ->
      parentsb FDefs Slots rc S FS (m, v) k = true ->
      exists d, SlotRel.In ((m, v), d) Slots /\ sKey d = k /\
        slotActive rc (m, v) d = true /\
        VSet.In u (evalReq R (sTarget d) (sReq d)) /\
        PkgSet.In (sTarget d, u) S /\
        FSet.Subset (slotRequests d dflt) (fsAt FS (sTarget d, u)).
  Proof.
    intros Hsite Hres m v k u Hpi Eb.
    apply parentsb_iff in Eb; destruct Eb as [HS [d [Hd [<- [Hact Hreq]]]]].
    destruct (parent_pick Hres m v d HS Hd Hact Hreq)
      as [u0 [Hpi0 [_ [Hu0 [Htgt Hsub]]]]].
    rewrite (res_pi_functional Hres Hpi Hpi0).
    exists d; repeat split; assumption.
  Qed.

  Theorem cargo_completeness :
    forall R support FDefs Slots Links g dflt rc rootFeats
           S FS pi,
      SiteFunctional Slots ->
      IsResolution R support FDefs Slots Links g dflt rc
        rootFeats S FS pi ->
      T.IsResolution
        (reduceReal g R support FDefs Slots Links rc)
        (reduceDeps g R support FDefs Slots Links dflt rc
           rootFeats) rootPkg
        (coreResolution g FDefs Slots Links rc S FS pi).
  Proof.
    intros R support FDefs Slots Links g dflt rc rootFeats
      S FS pi Hsite Hres.
    assert (HfsAt := fsAt_mem Hres).
    assert (Hpick := parent_pick Hres).
    assert (Hslot := parent_slot Hsite Hres).
    destruct rc as [rn rv].
    destruct Hres as [Hsub Hroot Hrootf Hdom Htot Hfun Hclass Hsupp
      Hpifun _ Hslotc Hfsame Hfdep Hlinks].
    constructor.
    - intros [n w] Hx; apply core_shape in Hx; apply real_shape.
      destruct n as [| m gr | m f gr | m gr d | m gr f d feat | l];
        cbn beta iota in Hx |- *.
      + exact Hx.
      + destruct Hx as [v [-> [HS ->]]]; exists v.
        repeat split; exact (Hsub _ HS).
      + destruct Hx as [v [fs [-> [Hfs [Hf ->]]]]]; exists v.
        repeat split; exact (Hsupp _ _ _ Hfs Hf).
      + destruct Hx as [v [u [-> [-> [Hpi [Eb [Hd Hact]]]]]]].
        destruct (Hslot _ _ _ _ Hpi Eb) as [d' [Hd' [Ha' [_ [Hu _]]]]].
        rewrite (Hsite (m, v) d' d Hd' Hd Ha') in Hu.
        split; [exists v | exists u]; auto.
      + destruct Hx
          as [v [u [e [-> [-> [Hpi [Eb [Hd [Hact [Hf [Ee _]]]]]]]]]]].
        destruct (Hslot _ _ _ _ Hpi Eb) as [d' [Hd' [Ha' [_ [Hu _]]]]].
        rewrite (Hsite (m, v) d' d Hd' Hd Ha') in Hu.
        split; [exists v, e; repeat split; assumption | exists u; auto].
      + destruct Hx as [m [v [-> [Hl HS]]]]; exists m, v.
        repeat split; [exact Hl | exact (Hsub _ HS)].
    - apply mem_coreResolution; left; reflexivity.
    - intros p Hp n vs Hed.
      apply mem_reduceDeps in Hed; destruct Hed as [_ Hh].
      destruct p as [[| m gr | m f gr | m gr1 d | m gr1 f d feat | l]
                     [| v0 | gr0 | q]];
        try (rewrite dep_inert in Hh by exact I;
             exfalso; exact (T.DependeesSet.empty_spec Hh)).
      + apply mem_dep_root in Hh.
        destruct Hh as [He | [f [Hf He]]]; injection He as E1 E2;
          subst n vs; exists (VPlus.WOrig rv);
          (split; [apply T.VSet.singleton_spec; reflexivity |]);
          apply core_shape.
        * exists rv; repeat split; exact Hroot.
        * exists rv, (fsAt FS (rn, rv)); repeat split;
            [exact (HfsAt _ Hroot) | exact (Hrootf _ (HfsAt _ Hroot) f Hf)].
      + apply mem_dep_crate in Hh.
        apply core_shape in Hp; cbn beta iota in Hp.
        destruct Hp as [v1 [Ev [HS _]]]; injection Ev as Ev; subst v1.
        destruct Hh
          as [<- [_ [[d [Hd [Hact [Hopt He]]]] | [l [Hl He]]]]];
          injection He as E1 E2; subst n vs.
        * destruct (Hpick _ _ _ HS Hd Hact (or_introl Hopt))
            as [u [Hpi [Eb [Hu [Htgt Hss]]]]].
          exists (VPlus.WClass (g u)); split.
          { apply mem_gransOf; exists u; split;
              [exact Hu | reflexivity]. }
          apply core_shape; exists v0, u; repeat split; assumption.
        * exists (VPlus.WName (NPlus.CCrate m (g v0))); split;
            [apply T.VSet.singleton_spec; reflexivity |].
          apply core_shape; exists m, v0; repeat split; assumption.
      + apply mem_dep_featP in Hh.
        apply core_shape in Hp; cbn beta iota in Hp.
        destruct Hp as [v1 [fs [Ev [Hfs [Hf _]]]]].
        injection Ev as Ev; subst v1.
        assert (Efs : fsAt FS (m, v0) = fs)
          by exact (fsAt_in FS (m, v0) fs Hfun Hfs).
        assert (HS : PkgSet.In (m, v0) S) by exact (Hdom _ _ Hfs).
        destruct Hh as [_ [_ [He | [e0 [Hfd Hcase]]]]].
        * injection He as E1 E2; subst n vs.
          exists (VPlus.WOrig v0); split;
            [apply T.VSet.singleton_spec; reflexivity |].
          apply core_shape; exists v0; repeat split; exact HS.
        * destruct Hcase as [[f' [Ee He]] | [Hcase | Hcase]].
          -- injection He as E1 E2; subst n vs e0.
             exists (VPlus.WOrig v0); split;
               [apply T.VSet.singleton_spec; reflexivity |].
             apply core_shape; exists v0, fs; repeat split;
               [exact Hfs | exact (Hfsame _ _ _ _ Hfs Hf Hfd)].
          -- destruct Hcase as [a [d [Ea [Hd [Ha [Hact He]]]]]]; subst a.
             injection He as E1 E2; subst n vs.
             assert (Hactd : Activated FDefs (fsAt FS (m, v0)) (m, v0)
                 (sAlias d)).
             { rewrite Efs; exists f; split; [exact Hf |].
               destruct e0 as [f0 | a0 | a0 feat0 | a0 feat0];
                 cbn [entryActivates] in Ea; try discriminate;
                 injection Ea as Ea; subst a0; eauto. }
             destruct (Hpick _ _ _ HS Hd Hact (or_intror Hactd))
               as [u [Hpi [Eb [Hu [Htgt Hss]]]]].
             exists (VPlus.WClass (g u)); split.
             { apply mem_gransOf; exists u; split;
                 [exact Hu | reflexivity]. }
             apply core_shape; exists v0, u; repeat split; assumption.
          -- destruct Hcase as [a [feat [d [Ea [Hd [Ha [Hact He]]]]]]];
               subst a.
             injection He as E1 E2; subst n vs.
             assert (Hactd : Activated FDefs (fsAt FS (m, v0)) (m, v0)
                 (sAlias d)).
             { rewrite Efs; exists f; split; [exact Hf |].
               destruct e0 as [f0 | a0 | a0 feat0 | a0 feat0];
                 cbn [entryFeatD] in Ea; try discriminate;
                 injection Ea as Ea1 Ea2; subst a0 feat0; eauto. }
             destruct (Hpick _ _ _ HS Hd Hact (or_intror Hactd))
               as [u [Hpi [Eb [Hu [Htgt Hss]]]]].
             exists (VPlus.WClass (g u)); split.
             { apply mem_gransOf; exists u; split;
                 [exact Hu | reflexivity]. }
             apply core_shape; exists v0, u, e0; repeat split;
               try assumption.
             rewrite Efs; exact Hf.
      + apply mem_dep_slot in Hh.
        destruct Hh as [_ [u0 [Hu0 [Hgu Hcase]]]].
        apply core_shape in Hp; cbn beta iota in Hp.
        destruct Hp as [v [u [Eu [Egr [Hpi [Eb [Hd Hact]]]]]]].
        injection Eu as ->.
        destruct (Hslot _ _ _ _ Hpi Eb)
          as [d' [Hd' [Ha' [Hact' [Hu' [Htgt Hss]]]]]].
        assert (Ed : d' = d) by exact (Hsite (m, v) d' d Hd' Hd Ha').
        subst d'.
        destruct Hcase as [He | [f0 [Hf0 He]]]; injection He as E1 E2;
          subst n vs; exists (VPlus.WOrig u);
          (split; [apply mem_inGran; exists u; auto |]); apply core_shape.
        * exists u; repeat split; assumption.
        * exists u, (fsAt FS (sTarget d, u)); repeat split; try assumption;
            [exact (HfsAt _ Htgt) | exact (Hss _ Hf0)].
      + apply mem_dep_dec in Hh.
        destruct Hh as [_ [u0 [Hu0 [Hgu Hcase]]]].
        apply core_shape in Hp; cbn beta iota in Hp.
        destruct Hp as [v [u [e [Eu [Egr [Hpi [Eb [Hd [Hact
          [Hfd2 [Ee2 Hf]]]]]]]]]]].
        injection Eu as ->; subst gr1.
        assert (HSnv : PkgSet.In (m, v) S)
          by (apply parentsb_iff in Eb; exact (proj1 Eb)).
        destruct (Hslot _ _ _ _ Hpi Eb)
          as [d' [Hd' [Ha' [Hact' [Hu' [Htgt Hss]]]]]].
        assert (Ed : d' = d) by exact (Hsite (m, v) d' d Hd' Hd Ha').
        subst d'.
        destruct Hcase as [He | He]; injection He as E1 E2; subst n vs.
        * exists (VPlus.WClass (g u)); split;
            [apply T.VSet.singleton_spec; reflexivity |].
          apply core_shape; exists v, u; repeat split; assumption.
        * exists (VPlus.WOrig u); split; [apply mem_inGran; exists u; auto |].
          apply core_shape; exists u, (fsAt FS (sTarget d, u));
            repeat split; try assumption; [exact (HfsAt _ Htgt) |].
          assert (Hor :
              FDefRel.In (((m, v), f), FEntry.EDepFeat (sAlias d) feat)
                FDefs \/
              FDefRel.In (((m, v), f), FEntry.EWeakFeat (sAlias d) feat)
                FDefs).
          { destruct e as [f0 | a0 | a0 feat0 | a0 feat0];
              cbn [entryFeatD] in Ee2; try discriminate;
              injection Ee2 as Ee1 Ee3; subst a0 feat0;
              [left | right]; exact Hfd2. }
          exact (Hfdep (m, v) (fsAt FS (m, v)) f (sAlias d) feat
                   (HfsAt _ HSnv) Hf Hor d u Hd eq_refl Hpi
                   (fsAt FS (sTarget d, u)) (HfsAt _ Htgt)).
    - intros n w w' Hw Hw'.
      apply core_shape in Hw; apply core_shape in Hw'.
      destruct n as [ | m gr | m f gr | m gr d | m gr f d feat | l ];
        cbn beta iota in Hw, Hw'.
      + subst w w'; reflexivity.
      + destruct Hw as [v [-> [HS Eg]]];
          destruct Hw' as [v' [-> [HS' Eg']]].
        destruct (V.eq_dec v v') as [E | NE];
          [rewrite E; reflexivity |].
        exfalso; apply (Hclass m v v' HS HS' NE); congruence.
      + destruct Hw as [v [fs [-> [Hfs [Hf Eg]]]]];
          destruct Hw' as [v' [fs' [-> [Hfs' [Hf' Eg']]]]].
        destruct (V.eq_dec v v') as [E | NE];
          [rewrite E; reflexivity |].
        exfalso; apply (Hclass m v v' (Hdom _ _ Hfs) (Hdom _ _ Hfs') NE);
          congruence.
      + destruct Hw as [v [u [-> [Egr [Hpi [Eb _]]]]]];
          destruct Hw' as [v' [u' [-> [Egr' [Hpi' [Eb' _]]]]]].
        apply parentsb_iff in Eb; apply parentsb_iff in Eb'.
        destruct (V.eq_dec v v') as [<- | NE];
          [| exfalso; apply (Hclass m v v' (proj1 Eb) (proj1 Eb') NE);
             congruence].
        rewrite (Hpifun (m, v) (sKey d) u u' Hpi Hpi'); reflexivity.
      + destruct Hw as [v [u [e [-> [Egr [Hpi [Eb _]]]]]]];
          destruct Hw' as [v' [u' [e' [-> [Egr' [Hpi' [Eb' _]]]]]]].
        apply parentsb_iff in Eb; apply parentsb_iff in Eb'.
        destruct (V.eq_dec v v') as [<- | NE];
          [| exfalso; apply (Hclass m v v' (proj1 Eb) (proj1 Eb') NE);
             congruence].
        rewrite (Hpifun (m, v) (sKey d) u u' Hpi Hpi'); reflexivity.
      + destruct Hw as [m [v [-> [Hl HS]]]];
          destruct Hw' as [m' [v' [-> [Hl' HS']]]].
        assert (E := Hlinks (m, v) (m', v') l HS HS' Hl Hl').
        injection E as <- <-; reflexivity.
  Qed.

  Module Lookup.
    Theorem versions_reduceRealRoot :
      forall g R support FDefs Slots Links rc w,
        T.PkgSet.In (NPlus.CRoot, w)
          (reduceReal g R support FDefs Slots Links rc) <->
        T.VSet.In w
          (versions g R support FDefs Slots Links rc NPlus.CRoot).
    Proof.
      intros; rewrite real_shape; cbn [versions].
      rewrite T.VSet.singleton_spec; reflexivity.
    Qed.

    Theorem versions_reduceRealCrate :
      forall g R support FDefs Slots Links rc m gr w,
        T.PkgSet.In (NPlus.CCrate m gr, w)
          (reduceReal g R support FDefs Slots Links rc) <->
        T.VSet.In w
          (versions g R support FDefs Slots Links rc
             (NPlus.CCrate m gr)).
    Proof.
      intros; rewrite real_shape; cbn [versions].
      rewrite SOpv2.mem_filterMap; split.
      - intros [v [-> [HR ->]]]; exists (m, v); split; [exact HR |].
        cbn beta iota; rewrite NEqb.eqb_refl, GEqb.eqb_refl; reflexivity.
      - intros [[n' v] [HR He]]; cbn beta iota in He.
        rewrite if_some_iff, andb_true_iff, NEqb.eqb_true_iff, GEqb.eqb_true_iff
          in He.
        destruct He as [[-> <-] <-]; exists v; auto.
    Qed.

    Theorem versions_reduceRealFeatP :
      forall g R support FDefs Slots Links rc m f gr w,
        T.PkgSet.In (NPlus.CFeatP m f gr, w)
          (reduceReal g R support FDefs Slots Links rc) <->
        T.VSet.In w
          (versions g R support FDefs Slots Links rc
             (NPlus.CFeatP m f gr)).
    Proof.
      intros; rewrite real_shape; cbn [versions].
      rewrite SOspv.mem_filterMap; split.
      - intros [v [-> [Hs ->]]]; exists ((m, v), f); split; [exact Hs |].
        cbn beta iota; rewrite NEqb.eqb_refl, FEqb.eqb_refl, GEqb.eqb_refl;
          reflexivity.
      - intros [[[n' v] f'] [Hs He]]; cbn beta iota in He.
        rewrite if_some_iff, !andb_true_iff, NEqb.eqb_true_iff,
          FEqb.eqb_true_iff, GEqb.eqb_true_iff in He.
        destruct He as [[[-> ->] <-] <-]; exists v; auto.
    Qed.

    Theorem versions_reduceRealSlot :
      forall g R support FDefs Slots Links rc m gr d w,
        T.PkgSet.In (NPlus.CSlot m gr d, w)
          (reduceReal g R support FDefs Slots Links rc) <->
        T.VSet.In w
          (versions g R support FDefs Slots Links rc
             (NPlus.CSlot m gr d)).
    Proof.
      intros; rewrite real_shape; cbn [versions].
      rewrite SOvv.in_if_empty, slotOwnedb_iff, mem_gransOf; reflexivity.
    Qed.

    Theorem versions_reduceRealDecision :
      forall g R support FDefs Slots Links rc m gr f d feat w,
        T.PkgSet.In (NPlus.CDec m gr f d feat, w)
          (reduceReal g R support FDefs Slots Links rc) <->
        T.VSet.In w
          (versions g R support FDefs Slots Links rc
             (NPlus.CDec m gr f d feat)).
    Proof.
      intros; rewrite real_shape; cbn [versions].
      rewrite SOvv.in_if_empty, decOwnedb_iff, mem_gransOf; reflexivity.
    Qed.

    Theorem versions_reduceRealLink :
      forall g R support FDefs Slots Links rc l w,
        T.PkgSet.In (NPlus.CLink l, w)
          (reduceReal g R support FDefs Slots Links rc) <->
        T.VSet.In w
          (versions g R support FDefs Slots Links rc
             (NPlus.CLink l)).
    Proof. intros; rewrite real_shape, mem_versions_link; reflexivity. Qed.

    Theorem dependees_reduceDeps :
      forall g R support FDefs Slots Links dflt rc rootFeats p,
        dependees g R support FDefs Slots Links dflt rc
          rootFeats p =
        T.dependees
          (reduceDeps g R support FDefs Slots Links dflt rc
             rootFeats) p.
    Proof.
      intros; apply T.DependeesSet.ext; intro h.
      rewrite T.mem_dependees, mem_reduceDeps; split.
      - intro Hh; split; [| exact Hh]; eapply dep_real; exact Hh.
      - intros [_ Hh]; exact Hh.
    Qed.

    Theorem dependees_reduceDepsInert :
      forall g R support FDefs Slots Links dflt rc rootFeats p,
        Inert p ->
        dependees g R support FDefs Slots Links dflt rc
          rootFeats p =
        T.dependees
          (reduceDeps g R support FDefs Slots Links dflt rc
             rootFeats) p.
    Proof. intros; apply dependees_reduceDeps. Qed.

    Module NSet := FSetUOT N.
    Module PkgPre := PreimageOfKeys N Pkg NSet PkgSet.
    Module SupportPre := PreimageOfKeys N PkgF NSet SupportSet.
    Module FDefPre := Preimage FDefElt FDefRel.
    Module SlotFibred := FibredRel Pkg SlotData SlotElt SlotRel.
    Module LinkFibred := FibredRel Pkg N LinkElt LinkRel.
    Module SupportFibred := FibredRel Pkg F PkgF SupportSet.
    Module SOsn := SetOps SlotElt N SlotRel NSet.

    Definition realPreimage (R : PkgSet.t) (ns : NSet.t) : PkgSet.t :=
      PkgPre.ofKeys fst ns R.

    Definition supportPreimage (support : SupportSet.t) (ns : NSet.t)
      : SupportSet.t :=
      SupportPre.ofKeys (fun x => fst (fst x)) ns support.

    Definition fdefFibre (FDefs : FDefRel.t) (p : Pkg.t) : FDefRel.t :=
      FDefPre.preimage (fun x => fst (fst x)) (fun q => PkgEqb.eqb q p) FDefs.

    Definition reads (Slots : SlotRel.t) (p : Pkg.t) : NSet.t :=
      NSet.add (fst p)
        (SOsn.map (fun x => sTarget (snd x)) (SlotFibred.tailFibre Slots p)).

    Definition claimants (R : PkgSet.t) (Links : LinkRel.t) (l : N.t)
      : PkgSet.t :=
      PkgSet.filter (fun q => LinkRel.mem (q, l) Links) R.

    Lemma mem_realPreimage : forall R ns q,
        PkgSet.In q (realPreimage R ns) <->
        PkgSet.In q R /\ NSet.In (fst q) ns.
    Proof. intros; unfold realPreimage; apply PkgPre.mem_ofKeys. Qed.

    Lemma evalReq_realPreimage : forall R ns m rg,
        NSet.In m ns ->
        evalReq (realPreimage R ns) m rg = evalReq R m rg.
    Proof.
      intros R ns m rg Hm; apply VSet.ext; intro u.
      rewrite !mem_evalReq, mem_realPreimage; cbn [fst]; tauto.
    Qed.

    Lemma mem_supportPreimage : forall support ns m v f,
        SupportSet.In ((m, v), f) (supportPreimage support ns) <->
        SupportSet.In ((m, v), f) support /\ NSet.In m ns.
    Proof.
      intros; unfold supportPreimage; rewrite SupportPre.mem_ofKeys;
        cbn [fst]; reflexivity.
    Qed.

    Lemma mem_fdefFibre : forall FDefs p q f e,
        FDefRel.In ((q, f), e) (fdefFibre FDefs p) <->
        FDefRel.In ((q, f), e) FDefs /\ q = p.
    Proof.
      intros; unfold fdefFibre; rewrite FDefPre.mem_preimage; cbn [fst].
      rewrite PkgEqb.eqb_true_iff; reflexivity.
    Qed.

    Lemma mem_claimants : forall R Links l q,
        PkgSet.In q (claimants R Links l) <->
        PkgSet.In q R /\ LinkRel.In (q, l) Links.
    Proof.
      intros; unfold claimants; rewrite PkgSet.filter_spec', LinkRel.mem_spec;
        reflexivity.
    Qed.

    Lemma reads_own : forall Slots p, NSet.In (fst p) (reads Slots p).
    Proof. intros; unfold reads; apply NSet.add_spec; left; reflexivity. Qed.

    Lemma reads_target : forall Slots p d,
        SlotRel.In (p, d) Slots -> NSet.In (sTarget d) (reads Slots p).
    Proof.
      intros Slots p d Hs; unfold reads; apply NSet.add_spec; right.
      apply SOsn.mem_map; exists (p, d); split; [| reflexivity].
      apply SlotFibred.mem_tailFibre; split; [exact Hs | reflexivity].
    Qed.

    Lemma in_realPreimage_own : forall R Slots p,
        PkgSet.In p R <-> PkgSet.In p (realPreimage R (reads Slots p)).
    Proof.
      intros; rewrite mem_realPreimage; split;
        [intro H; split; [exact H | apply reads_own] | intros [H _]; exact H].
    Qed.

    Lemma evalReq_reads : forall R Slots p d,
        SlotRel.In (p, d) Slots ->
        evalReq R (sTarget d) (sReq d) =
        evalReq (realPreimage R (reads Slots p)) (sTarget d) (sReq d).
    Proof.
      intros R Slots p d Hs; symmetry; apply evalReq_realPreimage.
      apply reads_target; exact Hs.
    Qed.

    Lemma in_slotFibre : forall Slots p d,
        SlotRel.In (p, d) Slots <->
        SlotRel.In (p, d) (SlotFibred.tailFibre Slots p).
    Proof.
      intros; rewrite SlotFibred.mem_tailFibre; split;
        [intro H; split; [exact H | reflexivity] | intros [H _]; exact H].
    Qed.

    Lemma in_linkFibre : forall Links p l,
        LinkRel.In (p, l) Links <->
        LinkRel.In (p, l) (LinkFibred.tailFibre Links p).
    Proof.
      intros; rewrite LinkFibred.mem_tailFibre; split;
        [intro H; split; [exact H | reflexivity] | intros [H _]; exact H].
    Qed.

    Lemma in_supportFibre : forall support p f,
        SupportSet.In (p, f) support <->
        SupportSet.In (p, f) (SupportFibred.tailFibre support p).
    Proof.
      intros; rewrite SupportFibred.mem_tailFibre; split;
        [intro H; split; [exact H | reflexivity] | intros [H _]; exact H].
    Qed.

    Lemma in_fdefFibre : forall FDefs p f e,
        FDefRel.In ((p, f), e) FDefs <->
        FDefRel.In ((p, f), e) (fdefFibre FDefs p).
    Proof.
      intros; rewrite mem_fdefFibre; split;
        [intro H; split; [exact H | reflexivity] | intros [H _]; exact H].
    Qed.

    Theorem versions_lookupRoot :
      forall g R support FDefs Slots Links rc,
        versions g R support FDefs Slots Links rc NPlus.CRoot =
        versions g PkgSet.empty SupportSet.empty FDefRel.empty SlotRel.empty
          LinkRel.empty rc NPlus.CRoot.
    Proof. reflexivity. Qed.

    Theorem versions_lookupCrate :
      forall g R support FDefs Slots Links rc m gr,
        versions g R support FDefs Slots Links rc (NPlus.CCrate m gr) =
        versions g (realPreimage R (NSet.singleton m)) SupportSet.empty
          FDefRel.empty SlotRel.empty LinkRel.empty rc (NPlus.CCrate m gr).
    Proof.
      intros; cbn [versions]; apply T.VSet.ext; intro w; symmetry.
      apply SOpv2.filterMap_restrict; [apply PkgPre.ofKeys_subset |].
      intros [n' v] HR He; cbn beta iota in He.
      rewrite if_some_iff, andb_true_iff, NEqb.eqb_true_iff in He.
      destruct He as [[-> _] _]; apply mem_realPreimage; split;
        [exact HR | apply NSet.singleton_spec; reflexivity].
    Qed.

    Theorem versions_lookupFeatP :
      forall g R support FDefs Slots Links rc m f gr,
        versions g R support FDefs Slots Links rc (NPlus.CFeatP m f gr) =
        versions g (realPreimage R (NSet.singleton m))
          (supportPreimage support (NSet.singleton m))
          FDefRel.empty SlotRel.empty LinkRel.empty rc (NPlus.CFeatP m f gr).
    Proof.
      intros; cbn [versions]; apply T.VSet.ext; intro w; symmetry.
      apply SOspv.filterMap_restrict; [apply SupportPre.ofKeys_subset |].
      intros [[n' v] f'] Hs He; cbn beta iota in He.
      rewrite if_some_iff, !andb_true_iff, NEqb.eqb_true_iff in He.
      destruct He as [[[-> _] _] _]; apply mem_supportPreimage; split;
        [exact Hs | apply NSet.singleton_spec; reflexivity].
    Qed.

    Lemma slotOwnedb_witness :
      forall g Slots rc m gr d u,
        SlotRel.In ((m, u), d) Slots -> g u = gr ->
        slotActive rc (m, u) d = true ->
        slotOwnedb g Slots rc m gr d = true /\
        slotOwnedb g (SlotFibred.tailFibre Slots (m, u)) rc m gr d = true.
    Proof.
      intros g Slots rc m gr d u Hs Hg Hact; split; apply slotOwnedb_iff;
        exists u; (split; [exact Hg | split; [| exact Hact]]);
        [exact Hs | exact (proj1 (in_slotFibre Slots (m, u) d) Hs)].
    Qed.

    Lemma decOwnedb_witness :
      forall g FDefs Slots rc m gr f d feat u e,
        FDefRel.In (((m, u), f), e) FDefs ->
        entryFeatD e = Some (sAlias d, feat) ->
        SlotRel.In ((m, u), d) Slots -> g u = gr ->
        slotActive rc (m, u) d = true ->
        decOwnedb g FDefs Slots rc m gr f d feat = true /\
        decOwnedb g (fdefFibre FDefs (m, u))
          (SlotFibred.tailFibre Slots (m, u)) rc m gr f d feat = true.
    Proof.
      intros g FDefs Slots rc m gr f d feat u e Hf Ee Hs Hg Hact;
        split; apply decOwnedb_iff; exists u, e;
        (split; [exact Hg |]).
      - repeat split; assumption.
      - split; [exact (proj1 (in_fdefFibre FDefs (m, u) f e) Hf) |].
        split; [exact Ee |].
        split; [exact (proj1 (in_slotFibre Slots (m, u) d) Hs) | exact Hact].
    Qed.

    Theorem versions_lookupSlot :
      forall g R support FDefs Slots Links rc m gr d u,
        SlotRel.In ((m, u), d) Slots -> g u = gr ->
        slotActive rc (m, u) d = true ->
        versions g R support FDefs Slots Links rc (NPlus.CSlot m gr d) =
        versions g (realPreimage R (NSet.singleton (sTarget d)))
          SupportSet.empty FDefRel.empty (SlotFibred.tailFibre Slots (m, u))
          LinkRel.empty rc (NPlus.CSlot m gr d).
    Proof.
      intros g R support FDefs Slots Links rc m gr d u Hs Hg Hact.
      destruct (slotOwnedb_witness g Slots rc m gr d u Hs Hg Hact)
        as [E1 E2].
      cbn [versions]; rewrite E1, E2.
      rewrite evalReq_realPreimage;
        [reflexivity | apply NSet.singleton_spec; reflexivity].
    Qed.

    Theorem versions_lookupDecision :
      forall g R support FDefs Slots Links rc m gr f d feat u e,
        FDefRel.In (((m, u), f), e) FDefs ->
        entryFeatD e = Some (sAlias d, feat) ->
        SlotRel.In ((m, u), d) Slots -> g u = gr ->
        slotActive rc (m, u) d = true ->
        versions g R support FDefs Slots Links rc
          (NPlus.CDec m gr f d feat) =
        versions g (realPreimage R (NSet.singleton (sTarget d)))
          SupportSet.empty (fdefFibre FDefs (m, u))
          (SlotFibred.tailFibre Slots (m, u))
          LinkRel.empty rc (NPlus.CDec m gr f d feat).
    Proof.
      intros g R support FDefs Slots Links rc m gr f d feat u e
        Hf Ee Hs Hg Hact.
      destruct (decOwnedb_witness g FDefs Slots rc m gr f d feat u e
                  Hf Ee Hs Hg Hact) as [E1 E2].
      cbn [versions]; rewrite E1, E2.
      rewrite evalReq_realPreimage;
        [reflexivity | apply NSet.singleton_spec; reflexivity].
    Qed.

    Theorem slot_declines :
      forall g R support FDefs Slots Links dflt rc rootFeats m gr d,
        ~ SlotOwned g Slots rc m gr d ->
        versions g R support FDefs Slots Links rc (NPlus.CSlot m gr d) =
        T.VSet.empty /\
        forall gr', dependees g R support FDefs Slots Links dflt rc rootFeats
                      (NPlus.CSlot m gr d, VPlus.WClass gr') =
                    T.DependeesSet.empty.
    Proof.
      intros g R support FDefs Slots Links dflt rc rootFeats m gr d Hn.
      assert (E : slotOwnedb g Slots rc m gr d = false)
        by (apply Bool.not_true_iff_false; rewrite slotOwnedb_iff; exact Hn).
      split; [cbn [versions]; rewrite E; reflexivity |].
      intro gr'; cbn [dependees]; rewrite E; reflexivity.
    Qed.

    Theorem decision_declines :
      forall g R support FDefs Slots Links dflt rc rootFeats m gr f d feat,
        ~ DecOwned g FDefs Slots rc m gr f d feat ->
        versions g R support FDefs Slots Links rc (NPlus.CDec m gr f d feat) =
        T.VSet.empty /\
        forall gr', dependees g R support FDefs Slots Links dflt rc rootFeats
                      (NPlus.CDec m gr f d feat, VPlus.WClass gr') =
                    T.DependeesSet.empty.
    Proof.
      intros g R support FDefs Slots Links dflt rc rootFeats m gr f d feat Hn.
      assert (E : decOwnedb g FDefs Slots rc m gr f d feat = false)
        by (apply Bool.not_true_iff_false; rewrite decOwnedb_iff; exact Hn).
      split; [cbn [versions]; rewrite E; reflexivity |].
      intro gr'; cbn [dependees]; rewrite E; reflexivity.
    Qed.

    Lemma crateReal_claimants : forall g R Links l,
        crateReal g (claimants R Links l) =
        ClsT.Reduction.Lookup.inClass (crateReal g R) (linkRel g Links)
          (NPlus.CLink l).
    Proof.
      intros; apply T.PkgSet.ext; intro x.
      rewrite ClsT.Reduction.Lookup.mem_inClass, !mem_crateReal.
      split.
      - intros [m [v [Hc ->]]]; apply mem_claimants in Hc.
        destruct Hc as [HR Hl]; split.
        + exists m, v; split; [exact HR | reflexivity].
        + apply mem_linkRel; exists m, v, l; repeat split; exact Hl.
      - intros [[m [v [HR ->]]] Hc].
        apply mem_linkRel in Hc; destruct Hc as [m' [v' [l' [Hl [E Ek]]]]].
        injection E as E1 _ E3; subst m' v'; injection Ek as <-.
        exists m, v; split; [apply mem_claimants; split; assumption
                            | reflexivity].
    Qed.

    Lemma linkRel_headFibre : forall g Links l,
        linkRel g (LinkFibred.headFibre Links l) =
        ClsT.Reduction.Lookup.classRelAt (linkRel g Links) (NPlus.CLink l).
    Proof.
      intros; apply ClsT.InClassRel.ext; intros [q k].
      rewrite ClsT.Reduction.Lookup.mem_classRelAt, !mem_linkRel.
      split.
      - intros [m [v [l' [Hl [-> ->]]]]].
        apply LinkFibred.mem_headFibre in Hl; destruct Hl as [Hl ->].
        split; [exists m, v, l; repeat split; exact Hl | reflexivity].
      - intros [[m [v [l' [Hl [-> ->]]]]] Ek]; injection Ek as ->.
        exists m, v, l; repeat split.
        apply LinkFibred.mem_headFibre; split; [exact Hl | reflexivity].
    Qed.

    Theorem versions_lookupLink :
      forall g R support FDefs Slots Links rc l,
        versions g R support FDefs Slots Links rc (NPlus.CLink l) =
        versions g (claimants R Links l) SupportSet.empty FDefRel.empty
          SlotRel.empty (LinkFibred.headFibre Links l) rc (NPlus.CLink l).
    Proof.
      intros; apply T.VSet.ext; intro w.
      rewrite !versions_link_reduceReal, crateReal_claimants,
        linkRel_headFibre, <- ClsT.Reduction.Lookup.versions_lookupClass.
      reflexivity.
    Qed.

    Lemma dep_crate_mono :
      forall g R R' support support' FDefs FDefs' Slots Slots' Links Links'
             dflt rc rootFeats rootFeats' m gr v,
        (forall d, SlotRel.In ((m, v), d) Slots ->
           SlotRel.In ((m, v), d) Slots') ->
        (forall d, SlotRel.In ((m, v), d) Slots ->
           evalReq R (sTarget d) (sReq d) = evalReq R' (sTarget d) (sReq d)) ->
        (PkgSet.In (m, v) R -> PkgSet.In (m, v) R') ->
        (forall l, LinkRel.In ((m, v), l) Links -> LinkRel.In ((m, v), l) Links') ->
        forall h,
          T.DependeesSet.In h
            (dependees g R support FDefs Slots Links dflt rc rootFeats
               (NPlus.CCrate m gr, VPlus.WOrig v)) ->
          T.DependeesSet.In h
            (dependees g R' support' FDefs' Slots' Links' dflt rc rootFeats'
               (NPlus.CCrate m gr, VPlus.WOrig v)).
    Proof.
      intros * HS Hev HR HL h Hh.
      apply mem_dep_crate in Hh; apply mem_dep_crate.
      destruct Hh as [Hg [Hm Hh]]; split; [exact Hg | split; [exact (HR Hm) |]].
      destruct Hh as [[d [Hd [Ha [Ho ->]]]] | [l [Hl ->]]].
      - left; exists d; rewrite <- (Hev d Hd).
        split; [exact (HS d Hd) | split; [exact Ha | split; [exact Ho | reflexivity]]].
      - right; exists l; split; [exact (HL l Hl) | reflexivity].
    Qed.

    Lemma dep_featP_mono :
      forall g R R' support support' FDefs FDefs' Slots Slots' Links Links'
             dflt rc rootFeats rootFeats' m f gr v,
        (forall d, SlotRel.In ((m, v), d) Slots ->
           SlotRel.In ((m, v), d) Slots') ->
        (forall d, SlotRel.In ((m, v), d) Slots ->
           evalReq R (sTarget d) (sReq d) = evalReq R' (sTarget d) (sReq d)) ->
        (SupportSet.In ((m, v), f) support -> SupportSet.In ((m, v), f) support') ->
        (forall e, FDefRel.In (((m, v), f), e) FDefs ->
           FDefRel.In (((m, v), f), e) FDefs') ->
        forall h,
          T.DependeesSet.In h
            (dependees g R support FDefs Slots Links dflt rc rootFeats
               (NPlus.CFeatP m f gr, VPlus.WOrig v)) ->
          T.DependeesSet.In h
            (dependees g R' support' FDefs' Slots' Links' dflt rc rootFeats'
               (NPlus.CFeatP m f gr, VPlus.WOrig v)).
    Proof.
      intros * HS Hev Hsp HF h Hh.
      apply mem_dep_featP in Hh; apply mem_dep_featP.
      destruct Hh as [Hg [Hs Hh]]; split; [exact Hg | split; [exact (Hsp Hs) |]].
      destruct Hh as [Hh | [e0 [Hfd Hc]]]; [left; exact Hh | right].
      exists e0; split; [exact (HF e0 Hfd) |].
      destruct Hc as [[f' [He ->]] | [[a [d [Ha [Hd [Hal [Hact ->]]]]]]
                                    | [a [feat [d [Ha [Hd [Hal [Hact ->]]]]]]]]].
      - left; exists f'; split; [exact He | reflexivity].
      - right; left; exists a, d; rewrite <- (Hev d Hd).
        split; [exact Ha | split; [exact (HS d Hd) |
          split; [exact Hal | split; [exact Hact | reflexivity]]]].
      - right; right; exists a, feat, d; rewrite <- (Hev d Hd).
        split; [exact Ha | split; [exact (HS d Hd) |
          split; [exact Hal | split; [exact Hact | reflexivity]]]].
    Qed.

    Lemma dep_crate_agree :
      forall g R R' support support' FDefs FDefs' Slots Slots' Links Links'
             dflt rc rootFeats rootFeats' m gr v,
        (forall d, SlotRel.In ((m, v), d) Slots <->
           SlotRel.In ((m, v), d) Slots') ->
        (forall d, SlotRel.In ((m, v), d) Slots ->
           evalReq R (sTarget d) (sReq d) = evalReq R' (sTarget d) (sReq d)) ->
        (PkgSet.In (m, v) R <-> PkgSet.In (m, v) R') ->
        (forall l, LinkRel.In ((m, v), l) Links <-> LinkRel.In ((m, v), l) Links') ->
        dependees g R support FDefs Slots Links dflt rc rootFeats
          (NPlus.CCrate m gr, VPlus.WOrig v) =
        dependees g R' support' FDefs' Slots' Links' dflt rc rootFeats'
          (NPlus.CCrate m gr, VPlus.WOrig v).
    Proof.
      intros * HS Hev HR HL; apply T.DependeesSet.ext; intro h; split.
      - apply dep_crate_mono;
          [intros d Hd; apply HS; exact Hd | exact Hev
           | apply HR | intros l Hl; apply HL; exact Hl].
      - apply dep_crate_mono;
          [intros d Hd; apply HS; exact Hd
           | intros d Hd; symmetry; apply Hev; apply HS; exact Hd
           | apply HR | intros l Hl; apply HL; exact Hl].
    Qed.

    Lemma dep_featP_agree :
      forall g R R' support support' FDefs FDefs' Slots Slots' Links Links'
             dflt rc rootFeats rootFeats' m f gr v,
        (forall d, SlotRel.In ((m, v), d) Slots <->
           SlotRel.In ((m, v), d) Slots') ->
        (forall d, SlotRel.In ((m, v), d) Slots ->
           evalReq R (sTarget d) (sReq d) = evalReq R' (sTarget d) (sReq d)) ->
        (SupportSet.In ((m, v), f) support <-> SupportSet.In ((m, v), f) support') ->
        (forall e, FDefRel.In (((m, v), f), e) FDefs <->
           FDefRel.In (((m, v), f), e) FDefs') ->
        dependees g R support FDefs Slots Links dflt rc rootFeats
          (NPlus.CFeatP m f gr, VPlus.WOrig v) =
        dependees g R' support' FDefs' Slots' Links' dflt rc rootFeats'
          (NPlus.CFeatP m f gr, VPlus.WOrig v).
    Proof.
      intros * HS Hev Hsp HF; apply T.DependeesSet.ext; intro h; split.
      - apply dep_featP_mono;
          [intros d Hd; apply HS; exact Hd | exact Hev
           | apply Hsp | intros e He; apply HF; exact He].
      - apply dep_featP_mono;
          [intros d Hd; apply HS; exact Hd
           | intros d Hd; symmetry; apply Hev; apply HS; exact Hd
           | apply Hsp | intros e He; apply HF; exact He].
    Qed.

    Theorem dependees_lookupRoot :
      forall g R support FDefs Slots Links dflt rc rootFeats,
        dependees g R support FDefs Slots Links dflt rc rootFeats rootPkg =
        dependees g PkgSet.empty SupportSet.empty FDefRel.empty SlotRel.empty
          LinkRel.empty dflt rc rootFeats rootPkg.
    Proof. reflexivity. Qed.

    Theorem dependees_lookupCrate :
      forall g R support FDefs Slots Links dflt rc rootFeats m gr v,
        dependees g R support FDefs Slots Links dflt rc rootFeats
          (NPlus.CCrate m gr, VPlus.WOrig v) =
        dependees g (realPreimage R (reads Slots (m, v))) SupportSet.empty
          FDefRel.empty (SlotFibred.tailFibre Slots (m, v))
          (LinkFibred.tailFibre Links (m, v)) dflt rc rootFeats
          (NPlus.CCrate m gr, VPlus.WOrig v).
    Proof.
      intros; apply dep_crate_agree;
        [intro d; apply in_slotFibre | apply evalReq_reads
         | apply in_realPreimage_own | intro l; apply in_linkFibre].
    Qed.

    Theorem dependees_lookupFeatP :
      forall g R support FDefs Slots Links dflt rc rootFeats m f gr v,
        dependees g R support FDefs Slots Links dflt rc rootFeats
          (NPlus.CFeatP m f gr, VPlus.WOrig v) =
        dependees g (realPreimage R (reads Slots (m, v)))
          (SupportFibred.tailFibre support (m, v)) (fdefFibre FDefs (m, v))
          (SlotFibred.tailFibre Slots (m, v)) LinkRel.empty dflt rc rootFeats
          (NPlus.CFeatP m f gr, VPlus.WOrig v).
    Proof.
      intros; apply dep_featP_agree;
        [intro d; apply in_slotFibre | apply evalReq_reads
         | apply in_supportFibre | intro e; apply in_fdefFibre].
    Qed.

    Theorem dependees_lookupSlot :
      forall g R support FDefs Slots Links dflt rc rootFeats m gr0 d gr u,
        SlotRel.In ((m, u), d) Slots -> g u = gr0 ->
        slotActive rc (m, u) d = true ->
        dependees g R support FDefs Slots Links dflt rc rootFeats
          (NPlus.CSlot m gr0 d, VPlus.WClass gr) =
        dependees g (realPreimage R (NSet.singleton (sTarget d)))
          SupportSet.empty FDefRel.empty (SlotFibred.tailFibre Slots (m, u))
          LinkRel.empty dflt rc rootFeats (NPlus.CSlot m gr0 d, VPlus.WClass gr).
    Proof.
      intros g R support FDefs Slots Links dflt rc rootFeats m gr0 d gr u
        Hs Hg Hact.
      destruct (slotOwnedb_witness g Slots rc m gr0 d u Hs Hg Hact)
        as [E1 E2].
      cbn [dependees]; rewrite E1, E2.
      rewrite evalReq_realPreimage;
        [reflexivity | apply NSet.singleton_spec; reflexivity].
    Qed.

    Theorem dependees_lookupDecision :
      forall g R support FDefs Slots Links dflt rc rootFeats
             m gr0 f d feat gr u e,
        FDefRel.In (((m, u), f), e) FDefs ->
        entryFeatD e = Some (sAlias d, feat) ->
        SlotRel.In ((m, u), d) Slots -> g u = gr0 ->
        slotActive rc (m, u) d = true ->
        dependees g R support FDefs Slots Links dflt rc rootFeats
          (NPlus.CDec m gr0 f d feat, VPlus.WClass gr) =
        dependees g (realPreimage R (NSet.singleton (sTarget d)))
          SupportSet.empty (fdefFibre FDefs (m, u))
          (SlotFibred.tailFibre Slots (m, u))
          LinkRel.empty dflt rc rootFeats
          (NPlus.CDec m gr0 f d feat, VPlus.WClass gr).
    Proof.
      intros g R support FDefs Slots Links dflt rc rootFeats m gr0 f d feat gr
        u e Hf Ee Hs Hg Hact.
      destruct (decOwnedb_witness g FDefs Slots rc m gr0 f d feat u e
                  Hf Ee Hs Hg Hact) as [E1 E2].
      cbn [dependees]; rewrite E1, E2.
      rewrite evalReq_realPreimage;
        [reflexivity | apply NSet.singleton_spec; reflexivity].
    Qed.

  End Lookup.

  Theorem cargoResolution_coreResolution :
    forall g FDefs Slots Links rc S FS pi,
      cargoResolution (coreResolution g FDefs Slots Links rc S FS pi) = S.
  Proof.
    intros g FDefs Slots Links rc S FS pi; apply PkgSet.ext; intros [m v].
    rewrite mem_cargoResolution; split.
    - intros [gr Hin]; apply core_shape in Hin; cbn beta iota in Hin.
      destruct Hin as [v' [Ev [HS _]]]; injection Ev as <-; exact HS.
    - intro HS; exists (g v); apply core_shape; exists v.
      repeat split; exact HS.
  Qed.

  Lemma featsAt_coreResolution
      {R support FDefs Slots Links g dflt rc rootFeats S FS pi} :
      IsResolution R support FDefs Slots Links g dflt rc
        rootFeats S FS pi ->
      forall p, PkgSet.In p S ->
      featsAt (coreResolution g FDefs Slots Links rc S FS pi) p = fsAt FS p.
  Proof.
    intros Hres [m v] Hp.
    apply FSet.ext; intro f; rewrite mem_featsAt; split.
    - intros [gr Hin]; apply core_shape in Hin; cbn beta iota in Hin.
      destruct Hin as [v' [fs [Ev [Hfs [Hf _]]]]]; injection Ev as <-.
      rewrite (fsAt_in FS (m, v) fs (res_fs_functional Hres) Hfs); exact Hf.
    - intro Hf; exists (g v); apply core_shape; exists v, (fsAt FS (m, v)).
      repeat split; [exact (fsAt_mem Hres _ Hp) | exact Hf].
  Qed.

  Theorem decodeFS_coreResolution :
    forall R support FDefs Slots Links g dflt rc rootFeats S FS pi,
      IsResolution R support FDefs Slots Links g dflt rc
        rootFeats S FS pi ->
      decodeFS (coreResolution g FDefs Slots Links rc S FS pi) = FS.
  Proof.
    intros R support FDefs Slots Links g dflt rc rootFeats
      S FS pi Hres.
    apply FeaturedSet.ext; intros [p fs].
    rewrite mem_decodeFS, cargoResolution_coreResolution; split.
    - intros [Hp ->]; rewrite (featsAt_coreResolution Hres _ Hp).
      exact (fsAt_mem Hres _ Hp).
    - intro Hfs; assert (Hp := res_fs_dom Hres Hfs).
      split; [exact Hp |].
      rewrite (featsAt_coreResolution Hres _ Hp); symmetry.
      exact (fsAt_in FS p fs (res_fs_functional Hres) Hfs).
  Qed.

  Theorem decodeParents_coreResolution :
    forall R support FDefs Slots Links g dflt rc rootFeats S FS pi,
      SiteFunctional Slots ->
      IsResolution R support FDefs Slots Links g dflt rc
        rootFeats S FS pi ->
      decodeParents FDefs Slots rc
        (coreResolution g FDefs Slots Links rc S FS pi) = pi.
  Proof.
    intros R support FDefs Slots Links g dflt rc rootFeats
      S FS pi Hsite Hres.
    assert (Hslot := parent_slot Hsite Hres).
    apply ParentRel.ext; intros [[[m v] k] u].
    rewrite mem_decodeParents; split.
    - intros [gr [gr' [d [Hsl [Hown [Hd [<- [_ [_ Hcr]]]]]]]]].
      apply core_shape in Hsl; cbn beta iota in Hsl.
      destruct Hsl as [v0 [u' [Eu [Egr [Hpi [Eb _]]]]]]; injection Eu as Eu.
      apply core_shape in Hown; cbn beta iota in Hown.
      destruct Hown as [v1 [Ev [HSv Egv]]]; injection Ev as <-.
      assert (Hv0 : PkgSet.In (m, v0) S)
        by (apply parentsb_iff in Eb; exact (proj1 Eb)).
      assert (v0 = v).
      { destruct (V.eq_dec v0 v) as [E | NE]; [exact E |].
        exfalso; apply (res_gran_unique Hres Hv0 HSv NE); congruence. }
      subst v0.
      destruct (Hslot _ _ _ _ Hpi Eb)
        as [d' [Hd' [Ha' [_ [_ [Htgt' _]]]]]].
      assert (d' = d) by exact (Hsite (m, v) d' d Hd' Hd Ha').
      subst d'.
      apply core_shape in Hcr; cbn beta iota in Hcr.
      destruct Hcr as [u'' [Eu'' [Htgt Eg]]]; injection Eu'' as <-.
      destruct (V.eq_dec u u') as [-> | NE]; [exact Hpi |].
      exfalso; apply (res_gran_unique Hres Htgt Htgt' NE); congruence.
    - intro Hpi.
      destruct (res_pi_dom Hres Hpi)
        as [fs [d [Hfs [Hd [<- [Hact Hreq]]]]]].
      assert (HS := res_fs_dom Hres Hfs).
      rewrite <- (fsAt_in FS (m, v) fs (res_fs_functional Hres) Hfs) in Hreq.
      assert (Eb : parentsb FDefs Slots rc S FS (m, v) (sKey d) = true).
      { apply parentsb_iff; split; [exact HS |].
        exists d; repeat split; assumption. }
      destruct (Hslot _ _ _ _ Hpi Eb)
        as [d' [Hd' [Ha' [_ [_ [Htgt _]]]]]].
      assert (d' = d) by exact (Hsite (m, v) d' d Hd' Hd Ha').
      subst d'.
      exists (g v), (g u), d; repeat split; try assumption;
        [| | rewrite (featsAt_coreResolution Hres _ HS); exact Hreq |];
        apply core_shape.
      + exists v, u; repeat split; assumption.
      + exists v; repeat split; exact HS.
      + exists u; repeat split; exact Htgt.
  Qed.
End Cargo.
