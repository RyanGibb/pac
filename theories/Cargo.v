From Stdlib Require Import MSets Bool.
From PackageCalculus Require Import Prelude Core Semver ConflictClass.

Create HintDb cmp_cargo.
Create Rewrite HintDb cmp_cargo.

Module Cargo (N V F G CfgS Src : UsualOrderedType) (PM : SemverMatch V).
  Module Source := Core N V.
  Module Pkg := Source.Pkg.
  Module PkgSet := Source.PkgSet.
  Module VSet := Source.VSet.

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
    | EDepFeat (a : N.t) (f' : F.t)
    | EWeakFeat (a : N.t) (f' : F.t).
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
  Module SDName := PairUOT N SDForm.
  Module SlotData := PairUOT N SDName.
  Module SlotElt := PairUOT Pkg SlotData.
  Module SlotRel := FSetUOT SlotElt.

  Definition sAlias (d : SlotData.t) : N.t := fst d.
  Definition sName (d : SlotData.t) : N.t := fst (snd d).
  Definition sRange (d : SlotData.t) : Range := fst (snd (snd d)).
  Definition sKind (d : SlotData.t) : Kind.t := fst (snd (snd (snd d))).
  Definition sOptional (d : SlotData.t) : bool :=
    fst (snd (snd (snd (snd d)))).
  Definition sDefault (d : SlotData.t) : bool :=
    fst (snd (snd (snd (snd (snd d))))).
  Definition sReqFeats (d : SlotData.t) : FSet.t :=
    fst (snd (snd (snd (snd (snd (snd d)))))).
  Definition sCfg (d : SlotData.t) : CfgS.t :=
    fst (snd (snd (snd (snd (snd (snd (snd d))))))).

  Module SiteTail := PairUOT KindOT CfgS.
  Module Site := PairUOT N SiteTail.
  Definition sSite (d : SlotData.t) : Site.t :=
    (sAlias d, (sKind d, sCfg d)).
  Definition siteAlias (k : Site.t) : N.t := fst k.

  Module LinkElt := PairUOT Pkg N.
  Module LinkRel := FSetUOT LinkElt.

  Module NAPair := PairUOT Pkg Site.
  Module ParentElt := PairUOT NAPair V.
  Module ParentRel := FSetUOT ParentElt.

  Definition slotActive (r p : Pkg.t) (d : SlotData.t) : bool :=
    match sKind d with
    | Kind.KDev => if Pkg.eq_dec p r then true else false
    | _ => true
    end.

  Definition Activated (FDefs : FDefRel.t) (fs : FSet.t) (p : Pkg.t)
      (a : N.t) : Prop :=
    exists f, FSet.In f fs /\
      (FDefRel.In ((p, f), FEntry.EDep a) FDefs \/
       (exists f', FDefRel.In ((p, f), FEntry.EDepFeat a f') FDefs) \/
       (exists f', FDefRel.In ((p, f), FEntry.EWeakFeat a f') FDefs)).

  Definition slotRequests (d : SlotData.t) (dflt : F.t) : FSet.t :=
    if sDefault d then FSet.add dflt (sReqFeats d) else sReqFeats d.

  Record Inst : Type := MkInst
    { inst_real : PkgSet.t
    ; inst_slots : SlotRel.t
    ; inst_fdefs : FDefRel.t
    ; inst_links : LinkRel.t
    ; inst_support : SupportSet.t
    ; inst_gran : V.t -> G.t
    ; inst_default : F.t
    ; inst_root : Pkg.t
    ; inst_rootFeats : FSet.t }.

  #[local] Set Implicit Arguments.
  Record IsResolution (I : Inst)
      (S : PkgSet.t) (FS : FeaturedSet.t) (pi : ParentRel.t) : Prop :=
    { res_subset : PkgSet.Subset S (inst_real I)
    ; res_root_mem : PkgSet.In (inst_root I) S
    ; res_class_unique :
        forall n v v', PkgSet.In (n, v) S -> PkgSet.In (n, v') S ->
        v <> v' -> inst_gran I v <> inst_gran I v'
    ; res_slot_closure :
        forall p fs, PkgSet.In p S -> FeaturedSet.In (p, fs) FS ->
        forall d, SlotRel.In (p, d) (inst_slots I) ->
        slotActive (inst_root I) p d = true ->
        (sOptional d = false \/ Activated (inst_fdefs I) fs p (sAlias d)) ->
        exists u, ParentRel.In ((p, sSite d), u) pi /\
          rgHolds (sRange d) u = true /\ PkgSet.In (sName d, u) S /\
          forall fs', FeaturedSet.In ((sName d, u), fs') FS ->
          FSet.Subset (slotRequests d (inst_default I)) fs'
    ; res_feat_closure :
        (forall p fs f f', FeaturedSet.In (p, fs) FS -> FSet.In f fs ->
         FDefRel.In ((p, f), FEntry.EFeat f') (inst_fdefs I) ->
         FSet.In f' fs) /\
        (forall p fs f a f', FeaturedSet.In (p, fs) FS -> FSet.In f fs ->
         (FDefRel.In ((p, f), FEntry.EDepFeat a f') (inst_fdefs I) \/
          FDefRel.In ((p, f), FEntry.EWeakFeat a f') (inst_fdefs I)) ->
         forall d u, SlotRel.In (p, d) (inst_slots I) -> sAlias d = a ->
         ParentRel.In ((p, sSite d), u) pi ->
         forall fs', FeaturedSet.In ((sName d, u), fs') FS ->
         FSet.In f' fs')
    ; res_links_unique :
        forall p q l, PkgSet.In p S -> PkgSet.In q S ->
        LinkRel.In (p, l) (inst_links I) -> LinkRel.In (q, l) (inst_links I) ->
        p = q
    ; res_fs_dom : forall p fs, FeaturedSet.In (p, fs) FS -> PkgSet.In p S
    ; res_fs_total : forall p, PkgSet.In p S ->
        exists fs, FeaturedSet.In (p, fs) FS
    ; res_fs_functional :
        forall p fs fs', FeaturedSet.In (p, fs) FS ->
        FeaturedSet.In (p, fs') FS -> fs = fs'
    ; res_root_feats :
        forall fs, FeaturedSet.In (inst_root I, fs) FS ->
        FSet.Subset (inst_rootFeats I) fs
    ; res_support_mem :
        forall p fs f, FeaturedSet.In (p, fs) FS -> FSet.In f fs ->
        SupportSet.In (p, f) (inst_support I)
    ; res_pi_functional :
        forall p k u u', ParentRel.In ((p, k), u) pi ->
        ParentRel.In ((p, k), u') pi -> u = u'
    ; res_parent_subset :
        forall p k u, ParentRel.In ((p, k), u) pi -> PkgSet.In p S }.
  #[local] Unset Implicit Arguments.

  Definition ParentDependency (I : Inst) (FS : FeaturedSet.t)
      (pi : ParentRel.t) : Prop :=
    forall p k u, ParentRel.In ((p, k), u) pi ->
      exists fs d, FeaturedSet.In (p, fs) FS /\
        SlotRel.In (p, d) (inst_slots I) /\
        sSite d = k /\ slotActive (inst_root I) p d = true /\
        (sOptional d = false \/ Activated (inst_fdefs I) fs p (sAlias d)).

  Module Reduction.
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
    Module SiteEqb := UOTEqb Site.

    Definition evalReqBy (Vq : N.t -> VSet.t) (m : N.t) (rg : Range) : VSet.t :=
      VSet.filter (rgHolds rg) (Vq m).

    Lemma mem_evalReqBy : forall Vq m rg u,
        VSet.In u (evalReqBy Vq m rg) <->
        VSet.In u (Vq m) /\ rgHolds rg u = true.
    Proof. intros; unfold evalReqBy; apply VSet.filter_spec'. Qed.

    Definition evalReq (R : PkgSet.t) (m : N.t) (rg : Range) : VSet.t :=
      evalReqBy (Source.versions R) m rg.

    Lemma mem_evalReq : forall R m rg u,
        VSet.In u (evalReq R m rg) <->
        PkgSet.In (m, u) R /\ rgHolds rg u = true.
    Proof.
      intros; unfold evalReq; rewrite mem_evalReqBy, Source.mem_versions;
        reflexivity.
    Qed.

    Definition slotsAt (Slots : SlotRel.t)
        (r : Pkg.t) (p : Pkg.t) (a : N.t) : SlotRel.t :=
      SlotRel.filter (fun '(q, d) =>
          andb (if Pkg.eq_dec q p then true else false)
            (andb (NEqb.eqb (sAlias d) a) (slotActive r q d)))
        Slots.

    Lemma mem_slotsAt : forall Slots r p a q d,
        SlotRel.In (q, d) (slotsAt Slots r p a) <->
        SlotRel.In (q, d) Slots /\ q = p /\ sAlias d = a /\
        slotActive r q d = true.
    Proof.
      intros Slots r p a q d; unfold slotsAt.
      rewrite SlotRel.filter_spec'; cbn beta iota.
      rewrite !andb_true_iff, NEqb.eqb_true_iff.
      destruct (Pkg.eq_dec q p); intuition congruence.
    Qed.

    Definition slotsAtKey (Slots : SlotRel.t)
        (r : Pkg.t) (p : Pkg.t) (k : Site.t) : SlotRel.t :=
      SlotRel.filter (fun '(q, d) =>
          andb (if Pkg.eq_dec q p then true else false)
            (andb (SiteEqb.eqb (sSite d) k) (slotActive r q d)))
        Slots.

    Lemma mem_slotsAtKey : forall Slots r p k q d,
        SlotRel.In (q, d) (slotsAtKey Slots r p k) <->
        SlotRel.In (q, d) Slots /\ q = p /\ sSite d = k /\
        slotActive r q d = true.
    Proof.
      intros Slots r p k q d; unfold slotsAtKey.
      rewrite SlotRel.filter_spec'; cbn beta iota.
      rewrite !andb_true_iff, SiteEqb.eqb_true_iff.
      destruct (Pkg.eq_dec q p); intuition congruence.
    Qed.

    Definition entryFeatD (e : FEntry.t) : option (N.t * F.t) :=
      match e with
      | FEntry.EDepFeat a f' => Some (a, f')
      | FEntry.EWeakFeat a f' => Some (a, f')
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
      sSite d = sSite d' -> d = d'.

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
        destruct He as [He | [[f' He] | [f' He]]];
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
        (r : Pkg.t)
        (S : PkgSet.t) (FS : FeaturedSet.t) (q : Pkg.t) (k : Site.t)
      : bool :=
      andb (PkgSet.mem q S)
        (SlotRel.exists_ (fun '(q', d) =>
             andb (PkgEqb.eqb q' q)
               (andb (SiteEqb.eqb (sSite d) k)
                  (andb (slotActive r q' d)
                     (requiredb FDefs (fsAt FS q) q d))))
           Slots).

    Lemma parentsb_iff : forall FDefs Slots r S FS q k,
        parentsb FDefs Slots r S FS q k = true <->
        PkgSet.In q S /\
        exists d, SlotRel.In (q, d) Slots /\ sSite d = k /\
          slotActive r q d = true /\
          (sOptional d = false \/
           Activated FDefs (fsAt FS q) q (sAlias d)).
    Proof.
      intros FDefs Slots r S FS q k; unfold parentsb.
      rewrite andb_true_iff, PkgSet.mem_spec, SlotRel.exists_spec'.
      split.
      - intros [HS [[q' d] [Hd Hb]]]; cbn beta iota in Hb.
        rewrite !andb_true_iff, PkgEqb.eqb_true_iff, SiteEqb.eqb_true_iff,
          requiredb_iff in Hb.
        destruct Hb as [-> Hb]; split; [exact HS |]; exists d; tauto.
      - intros [HS [d [Hd [<- [Hact Hreq]]]]]; split; [exact HS |].
        exists (q, d); split; [exact Hd | cbn beta iota].
        apply requiredb_iff in Hreq.
        rewrite PkgEqb.eqb_refl, SiteEqb.eqb_refl, Hact, Hreq; reflexivity.
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
      | CGran (n : N.t) (w : G.t)
      | CFeatP (n : N.t) (f : F.t) (w : G.t)
      | CSlot (n : N.t) (w : G.t) (d : SlotData.t)
      | CDec (n : N.t) (w : G.t) (f : F.t) (d : SlotData.t) (f' : F.t)
      | CCls (l : N.t).
      Definition t := name.

      Definition rank (x : t) : nat :=
        match x with
        | CRoot => 0 | CGran _ _ => 1 | CFeatP _ _ _ => 2
        | CSlot _ _ _ => 3 | CDec _ _ _ _ _ => 4 | CCls _ => 5
        end.

      Definition compare (x y : t) : comparison :=
        match Nat.compare (rank x) (rank y) with
        | Eq =>
            match x, y with
            | CGran n1 g1, CGran n2 g2 => NGPair.compare (n1, g1) (n2, g2)
            | CFeatP n1 f1 g1, CFeatP n2 f2 g2 =>
                NFGTrip.compare (n1, (f1, g1)) (n2, (f2, g2))
            | CSlot n1 v1 a1, CSlot n2 v2 a2 =>
                SlotName.compare (n1, (v1, a1)) (n2, (v2, a2))
            | CDec n1 v1 f1 a1 t1, CDec n2 v2 f2 a2 t2 =>
                DecName.compare (n1, (v1, (f1, (a1, t1))))
                  (n2, (v2, (f2, (a2, t2))))
            | CCls l1, CCls l2 => N.compare l1 l2
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
      | WClass (w : G.t)
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
    Module Reduced := ClsT.Source.

    Module SOvp := SetOps V Reduced.Pkg VSet Reduced.PkgSet.
    Module SOpp := SetOps Pkg Reduced.Pkg PkgSet Reduced.PkgSet.
    Module SOsp := SetOps PkgF Reduced.Pkg SupportSet Reduced.PkgSet.
    Module SOslp := SetOps SlotElt Reduced.Pkg SlotRel Reduced.PkgSet.
    Module SOfp := SetOps FDefElt Reduced.Pkg FDefRel Reduced.PkgSet.
    Module SOlp := SetOps LinkElt Reduced.Pkg LinkRel Reduced.PkgSet.
    Module SOvv := SetOps V VPOT VSet Reduced.VSet.

    Definition gransOf (g : V.t -> G.t) (vs : VSet.t) : Reduced.VSet.t :=
      SOvv.map (fun u => VPlus.WClass (g u)) vs.

    Definition inGran (g : V.t -> G.t) (w : G.t) (vs : VSet.t) : Reduced.VSet.t :=
      SOvv.filterMap
        (fun u => if GEqb.eqb (g u) w then Some (VPlus.WOrig u) else None) vs.

    Definition SlotOwned (g : V.t -> G.t) (Slots : SlotRel.t) (r : Pkg.t)
        (n : N.t) (w : G.t) (d : SlotData.t) : Prop :=
      exists v, g v = w /\ SlotRel.In ((n, v), d) Slots /\
        slotActive r (n, v) d = true.

    Definition DecOwned (g : V.t -> G.t) (FDefs : FDefRel.t) (Slots : SlotRel.t)
        (r : Pkg.t) (n : N.t) (w : G.t) (f : F.t) (d : SlotData.t)
        (f' : F.t) : Prop :=
      exists v e, g v = w /\ FDefRel.In (((n, v), f), e) FDefs /\
        entryFeatD e = Some (sAlias d, f') /\
        SlotRel.In ((n, v), d) Slots /\ slotActive r (n, v) d = true.

    Definition rootPkg : Reduced.Pkg.t := (NPlus.CRoot, VPlus.WUnit).

    Definition granReal (g : V.t -> G.t) (R : PkgSet.t) : Reduced.PkgSet.t :=
      SOpp.map (fun '(n, v) => (NPlus.CGran n (g v), VPlus.WOrig v)) R.

    Definition featReal (g : V.t -> G.t) (support : SupportSet.t)
      : Reduced.PkgSet.t :=
      SOsp.map (fun '((n, v), f) =>
          (NPlus.CFeatP n f (g v), VPlus.WOrig v)) support.

    Definition slotReal (g : V.t -> G.t) (R : PkgSet.t) (Slots : SlotRel.t)
        (r : Pkg.t) : Reduced.PkgSet.t :=
      SOslp.unionMap (fun '((n, v), d) =>
          if slotActive r (n, v) d
          then SOvp.map (fun u => (NPlus.CSlot n (g v) d, VPlus.WClass (g u)))
                 (evalReq R (sName d) (sRange d))
          else Reduced.PkgSet.empty)
        Slots.

    Definition decReal (g : V.t -> G.t) (R : PkgSet.t) (FDefs : FDefRel.t)
        (Slots : SlotRel.t) (r : Pkg.t)
      : Reduced.PkgSet.t :=
      SOfp.unionMap (fun '(((n, v), f), e) =>
          match entryFeatD e with
          | Some (a, f') =>
              SOslp.unionMap (fun '(_, d) =>
                  SOvp.map (fun u =>
                      (NPlus.CDec n (g v) f d f', VPlus.WClass (g u)))
                    (evalReq R (sName d) (sRange d)))
                (slotsAt Slots r (n, v) a)
          | None => Reduced.PkgSet.empty
          end)
        FDefs.

    Definition clsReal (g : V.t -> G.t) (R : PkgSet.t) (Links : LinkRel.t)
      : Reduced.PkgSet.t :=
      SOlp.filterMap (fun '((n, v), l) =>
          if PkgSet.mem (n, v) R
          then Some (NPlus.CCls l, VPlus.WName (NPlus.CGran n (g v)))
          else None)
        Links.

    Definition reduceReal (I : Inst) : Reduced.PkgSet.t :=
      Reduced.PkgSet.union (Reduced.PkgSet.singleton rootPkg)
        (Reduced.PkgSet.union (granReal (inst_gran I) (inst_real I))
           (Reduced.PkgSet.union (featReal (inst_gran I) (inst_support I))
              (Reduced.PkgSet.union
                 (slotReal (inst_gran I) (inst_real I) (inst_slots I)
                    (inst_root I))
                 (Reduced.PkgSet.union
                    (decReal (inst_gran I) (inst_real I) (inst_fdefs I)
                       (inst_slots I) (inst_root I))
                    (clsReal (inst_gran I) (inst_real I) (inst_links I)))))).

    Module SOlc := SetOps LinkElt ClsT.InClassElt LinkRel ClsT.InClassRel.
    Definition linkRel (g : V.t -> G.t) (Links : LinkRel.t)
      : ClsT.InClassRel.t :=
      SOlc.map (fun '((n, v), l) =>
          ((NPlus.CGran n (g v), VPlus.WOrig v), NPlus.CCls l))
        Links.

    Module SOlv := SetOps LinkElt VPOT LinkRel Reduced.VSet.
    Module SOpv2 := SetOps Pkg VPOT PkgSet Reduced.VSet.
    Module SOspv := SetOps PkgF VPOT SupportSet Reduced.VSet.
    Module SOsh := SetOps SlotElt Reduced.Dependees SlotRel Reduced.DependeesSet.
    Module SOfh := SetOps FDefElt Reduced.Dependees FDefRel Reduced.DependeesSet.
    Module SOlh := SetOps LinkElt Reduced.Dependees LinkRel Reduced.DependeesSet.
    Module SOfsh := SetOps F Reduced.Dependees FSet Reduced.DependeesSet.

    Definition versions (I : Inst) (m : NPlus.t) : Reduced.VSet.t :=
      match m with
      | NPlus.CRoot => Reduced.VSet.singleton VPlus.WUnit
      | NPlus.CGran n w =>
          SOpv2.filterMap (fun '(n', v) =>
              if andb (NEqb.eqb n' n) (GEqb.eqb (inst_gran I v) w)
              then Some (VPlus.WOrig v) else None)
            (inst_real I)
      | NPlus.CFeatP n f w =>
          SOspv.filterMap (fun '((n', v), f0) =>
              if andb (andb (NEqb.eqb n' n) (FEqb.eqb f0 f))
                   (GEqb.eqb (inst_gran I v) w)
              then Some (VPlus.WOrig v) else None)
            (inst_support I)
      | NPlus.CSlot _ _ d | NPlus.CDec _ _ _ d _ =>
          gransOf (inst_gran I) (evalReq (inst_real I) (sName d) (sRange d))
      | NPlus.CCls l =>
          SOlv.filterMap (fun '((n, v), l') =>
              if andb (NEqb.eqb l' l) (PkgSet.mem (n, v) (inst_real I))
              then Some (VPlus.WName (NPlus.CGran n (inst_gran I v))) else
                None)
            (inst_links I)
      end.

    Definition dependeesBy (Vq : N.t -> VSet.t) (I : Inst) (p : Reduced.Pkg.t)
      : Reduced.DependeesSet.t :=
      match p with
      | (NPlus.CRoot, VPlus.WUnit) =>
          let '(n, v) := inst_root I in
          Reduced.DependeesSet.add
            (NPlus.CGran n (inst_gran I v), Reduced.VSet.singleton (VPlus.WOrig v))
            (SOfsh.map (fun f =>
                 (NPlus.CFeatP n f (inst_gran I v),
                  Reduced.VSet.singleton (VPlus.WOrig v)))
               (inst_rootFeats I))
      | (NPlus.CGran n w, VPlus.WOrig v) =>
          Reduced.DependeesSet.union
            (SOsh.filterMap (fun '(q, d) =>
                 if andb (PkgEqb.eqb q (n, v))
                      (andb (slotActive (inst_root I) (n, v) d)
                         (negb (sOptional d)))
                 then Some (NPlus.CSlot n (inst_gran I v) d,
                            gransOf (inst_gran I)
                              (evalReqBy Vq (sName d) (sRange d)))
                 else None)
               (inst_slots I))
            (SOlh.filterMap (fun '(q, l) =>
                 if PkgEqb.eqb q (n, v)
                 then Some (NPlus.CCls l,
                            Reduced.VSet.singleton (VPlus.WName (NPlus.CGran n w)))
                 else None)
               (inst_links I))
      | (NPlus.CFeatP n f _, VPlus.WOrig v) =>
          Reduced.DependeesSet.add
            (NPlus.CGran n (inst_gran I v), Reduced.VSet.singleton (VPlus.WOrig v))
            (SOfh.unionMap (fun '(((n', v'), f0), e) =>
                 if negb (andb (PkgEqb.eqb (n', v') (n, v)) (FEqb.eqb f0 f))
                 then Reduced.DependeesSet.empty
                 else
                   Reduced.DependeesSet.union
                     (match e with
                      | FEntry.EFeat f2 =>
                          Reduced.DependeesSet.singleton
                            (NPlus.CFeatP n f2 (inst_gran I v),
                             Reduced.VSet.singleton (VPlus.WOrig v))
                      | _ => Reduced.DependeesSet.empty
                      end)
                     (Reduced.DependeesSet.union
                        (match entryActivates e with
                         | Some a =>
                             SOsh.map (fun '(_, d) =>
                                 (NPlus.CSlot n (inst_gran I v) d,
                                  gransOf (inst_gran I)
                                    (evalReqBy Vq (sName d) (sRange d))))
                               (slotsAt (inst_slots I) (inst_root I) (n, v) a)
                         | None => Reduced.DependeesSet.empty
                         end)
                        (match entryFeatD e with
                         | Some (a, f') =>
                             SOsh.map (fun '(_, d) =>
                                 (NPlus.CDec n (inst_gran I v) f d f',
                                  gransOf (inst_gran I)
                                    (evalReqBy Vq (sName d) (sRange d))))
                               (slotsAt (inst_slots I) (inst_root I) (n, v) a)
                         | None => Reduced.DependeesSet.empty
                         end)))
               (inst_fdefs I))
      | (NPlus.CSlot _ _ d, VPlus.WClass w) =>
          Reduced.DependeesSet.add
            (NPlus.CGran (sName d) w,
             inGran (inst_gran I) w (evalReqBy Vq (sName d) (sRange d)))
            (SOfsh.map (fun f =>
                 (NPlus.CFeatP (sName d) f w,
                  inGran (inst_gran I) w
                    (evalReqBy Vq (sName d) (sRange d))))
               (slotRequests d (inst_default I)))
      | (NPlus.CDec n w0 _ d f', VPlus.WClass w) =>
          Reduced.DependeesSet.add
            (NPlus.CSlot n w0 d, Reduced.VSet.singleton (VPlus.WClass w))
            (Reduced.DependeesSet.singleton
               (NPlus.CFeatP (sName d) f' w,
                inGran (inst_gran I) w
                  (evalReqBy Vq (sName d) (sRange d))))
      | _ => Reduced.DependeesSet.empty
      end.

    Definition dependees (I : Inst) (p : Reduced.Pkg.t) : Reduced.DependeesSet.t :=
      dependeesBy (Source.versions (inst_real I)) I p.

    Module SOhe := SetOps Reduced.Dependees Reduced.DepElt Reduced.DependeesSet Reduced.DepRel.
    Definition depEdges (p : Reduced.Pkg.t) (hs : Reduced.DependeesSet.t) : Reduced.DepRel.t :=
      SOhe.map (fun h => (p, h)) hs.

    Module SOpe := SetOps Reduced.Pkg Reduced.DepElt Reduced.PkgSet Reduced.DepRel.
    Definition reduceDeps (I : Inst) : Reduced.DepRel.t :=
      SOpe.unionMap (fun p =>
          depEdges p
            (dependees I p))
        (reduceReal I).

    Lemma mem_gransOf : forall g vs v,
        Reduced.VSet.In v (gransOf g vs) <->
        exists u, VSet.In u vs /\ v = VPlus.WClass (g u).
    Proof.
      intros g vs v; unfold gransOf; rewrite SOvv.mem_map; reflexivity.
    Qed.

    Lemma mem_inGran : forall g w vs v,
        Reduced.VSet.In v (inGran g w vs) <->
        exists u, VSet.In u vs /\ g u = w /\ v = VPlus.WOrig u.
    Proof.
      intros g w vs v; unfold inGran; rewrite SOvv.mem_filterMap_if.
      cbn beta; setoid_rewrite GEqb.eqb_true_iff; reflexivity.
    Qed.

    Lemma mem_granReal : forall g R p,
        Reduced.PkgSet.In p (granReal g R) <->
        exists n v, PkgSet.In (n, v) R /\
          p = (NPlus.CGran n (g v), VPlus.WOrig v).
    Proof.
      intros g R p; unfold granReal; rewrite SOpp.mem_map; split.
      - intros [[n v] [HR He]]; cbn beta iota in He.
        exists n, v; split; assumption.
      - intros [n [v [HR ->]]]; exists (n, v); split;
          [exact HR | reflexivity].
    Qed.

    Lemma mem_featReal : forall g support p,
        Reduced.PkgSet.In p (featReal g support) <->
        exists n v f, SupportSet.In ((n, v), f) support /\
          p = (NPlus.CFeatP n f (g v), VPlus.WOrig v).
    Proof.
      intros g support p; unfold featReal; rewrite SOsp.mem_map; split.
      - intros [[[n v] f] [HR He]]; cbn beta iota in He.
        exists n, v, f; split; assumption.
      - intros [n [v [f [HR ->]]]]; exists ((n, v), f); split;
          [exact HR | reflexivity].
    Qed.

    Lemma mem_slotReal : forall g R Slots r p,
        Reduced.PkgSet.In p (slotReal g R Slots r) <->
        exists n v d u, SlotRel.In ((n, v), d) Slots /\
          slotActive r (n, v) d = true /\
          VSet.In u (evalReq R (sName d) (sRange d)) /\
          p = (NPlus.CSlot n (g v) d, VPlus.WClass (g u)).
    Proof.
      intros g R Slots r p; unfold slotReal.
      rewrite SOslp.mem_unionMap; split.
      - intros [[[n v] d] [Hs Hx]]; cbn beta iota in Hx.
        apply SOslp.in_if_empty in Hx as [Ha Hx].
        apply SOvp.mem_map in Hx; destruct Hx as [u [Hu ->]].
        exists n, v, d, u; repeat split; assumption.
      - intros [n [v [d [u [Hs [Ha [Hu ->]]]]]]].
        exists ((n, v), d); split; [exact Hs | cbn beta iota].
        rewrite Ha; apply SOvp.mem_map; exists u; split;
          [exact Hu | reflexivity].
    Qed.

    Lemma mem_decReal : forall g R FDefs Slots r p,
        Reduced.PkgSet.In p (decReal g R FDefs Slots r) <->
        exists n v f e a f' d u,
          FDefRel.In (((n, v), f), e) FDefs /\
          entryFeatD e = Some (a, f') /\
          SlotRel.In ((n, v), d) Slots /\ sAlias d = a /\
          slotActive r (n, v) d = true /\
          VSet.In u (evalReq R (sName d) (sRange d)) /\
          p = (NPlus.CDec n (g v) f d f', VPlus.WClass (g u)).
    Proof.
      intros g R FDefs Slots r p; unfold decReal.
      rewrite SOfp.mem_unionMap; split.
      - intros [[[[n v] f] e] [Hf Hx]]; cbn beta iota in Hx.
        destruct (entryFeatD e) as [[a f'] |] eqn:Ee;
          [| exfalso; exact (SOslp.empty_in _ Hx)].
        apply SOslp.mem_unionMap in Hx; destruct Hx as [[q d] [Hq Hx]];
          cbn beta iota in Hx.
        apply mem_slotsAt in Hq; destruct Hq as [Hs [-> [Ha Hact]]].
        apply SOvp.mem_map in Hx; destruct Hx as [u [Hu ->]].
        exists n, v, f, e, a, f', d, u; repeat split; assumption.
      - intros [n [v [f [e [a [f' [d [u
          [Hf [Ee [Hs [Ha [Hact [Hu ->]]]]]]]]]]]]]].
        exists (((n, v), f), e); split; [exact Hf | cbn beta iota].
        rewrite Ee; apply SOslp.mem_unionMap; exists ((n, v), d); split.
        { apply mem_slotsAt; repeat split; assumption. }
        cbn beta iota; apply SOvp.mem_map; exists u; split;
          [exact Hu | reflexivity].
    Qed.

    Lemma mem_clsReal : forall g R Links p,
        Reduced.PkgSet.In p (clsReal g R Links) <->
        exists n v l, LinkRel.In ((n, v), l) Links /\ PkgSet.In (n, v) R /\
          p = (NPlus.CCls l, VPlus.WName (NPlus.CGran n (g v))).
    Proof.
      intros g R Links p; unfold clsReal; rewrite SOlp.mem_filterMap; split.
      - intros [[[n v] l] [Hl He]]; cbn beta iota in He.
        rewrite if_some_iff, PkgSet.mem_spec in He; destruct He as [HR <-].
        exists n, v, l; auto.
      - intros [n [v [l [Hl [HR ->]]]]]; exists ((n, v), l); split;
          [exact Hl | cbn beta iota].
        rewrite (proj2 (PkgSet.mem_spec _ _) HR); reflexivity.
    Qed.

    Lemma mem_linkRel : forall g Links q k,
        ClsT.InClassRel.In (q, k) (linkRel g Links) <->
        exists n v l, LinkRel.In ((n, v), l) Links /\
          q = (NPlus.CGran n (g v), VPlus.WOrig v) /\ k = NPlus.CCls l.
    Proof.
      intros g Links q k; unfold linkRel; rewrite SOlc.mem_map; split.
      - intros [[[n v] l] [Hl He]]; cbn beta iota in He.
        injection He as -> ->; exists n, v, l; repeat split; exact Hl.
      - intros [n [v [l [Hl [-> ->]]]]]; exists ((n, v), l); split;
          [exact Hl | reflexivity].
    Qed.

    Lemma mem_reduceReal :
      forall I p,
        Reduced.PkgSet.In p
          (reduceReal I) <->
        p = rootPkg \/ Reduced.PkgSet.In p (granReal (inst_gran I) (inst_real I)) \/
        Reduced.PkgSet.In p (featReal (inst_gran I) (inst_support I)) \/
        Reduced.PkgSet.In p
          (slotReal (inst_gran I) (inst_real I) (inst_slots I) (inst_root I)) \/
        Reduced.PkgSet.In p
          (decReal (inst_gran I) (inst_real I) (inst_fdefs I) (inst_slots I)
             (inst_root I)) \/
        Reduced.PkgSet.In p (clsReal (inst_gran I) (inst_real I) (inst_links I)).
    Proof.
      intros; unfold reduceReal; rewrite !Reduced.PkgSet.union_spec.
      rewrite Reduced.PkgSet.singleton_spec; reflexivity.
    Qed.

    Lemma real_shape :
      forall I m v',
        Reduced.PkgSet.In (m, v') (reduceReal I) <->
        match m with
        | NPlus.CRoot => v' = VPlus.WUnit
        | NPlus.CGran n w =>
            exists v, v' = VPlus.WOrig v /\ PkgSet.In (n, v) (inst_real I) /\
              w = inst_gran I v
        | NPlus.CFeatP n f w =>
            exists v, v' = VPlus.WOrig v /\
              SupportSet.In ((n, v), f) (inst_support I) /\ w = inst_gran I v
        | NPlus.CSlot n w d =>
            SlotOwned (inst_gran I) (inst_slots I) (inst_root I) n w d /\
            exists u, VSet.In u (evalReq (inst_real I) (sName d) (sRange d)) /\
              v' = VPlus.WClass (inst_gran I u)
        | NPlus.CDec n w f d f' =>
            DecOwned (inst_gran I) (inst_fdefs I) (inst_slots I) (inst_root I)
              n w f d f' /\
            exists u, VSet.In u (evalReq (inst_real I) (sName d) (sRange d)) /\
              v' = VPlus.WClass (inst_gran I u)
        | NPlus.CCls l =>
            exists n v, v' = VPlus.WName (NPlus.CGran n (inst_gran I v)) /\
              LinkRel.In ((n, v), l) (inst_links I) /\
              PkgSet.In (n, v) (inst_real I)
        end.
    Proof.
      intros I m v'.
      rewrite mem_reduceReal, mem_granReal, mem_featReal, mem_slotReal,
        mem_decReal, mem_clsReal; unfold rootPkg, SlotOwned, DecOwned.
      split.
      - intros [He | [He | [He | [He | [He | He]]]]]; mem_destruct; eauto 20.
      - destruct m as [| n w | n f w | n w d | n w f d f' | l];
          cbn beta iota.
        + intros ->; left; reflexivity.
        + intros [v [-> [HR ->]]]; right; left; exists n, v; auto.
        + intros [v [-> [Hs ->]]]; right; right; left; exists n, v, f; auto.
        + intros [[v [<- [Hs Hact]]] [u [Hu ->]]].
          right; right; right; left; exists n, v, d, u; auto.
        + intros [[v [e [<- [Hf [Ee [Hs Hact]]]]]] [u [Hu ->]]].
          right; right; right; right; left.
          exists n, v, f, e, (sAlias d), f', d, u; repeat split; assumption.
        + intros [n [v [-> [Hl HR]]]]; right; right; right; right; right.
          exists n, v, l; auto.
    Qed.

    Lemma mem_versions_cls : forall I l u,
        Reduced.VSet.In u (versions I (NPlus.CCls l))
        <-> exists n v, u = VPlus.WName (NPlus.CGran n (inst_gran I v)) /\
          LinkRel.In ((n, v), l) (inst_links I) /\
            PkgSet.In (n, v) (inst_real I).
    Proof.
      intros; cbn [versions]; rewrite SOlv.mem_filterMap; split.
      - intros [[[n v] l'] [Hl He]]; cbn beta iota in He.
        rewrite if_some_iff, andb_true_iff, NEqb.eqb_true_iff, PkgSet.mem_spec
          in He.
        destruct He as [[-> HR] <-]; exists n, v; auto.
      - intros [n [v [-> [Hl HR]]]]; exists ((n, v), l); split;
          [exact Hl | cbn beta iota].
        rewrite NEqb.eqb_refl, (proj2 (PkgSet.mem_spec _ _) HR); reflexivity.
    Qed.

    Lemma versions_cls_reduceReal :
      forall I l v,
        Reduced.VSet.In v
          (versions I (NPlus.CCls l)) <->
        exists n, v = VPlus.WName n /\
          ClsT.Reduction.Reduced.VSet.In (ClsT.Reduction.Version.Name n)
            (ClsT.Reduction.Reduced.versions
               (ClsT.Reduction.reduceReal
                  (granReal (inst_gran I) (inst_real I))
                  (linkRel (inst_gran I) (inst_links I)))
               (ClsT.Reduction.Name.Cls (NPlus.CCls l))).
    Proof.
      intros I l u.
      rewrite mem_versions_cls, ClsT.Reduction.Lookup.versions_cls.
      split.
      - intros [n [v [-> [Hl Em]]]].
        exists (NPlus.CGran n (inst_gran I v)); split; [reflexivity |].
        apply ClsT.Reduction.Lookup.SOpv.mem_map.
        exists (NPlus.CGran n (inst_gran I v), VPlus.WOrig v);
          split; [| reflexivity].
        apply ClsT.Reduction.Lookup.mem_inClass; split.
        + apply mem_granReal; exists n, v; split; [exact Em | reflexivity].
        + apply mem_linkRel; exists n, v, l; repeat split; exact Hl.
      - intros [m [-> Hn]]; apply ClsT.Reduction.Lookup.SOpv.mem_map in Hn.
        destruct Hn as [q [Hq E]]; injection E as ->.
        apply ClsT.Reduction.Lookup.mem_inClass in Hq; destruct Hq as [Hq Hc].
        apply mem_linkRel in Hc; destruct Hc as [n [v [l' [Hl [-> Ek]]]]].
        injection Ek as <-.
        apply mem_granReal in Hq; destruct Hq as [n' [v' [HR E]]].
        injection E as E1 _ E3; subst n' v'.
        exists n, v; auto.
    Qed.

    Lemma mem_reduceDeps :
      forall I (p : Reduced.Pkg.t) (h : Reduced.Dependees.t),
        Reduced.DepRel.In (p, h)
          (reduceDeps I) <->
        Reduced.PkgSet.In p
          (reduceReal I) /\
        Reduced.DependeesSet.In h
          (dependees I p).
    Proof.
      intros I p
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

    Definition Inert (p : Reduced.Pkg.t) : Prop :=
      match p with
      | (NPlus.CRoot, VPlus.WUnit) => False
      | (NPlus.CGran _ _, VPlus.WOrig _) => False
      | (NPlus.CFeatP _ _ _, VPlus.WOrig _) => False
      | (NPlus.CSlot _ _ _, VPlus.WClass _) => False
      | (NPlus.CDec _ _ _ _ _, VPlus.WClass _) => False
      | _ => True
      end.

    Lemma dep_inert :
      forall I p,
        Inert p ->
        dependees I p = Reduced.DependeesSet.empty.
    Proof.
      intros I [n w] Hi; destruct n; destruct w; try (exfalso; exact Hi);
        reflexivity.
    Qed.

    Lemma mem_dep_root :
      forall g R support FDefs Slots Links dflt rn rv rootFeats h,
        Reduced.DependeesSet.In h
          (dependees (MkInst R Slots FDefs Links support g dflt (rn, rv)
                        rootFeats) rootPkg) <->
        h = (NPlus.CGran rn (g rv), Reduced.VSet.singleton (VPlus.WOrig rv)) \/
        exists f, FSet.In f rootFeats /\
          h = (NPlus.CFeatP rn f (g rv), Reduced.VSet.singleton (VPlus.WOrig rv)).
    Proof.
      intros; cbn [dependees dependeesBy rootPkg inst_gran inst_root
                   inst_rootFeats].
      rewrite Reduced.DependeesSet.add_spec, SOfsh.mem_map.
      split; (intros [Hx | [f [Hf Hx]]];
              [left; exact Hx
               | right; exists f; split; [exact Hf | exact Hx]]).
    Qed.

    Lemma mem_depBy_gran :
      forall Vq I n w v h,
        Reduced.DependeesSet.In h
          (dependeesBy Vq I (NPlus.CGran n w, VPlus.WOrig v)) <->
        ((exists d, SlotRel.In ((n, v), d) (inst_slots I) /\
            slotActive (inst_root I) (n, v) d = true /\
            sOptional d = false /\
            h = (NPlus.CSlot n (inst_gran I v) d,
                 gransOf (inst_gran I) (evalReqBy Vq (sName d) (sRange d)))) \/
         (exists l, LinkRel.In ((n, v), l) (inst_links I) /\
            h = (NPlus.CCls l,
                 Reduced.VSet.singleton (VPlus.WName (NPlus.CGran n w))))).
    Proof.
      intros; cbn [dependeesBy].
      rewrite Reduced.DependeesSet.union_spec, SOsh.mem_filterMap,
        SOlh.mem_filterMap.
      split.
      - intros [[[q d] [Hs He]] | [[q l] [Hl He]]]; cbn beta iota in He;
          rewrite if_some_iff in He.
        + rewrite !andb_true_iff, PkgEqb.eqb_true_iff, negb_true_iff in He.
          destruct He as [[-> [Ha Ho]] <-]; left; exists d; auto.
        + rewrite PkgEqb.eqb_true_iff in He; destruct He as [-> <-].
          right; exists l; auto.
      - intros [[d [Hs [Ha [Ho ->]]]] | [l [Hl ->]]].
        + left; exists ((n, v), d); split; [exact Hs | cbn beta iota].
          rewrite PkgEqb.eqb_refl, Ha, Ho; reflexivity.
        + right; exists ((n, v), l); split; [exact Hl | cbn beta iota].
          rewrite PkgEqb.eqb_refl; reflexivity.
    Qed.

    Lemma mem_dep_gran :
      forall I n w v h,
        Reduced.DependeesSet.In h
          (dependees I (NPlus.CGran n w, VPlus.WOrig v)) <->
        ((exists d, SlotRel.In ((n, v), d) (inst_slots I) /\
            slotActive (inst_root I) (n, v) d = true /\
            sOptional d = false /\
            h = (NPlus.CSlot n (inst_gran I v) d,
                 gransOf (inst_gran I)
                   (evalReq (inst_real I) (sName d) (sRange d)))) \/
         (exists l, LinkRel.In ((n, v), l) (inst_links I) /\
            h = (NPlus.CCls l,
                 Reduced.VSet.singleton (VPlus.WName (NPlus.CGran n w))))).
    Proof.
      intros; unfold dependees; apply mem_depBy_gran.
    Qed.

    Lemma mem_depBy_featP :
      forall Vq I n f w v h,
        Reduced.DependeesSet.In h
          (dependeesBy Vq I (NPlus.CFeatP n f w, VPlus.WOrig v)) <->
        (h =
           (NPlus.CGran n (inst_gran I v), Reduced.VSet.singleton (VPlus.WOrig v)) \/
         exists e, FDefRel.In (((n, v), f), e) (inst_fdefs I) /\
           ((exists f', e = FEntry.EFeat f' /\
               h = (NPlus.CFeatP n f' (inst_gran I v),
                    Reduced.VSet.singleton (VPlus.WOrig v))) \/
            (exists a d, entryActivates e = Some a /\
               SlotRel.In ((n, v), d) (inst_slots I) /\ sAlias d = a /\
               slotActive (inst_root I) (n, v) d = true /\
               h = (NPlus.CSlot n (inst_gran I v) d,
                    gransOf (inst_gran I)
                      (evalReqBy Vq (sName d) (sRange d)))) \/
            (exists a f' d, entryFeatD e = Some (a, f') /\
               SlotRel.In ((n, v), d) (inst_slots I) /\ sAlias d = a /\
               slotActive (inst_root I) (n, v) d = true /\
               h = (NPlus.CDec n (inst_gran I v) f d f',
                    gransOf (inst_gran I)
                      (evalReqBy Vq (sName d) (sRange d)))))).
    Proof.
      intros; cbn [dependeesBy].
      rewrite Reduced.DependeesSet.add_spec, SOfh.mem_unionMap.
      split.
      - intros [Hh | [[[[n' v'] f0] e] [Hfd Hh]]].
        + left; exact Hh.
        + cbn beta iota in Hh.
          destruct (negb (andb (PkgEqb.eqb (n', v') (n, v))
                           (FEqb.eqb f0 f))) eqn:Ek;
            [exfalso; exact (Reduced.DependeesSet.empty_spec Hh) |].
          rewrite negb_false_iff, andb_true_iff, PkgEqb.eqb_true_iff,
            FEqb.eqb_true_iff in Ek; destruct Ek as [[= -> ->] ->].
          rewrite !Reduced.DependeesSet.union_spec in Hh.
          right; exists e; split; [exact Hfd |].
          destruct Hh as [Hh | [Hh | Hh]].
          * destruct e as [f2 | a0 | a0 feat0 | a0 feat0];
              try (exfalso; exact (Reduced.DependeesSet.empty_spec Hh)).
            apply Reduced.DependeesSet.singleton_spec in Hh; subst h.
            left; exists f2; split; reflexivity.
          * destruct (entryActivates e) as [a |] eqn:Ea;
              [| exfalso; exact (Reduced.DependeesSet.empty_spec Hh)].
            apply SOsh.mem_map in Hh; destruct Hh as [[q d] [Hq ->]].
            apply mem_slotsAt in Hq; destruct Hq as [Hs [-> [Ha Hact]]].
            right; left; exists a, d; repeat split; assumption.
          * destruct (entryFeatD e) as [[a f'] |] eqn:Ea;
              [| exfalso; exact (Reduced.DependeesSet.empty_spec Hh)].
            apply SOsh.mem_map in Hh; destruct Hh as [[q d] [Hq ->]].
            apply mem_slotsAt in Hq; destruct Hq as [Hs [-> [Ha Hact]]].
            right; right; exists a, f', d; repeat split; assumption.
      - intros [Hh | [e [Hfd Hcase]]]; [left; exact Hh | right].
        exists (((n, v), f), e); split; [exact Hfd | cbn beta iota].
        rewrite PkgEqb.eqb_refl, FEqb.eqb_refl; cbn [andb negb].
        rewrite !Reduced.DependeesSet.union_spec.
        destruct Hcase as [[f2 [-> ->]] | [Hc | Hc]].
        + left; cbn [entryActivates entryFeatD].
          apply Reduced.DependeesSet.singleton_spec; reflexivity.
        + destruct Hc as [a [d [Ea [Hs [Ha [Hact ->]]]]]].
          right; left; rewrite Ea; apply SOsh.mem_map.
          exists ((n, v), d); split; [| reflexivity].
          apply mem_slotsAt; repeat split; assumption.
        + destruct Hc as [a [f' [d [Ea [Hs [Ha [Hact ->]]]]]]].
          right; right; rewrite Ea; apply SOsh.mem_map.
          exists ((n, v), d); split; [| reflexivity].
          apply mem_slotsAt; repeat split; assumption.
    Qed.

    Lemma mem_dep_featP :
      forall I n f w v h,
        Reduced.DependeesSet.In h
          (dependees I (NPlus.CFeatP n f w, VPlus.WOrig v)) <->
        (h =
           (NPlus.CGran n (inst_gran I v), Reduced.VSet.singleton (VPlus.WOrig v)) \/
         exists e, FDefRel.In (((n, v), f), e) (inst_fdefs I) /\
           ((exists f', e = FEntry.EFeat f' /\
               h = (NPlus.CFeatP n f' (inst_gran I v),
                    Reduced.VSet.singleton (VPlus.WOrig v))) \/
            (exists a d, entryActivates e = Some a /\
               SlotRel.In ((n, v), d) (inst_slots I) /\ sAlias d = a /\
               slotActive (inst_root I) (n, v) d = true /\
               h = (NPlus.CSlot n (inst_gran I v) d,
                    gransOf (inst_gran I)
                      (evalReq (inst_real I) (sName d) (sRange d)))) \/
            (exists a f' d, entryFeatD e = Some (a, f') /\
               SlotRel.In ((n, v), d) (inst_slots I) /\ sAlias d = a /\
               slotActive (inst_root I) (n, v) d = true /\
               h = (NPlus.CDec n (inst_gran I v) f d f',
                    gransOf (inst_gran I)
                      (evalReq (inst_real I) (sName d) (sRange d)))))).
    Proof. intros; unfold dependees; apply mem_depBy_featP. Qed.

    Lemma mem_depBy_slot :
      forall Vq I n w d w' h,
        Reduced.DependeesSet.In h
          (dependeesBy Vq I (NPlus.CSlot n w d, VPlus.WClass w')) <->
        h = (NPlus.CGran (sName d) w',
             inGran (inst_gran I) w' (evalReqBy Vq (sName d) (sRange d))) \/
        exists f, FSet.In f (slotRequests d (inst_default I)) /\
          h = (NPlus.CFeatP (sName d) f w',
               inGran (inst_gran I) w' (evalReqBy Vq (sName d) (sRange d))).
    Proof.
      intros; cbn [dependeesBy].
      rewrite Reduced.DependeesSet.add_spec, SOfsh.mem_map; reflexivity.
    Qed.

    Lemma mem_dep_slot :
      forall I n w d w' h,
        Reduced.DependeesSet.In h
          (dependees I (NPlus.CSlot n w d, VPlus.WClass w')) <->
        h = (NPlus.CGran (sName d) w',
             inGran (inst_gran I) w'
               (evalReq (inst_real I) (sName d) (sRange d))) \/
        exists f, FSet.In f (slotRequests d (inst_default I)) /\
          h = (NPlus.CFeatP (sName d) f w',
               inGran (inst_gran I) w'
                 (evalReq (inst_real I) (sName d) (sRange d))).
    Proof. intros; unfold dependees; apply mem_depBy_slot. Qed.

    Lemma mem_depBy_dec :
      forall Vq I n w f d f' w' h,
        Reduced.DependeesSet.In h
          (dependeesBy Vq I (NPlus.CDec n w f d f', VPlus.WClass w')) <->
        h = (NPlus.CSlot n w d, Reduced.VSet.singleton (VPlus.WClass w')) \/
        h = (NPlus.CFeatP (sName d) f' w',
             inGran (inst_gran I) w' (evalReqBy Vq (sName d) (sRange d))).
    Proof.
      intros; cbn [dependeesBy].
      rewrite Reduced.DependeesSet.add_spec, Reduced.DependeesSet.singleton_spec;
        reflexivity.
    Qed.

    Lemma mem_dep_dec :
      forall I n w f d f' w' h,
        Reduced.DependeesSet.In h
          (dependees I (NPlus.CDec n w f d f', VPlus.WClass w')) <->
        h = (NPlus.CSlot n w d, Reduced.VSet.singleton (VPlus.WClass w')) \/
        h = (NPlus.CFeatP (sName d) f' w',
             inGran (inst_gran I) w'
               (evalReq (inst_real I) (sName d) (sRange d))).
    Proof. intros; unfold dependees; apply mem_depBy_dec. Qed.
    Module SOtp := SetOps Reduced.Pkg Pkg Reduced.PkgSet PkgSet.
    Definition cargoResolution (S : Reduced.PkgSet.t) : PkgSet.t :=
      SOtp.filterMap (fun '(m, u) =>
          match m, u with
          | NPlus.CGran n _, VPlus.WOrig v => Some (n, v)
          | _, _ => None
          end)
        S.

    Lemma mem_cargoResolution : forall S n v,
        PkgSet.In (n, v) (cargoResolution S) <->
        exists w, Reduced.PkgSet.In (NPlus.CGran n w, VPlus.WOrig v) S.
    Proof.
      intros S n v; unfold cargoResolution; rewrite SOtp.mem_filterMap; split.
      - intros [[m u] [Hin He]]; cbn beta iota in He.
        destruct m; try discriminate; destruct u; try discriminate.
        injection He as -> ->; exists w; exact Hin.
      - intros [w Hin]; exists (NPlus.CGran n w, VPlus.WOrig v); split;
          [exact Hin | reflexivity].
    Qed.

    Module SOtf := SetOps Reduced.Pkg F Reduced.PkgSet FSet.
    Definition featsAt (S : Reduced.PkgSet.t) (p : Pkg.t) : FSet.t :=
      SOtf.filterMap (fun '(m, u) =>
          match m, u with
          | NPlus.CFeatP n f _, VPlus.WOrig v =>
              if PkgEqb.eqb (n, v) p then Some f else None
          | _, _ => None
          end)
        S.

    Lemma mem_featsAt : forall S n v f,
        FSet.In f (featsAt S (n, v)) <->
        exists w, Reduced.PkgSet.In (NPlus.CFeatP n f w, VPlus.WOrig v) S.
    Proof.
      intros S n v f; unfold featsAt; rewrite SOtf.mem_filterMap; split.
      - intros [[m u] [Hin He]]; cbn beta iota in He.
        destruct m; try discriminate; destruct u; try discriminate.
        rewrite if_some_iff, PkgEqb.eqb_true_iff in He.
        destruct He as [[= -> ->] ->]; exists w; exact Hin.
      - intros [w Hin]; exists (NPlus.CFeatP n f w, VPlus.WOrig v); split;
          [exact Hin | cbn beta iota].
        rewrite PkgEqb.eqb_refl; reflexivity.
    Qed.

    Module SOpf := SetOps Pkg Featured PkgSet FeaturedSet.
    Definition features (S : Reduced.PkgSet.t) : FeaturedSet.t :=
      SOpf.map (fun p => (p, featsAt S p)) (cargoResolution S).

    Lemma mem_features : forall S p fs,
        FeaturedSet.In (p, fs) (features S) <->
        PkgSet.In p (cargoResolution S) /\ fs = featsAt S p.
    Proof.
      intros S p fs; unfold features; rewrite SOpf.mem_map; split.
      - intros [q [Hq He]]; injection He as -> ->; split;
          [exact Hq | reflexivity].
      - intros [Hp ->]; exists p; split; [exact Hp | reflexivity].
    Qed.

    Module SOtv2 := SetOps Reduced.Pkg V Reduced.PkgSet VSet.
    Definition versionsAt (S : Reduced.PkgSet.t) (n : N.t) (w : G.t) : VSet.t :=
      SOtv2.filterMap (fun '(m, v) =>
          match m, v with
          | NPlus.CGran n' w', VPlus.WOrig u =>
              if andb (NEqb.eqb n' n) (GEqb.eqb w' w) then Some u else None
          | _, _ => None
          end)
        S.

    Lemma mem_versionsAt : forall S n w u,
        VSet.In u (versionsAt S n w) <->
        Reduced.PkgSet.In (NPlus.CGran n w, VPlus.WOrig u) S.
    Proof.
      intros S n w u; unfold versionsAt; rewrite SOtv2.mem_filterMap; split.
      - intros [[m v] [Hin He]]; cbn beta iota in He.
        destruct m; try discriminate; destruct v; try discriminate.
        rewrite if_some_iff, andb_true_iff, NEqb.eqb_true_iff, GEqb.eqb_true_iff
          in He.
        destruct He as [[-> ->] ->]; exact Hin.
      - intro Hin; exists (NPlus.CGran n w, VPlus.WOrig u); split;
          [exact Hin | cbn beta iota].
        rewrite NEqb.eqb_refl, GEqb.eqb_refl; reflexivity.
    Qed.

    Module SOtpar := SetOps Reduced.Pkg ParentElt Reduced.PkgSet ParentRel.
    Module SOvpar := SetOps V ParentElt VSet ParentRel.
    Definition parents (I : Inst) (S : Reduced.PkgSet.t) : ParentRel.t :=
      SOtpar.unionMap (fun '(m, v') =>
          match m, v' with
          | NPlus.CSlot n w d, VPlus.WClass w' =>
              SOvpar.unionMap (fun v =>
                  if andb (SlotRel.mem ((n, v), d) (inst_slots I))
                       (andb (slotActive (inst_root I) (n, v) d)
                          (orb (negb (sOptional d))
                             (activatedb (inst_fdefs I) (featsAt S (n, v))
                                (n, v)
                                (sAlias d))))
                  then SOvpar.map (fun u => (((n, v), sSite d), u))
                         (versionsAt S (sName d) w')
                  else ParentRel.empty)
                (versionsAt S n w)
          | _, _ => ParentRel.empty
          end)
        S.

    Lemma mem_parents : forall I S n v k u,
        ParentRel.In (((n, v), k), u) (parents I S) <->
        exists w w' d, Reduced.PkgSet.In (NPlus.CSlot n w d, VPlus.WClass w') S /\
          Reduced.PkgSet.In (NPlus.CGran n w, VPlus.WOrig v) S /\
          SlotRel.In ((n, v), d) (inst_slots I) /\ sSite d = k /\
          slotActive (inst_root I) (n, v) d = true /\
          (sOptional d = false \/
           Activated (inst_fdefs I) (featsAt S (n, v)) (n, v) (sAlias d)) /\
          Reduced.PkgSet.In (NPlus.CGran (sName d) w', VPlus.WOrig u) S.
    Proof.
      intros I S n v k u; unfold parents.
      rewrite SOtpar.mem_unionMap; split.
      - intros [[m v'] [Hin Hy]]; cbn beta iota in Hy.
        destruct m; try (exfalso; exact (SOvpar.empty_in _ Hy));
          destruct v'; try (exfalso; exact (SOvpar.empty_in _ Hy)).
        rewrite SOvpar.mem_unionMap_if in Hy; cbn beta in Hy.
        destruct Hy as [v0 [Hv0 [Eb Hy]]].
        rewrite !andb_true_iff, SlotRel.mem_spec in Eb.
        destruct Eb as [Hs [Hact Ereq]].
        change (requiredb (inst_fdefs I) (featsAt S (n0, v0)) (n0, v0) d = true)
          in Ereq.
        apply requiredb_iff in Ereq.
        apply SOvpar.mem_map in Hy; destruct Hy as [u' [Hu' He]].
        injection He as -> -> -> ->.
        exists w, w0, d; repeat split; try assumption.
        + apply mem_versionsAt; exact Hv0.
        + apply mem_versionsAt; exact Hu'.
      - intros [w [w' [d [Hslot [Hown [Hs [Ha [Hact [Hreq Hcr]]]]]]]]].
        exists (NPlus.CSlot n w d, VPlus.WClass w'); split;
          [exact Hslot | cbn beta iota].
        apply SOvpar.mem_unionMap; exists v; split;
          [apply mem_versionsAt; exact Hown | cbn beta iota].
        rewrite (proj2 (SlotRel.mem_spec _ _) Hs), Hact.
        apply requiredb_iff in Hreq; unfold requiredb in Hreq; rewrite Hreq.
        cbn [andb].
        apply SOvpar.mem_map; exists u; split;
          [apply mem_versionsAt; exact Hcr | rewrite Ha; reflexivity].
    Qed.

    Theorem cargo_soundness :
      forall I (S : Reduced.PkgSet.t),
        SiteFunctional (inst_slots I) ->
        Reduced.IsResolution (reduceReal I) (reduceDeps I) rootPkg S ->
        IsResolution I (cargoResolution S) (features S) (parents I S).
    Proof.
      intros [R Slots FDefs Links support g dflt [rn rv] rootFeats] S
        Hsite Hres.
      cbn [inst_slots] in Hsite.
      destruct Hres as [Hsub Hroot Hdep Huniq].
      assert (A1 : forall n w v,
          Reduced.PkgSet.In (NPlus.CGran n w, VPlus.WOrig v) S ->
          PkgSet.In (n, v) R /\ w = g v).
      { intros n w v Hin; apply Hsub, real_shape in Hin.
        destruct Hin as [v' [E [HR ->]]]; injection E as <-; auto. }
      assert (A2 : forall n f w v,
          Reduced.PkgSet.In (NPlus.CFeatP n f w, VPlus.WOrig v) S ->
          SupportSet.In ((n, v), f) support /\ w = g v).
      { intros n f w v Hin; apply Hsub, real_shape in Hin.
        destruct Hin as [v' [E [Hsp ->]]]; injection E as <-; auto. }
      assert (A3 : forall n w d w',
          Reduced.PkgSet.In (NPlus.CSlot n w d, VPlus.WClass w') S ->
          exists u, VSet.In u (evalReq R (sName d) (sRange d)) /\ g u = w').
      { intros n w d w' Hin; apply Hsub, real_shape in Hin.
        destruct Hin as [_ [u [Hu E]]]; injection E as ->; eauto. }
      assert (A5 : forall n f w u u',
          Reduced.PkgSet.In (NPlus.CFeatP n f w, VPlus.WOrig u') S ->
          Reduced.PkgSet.In (NPlus.CGran n w, VPlus.WOrig u) S -> u' = u).
      { intros n f w u u' Hf Hc.
        destruct (A2 _ _ _ _ Hf) as [Hsp Egr]; subst w.
        assert (Hed : Reduced.DepRel.In
            ((NPlus.CFeatP n f (g u'), VPlus.WOrig u'),
             (NPlus.CGran n (g u'), Reduced.VSet.singleton (VPlus.WOrig u')))
            (reduceDeps
               (MkInst R Slots FDefs Links support g dflt (rn, rv) rootFeats))).
        { apply mem_reduceDeps; split; [exact (Hsub _ Hf) |].
          apply mem_dep_featP; left; reflexivity. }
        destruct (Hdep _ Hf _ _ Hed) as [w [Hw HwS]].
        apply Reduced.VSet.singleton_spec in Hw; subst w.
        assert (E := Huniq _ _ _ HwS Hc); injection E as E; exact E. }
      constructor;
        cbn [inst_real inst_support inst_fdefs inst_slots inst_links inst_gran
           inst_default inst_root inst_rootFeats].
      - intros [n v] Hp; apply mem_cargoResolution in Hp; destruct Hp as [w Hp].
        exact (proj1 (A1 _ _ _ Hp)).
      - assert (Hed : Reduced.DepRel.In
            (rootPkg, (NPlus.CGran rn (g rv),
                         Reduced.VSet.singleton (VPlus.WOrig rv)))
            (reduceDeps
               (MkInst R Slots FDefs Links support g dflt (rn, rv) rootFeats))).
        { apply mem_reduceDeps; split; [exact (Hsub _ Hroot) |].
          apply mem_dep_root; left; reflexivity. }
        destruct (Hdep _ Hroot _ _ Hed) as [w [Hw HwS]].
        apply Reduced.VSet.singleton_spec in Hw; subst w.
        apply mem_cargoResolution; exists (g rv); exact HwS.
      - intros n v v' Hv Hv' NE Hg.
        apply mem_cargoResolution in Hv; destruct Hv as [w Hv].
        apply mem_cargoResolution in Hv'; destruct Hv' as [w' Hv'].
        destruct (A1 _ _ _ Hv) as [_ Egr]; subst w.
        destruct (A1 _ _ _ Hv') as [_ Egr']; subst w'.
        rewrite <- Hg in Hv'.
        assert (E := Huniq _ _ _ Hv Hv'); injection E as E.
        contradiction NE.
      - intros [n v] fs Hp Hfs d Hd Hact Hopt.
        apply mem_features in Hfs; destruct Hfs as [_ ->].
        apply mem_cargoResolution in Hp; destruct Hp as [w0 Hp].
        destruct (A1 _ _ _ Hp) as [_ Egr0]; subst w0.
        assert (Achain : forall w,
            Reduced.PkgSet.In (NPlus.CSlot n (g v) d, VPlus.WClass w) S ->
            exists u, ParentRel.In (((n, v), sSite d), u)
                        (parents
                           (MkInst R Slots FDefs Links support g dflt (rn, rv)
                              rootFeats) S) /\
              rgHolds (sRange d) u = true /\
              PkgSet.In (sName d, u) (cargoResolution S) /\
              forall fs', FeaturedSet.In ((sName d, u), fs')
                (features S) ->
              FSet.Subset (slotRequests d dflt) fs').
        { intros w Hslot.
          destruct (A3 _ _ _ _ Hslot) as [u0 [Hu0 Egr]].
          subst w.
          assert (Hed : Reduced.DepRel.In
              ((NPlus.CSlot n (g v) d, VPlus.WClass (g u0)),
               (NPlus.CGran (sName d) (g u0),
                inGran g (g u0) (evalReq R (sName d) (sRange d))))
              (reduceDeps
                 (MkInst R Slots FDefs Links support g dflt (rn, rv)
                    rootFeats))).
          { apply mem_reduceDeps; split; [exact (Hsub _ Hslot) |].
            apply mem_dep_slot; left; reflexivity. }
          destruct (Hdep _ Hslot _ _ Hed) as [w [Hw HwS]].
          apply mem_inGran in Hw; destruct Hw as [u [Hu [Hgu ->]]].
          exists u; repeat split.
          - apply mem_parents; exists (g v), (g u0), d.
            split; [exact Hslot |].
            split; [exact Hp |].
            split; [exact Hd |].
            split; [reflexivity |].
            split; [exact Hact |].
            split; [exact Hopt | exact HwS].
          - apply mem_evalReq in Hu; exact (proj2 Hu).
          - apply mem_cargoResolution; exists (g u0); exact HwS.
          - intros fs' Hfs'; apply mem_features in Hfs';
              destruct Hfs' as [_ ->]; intros f Hf.
            assert (Hef : Reduced.DepRel.In
                ((NPlus.CSlot n (g v) d, VPlus.WClass (g u0)),
                 (NPlus.CFeatP (sName d) f (g u0),
                  inGran g (g u0) (evalReq R (sName d) (sRange d))))
                (reduceDeps
                   (MkInst R Slots FDefs Links support g dflt (rn, rv)
                      rootFeats))).
            { apply mem_reduceDeps; split; [exact (Hsub _ Hslot) |].
              apply mem_dep_slot; right; exists f; split;
                [exact Hf | reflexivity]. }
            destruct (Hdep _ Hslot _ _ Hef) as [w' [Hw' Hw'S]].
            apply mem_inGran in Hw'; destruct Hw' as [u' [Hu' [Hgu' ->]]].
            assert (u' = u) by (apply (A5 (sName d) f (g u0));
                                assumption).
            subst u'.
            apply mem_featsAt; exists (g u0); exact Hw'S. }
        destruct Hopt as [Hno | Hacted].
        + assert (Hed : Reduced.DepRel.In
              ((NPlus.CGran n (g v), VPlus.WOrig v),
               (NPlus.CSlot n (g v) d,
                gransOf g (evalReq R (sName d) (sRange d))))
              (reduceDeps
                 (MkInst R Slots FDefs Links support g dflt (rn, rv)
                    rootFeats))).
          { apply mem_reduceDeps; split; [exact (Hsub _ Hp) |].
            apply mem_dep_gran; left; exists d; repeat split; assumption. }
          destruct (Hdep _ Hp _ _ Hed) as [w [Hw HwS]].
          apply mem_gransOf in Hw; destruct Hw as [u1 [Hu1 ->]].
          exact (Achain _ HwS).
        + destruct Hacted as [f [Hffs Hent]].
          apply mem_featsAt in Hffs; destruct Hffs as [w1 Hffs].
          destruct (A2 _ _ _ _ Hffs) as [_ Egr1]; subst w1.
          assert (Hea : exists e', FDefRel.In (((n, v), f), e') FDefs /\
              entryActivates e' = Some (sAlias d)).
          { destruct Hent as [He | [[f' He] | [f' He]]].
            - exists (FEntry.EDep (sAlias d)); split;
                [exact He | reflexivity].
            - exists (FEntry.EDepFeat (sAlias d) f'); split;
                [exact He | reflexivity].
            - exists (FEntry.EWeakFeat (sAlias d) f'); split;
                [exact He | reflexivity]. }
          destruct Hea as [e' [He' Ea]].
          assert (Hed : Reduced.DepRel.In
              ((NPlus.CFeatP n f (g v), VPlus.WOrig v),
               (NPlus.CSlot n (g v) d,
                gransOf g (evalReq R (sName d) (sRange d))))
              (reduceDeps
                 (MkInst R Slots FDefs Links support g dflt (rn, rv)
                    rootFeats))).
          { apply mem_reduceDeps; split; [exact (Hsub _ Hffs) |].
            apply mem_dep_featP; right; exists e'; split; [exact He' |].
            right; left; exists (sAlias d), d; repeat split; assumption. }
          destruct (Hdep _ Hffs _ _ Hed) as [w [Hw HwS]].
          apply mem_gransOf in Hw; destruct Hw as [u1 [Hu1 ->]].
          exact (Achain _ HwS).
      - split.
        + intros [n v] fs f f0 Hfs Hf He.
          apply mem_features in Hfs; destruct Hfs as [_ ->].
          apply mem_featsAt in Hf; destruct Hf as [w Hf].
          destruct (A2 _ _ _ _ Hf) as [_ Egr]; subst w.
          assert (Hed : Reduced.DepRel.In
              ((NPlus.CFeatP n f (g v), VPlus.WOrig v),
               (NPlus.CFeatP n f0 (g v), Reduced.VSet.singleton (VPlus.WOrig v)))
              (reduceDeps
                 (MkInst R Slots FDefs Links support g dflt (rn, rv)
                    rootFeats))).
          { apply mem_reduceDeps; split; [exact (Hsub _ Hf) |].
            apply mem_dep_featP; right; exists (FEntry.EFeat f0);
              split; [exact He |].
            left; exists f0; split; reflexivity. }
          destruct (Hdep _ Hf _ _ Hed) as [w [Hw HwS]].
          apply Reduced.VSet.singleton_spec in Hw; subst w.
          apply mem_featsAt; exists (g v); exact HwS.
        + intros [n v] fs f a f' Hfs Hf Hent d u Hd Halias Hpi fs' Hfs'.
          apply mem_features in Hfs; destruct Hfs as [_ ->].
          apply mem_featsAt in Hf; destruct Hf as [w Hf].
          destruct (A2 _ _ _ _ Hf) as [_ Egr]; subst w.
          subst a.
          assert (He' : exists e', FDefRel.In (((n, v), f), e') FDefs /\
              entryFeatD e' = Some (sAlias d, f')).
          { destruct Hent as [He | He].
            - exists (FEntry.EDepFeat (sAlias d) f'); split;
                [exact He | reflexivity].
            - exists (FEntry.EWeakFeat (sAlias d) f'); split;
                [exact He | reflexivity]. }
          destruct He' as [e' [He' Ee]].
          apply mem_parents in Hpi;
            destruct Hpi as [w2 [w2' [d2 [Hslot2 [Hcr2 [Hs2 [Ha2 [Hact2
              [_ Hcr2t]]]]]]]]].
          assert (d2 = d) by exact (Hsite (n, v) d2 d Hs2 Hd Ha2); subst d2.
          destruct (A1 _ _ _ Hcr2) as [_ ->].
          assert (Hed : Reduced.DepRel.In
              ((NPlus.CFeatP n f (g v), VPlus.WOrig v),
               (NPlus.CDec n (g v) f d f',
                gransOf g (evalReq R (sName d) (sRange d))))
              (reduceDeps
                 (MkInst R Slots FDefs Links support g dflt (rn, rv)
                    rootFeats))).
          { apply mem_reduceDeps; split; [exact (Hsub _ Hf) |].
            apply mem_dep_featP; right; exists e'; split; [exact He' |].
            right; right; exists (sAlias d), f', d; repeat split;
              assumption. }
          destruct (Hdep _ Hf _ _ Hed) as [w [Hw HwS]].
          apply mem_gransOf in Hw; destruct Hw as [u1 [Hu1 ->]].
          assert (Hpin : Reduced.DepRel.In
              ((NPlus.CDec n (g v) f d f', VPlus.WClass (g u1)),
               (NPlus.CSlot n (g v) d,
                Reduced.VSet.singleton (VPlus.WClass (g u1))))
              (reduceDeps
                 (MkInst R Slots FDefs Links support g dflt (rn, rv)
                    rootFeats))).
          { apply mem_reduceDeps; split; [exact (Hsub _ HwS) |].
            apply mem_dep_dec; left; reflexivity. }
          destruct (Hdep _ HwS _ _ Hpin) as [w [Hx HxS]].
          apply Reduced.VSet.singleton_spec in Hx; subst w.
          assert (Hdel : Reduced.DepRel.In
              ((NPlus.CDec n (g v) f d f', VPlus.WClass (g u1)),
               (NPlus.CFeatP (sName d) f' (g u1),
                inGran g (g u1) (evalReq R (sName d) (sRange d))))
              (reduceDeps
                 (MkInst R Slots FDefs Links support g dflt (rn, rv)
                    rootFeats))).
          { apply mem_reduceDeps; split; [exact (Hsub _ HwS) |].
            apply mem_dep_dec; right; reflexivity. }
          destruct (Hdep _ HwS _ _ Hdel) as [w [Hy HyS]].
          apply mem_inGran in Hy; destruct Hy as [u2 [Hu2 [Hgu2 ->]]].
          assert (Egr : VPlus.WClass w2' = VPlus.WClass (g u1))
            by exact (Huniq _ _ _ Hslot2 HxS).
          injection Egr as Egr; subst w2'.
          assert (u2 = u) by (apply (A5 (sName d) f' (g u1)); assumption).
          subst u2.
          apply mem_features in Hfs'; destruct Hfs' as [_ ->].
          apply mem_featsAt; exists (g u1); exact HyS.
      - intros p q l Hp Hq Hlp Hlq.
        destruct p as [pn pv]; destruct q as [qn qv].
        apply mem_cargoResolution in Hp; destruct Hp as [grp Hp].
        apply mem_cargoResolution in Hq; destruct Hq as [grq Hq].
        destruct (A1 _ _ _ Hp) as [HpR Egp]; subst grp.
        destruct (A1 _ _ _ Hq) as [HqR Egq]; subst grq.
        assert (Hep : Reduced.DepRel.In
            ((NPlus.CGran pn (g pv), VPlus.WOrig pv),
             (NPlus.CCls l,
              Reduced.VSet.singleton (VPlus.WName (NPlus.CGran pn (g pv)))))
            (reduceDeps
               (MkInst R Slots FDefs Links support g dflt (rn, rv) rootFeats))).
        { apply mem_reduceDeps; split; [exact (Hsub _ Hp) |].
          apply mem_dep_gran; right; exists l; split;
            [exact Hlp | reflexivity]. }
        assert (Heq : Reduced.DepRel.In
            ((NPlus.CGran qn (g qv), VPlus.WOrig qv),
             (NPlus.CCls l,
              Reduced.VSet.singleton (VPlus.WName (NPlus.CGran qn (g qv)))))
            (reduceDeps
               (MkInst R Slots FDefs Links support g dflt (rn, rv) rootFeats))).
        { apply mem_reduceDeps; split; [exact (Hsub _ Hq) |].
          apply mem_dep_gran; right; exists l; split;
            [exact Hlq | reflexivity]. }
        destruct (Hdep _ Hp _ _ Hep) as [v [Hx HxS]].
        destruct (Hdep _ Hq _ _ Heq) as [u [Hy HyS]].
        apply Reduced.VSet.singleton_spec in Hx; subst v.
        apply Reduced.VSet.singleton_spec in Hy; subst u.
        assert (E := Huniq _ _ _ HxS HyS); injection E as E1 E2.
        subst qn; rewrite <- E2 in Hq.
        assert (E' := Huniq _ _ _ Hp Hq); injection E' as E'.
        rewrite E'; reflexivity.
      - intros p fs Hfs; apply mem_features in Hfs; exact (proj1 Hfs).
      - intros p Hp; exists (featsAt S p); apply mem_features; split;
          [exact Hp | reflexivity].
      - intros p fs fs' Hfs Hfs'.
        apply mem_features in Hfs; destruct Hfs as [_ ->].
        apply mem_features in Hfs'; destruct Hfs' as [_ ->]; reflexivity.
      - intros fs Hfs; apply mem_features in Hfs;
          destruct Hfs as [_ ->]; intros f Hf.
        assert (Hed : Reduced.DepRel.In
            (rootPkg, (NPlus.CFeatP rn f (g rv),
                     Reduced.VSet.singleton (VPlus.WOrig rv)))
            (reduceDeps
               (MkInst R Slots FDefs Links support g dflt (rn, rv) rootFeats))).
        { apply mem_reduceDeps; split; [exact (Hsub _ Hroot) |].
          apply mem_dep_root; right; exists f; split;
            [exact Hf | reflexivity]. }
        destruct (Hdep _ Hroot _ _ Hed) as [w [Hw HwS]].
        apply Reduced.VSet.singleton_spec in Hw; subst w.
        apply mem_featsAt; exists (g rv); exact HwS.
      - intros [n v] fs f Hfs Hf.
        apply mem_features in Hfs; destruct Hfs as [_ ->].
        apply mem_featsAt in Hf; destruct Hf as [w Hf].
        exact (proj1 (A2 _ _ _ _ Hf)).
      - intros [n v] a u u' Hu Hu'.
        apply mem_parents in Hu;
          destruct Hu as [w [w1 [d [Hslot [Hown [Hs [Ha [Hact [_ Hcr]]]]]]]]].
        apply mem_parents in Hu';
          destruct Hu' as [w' [w1' [d' [Hslot' [Hown' [Hs' [Ha' [Hact'
            [_ Hcr']]]]]]]]].
        assert (d' = d)
          by exact (Hsite (n, v) d' d Hs' Hs (eq_trans Ha' (eq_sym Ha))).
        subst d'.
        destruct (A1 _ _ _ Hown) as [_ ->].
        destruct (A1 _ _ _ Hown') as [_ ->].
        assert (E := Huniq _ _ _ Hslot Hslot'); injection E as E; subst w1'.
        assert (E2 := Huniq _ _ _ Hcr Hcr'); injection E2 as E2; exact E2.
      - intros [n v] k u Hpi.
        apply mem_parents in Hpi; destruct Hpi as [w [_ [_ [_ [Hown _]]]]].
        apply mem_cargoResolution; exists w; exact Hown.
    Qed.

    Module SOfw2 := SetOps Featured Reduced.Pkg FeaturedSet Reduced.PkgSet.
    Module SOfsp := SetOps F Reduced.Pkg FSet Reduced.PkgSet.
    Module SOparp := SetOps ParentElt Reduced.Pkg ParentRel Reduced.PkgSet.

    Definition wFeats (g : V.t -> G.t) (FS : FeaturedSet.t) : Reduced.PkgSet.t :=
      SOfw2.unionMap (fun '((n, v), fs) =>
          SOfsp.map (fun f => (NPlus.CFeatP n f (g v), VPlus.WOrig v)) fs)
        FS.

    Lemma mem_wFeats : forall g FS p,
        Reduced.PkgSet.In p (wFeats g FS) <->
        exists n v fs f, FeaturedSet.In ((n, v), fs) FS /\ FSet.In f fs /\
          p = (NPlus.CFeatP n f (g v), VPlus.WOrig v).
    Proof.
      intros g FS p; unfold wFeats; rewrite SOfw2.mem_unionMap; split.
      - intros [[[n v] fs] [Hin Hx]]; cbn beta iota in Hx.
        apply SOfsp.mem_map in Hx; destruct Hx as [f [Hf ->]].
        exists n, v, fs, f; repeat split; assumption.
      - intros [n [v [fs [f [Hin [Hf ->]]]]]].
        exists ((n, v), fs); split; [exact Hin | cbn beta iota].
        apply SOfsp.mem_map; exists f; split; [exact Hf | reflexivity].
    Qed.

    Definition wSlots (g : V.t -> G.t) (FDefs : FDefRel.t)
        (Slots : SlotRel.t) (r : Pkg.t)
        (S : PkgSet.t) (FS : FeaturedSet.t) (pi : ParentRel.t) : Reduced.PkgSet.t :=
      SOparp.unionMap (fun '(((n, v), k), u) =>
          if parentsb FDefs Slots r S FS (n, v) k
          then SOslp.map (fun '(_, d) =>
                   (NPlus.CSlot n (g v) d, VPlus.WClass (g u)))
                 (slotsAtKey Slots r (n, v) k)
          else Reduced.PkgSet.empty)
        pi.

    Lemma mem_wSlots : forall g FDefs Slots r S FS pi p,
        Reduced.PkgSet.In p (wSlots g FDefs Slots r S FS pi) <->
        exists n v k u d, ParentRel.In (((n, v), k), u) pi /\
          parentsb FDefs Slots r S FS (n, v) k = true /\
          SlotRel.In ((n, v), d) Slots /\ sSite d = k /\
          slotActive r (n, v) d = true /\
          p = (NPlus.CSlot n (g v) d, VPlus.WClass (g u)).
    Proof.
      intros g FDefs Slots r S FS pi p; unfold wSlots.
      rewrite SOparp.mem_unionMap; split.
      - intros [[[[n v] k] u] [Hin Hx]]; cbn beta iota in Hx.
        apply SOslp.in_if_empty in Hx as [Eb Hx].
        apply SOslp.mem_map in Hx; destruct Hx as [[q d] [Hq ->]].
        apply mem_slotsAtKey in Hq; destruct Hq as [Hs [-> [Ha Hact]]].
        exists n, v, k, u, d; repeat split; assumption.
      - intros [n [v [k [u [d [Hin [Eb [Hs [Ha [Hact ->]]]]]]]]]].
        exists (((n, v), k), u); split; [exact Hin | cbn beta iota].
        rewrite Eb; apply SOslp.mem_map; exists ((n, v), d); split;
          [apply mem_slotsAtKey; repeat split; assumption | reflexivity].
    Qed.

    Definition wDecs (g : V.t -> G.t) (FDefs : FDefRel.t)
        (Slots : SlotRel.t) (r : Pkg.t)
        (S : PkgSet.t) (FS : FeaturedSet.t) (pi : ParentRel.t) : Reduced.PkgSet.t :=
      SOparp.unionMap (fun '(((n, v), k), u) =>
          if parentsb FDefs Slots r S FS (n, v) k
          then SOfp.unionMap (fun '((q, f), e) =>
                 match entryFeatD e with
                 | Some (a', f') =>
                     if andb (andb (PkgEqb.eqb q (n, v))
                                (NEqb.eqb a' (siteAlias k)))
                          (FSet.mem f (fsAt FS (n, v)))
                     then SOslp.map (fun '(_, d) =>
                              (NPlus.CDec n (g v) f d f', VPlus.WClass (g u)))
                            (slotsAtKey Slots r (n, v) k)
                     else Reduced.PkgSet.empty
                 | None => Reduced.PkgSet.empty
                 end)
               FDefs
          else Reduced.PkgSet.empty)
        pi.

    Lemma mem_wDecs : forall g FDefs Slots r S FS pi p,
        Reduced.PkgSet.In p (wDecs g FDefs Slots r S FS pi) <->
        exists n v k u f e f' d, ParentRel.In (((n, v), k), u) pi /\
          parentsb FDefs Slots r S FS (n, v) k = true /\
          FDefRel.In (((n, v), f), e) FDefs /\
          entryFeatD e = Some (siteAlias k, f') /\
          FSet.In f (fsAt FS (n, v)) /\
          SlotRel.In ((n, v), d) Slots /\ sSite d = k /\
          slotActive r (n, v) d = true /\
          p = (NPlus.CDec n (g v) f d f', VPlus.WClass (g u)).
    Proof.
      intros g FDefs Slots r S FS pi p; unfold wDecs.
      rewrite SOparp.mem_unionMap; split.
      - intros [[[[n v] k] u] [Hin Hx]]; cbn beta iota in Hx.
        apply SOslp.in_if_empty in Hx as [Eb Hx].
        apply SOfp.mem_unionMap in Hx; destruct Hx as [[[q f] e] [Hf Hx]].
        cbn beta iota in Hx.
        destruct (entryFeatD e) as [[a' f'] |] eqn:Ee;
          [| exfalso; exact (SOslp.empty_in _ Hx)].
        rewrite SOslp.in_if_empty, !andb_true_iff, PkgEqb.eqb_true_iff,
          NEqb.eqb_true_iff, FSet.mem_spec in Hx.
        destruct Hx as [[[-> ->] Em] Hx].
        apply SOslp.mem_map in Hx; destruct Hx as [[q d] [Hq ->]].
        apply mem_slotsAtKey in Hq; destruct Hq as [Hs [-> [Ha Hact]]].
        exists n, v, k, u, f, e, f', d; repeat split; assumption.
      - intros [n [v [k [u [f [e [f' [d
          [Hin [Eb [Hf [Ee [Em [Hs [Ha [Hact ->]]]]]]]]]]]]]]]].
        exists (((n, v), k), u); split; [exact Hin | cbn beta iota].
        rewrite Eb; apply SOfp.mem_unionMap.
        exists (((n, v), f), e); split; [exact Hf | cbn beta iota].
        rewrite Ee, PkgEqb.eqb_refl, NEqb.eqb_refl,
          (proj2 (FSet.mem_spec _ _) Em); cbn [andb].
        apply SOslp.mem_map; exists ((n, v), d); split;
          [apply mem_slotsAtKey; repeat split; assumption | reflexivity].
    Qed.

    Definition coreResolution (I : Inst) (S : PkgSet.t)
        (FS : FeaturedSet.t) (pi : ParentRel.t) : Reduced.PkgSet.t :=
      Reduced.PkgSet.add rootPkg
        (Reduced.PkgSet.union (granReal (inst_gran I) S)
           (Reduced.PkgSet.union (wFeats (inst_gran I) FS)
              (Reduced.PkgSet.union
                 (wSlots (inst_gran I) (inst_fdefs I) (inst_slots I)
                    (inst_root I)
                    S FS pi)
                 (Reduced.PkgSet.union
                    (wDecs (inst_gran I) (inst_fdefs I) (inst_slots I)
                       (inst_root I) S FS pi)
                    (clsReal (inst_gran I) S (inst_links I)))))).

    Lemma mem_coreResolution :
      forall I S FS pi p,
        Reduced.PkgSet.In p
          (coreResolution I S FS pi) <->
        p = rootPkg \/ Reduced.PkgSet.In p (granReal (inst_gran I) S) \/
        Reduced.PkgSet.In p (wFeats (inst_gran I) FS) \/
        Reduced.PkgSet.In p
          (wSlots (inst_gran I) (inst_fdefs I) (inst_slots I) (inst_root I)
             S FS pi) \/
        Reduced.PkgSet.In p
          (wDecs (inst_gran I) (inst_fdefs I) (inst_slots I) (inst_root I)
             S FS pi) \/
        Reduced.PkgSet.In p (clsReal (inst_gran I) S (inst_links I)).
    Proof.
      intros; unfold coreResolution.
      rewrite Reduced.PkgSet.add_spec, !Reduced.PkgSet.union_spec; reflexivity.
    Qed.

    Lemma core_shape :
      forall I S FS pi m v',
        Reduced.PkgSet.In (m, v')
          (coreResolution I S FS pi) <->
        match m with
        | NPlus.CRoot => v' = VPlus.WUnit
        | NPlus.CGran n w =>
            exists v, v' = VPlus.WOrig v /\ PkgSet.In (n, v) S /\
              w = inst_gran I v
        | NPlus.CFeatP n f w =>
            exists v fs, v' = VPlus.WOrig v /\ FeaturedSet.In ((n, v), fs) FS /\
              FSet.In f fs /\ w = inst_gran I v
        | NPlus.CSlot n w d =>
            exists v u, v' = VPlus.WClass (inst_gran I u) /\
              w = inst_gran I v /\
              ParentRel.In (((n, v), sSite d), u) pi /\
              parentsb (inst_fdefs I) (inst_slots I) (inst_root I) S FS (n, v)
                (sSite d) = true /\
              SlotRel.In ((n, v), d) (inst_slots I) /\
              slotActive (inst_root I) (n, v) d = true
        | NPlus.CDec n w f d f' =>
            exists v u e, v' = VPlus.WClass (inst_gran I u) /\
              w = inst_gran I v /\
              ParentRel.In (((n, v), sSite d), u) pi /\
              parentsb (inst_fdefs I) (inst_slots I) (inst_root I) S FS (n, v)
                (sSite d) = true /\
              SlotRel.In ((n, v), d) (inst_slots I) /\
              slotActive (inst_root I) (n, v) d = true /\
              FDefRel.In (((n, v), f), e) (inst_fdefs I) /\
              entryFeatD e = Some (sAlias d, f') /\
              FSet.In f (fsAt FS (n, v))
        | NPlus.CCls l =>
            exists n v, v' = VPlus.WName (NPlus.CGran n (inst_gran I v)) /\
              LinkRel.In ((n, v), l) (inst_links I) /\ PkgSet.In (n, v) S
        end.
    Proof.
      intros I S FS pi m v'.
      rewrite mem_coreResolution, mem_granReal, mem_wFeats, mem_wSlots,
        mem_wDecs, mem_clsReal; unfold rootPkg; split.
      - intros [He | [He | [He | [He | [He | He]]]]]; mem_destruct; eauto 20.
      - destruct m as [| n w | n f w | n w d | n w f d f' | l];
          cbn beta iota.
        + intros ->; left; reflexivity.
        + intros [v [-> [HS ->]]]; right; left; exists n, v; auto.
        + intros [v [fs [-> [Hfs [Hf ->]]]]].
          right; right; left; exists n, v, fs, f; auto.
        + intros [v [u [-> [-> [Hpi [Eb [Hs Hact]]]]]]].
          right; right; right; left; exists n, v, (sSite d), u, d.
          repeat split; assumption.
        + intros [v [u [e [-> [-> [Hpi [Eb [Hs [Hact [Hf [Ee Hfs]]]]]]]]]]].
          right; right; right; right; left.
          exists n, v, (sSite d), u, f, e, f', d; repeat split; assumption.
        + intros [n [v [-> [Hl HS]]]]; right; right; right; right; right.
          exists n, v, l; auto.
    Qed.

    Lemma fsAt_mem
        {I S FS pi} :
        IsResolution I S FS pi ->
        forall p, PkgSet.In p S -> FeaturedSet.In (p, fsAt FS p) FS.
    Proof.
      intros Hres p Hp; destruct (res_fs_total Hres Hp) as [fs Hfs].
      rewrite (fsAt_in FS p fs (res_fs_functional Hres) Hfs); exact Hfs.
    Qed.

    Lemma parent_pick
        {I S FS pi} :
        IsResolution I S FS pi ->
        forall n v d, PkgSet.In (n, v) S ->
        SlotRel.In ((n, v), d) (inst_slots I) ->
        slotActive (inst_root I) (n, v) d = true ->
        (sOptional d = false \/
         Activated (inst_fdefs I) (fsAt FS (n, v)) (n, v) (sAlias d)) ->
        exists u, ParentRel.In (((n, v), sSite d), u) pi /\
          parentsb (inst_fdefs I) (inst_slots I) (inst_root I) S FS (n, v)
            (sSite d) = true /\
          VSet.In u (evalReq (inst_real I) (sName d) (sRange d)) /\
          PkgSet.In (sName d, u) S /\
          FSet.Subset (slotRequests d (inst_default I)) (fsAt FS (sName d, u)).
    Proof.
      intros Hres n v d HS Hd Hact Hopt.
      destruct (res_slot_closure Hres HS (fsAt_mem Hres _ HS) Hd Hact Hopt)
        as [u [Hpi [Hrg [Hname Hsub]]]].
      exists u; repeat split; try assumption.
      - apply parentsb_iff; split; [exact HS |].
        exists d; repeat split; assumption.
      - apply mem_evalReq; split; [exact (res_subset Hres Hname) | exact Hrg].
      - exact (Hsub _ (fsAt_mem Hres _ Hname)).
    Qed.

    Lemma parent_slot
        {I S FS pi} :
        SiteFunctional (inst_slots I) ->
        IsResolution I S FS pi ->
        forall n v k u, ParentRel.In (((n, v), k), u) pi ->
        parentsb (inst_fdefs I) (inst_slots I) (inst_root I) S FS (n, v) k
          = true ->
        exists d, SlotRel.In ((n, v), d) (inst_slots I) /\ sSite d = k /\
          slotActive (inst_root I) (n, v) d = true /\
          VSet.In u (evalReq (inst_real I) (sName d) (sRange d)) /\
          PkgSet.In (sName d, u) S /\
          FSet.Subset (slotRequests d (inst_default I)) (fsAt FS (sName d, u)).
    Proof.
      intros Hsite Hres n v k u Hpi Eb.
      apply parentsb_iff in Eb; destruct Eb as [HS [d [Hd [<- [Hact Hreq]]]]].
      destruct (parent_pick Hres n v d HS Hd Hact Hreq)
        as [u0 [Hpi0 [_ [Hu0 [Hname Hsub]]]]].
      rewrite (res_pi_functional Hres Hpi Hpi0).
      exists d; repeat split; assumption.
    Qed.

    Theorem cargo_completeness :
      forall I S FS pi,
        SiteFunctional (inst_slots I) ->
        IsResolution I S FS pi ->
        Reduced.IsResolution (reduceReal I) (reduceDeps I) rootPkg
          (coreResolution I S FS pi).
    Proof.
      intros [R Slots FDefs Links support g dflt [rn rv] rootFeats]
        S FS pi Hsite Hres.
      assert (HfsAt := fsAt_mem Hres).
      assert (Hpick := parent_pick Hres).
      assert (Hslot := parent_slot Hsite Hres).
      cbn [inst_real inst_support inst_fdefs inst_slots inst_links inst_gran
           inst_default inst_root inst_rootFeats] in Hsite, Hpick, Hslot.
      destruct Hres as [Hsub Hroot Hclass Hslotc [Hfsame Hfdep] Hlinks
        Hdom Htot Hfun Hrootf Hsupp Hpifun _].
      cbn [inst_real inst_support inst_fdefs inst_slots inst_links inst_gran
           inst_default inst_root inst_rootFeats] in *.
      constructor.
      - intros [m v'] Hx; apply core_shape in Hx; apply real_shape.
        destruct m as [| n w | n f w | n w d | n w f d f' | l];
          cbn beta iota in Hx |- *.
        + exact Hx.
        + destruct Hx as [v [-> [HS ->]]]; exists v.
          repeat split; exact (Hsub _ HS).
        + destruct Hx as [v [fs [-> [Hfs [Hf ->]]]]]; exists v.
          repeat split; exact (Hsupp _ _ _ Hfs Hf).
        + destruct Hx as [v [u [-> [-> [Hpi [Eb [Hd Hact]]]]]]].
          destruct (Hslot _ _ _ _ Hpi Eb) as [d' [Hd' [Ha' [_ [Hu _]]]]].
          rewrite (Hsite (n, v) d' d Hd' Hd Ha') in Hu.
          split; [exists v | exists u]; auto.
        + destruct Hx
            as [v [u [e [-> [-> [Hpi [Eb [Hd [Hact [Hf [Ee _]]]]]]]]]]].
          destruct (Hslot _ _ _ _ Hpi Eb) as [d' [Hd' [Ha' [_ [Hu _]]]]].
          rewrite (Hsite (n, v) d' d Hd' Hd Ha') in Hu.
          split; [exists v, e; repeat split; assumption | exists u; auto].
        + destruct Hx as [n [v [-> [Hl HS]]]]; exists n, v.
          repeat split; [exact Hl | exact (Hsub _ HS)].
      - apply mem_coreResolution; left; reflexivity.
      - intros p Hp m vs Hed.
        apply mem_reduceDeps in Hed; destruct Hed as [_ Hh].
        destruct p as [[| n w | n f w | n w1 d | n w1 f d f' | l]
                       [| v0 | w0 | q]];
          try (rewrite dep_inert in Hh by exact I;
               exfalso; exact (Reduced.DependeesSet.empty_spec Hh)).
        + apply mem_dep_root in Hh.
          destruct Hh as [He | [f [Hf He]]]; injection He as E1 E2;
            subst m vs; exists (VPlus.WOrig rv);
            (split; [apply Reduced.VSet.singleton_spec; reflexivity |]);
            apply core_shape.
          * exists rv; repeat split; exact Hroot.
          * exists rv, (fsAt FS (rn, rv)); repeat split;
              [exact (HfsAt _ Hroot) | exact (Hrootf _ (HfsAt _ Hroot) f Hf)].
        + apply mem_dep_gran in Hh.
          apply core_shape in Hp; cbn beta iota in Hp.
          destruct Hp as [v1 [Ev [HS ->]]]; injection Ev as Ev; subst v1.
          destruct Hh
            as [[d [Hd [Hact [Hopt He]]]] | [l [Hl He]]];
            injection He as E1 E2; subst m vs.
          * destruct (Hpick _ _ _ HS Hd Hact (or_introl Hopt))
              as [u [Hpi [Eb [Hu [Hname Hss]]]]].
            exists (VPlus.WClass (g u)); split.
            { apply mem_gransOf; exists u; split;
                [exact Hu | reflexivity]. }
            apply core_shape; exists v0, u; repeat split; assumption.
          * exists (VPlus.WName (NPlus.CGran n (g v0))); split;
              [apply Reduced.VSet.singleton_spec; reflexivity |].
            apply core_shape; exists n, v0; repeat split; assumption.
        + apply mem_dep_featP in Hh.
          apply core_shape in Hp; cbn beta iota in Hp.
          destruct Hp as [v1 [fs [Ev [Hfs [Hf _]]]]].
          injection Ev as Ev; subst v1.
          assert (Efs : fsAt FS (n, v0) = fs)
            by exact (fsAt_in FS (n, v0) fs Hfun Hfs).
          assert (HS : PkgSet.In (n, v0) S) by exact (Hdom _ _ Hfs).
          destruct Hh as [He | [e0 [Hfd Hcase]]].
          * injection He as E1 E2; subst m vs.
            exists (VPlus.WOrig v0); split;
              [apply Reduced.VSet.singleton_spec; reflexivity |].
            apply core_shape; exists v0; repeat split; exact HS.
          * destruct Hcase as [[f1 [Ee He]] | [Hcase | Hcase]].
            -- injection He as E1 E2; subst m vs e0.
               exists (VPlus.WOrig v0); split;
                 [apply Reduced.VSet.singleton_spec; reflexivity |].
               apply core_shape; exists v0, fs; repeat split;
                 [exact Hfs | exact (Hfsame _ _ _ _ Hfs Hf Hfd)].
            -- destruct Hcase as [a [d [Ea [Hd [Ha [Hact He]]]]]]; subst a.
               injection He as E1 E2; subst m vs.
               assert (Hactd : Activated FDefs (fsAt FS (n, v0)) (n, v0)
                   (sAlias d)).
               { rewrite Efs; exists f; split; [exact Hf |].
                 destruct e0 as [f0 | a0 | a0 feat0 | a0 feat0];
                   cbn [entryActivates] in Ea; try discriminate;
                   injection Ea as Ea; subst a0; eauto. }
               destruct (Hpick _ _ _ HS Hd Hact (or_intror Hactd))
                 as [u [Hpi [Eb [Hu [Hname Hss]]]]].
               exists (VPlus.WClass (g u)); split.
               { apply mem_gransOf; exists u; split;
                   [exact Hu | reflexivity]. }
               apply core_shape; exists v0, u; repeat split; assumption.
            -- destruct Hcase as [a [f' [d [Ea [Hd [Ha [Hact He]]]]]]];
                 subst a.
               injection He as E1 E2; subst m vs.
               assert (Hactd : Activated FDefs (fsAt FS (n, v0)) (n, v0)
                   (sAlias d)).
               { rewrite Efs; exists f; split; [exact Hf |].
                 destruct e0 as [f0 | a0 | a0 feat0 | a0 feat0];
                   cbn [entryFeatD] in Ea; try discriminate;
                   injection Ea as Ea1 Ea2; subst a0 feat0; eauto. }
               destruct (Hpick _ _ _ HS Hd Hact (or_intror Hactd))
                 as [u [Hpi [Eb [Hu [Hname Hss]]]]].
               exists (VPlus.WClass (g u)); split.
               { apply mem_gransOf; exists u; split;
                   [exact Hu | reflexivity]. }
               apply core_shape; exists v0, u, e0; repeat split;
                 try assumption.
               rewrite Efs; exact Hf.
        + apply mem_dep_slot in Hh; rename Hh into Hcase.
          apply core_shape in Hp; cbn beta iota in Hp.
          destruct Hp as [v [u [Eu [Egr [Hpi [Eb [Hd Hact]]]]]]].
          injection Eu as ->.
          destruct (Hslot _ _ _ _ Hpi Eb)
            as [d' [Hd' [Ha' [Hact' [Hu' [Hname Hss]]]]]].
          assert (Ed : d' = d) by exact (Hsite (n, v) d' d Hd' Hd Ha').
          subst d'.
          destruct Hcase as [He | [f0 [Hf0 He]]]; injection He as E1 E2;
            subst m vs; exists (VPlus.WOrig u);
            (split; [apply mem_inGran; exists u; auto |]); apply core_shape.
          * exists u; repeat split; assumption.
          * exists u, (fsAt FS (sName d, u)); repeat split; try assumption;
              [exact (HfsAt _ Hname) | exact (Hss _ Hf0)].
        + apply mem_dep_dec in Hh; rename Hh into Hcase.
          apply core_shape in Hp; cbn beta iota in Hp.
          destruct Hp as [v [u [e [Eu [Egr [Hpi [Eb [Hd [Hact
            [Hfd2 [Ee2 Hf]]]]]]]]]]].
          injection Eu as ->; subst w1.
          assert (HSnv : PkgSet.In (n, v) S)
            by (apply parentsb_iff in Eb; exact (proj1 Eb)).
          destruct (Hslot _ _ _ _ Hpi Eb)
            as [d' [Hd' [Ha' [Hact' [Hu' [Hname Hss]]]]]].
          assert (Ed : d' = d) by exact (Hsite (n, v) d' d Hd' Hd Ha').
          subst d'.
          destruct Hcase as [He | He]; injection He as E1 E2; subst m vs.
          * exists (VPlus.WClass (g u)); split;
              [apply Reduced.VSet.singleton_spec; reflexivity |].
            apply core_shape; exists v, u; repeat split; assumption.
          * exists (VPlus.WOrig u); split; [apply mem_inGran; exists u; auto |].
            apply core_shape; exists u, (fsAt FS (sName d, u));
              repeat split; try assumption; [exact (HfsAt _ Hname) |].
            assert (Hor :
                FDefRel.In (((n, v), f), FEntry.EDepFeat (sAlias d) f')
                  FDefs \/
                FDefRel.In (((n, v), f), FEntry.EWeakFeat (sAlias d) f')
                  FDefs).
            { destruct e as [f0 | a0 | a0 feat0 | a0 feat0];
                cbn [entryFeatD] in Ee2; try discriminate;
                injection Ee2 as Ee1 Ee3; subst a0 feat0;
                [left | right]; exact Hfd2. }
            exact (Hfdep (n, v) (fsAt FS (n, v)) f (sAlias d) f'
                     (HfsAt _ HSnv) Hf Hor d u Hd eq_refl Hpi
                     (fsAt FS (sName d, u)) (HfsAt _ Hname)).
      - intros m w1 w2 Hw Hw'.
        apply core_shape in Hw; apply core_shape in Hw'.
        destruct m as [ | n w | n f w | n w d | n w f d f' | l ];
          cbn [inst_gran inst_fdefs inst_slots inst_root inst_links] in Hw, Hw'.
        + subst w1 w2; reflexivity.
        + destruct Hw as [v [-> [HS Eg]]];
            destruct Hw' as [v' [-> [HS' Eg']]].
          destruct (V.eq_dec v v') as [E | NE];
            [rewrite E; reflexivity |].
          exfalso; apply (Hclass n v v' HS HS' NE); congruence.
        + destruct Hw as [v [fs [-> [Hfs [Hf Eg]]]]];
            destruct Hw' as [v' [fs' [-> [Hfs' [Hf' Eg']]]]].
          destruct (V.eq_dec v v') as [E | NE];
            [rewrite E; reflexivity |].
          exfalso; apply (Hclass n v v' (Hdom _ _ Hfs) (Hdom _ _ Hfs') NE);
            congruence.
        + destruct Hw as [v [u [-> [Egr [Hpi [Eb _]]]]]];
            destruct Hw' as [v' [u' [-> [Egr' [Hpi' [Eb' _]]]]]].
          apply parentsb_iff in Eb; apply parentsb_iff in Eb'.
          destruct (V.eq_dec v v') as [<- | NE];
            [| exfalso; apply (Hclass n v v' (proj1 Eb) (proj1 Eb') NE);
               congruence].
          rewrite (Hpifun (n, v) (sSite d) u u' Hpi Hpi'); reflexivity.
        + destruct Hw as [v [u [e [-> [Egr [Hpi [Eb _]]]]]]];
            destruct Hw' as [v' [u' [e' [-> [Egr' [Hpi' [Eb' _]]]]]]].
          apply parentsb_iff in Eb; apply parentsb_iff in Eb'.
          destruct (V.eq_dec v v') as [<- | NE];
            [| exfalso; apply (Hclass n v v' (proj1 Eb) (proj1 Eb') NE);
               congruence].
          rewrite (Hpifun (n, v) (sSite d) u u' Hpi Hpi'); reflexivity.
        + destruct Hw as [n [v [-> [Hl HS]]]];
            destruct Hw' as [n' [v' [-> [Hl' HS']]]].
          assert (E := Hlinks (n, v) (n', v') l HS HS' Hl Hl').
          injection E as <- <-; reflexivity.
    Qed.

    Module Lookup.
      Theorem versions_reduceRealRoot :
        forall I v,
          Reduced.PkgSet.In (NPlus.CRoot, v)
            (reduceReal I) <->
          Reduced.VSet.In v
            (versions I NPlus.CRoot).
      Proof.
        intros; rewrite real_shape; cbn [versions].
        rewrite Reduced.VSet.singleton_spec; reflexivity.
      Qed.

      Theorem versions_reduceRealGranular :
        forall I n w v,
          Reduced.PkgSet.In (NPlus.CGran n w, v)
            (reduceReal I) <->
          Reduced.VSet.In v
            (versions I
               (NPlus.CGran n w)).
      Proof.
        intros I n w u; rewrite real_shape; cbn [versions].
        rewrite SOpv2.mem_filterMap; split.
        - intros [v [-> [HR ->]]]; exists (n, v); split; [exact HR |].
          cbn beta iota; rewrite NEqb.eqb_refl, GEqb.eqb_refl; reflexivity.
        - intros [[n' v] [HR He]]; cbn beta iota in He.
          rewrite if_some_iff, andb_true_iff, NEqb.eqb_true_iff,
            GEqb.eqb_true_iff
            in He.
          destruct He as [[-> <-] <-]; exists v; auto.
      Qed.

      Theorem versions_reduceRealFeatP :
        forall I n f w v,
          Reduced.PkgSet.In (NPlus.CFeatP n f w, v)
            (reduceReal I) <->
          Reduced.VSet.In v
            (versions I
               (NPlus.CFeatP n f w)).
      Proof.
        intros I n f w u; rewrite real_shape; cbn [versions].
        rewrite SOspv.mem_filterMap; split.
        - intros [v [-> [Hs ->]]]; exists ((n, v), f); split; [exact Hs |].
          cbn beta iota; rewrite NEqb.eqb_refl, FEqb.eqb_refl, GEqb.eqb_refl;
            reflexivity.
        - intros [[[n' v] f'] [Hs He]]; cbn beta iota in He.
          rewrite if_some_iff, !andb_true_iff, NEqb.eqb_true_iff,
            FEqb.eqb_true_iff, GEqb.eqb_true_iff in He.
          destruct He as [[[-> ->] <-] <-]; exists v; auto.
      Qed.

      Theorem versions_reduceRealSlot :
        forall I n w d v,
          SlotOwned (inst_gran I) (inst_slots I) (inst_root I) n w d ->
          Reduced.PkgSet.In (NPlus.CSlot n w d, v)
            (reduceReal I) <->
          Reduced.VSet.In v
            (versions I
               (NPlus.CSlot n w d)).
      Proof.
        intros I n w d v Ho; rewrite real_shape; cbn [versions].
        rewrite mem_gransOf; tauto.
      Qed.

      Theorem versions_reduceRealDecision :
        forall I n w f d f' v,
          DecOwned (inst_gran I) (inst_fdefs I) (inst_slots I) (inst_root I)
            n w f d f' ->
          Reduced.PkgSet.In (NPlus.CDec n w f d f', v)
            (reduceReal I) <->
          Reduced.VSet.In v
            (versions I
               (NPlus.CDec n w f d f')).
      Proof.
        intros I n w f d f' v Ho; rewrite real_shape; cbn [versions].
        rewrite mem_gransOf; tauto.
      Qed.

      Theorem versions_reduceRealCls :
        forall I l v,
          Reduced.PkgSet.In (NPlus.CCls l, v)
            (reduceReal I) <->
          Reduced.VSet.In v
            (versions I
               (NPlus.CCls l)).
      Proof. intros; rewrite real_shape, mem_versions_cls; reflexivity. Qed.

      Theorem dependees_reduceDeps :
        forall I p,
          Reduced.PkgSet.In p (reduceReal I) ->
          dependees I p =
          Reduced.dependees
            (reduceDeps I) p.
      Proof.
        intros I p Hp; apply Reduced.DependeesSet.ext; intro h.
        rewrite Reduced.mem_dependees, mem_reduceDeps; tauto.
      Qed.

      Theorem dependees_reduceDepsInert :
        forall I p,
          Inert p ->
          dependees I p =
          Reduced.dependees
            (reduceDeps I) p.
      Proof.
        intros I p Hi; apply Reduced.DependeesSet.ext; intro h.
        rewrite Reduced.mem_dependees, mem_reduceDeps, dep_inert by exact Hi.
        split; [intro Hh; destruct (Reduced.DependeesSet.empty_spec Hh) |].
        intros [_ Hh]; exact Hh.
      Qed.

      Module NSet := Source.NSet.
      Module FDefPre := Preimage FDefElt FDefRel.
      Module SlotFibred := FibredRel Pkg SlotData SlotElt SlotRel.
      Module LinkFibred := FibredRel Pkg N LinkElt LinkRel.
      Module SupportFibred := FibredRel Pkg F PkgF SupportSet.
      Module SOsn := SetOps SlotElt N SlotRel NSet.

      Definition supportAt (support : SupportSet.t) (n : N.t) (f : F.t)
        : SupportSet.t :=
        SupportSet.filter (fun '((m, _), f') =>
            andb (NEqb.eqb m n) (FEqb.eqb f' f))
          support.

      Definition fdefFibre (FDefs : FDefRel.t) (p : Pkg.t) : FDefRel.t :=
        FDefPre.preimage (fun x => fst (fst x)) (fun q => PkgEqb.eqb q p) FDefs.

      Definition reads (Slots : SlotRel.t) (p : Pkg.t) : NSet.t :=
        NSet.add (fst p)
          (SOsn.map (fun x => sName (snd x)) (SlotFibred.tailFibre Slots p)).

      Definition claimants (R : PkgSet.t) (Links : LinkRel.t) (l : N.t)
        : PkgSet.t :=
        PkgSet.filter (fun q => LinkRel.mem (q, l) Links) R.

      Lemma evalReq_namePreimage : forall R ns m rg,
          NSet.In m ns ->
          evalReq (Source.namePreimage R ns) m rg = evalReq R m rg.
      Proof.
        intros R ns m rg Hm; apply VSet.ext; intro u.
        rewrite !mem_evalReq, Source.mem_namePreimage; cbn [fst]; tauto.
      Qed.

      Lemma mem_supportAt : forall support n f m v f',
          SupportSet.In ((m, v), f') (supportAt support n f) <->
          SupportSet.In ((m, v), f') support /\ m = n /\ f' = f.
      Proof.
        intros; unfold supportAt; rewrite SupportSet.filter_spec';
          cbn beta iota.
        rewrite andb_true_iff, NEqb.eqb_true_iff, FEqb.eqb_true_iff;
          reflexivity.
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

      Lemma reads_name : forall Slots p d,
          SlotRel.In (p, d) Slots -> NSet.In (sName d) (reads Slots p).
      Proof.
        intros Slots p d Hs; unfold reads; apply NSet.add_spec; right.
        apply SOsn.mem_map; exists (p, d); split; [| reflexivity].
        apply SlotFibred.mem_tailFibre; split; [exact Hs | reflexivity].
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

      Lemma in_fdefFibre : forall FDefs p f e,
          FDefRel.In ((p, f), e) FDefs <->
          FDefRel.In ((p, f), e) (fdefFibre FDefs p).
      Proof.
        intros; rewrite mem_fdefFibre; split;
          [intro H; split; [exact H | reflexivity] | intros [H _]; exact H].
      Qed.

      Theorem versions_lookupRoot :
        forall I,
          versions I NPlus.CRoot =
          versions
            (MkInst PkgSet.empty SlotRel.empty FDefRel.empty LinkRel.empty
               SupportSet.empty (inst_gran I) (inst_default I) (inst_root I)
               (inst_rootFeats I))
            NPlus.CRoot.
      Proof. reflexivity. Qed.

      Theorem versions_lookupGranular :
        forall I n w,
          versions I (NPlus.CGran n w) =
          versions
            (MkInst (Source.namePreimage (inst_real I) (NSet.singleton n))
               SlotRel.empty FDefRel.empty LinkRel.empty SupportSet.empty
               (inst_gran I) (inst_default I) (inst_root I) (inst_rootFeats I))
            (NPlus.CGran n w).
      Proof.
        intros; cbn [versions inst_real inst_gran];
          apply Reduced.VSet.ext; intro u; symmetry.
        apply SOpv2.filterMap_restrict; [apply Source.PkgPreimage.ofKeys_subset |].
        intros [n' v] HR He; cbn beta iota in He.
        rewrite if_some_iff, andb_true_iff, NEqb.eqb_true_iff in He.
        destruct He as [[-> _] _]; apply Source.mem_namePreimage; split;
          [exact HR | apply NSet.singleton_spec; reflexivity].
      Qed.

      Theorem versions_lookupFeatP :
        forall I n f w,
          versions I (NPlus.CFeatP n f w) =
          versions
            (MkInst (Source.namePreimage (inst_real I) (NSet.singleton n))
               SlotRel.empty FDefRel.empty LinkRel.empty
               (supportAt (inst_support I) n f)
               (inst_gran I) (inst_default I) (inst_root I) (inst_rootFeats I))
            (NPlus.CFeatP n f w).
      Proof.
        intros; cbn [versions inst_support inst_gran];
          apply Reduced.VSet.ext; intro u; symmetry.
        apply SOspv.filterMap_restrict.
        - intros [[m v] f'] Hs; apply mem_supportAt in Hs; exact (proj1 Hs).
        - intros [[n' v] f'] Hs He; cbn beta iota in He.
          rewrite if_some_iff, !andb_true_iff, NEqb.eqb_true_iff,
            FEqb.eqb_true_iff in He.
          destruct He as [[[-> ->] _] _]; apply mem_supportAt; auto.
      Qed.

      Theorem versions_lookupSlot :
        forall I n w d,
          versions I (NPlus.CSlot n w d) =
          versions
            (MkInst (Source.namePreimage (inst_real I) (NSet.singleton (sName d)))
               SlotRel.empty FDefRel.empty LinkRel.empty SupportSet.empty
               (inst_gran I) (inst_default I) (inst_root I) (inst_rootFeats I))
            (NPlus.CSlot n w d).
      Proof.
        intros I n w d; cbn [versions inst_real inst_gran].
        rewrite evalReq_namePreimage;
          [reflexivity | apply NSet.singleton_spec; reflexivity].
      Qed.

      Theorem versions_lookupDecision :
        forall I n w f d f',
          versions I (NPlus.CDec n w f d f') =
          versions
            (MkInst (Source.namePreimage (inst_real I) (NSet.singleton (sName d)))
               SlotRel.empty FDefRel.empty LinkRel.empty SupportSet.empty
               (inst_gran I) (inst_default I) (inst_root I) (inst_rootFeats I))
            (NPlus.CDec n w f d f').
      Proof.
        intros I n w f d f'; cbn [versions inst_real inst_gran].
        rewrite evalReq_namePreimage;
          [reflexivity | apply NSet.singleton_spec; reflexivity].
      Qed.

      Lemma granReal_claimants : forall g R Links l,
          granReal g (claimants R Links l) =
          ClsT.Reduction.Lookup.inClass (granReal g R) (linkRel g Links)
            (NPlus.CCls l).
      Proof.
        intros; apply Reduced.PkgSet.ext; intro x.
        rewrite ClsT.Reduction.Lookup.mem_inClass, !mem_granReal.
        split.
        - intros [n [v [Hc ->]]]; apply mem_claimants in Hc.
          destruct Hc as [HR Hl]; split.
          + exists n, v; split; [exact HR | reflexivity].
          + apply mem_linkRel; exists n, v, l; repeat split; exact Hl.
        - intros [[n [v [HR ->]]] Hc].
          apply mem_linkRel in Hc; destruct Hc as [n' [v' [l' [Hl [E Ek]]]]].
          injection E as E1 _ E3; subst n' v'; injection Ek as <-.
          exists n, v; split; [apply mem_claimants; split; assumption
                              | reflexivity].
      Qed.

      Lemma linkRel_headFibre : forall g Links l,
          linkRel g (LinkFibred.headFibre Links l) =
          ClsT.Reduction.Lookup.classRelAt (linkRel g Links) (NPlus.CCls l).
      Proof.
        intros; apply ClsT.InClassRel.ext; intros [q k].
        rewrite ClsT.Reduction.Lookup.mem_classRelAt, !mem_linkRel.
        split.
        - intros [n [v [l' [Hl [-> ->]]]]].
          apply LinkFibred.mem_headFibre in Hl; destruct Hl as [Hl ->].
          split; [exists n, v, l; repeat split; exact Hl | reflexivity].
        - intros [[n [v [l' [Hl [-> ->]]]]] Ek]; injection Ek as ->.
          exists n, v, l; repeat split.
          apply LinkFibred.mem_headFibre; split; [exact Hl | reflexivity].
      Qed.

      Theorem versions_lookupCls :
        forall I l,
          versions I (NPlus.CCls l) =
          versions
            (MkInst (claimants (inst_real I) (inst_links I) l) SlotRel.empty
               FDefRel.empty (LinkFibred.headFibre (inst_links I) l)
               SupportSet.empty
               (inst_gran I) (inst_default I) (inst_root I) (inst_rootFeats I))
            (NPlus.CCls l).
      Proof.
        intros; apply Reduced.VSet.ext; intro w.
        rewrite !versions_cls_reduceReal; cbn [inst_real inst_links inst_gran].
        rewrite granReal_claimants,
          linkRel_headFibre, <- ClsT.Reduction.Lookup.versions_lookupClass.
        reflexivity.
      Qed.

      Lemma versions_cls_mono : forall I' I l,
          PkgSet.Subset (inst_real I') (inst_real I) ->
          LinkRel.Subset (inst_links I') (inst_links I) ->
          (forall v, inst_gran I' v = inst_gran I v) ->
          Reduced.VSet.Subset (versions I' (NPlus.CCls l))
            (versions I (NPlus.CCls l)).
      Proof.
        intros I' I l HR HL Hg w; rewrite !mem_versions_cls.
        intros [n [v [-> [Hl Hv]]]]; exists n, v.
        rewrite Hg; split; [reflexivity |].
        split; [exact (HL _ Hl) | exact (HR _ Hv)].
      Qed.

      Lemma dep_gran_mono :
        forall Vq Vq' g R R' support support' FDefs FDefs' Slots Slots' Links
               Links' dflt r rootFeats rootFeats' n w v,
          (forall d, SlotRel.In ((n, v), d) Slots ->
             SlotRel.In ((n, v), d) Slots') ->
          (forall d, SlotRel.In ((n, v), d) Slots ->
             evalReqBy Vq (sName d) (sRange d) =
             evalReqBy Vq' (sName d) (sRange d)) ->
          (forall l, LinkRel.In ((n, v), l) Links ->
             LinkRel.In ((n, v), l) Links') ->
          forall h,
            Reduced.DependeesSet.In h
              (dependeesBy Vq
                 (MkInst R Slots FDefs Links support g dflt r rootFeats)
                 (NPlus.CGran n w, VPlus.WOrig v)) ->
            Reduced.DependeesSet.In h
              (dependeesBy Vq'
                 (MkInst R' Slots' FDefs' Links' support' g dflt r rootFeats')
                 (NPlus.CGran n w, VPlus.WOrig v)).
      Proof.
        intros * HS Hev HL h Hh.
        apply mem_depBy_gran in Hh; apply mem_depBy_gran.
        cbn [inst_slots inst_links inst_gran inst_root] in Hh |- *.
        destruct Hh as [[d [Hd [Ha [Ho ->]]]] | [l [Hl ->]]].
        - left; exists d; rewrite <- (Hev d Hd).
          split; [exact (HS d Hd) | split; [exact Ha | split; [exact Ho | reflexivity]]].
        - right; exists l; split; [exact (HL l Hl) | reflexivity].
      Qed.

      Lemma dep_featP_mono :
        forall Vq Vq' g R R' support support' FDefs FDefs' Slots Slots' Links
               Links' dflt r rootFeats rootFeats' n f w v,
          (forall d, SlotRel.In ((n, v), d) Slots ->
             SlotRel.In ((n, v), d) Slots') ->
          (forall d, SlotRel.In ((n, v), d) Slots ->
             evalReqBy Vq (sName d) (sRange d) =
             evalReqBy Vq' (sName d) (sRange d)) ->
          (forall e, FDefRel.In (((n, v), f), e) FDefs ->
             FDefRel.In (((n, v), f), e) FDefs') ->
          forall h,
            Reduced.DependeesSet.In h
              (dependeesBy Vq
                 (MkInst R Slots FDefs Links support g dflt r rootFeats)
                 (NPlus.CFeatP n f w, VPlus.WOrig v)) ->
            Reduced.DependeesSet.In h
              (dependeesBy Vq'
                 (MkInst R' Slots' FDefs' Links' support' g dflt r rootFeats')
                 (NPlus.CFeatP n f w, VPlus.WOrig v)).
      Proof.
        intros * HS Hev HF h Hh.
        apply mem_depBy_featP in Hh; apply mem_depBy_featP.
        cbn [inst_support inst_fdefs inst_slots inst_gran inst_root] in Hh |- *.
        destruct Hh as [Hh | [e0 [Hfd Hc]]]; [left; exact Hh | right].
        exists e0; split; [exact (HF e0 Hfd) |].
        destruct Hc as [[f0 [He ->]] | [[a [d [Ha [Hd [Hal [Hact ->]]]]]]
                                      | [a
                                          [f' [d [Ha [Hd [Hal [Hact ->]]]]]]]]].
        - left; exists f0; split; [exact He | reflexivity].
        - right; left; exists a, d; rewrite <- (Hev d Hd).
          split; [exact Ha | split; [exact (HS d Hd) |
            split; [exact Hal | split; [exact Hact | reflexivity]]]].
        - right; right; exists a, f', d; rewrite <- (Hev d Hd).
          split; [exact Ha | split; [exact (HS d Hd) |
            split; [exact Hal | split; [exact Hact | reflexivity]]]].
      Qed.

      Lemma dep_gran_agree :
        forall Vq Vq' g R R' support support' FDefs FDefs' Slots Slots' Links
               Links' dflt r rootFeats rootFeats' n w v,
          (forall d, SlotRel.In ((n, v), d) Slots <->
             SlotRel.In ((n, v), d) Slots') ->
          (forall d, SlotRel.In ((n, v), d) Slots ->
             evalReqBy Vq (sName d) (sRange d) =
             evalReqBy Vq' (sName d) (sRange d)) ->
          (forall l, LinkRel.In ((n, v), l) Links <->
             LinkRel.In ((n, v), l) Links') ->
          dependeesBy Vq (MkInst R Slots FDefs Links support g dflt r rootFeats)
            (NPlus.CGran n w, VPlus.WOrig v) =
          dependeesBy Vq'
            (MkInst R' Slots' FDefs' Links' support' g dflt r rootFeats')
            (NPlus.CGran n w, VPlus.WOrig v).
      Proof.
        intros * HS Hev HL; apply Reduced.DependeesSet.ext; intro h; split.
        - apply dep_gran_mono;
            [intros d Hd; apply HS; exact Hd | exact Hev
             | intros l Hl; apply HL; exact Hl].
        - apply dep_gran_mono;
            [intros d Hd; apply HS; exact Hd
             | intros d Hd; symmetry; apply Hev; apply HS; exact Hd
             | intros l Hl; apply HL; exact Hl].
      Qed.

      Lemma dep_featP_agree :
        forall Vq Vq' g R R' support support' FDefs FDefs' Slots Slots' Links
               Links' dflt r rootFeats rootFeats' n f w v,
          (forall d, SlotRel.In ((n, v), d) Slots <->
             SlotRel.In ((n, v), d) Slots') ->
          (forall d, SlotRel.In ((n, v), d) Slots ->
             evalReqBy Vq (sName d) (sRange d) =
             evalReqBy Vq' (sName d) (sRange d)) ->
          (forall e, FDefRel.In (((n, v), f), e) FDefs <->
             FDefRel.In (((n, v), f), e) FDefs') ->
          dependeesBy Vq (MkInst R Slots FDefs Links support g dflt r rootFeats)
            (NPlus.CFeatP n f w, VPlus.WOrig v) =
          dependeesBy Vq'
            (MkInst R' Slots' FDefs' Links' support' g dflt r rootFeats')
            (NPlus.CFeatP n f w, VPlus.WOrig v).
      Proof.
        intros * HS Hev HF; apply Reduced.DependeesSet.ext; intro h; split.
        - apply dep_featP_mono;
            [intros d Hd; apply HS; exact Hd | exact Hev
             | intros e He; apply HF; exact He].
        - apply dep_featP_mono;
            [intros d Hd; apply HS; exact Hd
             | intros d Hd; symmetry; apply Hev; apply HS; exact Hd
             | intros e He; apply HF; exact He].
      Qed.

      Lemma evalReqBy_reads : forall R Slots p d Vq,
          (forall m, NSet.In m (reads Slots p) -> Vq m = Source.versions R m) ->
          SlotRel.In (p, d) Slots ->
          evalReq R (sName d) (sRange d) = evalReqBy Vq (sName d) (sRange d).
      Proof.
        intros R Slots p d Vq HVq Hs; unfold evalReq, evalReqBy.
        rewrite (HVq (sName d)); [reflexivity | apply reads_name; exact Hs].
      Qed.

      Theorem dependees_lookupRoot :
        forall I Vq,
          dependees I rootPkg =
          dependeesBy Vq
            (MkInst PkgSet.empty SlotRel.empty FDefRel.empty LinkRel.empty
               SupportSet.empty (inst_gran I) (inst_default I) (inst_root I)
               (inst_rootFeats I))
            rootPkg.
      Proof. reflexivity. Qed.

      Theorem dependees_lookupGranular :
        forall I n w v Vq,
          (forall m, NSet.In m (reads (inst_slots I) (n, v)) ->
             Vq m = Source.versions (inst_real I) m) ->
          dependees I (NPlus.CGran n w, VPlus.WOrig v) =
          dependeesBy Vq
            (MkInst PkgSet.empty (SlotFibred.tailFibre (inst_slots I) (n, v))
               FDefRel.empty (LinkFibred.tailFibre (inst_links I) (n, v))
               SupportSet.empty
               (inst_gran I) (inst_default I) (inst_root I) (inst_rootFeats I))
            (NPlus.CGran n w, VPlus.WOrig v).
      Proof.
        intros [R Slots FDefs Links support g dflt r rootFeats] n w v Vq HVq.
        cbn [inst_real inst_slots inst_links inst_gran inst_default inst_root
             inst_rootFeats] in HVq |- *.
        unfold dependees; cbn [inst_real].
        apply dep_gran_agree;
          [intro d; apply in_slotFibre
           | intros d Hd; exact (evalReqBy_reads R Slots (n, v) d Vq HVq Hd)
           | intro l; apply in_linkFibre].
      Qed.

      Theorem dependees_lookupFeatP :
        forall I n f w v Vq,
          (forall m, NSet.In m (reads (inst_slots I) (n, v)) ->
             Vq m = Source.versions (inst_real I) m) ->
          dependees I (NPlus.CFeatP n f w, VPlus.WOrig v) =
          dependeesBy Vq
            (MkInst PkgSet.empty
               (SlotFibred.tailFibre (inst_slots I) (n, v))
               (fdefFibre (inst_fdefs I) (n, v)) LinkRel.empty
               (SupportFibred.tailFibre (inst_support I) (n, v))
               (inst_gran I) (inst_default I) (inst_root I) (inst_rootFeats I))
            (NPlus.CFeatP n f w, VPlus.WOrig v).
      Proof.
        intros [R Slots FDefs Links support g dflt r rootFeats] n f w v Vq HVq.
        cbn [inst_real inst_support inst_fdefs inst_slots inst_gran inst_default
             inst_root inst_rootFeats] in HVq |- *.
        unfold dependees; cbn [inst_real].
        apply dep_featP_agree;
          [intro d; apply in_slotFibre
           | intros d Hd; exact (evalReqBy_reads R Slots (n, v) d Vq HVq Hd)
           | intro e; apply in_fdefFibre].
      Qed.

      Theorem dependees_lookupSlot :
        forall I n w d w' Vq,
          Vq (sName d) = Source.versions (inst_real I) (sName d) ->
          dependees I (NPlus.CSlot n w d, VPlus.WClass w') =
          dependeesBy Vq
            (MkInst PkgSet.empty SlotRel.empty FDefRel.empty LinkRel.empty
               SupportSet.empty (inst_gran I) (inst_default I) (inst_root I)
               (inst_rootFeats I))
            (NPlus.CSlot n w d, VPlus.WClass w').
      Proof.
        intros I n w d w' Vq HVq.
        unfold dependees; cbn [dependeesBy inst_gran inst_default].
        unfold evalReqBy; rewrite HVq; reflexivity.
      Qed.

      Theorem dependees_lookupDecision :
        forall I n w f d f' w' Vq,
          Vq (sName d) = Source.versions (inst_real I) (sName d) ->
          dependees I (NPlus.CDec n w f d f', VPlus.WClass w') =
          dependeesBy Vq
            (MkInst PkgSet.empty SlotRel.empty FDefRel.empty LinkRel.empty
               SupportSet.empty (inst_gran I) (inst_default I) (inst_root I)
               (inst_rootFeats I))
            (NPlus.CDec n w f d f', VPlus.WClass w').
      Proof.
        intros I n w f d f' w' Vq HVq.
        unfold dependees; cbn [dependeesBy inst_gran].
        unfold evalReqBy; rewrite HVq; reflexivity.
      Qed.

    End Lookup.

    Lemma cargoResolution_coreResolution :
      forall I S FS pi,
        cargoResolution (coreResolution I S FS pi) = S.
    Proof.
      intros I S FS pi; apply PkgSet.ext; intros [n v].
      rewrite mem_cargoResolution; split.
      - intros [w Hin]; apply core_shape in Hin; cbn beta iota in Hin.
        destruct Hin as [v' [Ev [HS _]]]; injection Ev as <-; exact HS.
      - intro HS; exists (inst_gran I v); apply core_shape; exists v.
        repeat split; exact HS.
    Qed.

    Lemma featsAt_coreResolution
        {I S FS pi} :
        IsResolution I S FS pi ->
        forall p, PkgSet.In p S ->
        featsAt (coreResolution I S FS pi) p = fsAt FS p.
    Proof.
      intros Hres [n v] Hp.
      apply FSet.ext; intro f; rewrite mem_featsAt; split.
      - intros [w Hin]; apply core_shape in Hin; cbn beta iota in Hin.
        destruct Hin as [v' [fs [Ev [Hfs [Hf _]]]]]; injection Ev as <-.
        rewrite (fsAt_in FS (n, v) fs (res_fs_functional Hres) Hfs); exact Hf.
      - intro Hf; exists (inst_gran I v); apply core_shape;
          exists v, (fsAt FS (n, v)).
        repeat split; [exact (fsAt_mem Hres _ Hp) | exact Hf].
    Qed.

    Lemma features_coreResolution :
      forall I S FS pi,
        IsResolution I S FS pi ->
        features (coreResolution I S FS pi) = FS.
    Proof.
      intros I S FS pi Hres.
      apply FeaturedSet.ext; intros [p fs].
      rewrite mem_features, cargoResolution_coreResolution; split.
      - intros [Hp ->]; rewrite (featsAt_coreResolution Hres _ Hp).
        exact (fsAt_mem Hres _ Hp).
      - intro Hfs; assert (Hp := res_fs_dom Hres Hfs).
        split; [exact Hp |].
        rewrite (featsAt_coreResolution Hres _ Hp); symmetry.
        exact (fsAt_in FS p fs (res_fs_functional Hres) Hfs).
    Qed.

    Lemma parents_coreResolution_iff :
      forall I S FS pi,
        SiteFunctional (inst_slots I) ->
        IsResolution I S FS pi ->
        forall p k u,
          ParentRel.In ((p, k), u) (parents I (coreResolution I S FS pi))
          <-> ParentRel.In ((p, k), u) pi /\
              exists fs d, FeaturedSet.In (p, fs) FS /\
                SlotRel.In (p, d) (inst_slots I) /\
                sSite d = k /\ slotActive (inst_root I) p d = true /\
                (sOptional d = false \/
                 Activated (inst_fdefs I) fs p (sAlias d)).
    Proof.
      intros I S FS pi Hsite Hres [n v] k u.
      assert (Hslot := parent_slot Hsite Hres).
      rewrite mem_parents; split.
      - intros [w [w' [d [Hsl [Hown [Hd [<- [Hact [Hreq Hcr]]]]]]]]].
        apply core_shape in Hsl; cbn beta iota in Hsl.
        destruct Hsl as [v0 [u' [Eu [Egr [Hpi [Eb _]]]]]]; injection Eu as Eu.
        apply core_shape in Hown; cbn beta iota in Hown.
        destruct Hown as [v1 [Ev [HSv Egv]]]; injection Ev as <-.
        split.
        2:{ exists (fsAt FS (n, v)), d.
            split; [exact (fsAt_mem Hres _ HSv) |].
            split; [exact Hd | split; [reflexivity | split; [exact Hact |]]].
            rewrite (featsAt_coreResolution Hres _ HSv) in Hreq; exact Hreq. }
        assert (Hv0 : PkgSet.In (n, v0) S)
          by (apply parentsb_iff in Eb; exact (proj1 Eb)).
        assert (v0 = v).
        { destruct (V.eq_dec v0 v) as [E | NE]; [exact E |].
          exfalso; apply (res_class_unique Hres Hv0 HSv NE);
            congruence. }
        subst v0.
        destruct (Hslot _ _ _ _ Hpi Eb)
          as [d' [Hd' [Ha' [_ [_ [Hname' _]]]]]].
        assert (d' = d) by exact (Hsite (n, v) d' d Hd' Hd Ha').
        subst d'.
        apply core_shape in Hcr; cbn beta iota in Hcr.
        destruct Hcr as [u'' [Eu'' [Hname Eg]]]; injection Eu'' as <-.
        destruct (V.eq_dec u u') as [-> | NE]; [exact Hpi |].
        exfalso; apply (res_class_unique Hres Hname Hname' NE);
          congruence.
      - intros [Hpi [fs [d [Hfs [Hd [<- [Hact Hreq]]]]]]].
        assert (HS := res_fs_dom Hres Hfs).
        rewrite <- (fsAt_in FS (n, v) fs (res_fs_functional Hres) Hfs) in Hreq.
        assert (Eb : parentsb (inst_fdefs I) (inst_slots I) (inst_root I) S FS
                       (n, v) (sSite d) = true).
        { apply parentsb_iff; split; [exact HS |].
          exists d; repeat split; assumption. }
        destruct (Hslot _ _ _ _ Hpi Eb)
          as [d' [Hd' [Ha' [_ [_ [Hname _]]]]]].
        assert (d' = d) by exact (Hsite (n, v) d' d Hd' Hd Ha').
        subst d'.
        exists (inst_gran I v), (inst_gran I u), d; repeat split;
          try assumption;
          [| | rewrite (featsAt_coreResolution Hres _ HS); exact Hreq |];
          apply core_shape.
        + exists v, u; repeat split; assumption.
        + exists v; repeat split; exact HS.
        + exists u; repeat split; exact Hname.
    Qed.

    Theorem cargo_retraction :
      forall I S FS pi,
        SiteFunctional (inst_slots I) ->
        IsResolution I S FS pi -> ParentDependency I FS pi ->
        cargoResolution (coreResolution I S FS pi) = S /\
        features (coreResolution I S FS pi) = FS /\
        parents I (coreResolution I S FS pi) = pi.
    Proof.
      intros I S FS pi Hsite Hres Hdep.
      split; [apply cargoResolution_coreResolution |].
      split; [exact (features_coreResolution _ _ _ _ Hres) |].
      apply ParentRel.ext; intros [[p k] u].
      rewrite (parents_coreResolution_iff _ _ _ _ Hsite Hres).
      split; [intros [H _]; exact H | intro H; exact (conj H (Hdep _ _ _ H))].
    Qed.
  End Reduction.
End Cargo.
