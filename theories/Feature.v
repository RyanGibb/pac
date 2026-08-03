From Stdlib Require Import MSets.
From PackageCalculus Require Import Prelude Core.

Create HintDb cmp_feat.
Create Rewrite HintDb cmp_feat.

Module Feature (N V F : UsualOrderedType).
  Module C := Core N V.
  Module Pkg := C.Pkg.
  Module PkgSet := C.PkgSet.
  Module VSet := C.VSet.

  Module FSet := FSetUOT F.

  Module Featured := PairUOT Pkg FSet.AsUOT.
  Module FeaturedSet := FSetUOT Featured.

  Module PkgF := PairUOT Pkg F.
  Module SupportSet := FSetUOT PkgF.

  Module VSFS := PairUOT VSet.AsUOT FSet.AsUOT.
  Module Dependees := PairUOT N VSFS.
  Module FeatDepElt := PairUOT Pkg Dependees.
  Module FeatDepRel := FSetUOT FeatDepElt.

  Module AddlDepElt := PairUOT PkgF Dependees.
  Module AddlDepRel := FSetUOT AddlDepElt.

  Record IsResolution
      (R : PkgSet.t) (support : SupportSet.t)
      (Df : FeatDepRel.t) (Da : AddlDepRel.t)
      (r : Pkg.t) (S : FeaturedSet.t) : Prop :=
    { res_no_root_support : forall f, ~ SupportSet.In (r, f) support
    ; res_subset : forall p fs, FeaturedSet.In (p, fs) S -> PkgSet.In p R
    ; res_root_mem : FeaturedSet.In (r, FSet.empty) S
    ; res_dep_closure :
        forall p fs_p, FeaturedSet.In (p, fs_p) S ->
        forall n vs fs, FeatDepRel.In (p, (n, (vs, fs))) Df ->
        exists v, VSet.In v vs /\
          exists fs', FSet.Subset fs fs' /\ FeaturedSet.In ((n, v), fs') S
    ; res_addl_dep_closure :
        forall p fs_p, FeaturedSet.In (p, fs_p) S ->
        forall f, FSet.In f fs_p ->
        forall n vs fs, AddlDepRel.In ((p, f), (n, (vs, fs))) Da ->
        exists v, VSet.In v vs /\
          exists fs', FSet.Subset fs fs' /\ FeaturedSet.In ((n, v), fs') S
    ; res_feature_unification :
        forall n v v' fs fs',
          FeaturedSet.In ((n, v), fs) S ->
          FeaturedSet.In ((n, v'), fs') S -> fs = fs'
    ; res_version_unique :
        forall n v v' fs fs',
          FeaturedSet.In ((n, v), fs) S ->
          FeaturedSet.In ((n, v'), fs') S -> v = v'
    ; res_support_mem :
        forall n v fs f,
          FeaturedSet.In ((n, v), fs) S -> FSet.In f fs ->
          SupportSet.In ((n, v), f) support }.

  Module Reduction.
    Module NFPair := PairUOT N F.
    Module NFF := UOTCompareFacts NFPair.
    Module NF := UOTCompareFacts N.
    #[local] Hint Rewrite NFF.compare_eq_iff NF.compare_eq_iff : cmp_feat.
    #[local] Hint Extern 1 => cmp_by NFF.compare_antisym : cmp_feat.
    #[local] Hint Extern 1 => cmp_by NF.compare_antisym : cmp_feat.
    #[local] Hint Extern 1 => cmp_by NFF.compare_lt_trans : cmp_feat.
    #[local] Hint Extern 1 => cmp_by NF.compare_lt_trans : cmp_feat.

    Module Name.
      Inductive name : Type :=
      | Orig (n : N.t)
      | FeatPkg (n : N.t) (f : F.t).
      Definition t := name.

      Definition compare (x y : t) : comparison :=
        match x, y with
        | Orig n1, Orig n2 => N.compare n1 n2
        | Orig _, FeatPkg _ _ => Lt
        | FeatPkg _ _, Orig _ => Gt
        | FeatPkg n1 f1, FeatPkg n2 f2 => NFPair.compare (n1, f1) (n2, f2)
        end.

      Lemma compare_eq_iff : forall x y, compare x y = Eq <-> x = y.
      Proof. cmp_eq_iff cmp_feat. Qed.

      Lemma compare_antisym : forall x y, compare y x = CompOpp (compare x y).
      Proof. cmp_antisym cmp_feat. Qed.

      Lemma compare_lt_trans : forall x y z,
          compare x y = Lt -> compare y z = Lt -> compare x z = Lt.
      Proof. cmp_lt_trans cmp_feat. Qed.
    End Name.
    Module NameOT := UOTFromCompare Name.

    Module T := Core NameOT V.

    (* The target core is a distinct instantiation even though versions are
       unchanged, so version sets are rebuilt element-wise. *)
    Module SOvt := SetOps V V VSet T.VSet.
    Definition embedVS (vs : VSet.t) : T.VSet.t :=
      SOvt.map (fun v => v) vs.

    Definition embedPkg (p : Pkg.t) : T.Pkg.t :=
      let '(n, v) := p in (Name.Orig n, v).

    Module SOpt := SetOps Pkg T.Pkg PkgSet T.PkgSet.
    Definition embedSet (S : PkgSet.t) : T.PkgSet.t :=
      SOpt.map embedPkg S.

    Module SOst := SetOps PkgF T.Pkg SupportSet T.PkgSet.
    Definition featPkgReal (R : PkgSet.t)
        (support : SupportSet.t) : T.PkgSet.t :=
      SOst.filterMap (fun '((n, v), f) =>
          if PkgSet.mem (n, v) R
          then Some (Name.FeatPkg n f, v)
          else None)
        support.

    Definition reduceReal (R : PkgSet.t) (support : SupportSet.t)
        : T.PkgSet.t :=
      T.PkgSet.union (embedSet R) (featPkgReal R support).

    Module SOsd := SetOps PkgF T.DepElt SupportSet T.DepRel.
    Definition supportEdges (R : PkgSet.t)
        (support : SupportSet.t) : T.DepRel.t :=
      SOsd.filterMap (fun '((n, v), f) =>
          if PkgSet.mem (n, v) R
          then Some ((Name.FeatPkg n f, v),
                     (Name.Orig n, T.VSet.singleton v))
          else None)
        support.

    Module SOfd := SetOps FeatDepElt T.DepElt FeatDepRel T.DepRel.
    Definition featDepOrigEdges (Df : FeatDepRel.t) : T.DepRel.t :=
      SOfd.filterMap (fun '(p, (n, (vs, fs))) =>
          if FSet.is_empty fs
          then Some (embedPkg p, (Name.Orig n, embedVS vs))
          else None)
        Df.

    Module SOfsd := SetOps F T.DepElt FSet T.DepRel.
    Definition featDepFeatPkgEdges (Df : FeatDepRel.t) : T.DepRel.t :=
      SOfd.unionMap (fun '(p, (n, (vs, fs))) =>
          if FSet.is_empty fs then T.DepRel.empty
          else SOfsd.map (fun f =>
                   (embedPkg p, (Name.FeatPkg n f, embedVS vs)))
                 fs)
        Df.

    Module SOad := SetOps AddlDepElt T.DepElt AddlDepRel T.DepRel.
    Definition addlDepOrigEdges (Da : AddlDepRel.t) : T.DepRel.t :=
      SOad.filterMap (fun '(((n, v), f), (m, (vs, fs))) =>
          if FSet.is_empty fs
          then Some ((Name.FeatPkg n f, v), (Name.Orig m, embedVS vs))
          else None)
        Da.

    Definition addlDepFeatPkgEdges (Da : AddlDepRel.t) : T.DepRel.t :=
      SOad.unionMap (fun '(((n, v), f), (m, (vs, fs))) =>
          if FSet.is_empty fs then T.DepRel.empty
          else SOfsd.map (fun f' =>
                   ((Name.FeatPkg n f, v),
                    (Name.FeatPkg m f', embedVS vs)))
                 fs)
        Da.

    Definition reduceDeps (R : PkgSet.t) (support : SupportSet.t)
        (Df : FeatDepRel.t) (Da : AddlDepRel.t) : T.DepRel.t :=
      T.DepRel.union (supportEdges R support)
        (T.DepRel.union (featDepOrigEdges Df)
           (T.DepRel.union (featDepFeatPkgEdges Df)
              (T.DepRel.union (addlDepOrigEdges Da)
                 (addlDepFeatPkgEdges Da)))).

    Lemma mem_embedVS : forall vs v, T.VSet.In v (embedVS vs) <-> VSet.In v vs.
    Proof.
      intros vs v; unfold embedVS.
      exact (SOvt.mem_map_inj (fun w => w) vs v (fun x y H => H)).
    Qed.

    Lemma mem_featPkgReal : forall R support q,
        T.PkgSet.In q (featPkgReal R support) <->
        exists n v f, SupportSet.In ((n, v), f) support /\ PkgSet.In (n, v) R /\
          q = (Name.FeatPkg n f, v).
    Proof.
      intros R support q; unfold featPkgReal; rewrite SOst.mem_filterMap.
      split.
      - intros [[[pn pv] f0] [Hs Hq]]; cbn beta iota in Hq.
        destruct (PkgSet.mem (pn, pv) R) eqn:Em; [| discriminate].
        injection Hq as <-.
        exists pn, pv, f0; repeat split;
          [exact Hs | apply PkgSet.mem_spec; exact Em].
      - intros [n [v [f0 [Hs [HR ->]]]]].
        exists ((n, v), f0); split; [exact Hs | cbn beta iota].
        rewrite <- PkgSet.mem_spec in HR; rewrite HR; reflexivity.
    Qed.

    Lemma mem_reduceReal : forall R support q,
        T.PkgSet.In q (reduceReal R support) <->
        (exists p, PkgSet.In p R /\ q = embedPkg p) \/
        (exists n v f, SupportSet.In ((n, v), f) support /\
           PkgSet.In (n, v) R /\
           q = (Name.FeatPkg n f, v)).
    Proof.
      intros R support q; unfold reduceReal, embedSet.
      rewrite T.PkgSet.union_spec, SOpt.mem_map, mem_featPkgReal; reflexivity.
    Qed.

    Lemma mem_supportEdges :
      forall R support (q : T.Pkg.t) (m : NameOT.t) (ws : T.VSet.t),
        T.DepRel.In (q, (m, ws)) (supportEdges R support) <->
        exists n v f, SupportSet.In ((n, v), f) support /\ PkgSet.In (n, v) R /\
          q = (Name.FeatPkg n f, v) /\ m = Name.Orig n /\
          ws = T.VSet.singleton v.
    Proof.
      intros R support q m ws; unfold supportEdges; rewrite SOsd.mem_filterMap.
      split.
      - intros [[[pn pv] f0] [Hs Hy]]; cbn beta iota in Hy.
        destruct (PkgSet.mem (pn, pv) R) eqn:Em; [| discriminate].
        injection Hy as <- <- <-.
        exists pn, pv, f0; repeat split;
          [exact Hs | apply PkgSet.mem_spec; exact Em].
      - intros [n [v [f0 [Hs [HR [Hsrc [Htn Htvs]]]]]]]; subst q m ws.
        exists ((n, v), f0); split; [exact Hs | cbn beta iota].
        rewrite <- PkgSet.mem_spec in HR; rewrite HR; reflexivity.
    Qed.

    Lemma mem_featDepOrigEdges :
      forall Df (q : T.Pkg.t) (m : NameOT.t) (ws : T.VSet.t),
        T.DepRel.In (q, (m, ws)) (featDepOrigEdges Df) <->
        exists p n vs, FeatDepRel.In (p, (n, (vs, FSet.empty))) Df /\
          q = embedPkg p /\ m = Name.Orig n /\ ws = embedVS vs.
    Proof.
      intros Df q m ws; unfold featDepOrigEdges; rewrite SOfd.mem_filterMap.
      split.
      - intros [[p [m0 [vs0 fs0]]] [He2 Hy]]; cbn beta iota in Hy.
        destruct (FSet.is_empty fs0) eqn:E0; [| discriminate].
        injection Hy as <- <- <-.
        apply FSet.is_empty_iff in E0; subst fs0.
        exists p, m0, vs0; repeat split; exact He2.
      - intros [p [m0 [vs0 [He2 [Hsrc [Htn Htvs]]]]]]; subst q m ws.
        exists (p, (m0, (vs0, FSet.empty))); split; [exact He2 | simpl];
          reflexivity.
    Qed.

    Lemma mem_featDepFeatPkgEdges :
      forall Df (q : T.Pkg.t) (m : NameOT.t) (ws : T.VSet.t),
        T.DepRel.In (q, (m, ws)) (featDepFeatPkgEdges Df) <->
        exists p n vs fs f, FeatDepRel.In (p, (n, (vs, fs))) Df /\
          FSet.is_empty fs = false /\ FSet.In f fs /\
          q = embedPkg p /\ m = Name.FeatPkg n f /\ ws = embedVS vs.
    Proof.
      intros Df q m ws; unfold featDepFeatPkgEdges; rewrite SOfd.mem_unionMap.
      split.
      - intros [[p [m0 [vs0 fs0]]] [He3 Hy]]; cbn beta iota in Hy.
        destruct (FSet.is_empty fs0) eqn:E0; [destruct (SOfd.empty_in _ Hy) |].
        apply SOfsd.mem_map in Hy; destruct Hy as [f [Hf Hy]].
        injection Hy as -> -> ->.
        exists p, m0, vs0, fs0, f; repeat split; assumption.
      - intros [p [m0 [vs0 [fs0 [f [He3 [E0 [Hf [Hsrc [Htn Htvs]]]]]]]]]];
          subst q m ws.
        exists (p, (m0, (vs0, fs0))); split; [exact He3 | cbn beta iota].
        rewrite E0.
        apply SOfsd.mem_map; exists f; split; [exact Hf | reflexivity].
    Qed.

    Lemma mem_addlDepOrigEdges :
      forall Da (q : T.Pkg.t) (m : NameOT.t) (ws : T.VSet.t),
        T.DepRel.In (q, (m, ws)) (addlDepOrigEdges Da) <->
        exists n v f m' vs,
          AddlDepRel.In (((n, v), f), (m', (vs, FSet.empty))) Da /\
          q = (Name.FeatPkg n f, v) /\ m = Name.Orig m' /\ ws = embedVS vs.
    Proof.
      intros Da q m ws; unfold addlDepOrigEdges; rewrite SOad.mem_filterMap.
      split.
      - intros [[[[pn pv] f0] [m0 [vs0 fs0]]] [He4 Hy]]; cbn beta iota in Hy.
        destruct (FSet.is_empty fs0) eqn:E0; [| discriminate].
        injection Hy as <- <- <-.
        apply FSet.is_empty_iff in E0; subst fs0.
        exists pn, pv, f0, m0, vs0; repeat split; exact He4.
      - intros [n [v [f0 [m0 [vs0 [He4 [Hsrc [Htn Htvs]]]]]]]]; subst q m ws.
        exists (((n, v), f0), (m0, (vs0, FSet.empty)));
          split; [exact He4 | simpl]; reflexivity.
    Qed.

    Lemma mem_addlDepFeatPkgEdges :
      forall Da (q : T.Pkg.t) (m : NameOT.t) (ws : T.VSet.t),
        T.DepRel.In (q, (m, ws)) (addlDepFeatPkgEdges Da) <->
        exists n v f m' vs fs f',
          AddlDepRel.In (((n, v), f), (m', (vs, fs))) Da /\
          FSet.is_empty fs = false /\ FSet.In f' fs /\
          q = (Name.FeatPkg n f, v) /\ m = Name.FeatPkg m' f' /\
          ws = embedVS vs.
    Proof.
      intros Da q m ws; unfold addlDepFeatPkgEdges; rewrite SOad.mem_unionMap.
      split.
      - intros [[[[pn pv] f0] [m0 [vs0 fs0]]] [He5 Hy]]; cbn beta iota in Hy.
        destruct (FSet.is_empty fs0) eqn:E0; [destruct (SOad.empty_in _ Hy) |].
        apply SOfsd.mem_map in Hy; destruct Hy as [f' [Hf' Hy]].
        injection Hy as -> -> ->.
        exists pn, pv, f0, m0, vs0, fs0, f'; repeat split; assumption.
      - intros [n [v [f0 [m0 [vs0 [fs0 [f'
                  [He5 [E0 [Hf' [Hsrc [Htn Htvs]]]]]]]]]]]]; subst q m ws.
        exists (((n, v), f0), (m0, (vs0, fs0)));
          split; [exact He5 | cbn beta iota].
        rewrite E0.
        apply SOfsd.mem_map; exists f'; split; [exact Hf' | reflexivity].
    Qed.

    Lemma mem_reduceDeps :
      forall R support Df Da (q : T.Pkg.t) (m : NameOT.t) (ws : T.VSet.t),
        T.DepRel.In (q, (m, ws)) (reduceDeps R support Df Da) <->
        (exists n v f, SupportSet.In ((n, v), f) support /\
           PkgSet.In (n, v) R /\
           q = (Name.FeatPkg n f, v) /\ m = Name.Orig n /\
           ws = T.VSet.singleton v) \/
        (exists p n vs, FeatDepRel.In (p, (n, (vs, FSet.empty))) Df /\
           q = embedPkg p /\ m = Name.Orig n /\ ws = embedVS vs) \/
        (exists p n vs fs f, FeatDepRel.In (p, (n, (vs, fs))) Df /\
           FSet.is_empty fs = false /\ FSet.In f fs /\
           q = embedPkg p /\ m = Name.FeatPkg n f /\ ws = embedVS vs) \/
        (exists n v f m' vs,
           AddlDepRel.In (((n, v), f), (m', (vs, FSet.empty))) Da /\
           q = (Name.FeatPkg n f, v) /\ m = Name.Orig m' /\ ws = embedVS vs) \/
        (exists n v f m' vs fs f',
           AddlDepRel.In (((n, v), f), (m', (vs, fs))) Da /\
           FSet.is_empty fs = false /\ FSet.In f' fs /\
           q = (Name.FeatPkg n f, v) /\ m = Name.FeatPkg m' f' /\
           ws = embedVS vs).
    Proof.
      intros R support Df Da q m ws; unfold reduceDeps.
      rewrite !T.DepRel.union_spec, mem_supportEdges, mem_featDepOrigEdges,
        mem_featDepFeatPkgEdges, mem_addlDepOrigEdges,
        mem_addlDepFeatPkgEdges.
      tauto.
    Qed.

    Module SOtf := SetOps T.Pkg F T.PkgSet FSet.
    (* Decoding reads the features off the resolution rather than sieving the
       feature universe by membership in it: the two agree, but only this
       direction is defined when F is unbounded, as a package ecosystem's
       feature names are. *)
    Definition featsOf (n : N.t) (v : V.t) (S : T.PkgSet.t) : FSet.t :=
      SOtf.filterMap (fun q =>
          match q with
          | (Name.FeatPkg n' f, v') =>
              if T.Pkg.eq_dec (Name.FeatPkg n' f, v') (Name.FeatPkg n f, v)
              then Some f
              else None
          | _ => None
          end)
        S.

    Lemma featsOf_spec : forall n v S f,
        FSet.In f (featsOf n v S) <-> T.PkgSet.In (Name.FeatPkg n f, v) S.
    Proof.
      intros n v S f; unfold featsOf; rewrite SOtf.mem_filterMap.
      split.
      - intros [[[n' | n' f'] v'] [HS He]]; cbn beta iota in He;
          [discriminate |].
        destruct (T.Pkg.eq_dec (Name.FeatPkg n' f', v') (Name.FeatPkg n f', v))
          as [E | NE]; [| discriminate].
        injection He as <-; rewrite <- E; exact HS.
      - intro HS; exists (Name.FeatPkg n f, v);
          split; [exact HS | cbn beta iota].
        destruct (T.Pkg.eq_dec (Name.FeatPkg n f, v) (Name.FeatPkg n f, v))
          as [_ | NE]; [reflexivity | exfalso; exact (NE eq_refl)].
    Qed.

    Module SOts := SetOps T.Pkg Featured T.PkgSet FeaturedSet.
    Definition featureResolution (S : T.PkgSet.t) : FeaturedSet.t :=
      SOts.filterMap (fun p' =>
          match p' with
          | (Name.Orig n, v) => Some ((n, v), featsOf n v S)
          | _ => None
          end)
        S.

    Lemma mem_featureResolution : forall (S : T.PkgSet.t) (y : Featured.t),
        FeaturedSet.In y (featureResolution S) <->
        exists n v,
          T.PkgSet.In (Name.Orig n, v) S /\ y = ((n, v), featsOf n v S).
    Proof.
      intros S y; unfold featureResolution; rewrite SOts.mem_filterMap.
      split.
      - intros [[[n | n f] v] [HeS Hy]]; cbn beta iota in Hy; [| discriminate].
        injection Hy as <-; exists n, v; split; [exact HeS | reflexivity].
      - intros [n [v [HS ->]]].
        exists (Name.Orig n, v); split; [exact HS | reflexivity].
    Qed.

    Theorem feature_soundness :
      forall (R : PkgSet.t) (support : SupportSet.t)
             (Df : FeatDepRel.t) (Da : AddlDepRel.t)
             (r : Pkg.t) (S : T.PkgSet.t),
        T.IsResolution (reduceReal R support) (reduceDeps R support Df Da)
          (embedPkg r) S ->
        (forall f, ~ SupportSet.In (r, f) support) ->
        IsResolution R support Df Da r (featureResolution S).
    Proof.
      intros R support Df Da r S Hres Hnosupp.
      destruct Hres as [Hsub Hroot Hdep Huniq].
      destruct r as [rn rv].
      unfold embedPkg in Hroot; simpl in Hroot.
      assert (HorigR : forall n v,
                 T.PkgSet.In (Name.Orig n, v) S -> PkgSet.In (n, v) R).
      { intros n v HS.
        pose proof (Hsub _ HS) as HF; rewrite mem_reduceReal in HF.
        destruct HF as [[p [HpR Hq]] | [n' [v' [f' [Hsupp [HR Hq]]]]]].
        - destruct p as [pn pv]; unfold embedPkg in Hq; simpl in Hq.
          injection Hq as E1 E2; subst pn pv; exact HpR.
        - discriminate Hq. }
      assert (HnorootF : forall f, ~ T.PkgSet.In (Name.FeatPkg rn f, rv) S).
      { intros f HS.
        pose proof (Hsub _ HS) as HF; rewrite mem_reduceReal in HF.
        destruct HF as [[p [HpR Hq]] | [n' [v' [f' [Hsupp [HR Hq]]]]]].
        - destruct p as [pn pv]; unfold embedPkg in Hq; simpl in Hq;
            discriminate Hq.
        - injection Hq as E1 E2 E3; subst n' f' v'.
          exact (Hnosupp _ Hsupp). }
      assert (HfeatOrig : forall n f v,
                 T.PkgSet.In (Name.FeatPkg n f, v) S ->
                 T.PkgSet.In (Name.Orig n, v) S).
      { intros n f v HS.
        pose proof (Hsub _ HS) as HF; rewrite mem_reduceReal in HF.
        destruct HF as [[p [HpR Hq]] | [n' [v' [f' [Hsupp [HR Hq]]]]]].
        - destruct p as [pn pv]; unfold embedPkg in Hq; simpl in Hq;
            discriminate Hq.
        - injection Hq as E1 E2 E3; subst n' f' v'.
          assert (Hd : T.DepRel.In
                         ((Name.FeatPkg n f, v),
                          (Name.Orig n, T.VSet.singleton v))
                         (reduceDeps R support Df Da)).
          { rewrite mem_reduceDeps.
            left; exists n, v, f.
            split; [exact Hsupp | split; [exact HR |]].
            split; [reflexivity | split; reflexivity]. }
          destruct (Hdep _ HS _ _ Hd) as [v0 [Hv0 Hv0S]].
          rewrite SOvt.singleton_in in Hv0; subst v0.
          exact Hv0S. }
      constructor.
      - exact Hnosupp.
      - intros p fs Hmem.
        apply mem_featureResolution in Hmem;
          destruct Hmem as [n [v [HS Heq]]].
        injection Heq as E1 E2; subst p.
        exact (HorigR n v HS).
      - assert (Hfe : featsOf rn rv S = FSet.empty).
        { apply FSet.ext; intro f; rewrite featsOf_spec; split; intro H.
          + exfalso; exact (HnorootF f H).
          + exfalso; exact (FSet.empty_spec H). }
        rewrite <- Hfe.
        apply mem_featureResolution; exists rn, rv;
          split; [exact Hroot | reflexivity].
      - intros p fs_p Hmem n vs fs Hdf.
        apply mem_featureResolution in Hmem;
          destruct Hmem as [pn [pv [HpS Heq]]].
        injection Heq as E1 E2; subst p fs_p.
        destruct (FSet.is_empty fs) eqn:E.
        + apply FSet.is_empty_iff in E; subst fs.
          assert (Hd : T.DepRel.In
                         ((Name.Orig pn, pv), (Name.Orig n, embedVS vs))
                         (reduceDeps R support Df Da)).
          { rewrite mem_reduceDeps.
            right; left; exists (pn, pv), n, vs.
            split; [exact Hdf | split; [reflexivity | split; reflexivity]]. }
          destruct (Hdep _ HpS _ _ Hd) as [v [Hv HvS]].
          rewrite mem_embedVS in Hv.
          exists v; split; [exact Hv |].
          exists (featsOf n v S); split.
          * intros x Hx; exfalso; exact (FSet.empty_spec Hx).
          * apply mem_featureResolution; exists n, v;
              split; [exact HvS | reflexivity].
        + destruct (FSet.choose_nonempty _ E) as [f0 Hf0].
          assert (Hd0 : T.DepRel.In
                          ((Name.Orig pn, pv), (Name.FeatPkg n f0, embedVS vs))
                          (reduceDeps R support Df Da)).
          { rewrite mem_reduceDeps.
            right; right; left; exists (pn, pv), n, vs, fs, f0.
            split; [exact Hdf | split; [exact E | split; [exact Hf0 |]]].
            split; [reflexivity | split; reflexivity]. }
          destruct (Hdep _ HpS _ _ Hd0) as [v [Hv HvS]].
          rewrite mem_embedVS in Hv.
          pose proof (HfeatOrig _ _ _ HvS) as HvO.
          exists v; split; [exact Hv |].
          exists (featsOf n v S); split.
          * intros f' Hf'; rewrite featsOf_spec.
            assert (Hd' : T.DepRel.In
                            ((Name.Orig pn, pv),
                             (Name.FeatPkg n f', embedVS vs))
                            (reduceDeps R support Df Da)).
            { rewrite mem_reduceDeps.
              right; right; left; exists (pn, pv), n, vs, fs, f'.
              split; [exact Hdf | split; [exact E | split; [exact Hf' |]]].
              split; [reflexivity | split; reflexivity]. }
            destruct (Hdep _ HpS _ _ Hd') as [v' [Hv' Hv'S]].
            pose proof (HfeatOrig _ _ _ Hv'S) as Hv'O.
            assert (Ev : v = v') by exact (Huniq (Name.Orig n) v v' HvO Hv'O).
            rewrite Ev; exact Hv'S.
          * apply mem_featureResolution; exists n, v;
              split; [exact HvO | reflexivity].
      - intros p fs_p Hmem f Hf n vs fs Hda.
        apply mem_featureResolution in Hmem;
          destruct Hmem as [pn [pv [HpS Heq]]].
        injection Heq as E1 E2; subst p fs_p.
        rewrite featsOf_spec in Hf.
        destruct (FSet.is_empty fs) eqn:E.
        + apply FSet.is_empty_iff in E; subst fs.
          assert (Hd : T.DepRel.In
                         ((Name.FeatPkg pn f, pv), (Name.Orig n, embedVS vs))
                         (reduceDeps R support Df Da)).
          { rewrite mem_reduceDeps.
            right; right; right; left; exists pn, pv, f, n, vs.
            split; [exact Hda | split; [reflexivity | split; reflexivity]]. }
          destruct (Hdep _ Hf _ _ Hd) as [v0 [Hv0 Hv0S]].
          rewrite mem_embedVS in Hv0.
          exists v0; split; [exact Hv0 |].
          exists (featsOf n v0 S); split.
          * intros x Hx; exfalso; exact (FSet.empty_spec Hx).
          * apply mem_featureResolution; exists n, v0;
              split; [exact Hv0S | reflexivity].
        + destruct (FSet.choose_nonempty _ E) as [f0 Hf0].
          assert (Hd0 : T.DepRel.In
                          ((Name.FeatPkg pn f, pv),
                           (Name.FeatPkg n f0, embedVS vs))
                          (reduceDeps R support Df Da)).
          { rewrite mem_reduceDeps.
            right; right; right; right; exists pn, pv, f, n, vs, fs, f0.
            split; [exact Hda | split; [exact E | split; [exact Hf0 |]]].
            split; [reflexivity | split; reflexivity]. }
          destruct (Hdep _ Hf _ _ Hd0) as [v0 [Hv0 Hv0S]].
          rewrite mem_embedVS in Hv0.
          pose proof (HfeatOrig _ _ _ Hv0S) as HvO.
          exists v0; split; [exact Hv0 |].
          exists (featsOf n v0 S); split.
          * intros f' Hf'; rewrite featsOf_spec.
            assert (Hd' : T.DepRel.In
                            ((Name.FeatPkg pn f, pv),
                             (Name.FeatPkg n f', embedVS vs))
                            (reduceDeps R support Df Da)).
            { rewrite mem_reduceDeps.
              right; right; right; right; exists pn, pv, f, n, vs, fs, f'.
              split; [exact Hda | split; [exact E | split; [exact Hf' |]]].
              split; [reflexivity | split; reflexivity]. }
            destruct (Hdep _ Hf _ _ Hd') as [v' [Hv' Hv'S]].
            pose proof (HfeatOrig _ _ _ Hv'S) as Hv'O.
            assert (Ev : v0 = v') by exact (Huniq (Name.Orig n) v0 v' HvO Hv'O).
            rewrite Ev; exact Hv'S.
          * apply mem_featureResolution; exists n, v0;
              split; [exact HvO | reflexivity].
      - intros n v v' fs fs' H1 H2.
        apply mem_featureResolution in H1; destruct H1 as [n1 [v1 [HS1 Heq1]]].
        apply mem_featureResolution in H2; destruct H2 as [n2 [v2 [HS2 Heq2]]].
        injection Heq1 as E1 E2 E3; subst n1 v1 fs.
        injection Heq2 as E4 E5 E6; subst n2 v2 fs'.
        assert (Ev : v = v') by exact (Huniq (Name.Orig n) v v' HS1 HS2).
        rewrite Ev; reflexivity.
      - intros n v v' fs fs' H1 H2.
        apply mem_featureResolution in H1; destruct H1 as [n1 [v1 [HS1 Heq1]]].
        apply mem_featureResolution in H2; destruct H2 as [n2 [v2 [HS2 Heq2]]].
        injection Heq1 as E1 E2 E3; subst n1 v1 fs.
        injection Heq2 as E4 E5 E6; subst n2 v2 fs'.
        exact (Huniq (Name.Orig n) v v' HS1 HS2).
      - intros n v fs f Hmem Hf.
        apply mem_featureResolution in Hmem;
          destruct Hmem as [n1 [v1 [HS Heq]]].
        injection Heq as E1 E2 E3; subst n1 v1 fs.
        rewrite featsOf_spec in Hf.
        pose proof (Hsub _ Hf) as HF; rewrite mem_reduceReal in HF.
        destruct HF as [[p [HpR Hq]] | [n' [v' [f' [Hsupp [HR Hq]]]]]].
        + destruct p as [pn pv]; unfold embedPkg in Hq; simpl in Hq;
            discriminate Hq.
        + injection Hq as E4 E5 E6; subst n' f' v'.
          exact Hsupp.
    Qed.

    Module SOsw := SetOps Featured T.Pkg FeaturedSet T.PkgSet.
    Module SOft := SetOps F T.Pkg FSet T.PkgSet.
    Definition coreResolution (S_f : FeaturedSet.t) : T.PkgSet.t :=
      T.PkgSet.union
        (SOsw.map (fun '((n, v), _) => (Name.Orig n, v)) S_f)
        (SOsw.unionMap (fun '((n, v), fs) =>
             SOft.map (fun f => (Name.FeatPkg n f, v)) fs)
           S_f).

    Lemma mem_coreResolution : forall S_f (q : T.Pkg.t),
        T.PkgSet.In q (coreResolution S_f) <->
        (exists n v fs,
           FeaturedSet.In ((n, v), fs) S_f /\ q = (Name.Orig n, v)) \/
        (exists n v fs f, FeaturedSet.In ((n, v), fs) S_f /\ FSet.In f fs /\
           q = (Name.FeatPkg n f, v)).
    Proof.
      intros S_f q; unfold coreResolution.
      rewrite T.PkgSet.union_spec, SOsw.mem_map, SOsw.mem_unionMap.
      split.
      - intros [[[[pn pv] fs0] [HxS Hy]] | [[[pn pv] fs0] [HxS Hy]]];
          cbn beta iota in Hy.
        + left; exists pn, pv, fs0; split; [exact HxS | exact Hy].
        + apply SOft.mem_map in Hy; destruct Hy as [f [Hf Hy]].
          right; exists pn, pv, fs0, f;
            split; [exact HxS | split; [exact Hf | exact Hy]].
      - intros [[n [v [fs [HxS ->]]]] | [n [v [fs [f [HxS [Hf ->]]]]]]].
        + left; exists ((n, v), fs); split; [exact HxS | reflexivity].
        + right; exists ((n, v), fs); split; [exact HxS | cbn beta iota].
          apply SOft.mem_map; exists f; split; [exact Hf | reflexivity].
    Qed.

    Theorem feature_completeness :
      forall (R : PkgSet.t) (support : SupportSet.t)
             (Df : FeatDepRel.t) (Da : AddlDepRel.t)
             (r : Pkg.t) (S_f : FeaturedSet.t),
        IsResolution R support Df Da r S_f ->
        T.IsResolution (reduceReal R support) (reduceDeps R support Df Da)
          (embedPkg r) (coreResolution S_f).
    Proof.
      intros R support Df Da r S_f Hres.
      destruct Hres as [Hnrs Hsubset Hrootm Hdepc Haddlc Hfu Hvu Hsm].
      destruct r as [rn rv].
      constructor.
      - intros q Hq.
        rewrite mem_coreResolution in Hq.
        rewrite mem_reduceReal.
        destruct Hq as [[n [v [fs [HS ->]]]] | [n [v [fs [f [HS [Hf ->]]]]]]].
        + left; exists (n, v); split; [exact (Hsubset _ _ HS) | reflexivity].
        + right; exists n, v, f.
          split; [exact (Hsm n v fs f HS Hf) |].
          split; [exact (Hsubset _ _ HS) | reflexivity].
      - rewrite mem_coreResolution.
        left; exists rn, rv, FSet.empty; split; [exact Hrootm | reflexivity].
      - intros q Hq m vs Hd.
        rewrite mem_coreResolution in Hq.
        rewrite mem_reduceDeps in Hd.
        destruct Hq as [[pn [pv [fs [HS Hq]]]] |
                        [pn [pv [fs [f0 [HS [Hf0 Hq]]]]]]]; subst q.
        + destruct Hd as [D1 | [D2 | [D3 | [D4 | D5]]]].
          * destruct D1 as [n [v [f [_ [_ [Hsrc _]]]]]]; discriminate Hsrc.
          * destruct D2 as [q' [m' [vs' [Hdf [Hsrc [Htn Htvs]]]]]]; subst m vs.
            destruct q' as [qn qv]; unfold embedPkg in Hsrc; simpl in Hsrc.
            injection Hsrc as E1 E2; subst qn qv.
            destruct (Hdepc _ _ HS _ _ _ Hdf) as [v' [Hv' [fs' [_ Hfs']]]].
            exists v'; split; [rewrite mem_embedVS; exact Hv' |].
            rewrite mem_coreResolution.
            left; exists m', v', fs'; split; [exact Hfs' | reflexivity].
          * destruct D3
              as [q' [m' [vs' [fs0 [f [Hdf [E0 [Hf [Hsrc [Htn Htvs]]]]]]]]]];
              subst m vs.
            destruct q' as [qn qv]; unfold embedPkg in Hsrc; simpl in Hsrc.
            injection Hsrc as E1 E2; subst qn qv.
            destruct (Hdepc _ _ HS _ _ _ Hdf) as [v' [Hv' [fs' [Hsub' Hfs']]]].
            exists v'; split; [rewrite mem_embedVS; exact Hv' |].
            rewrite mem_coreResolution.
            right; exists m', v', fs', f.
            split; [exact Hfs' | split; [exact (Hsub' _ Hf) | reflexivity]].
          * destruct D4 as [n [v [f [m' [vs' [_ [Hsrc _]]]]]]];
              discriminate Hsrc.
          * destruct D5 as
              [n [v [f [m' [vs' [fs0 [f' [_ [_ [_ [Hsrc _]]]]]]]]]]];
              discriminate Hsrc.
        + destruct Hd as [D1 | [D2 | [D3 | [D4 | D5]]]].
          * destruct D1 as [n [v [f [Hsupp [HR [Hsrc [Htn Htvs]]]]]]];
              subst m vs.
            injection Hsrc as E1 E2 E3; subst n f v.
            exists pv; split; [rewrite SOvt.singleton_in; reflexivity |].
            rewrite mem_coreResolution.
            left; exists pn, pv, fs; split; [exact HS | reflexivity].
          * destruct D2 as [q' [m' [vs' [_ [Hsrc _]]]]].
            destruct q' as [qn qv]; unfold embedPkg in Hsrc; simpl in Hsrc;
              discriminate Hsrc.
          * destruct D3 as [q' [m' [vs' [fs0 [f [_ [_ [_ [Hsrc _]]]]]]]]].
            destruct q' as [qn qv]; unfold embedPkg in Hsrc; simpl in Hsrc;
              discriminate Hsrc.
          * destruct D4 as [n [v [f [m' [vs' [Hda [Hsrc [Htn Htvs]]]]]]]];
              subst m vs.
            injection Hsrc as E1 E2 E3; subst n f v.
            destruct (Haddlc _ _ HS f0 Hf0 _ _ _ Hda)
              as [v' [Hv' [fs' [_ Hfs']]]].
            exists v'; split; [rewrite mem_embedVS; exact Hv' |].
            rewrite mem_coreResolution.
            left; exists m', v', fs'; split; [exact Hfs' | reflexivity].
          * destruct D5 as [n [v [f [m' [vs' [fs0 [f'
                            [Hda [E0 [Hf' [Hsrc [Htn Htvs]]]]]]]]]]]];
              subst m vs.
            injection Hsrc as E1 E2 E3; subst n f v.
            destruct (Haddlc _ _ HS f0 Hf0 _ _ _ Hda)
              as [v' [Hv' [fs' [Hsub' Hfs']]]].
            exists v'; split; [rewrite mem_embedVS; exact Hv' |].
            rewrite mem_coreResolution.
            right; exists m', v', fs', f'.
            split; [exact Hfs' | split; [exact (Hsub' _ Hf') | reflexivity]].
      - intros nm v1 v2 H1 H2.
        rewrite mem_coreResolution in H1, H2.
        destruct H1 as [[n1 [w1 [fs1 [HS1 Hq1]]]] |
                        [n1 [w1 [fs1 [f1 [HS1 [Hf1 Hq1]]]]]]];
          destruct H2 as [[n2 [w2 [fs2 [HS2 Hq2]]]] |
                          [n2 [w2 [fs2 [f2 [HS2 [Hf2 Hq2]]]]]]].
        + injection Hq1 as E1 E2; subst nm v1.
          injection Hq2 as E3 E4; subst n2 v2.
          exact (Hvu _ _ _ _ _ HS1 HS2).
        + injection Hq1 as E1 E2; subst nm v1.
          discriminate Hq2.
        + injection Hq1 as E1 E2; subst nm v1.
          discriminate Hq2.
        + injection Hq1 as E1 E2; subst nm v1.
          injection Hq2 as E3 E4 E5; subst n2 f2 v2.
          exact (Hvu _ _ _ _ _ HS1 HS2).
    Qed.

    Module Lookup.
      Lemma reduceDeps_mono :
        forall R R' support support' Df Df' Da Da' (y : T.DepElt.t),
          PkgSet.Subset R' R -> SupportSet.Subset support' support ->
          FeatDepRel.Subset Df' Df -> AddlDepRel.Subset Da' Da ->
          T.DepRel.In y (reduceDeps R' support' Df' Da') ->
          T.DepRel.In y (reduceDeps R support Df Da).
      Proof.
        intros R R' support support' Df Df' Da Da' y HR Hs HDf HDa; revert y.
        unfold reduceDeps, supportEdges, featDepOrigEdges,
          featDepFeatPkgEdges, addlDepOrigEdges, addlDepFeatPkgEdges.
        repeat apply SOsd.union_subset.
        - apply SOsd.filterMap_mono; [exact Hs |].
          intros [[n v] f] z Hz; cbn beta iota in Hz |- *.
          destruct (PkgSet.mem (n, v) R') eqn:Em; [| discriminate Hz].
          rewrite PkgSet.mem_spec in Em; apply HR in Em.
          rewrite <- PkgSet.mem_spec in Em; rewrite Em; exact Hz.
        - apply SOfd.filterMap_mono; [exact HDf | intros x z Hz; exact Hz].
        - apply SOfd.unionMap_mono; [exact HDf | intros x z Hz; exact Hz].
        - apply SOad.filterMap_mono; [exact HDa | intros x z Hz; exact Hz].
        - apply SOad.unionMap_mono; [exact HDa | intros x z Hz; exact Hz].
      Qed.

      Module FeatDepRelFibred :=
        FibredLabelledRel Pkg N VSFS FeatDepElt FeatDepRel.
      Theorem dependees_lookupOrig :
        forall R support Df Da (n : N.t) (v : V.t),
          T.dependees (reduceDeps R support Df Da) (Name.Orig n, v) =
          T.dependees
            (reduceDeps PkgSet.empty SupportSet.empty
               (FeatDepRelFibred.tailFibre Df (n, v))
               AddlDepRel.empty)
            (Name.Orig n, v).
      Proof.
        intros R support Df Da n v; apply T.dependees_ext; intros [m ws].
        split; [| apply reduceDeps_mono;
                  [apply PkgSet.empty_subset
                  | apply SupportSet.empty_subset
                  | apply FeatDepRelFibred.tailFibre_subset
                  | apply AddlDepRel.empty_subset]].
        intro H; apply mem_reduceDeps in H; apply mem_reduceDeps.
        destruct H as [D1 | [D2 | [D3 | [D4 | D5]]]].
        - destruct D1 as [n1 [v1 [f1 [_ [_ [Hsrc _]]]]]]; discriminate Hsrc.
        - destruct D2 as [p [m0 [vs0 [HD [Hsrc [Htn Htvs]]]]]].
          destruct p as [qn qv]; unfold embedPkg in Hsrc; simpl in Hsrc.
          injection Hsrc as E1 E2; subst qn qv.
          right; left; exists (n, v), m0, vs0.
          split; [rewrite FeatDepRelFibred.mem_tailFibre;
                  split; [exact HD | reflexivity] |].
          split; [reflexivity | split; [exact Htn | exact Htvs]].
        - destruct D3
            as [p [m0 [vs0 [fs0 [f [HD [E0 [Hf [Hsrc [Htn Htvs]]]]]]]]]].
          destruct p as [qn qv]; unfold embedPkg in Hsrc; simpl in Hsrc.
          injection Hsrc as E1 E2; subst qn qv.
          right; right; left; exists (n, v), m0, vs0, fs0, f.
          split; [rewrite FeatDepRelFibred.mem_tailFibre;
                  split; [exact HD | reflexivity] |].
          split; [exact E0 | split; [exact Hf |]].
          split; [reflexivity | split; [exact Htn | exact Htvs]].
        - destruct D4 as [n1 [v1 [f1 [m0 [vs0 [_ [Hsrc _]]]]]]];
            discriminate Hsrc.
        - destruct D5
            as [n1 [v1 [f1 [m0 [vs0 [fs0 [f' [_ [_ [_ [Hsrc _]]]]]]]]]]];
            discriminate Hsrc.
      Qed.

      Module PkgFibred := FibredRel N V Pkg PkgSet.
      Module SupportFibred := FibredRel Pkg F PkgF SupportSet.
      Module AddlDepRelFibred :=
        FibredLabelledRel PkgF N VSFS AddlDepElt AddlDepRel.
      Theorem dependees_lookupFeatPkg : forall R support Df Da n v f,
          T.dependees (reduceDeps R support Df Da) (Name.FeatPkg n f, v) =
          T.dependees
            (reduceDeps (PkgFibred.idFibre R (n, v))
               (SupportFibred.idFibre support ((n, v), f)) FeatDepRel.empty
               (AddlDepRelFibred.tailFibre Da ((n, v), f)))
            (Name.FeatPkg n f, v).
      Proof.
        intros R support Df Da n v f; apply T.dependees_ext; intros [m ws].
        split; [| apply reduceDeps_mono;
                  [apply PkgFibred.idFibre_subset
                  | apply SupportFibred.idFibre_subset
                  | apply FeatDepRel.empty_subset
                  | apply AddlDepRelFibred.tailFibre_subset]].
        intro H; apply mem_reduceDeps in H; apply mem_reduceDeps.
        destruct H as [D1 | [D2 | [D3 | [D4 | D5]]]].
        - destruct D1 as [n1 [v1 [f1 [Hsupp [HR [Hsrc [Htn Htvs]]]]]]].
          injection Hsrc as E1 E2 E3; subst n1 f1 v1.
          left; exists n, v, f.
          split; [rewrite SupportFibred.mem_idFibre;
                  split; [exact Hsupp | reflexivity] |].
          split; [rewrite PkgFibred.mem_idFibre;
                  split; [exact HR | reflexivity] |].
          split; [reflexivity | split; [exact Htn | exact Htvs]].
        - destruct D2 as [p [m0 [vs0 [_ [Hsrc _]]]]].
          destruct p as [qn qv]; unfold embedPkg in Hsrc; simpl in Hsrc;
            discriminate Hsrc.
        - destruct D3 as [p [m0 [vs0 [fs0 [f1 [_ [_ [_ [Hsrc _]]]]]]]]].
          destruct p as [qn qv]; unfold embedPkg in Hsrc; simpl in Hsrc;
            discriminate Hsrc.
        - destruct D4 as [n1 [v1 [f1 [m0 [vs0 [Hda [Hsrc [Htn Htvs]]]]]]]].
          injection Hsrc as E1 E2 E3; subst n1 f1 v1.
          right; right; right; left; exists n, v, f, m0, vs0.
          split; [rewrite AddlDepRelFibred.mem_tailFibre;
                  split; [exact Hda | reflexivity] |].
          split; [reflexivity | split; [exact Htn | exact Htvs]].
        - destruct D5 as
            [n1 [v1 [f1 [m0 [vs0 [fs0 [f'
              [Hda [E0 [Hf' [Hsrc [Htn Htvs]]]]]]]]]]]].
          injection Hsrc as E1 E2 E3; subst n1 f1 v1.
          right; right; right; right; exists n, v, f, m0, vs0, fs0, f'.
          split; [rewrite AddlDepRelFibred.mem_tailFibre;
                  split; [exact Hda | reflexivity] |].
          split; [exact E0 | split; [exact Hf' |]].
          split; [reflexivity | split; [exact Htn | exact Htvs]].
      Qed.

      Theorem reduceReal_lookupOrig : forall R support n v,
          T.PkgSet.In (Name.Orig n, v) (reduceReal R support) <->
          T.PkgSet.In (Name.Orig n, v)
            (reduceReal (PkgFibred.idFibre R (n, v)) SupportSet.empty).
      Proof.
        intros R support n v; rewrite !mem_reduceReal.
        split.
        - intros [[[qn qv] [HR Hq]] | [n1 [v1 [f1 [_ [_ Hq]]]]]].
          + unfold embedPkg in Hq; injection Hq as <- <-.
            left; exists (n, v).
            split; [apply PkgFibred.mem_idFibre; split; [exact HR | reflexivity]
                   | reflexivity].
          + discriminate Hq.
        - intros [[[qn qv] [HR Hq]] | [n1 [v1 [f1 [Hs _]]]]].
          + apply PkgFibred.mem_idFibre in HR; destruct HR as [HR _].
            left; exists (qn, qv); split; [exact HR | exact Hq].
          + destruct (SupportSet.empty_spec Hs).
      Qed.

      Theorem reduceReal_lookupFeatPkg : forall R support n v f,
          T.PkgSet.In (Name.FeatPkg n f, v) (reduceReal R support) <->
          T.PkgSet.In (Name.FeatPkg n f, v)
            (reduceReal (PkgFibred.idFibre R (n, v))
               (SupportFibred.idFibre support ((n, v), f))).
      Proof.
        intros R support n v f; rewrite !mem_reduceReal.
        split.
        - intros [[[qn qv] [_ Hq]] | [n1 [v1 [f1 [Hs [HR Hq]]]]]].
          + unfold embedPkg in Hq; discriminate Hq.
          + injection Hq as <- <- <-.
            right; exists n, v, f.
            split; [apply SupportFibred.mem_idFibre;
                    split; [exact Hs | reflexivity] |].
            split; [apply PkgFibred.mem_idFibre; split; [exact HR | reflexivity]
                   | reflexivity].
        - intros [[[qn qv] [_ Hq]] | [n1 [v1 [f1 [Hs [HR Hq]]]]]].
          + unfold embedPkg in Hq; discriminate Hq.
          + apply SupportFibred.mem_idFibre in Hs; destruct Hs as [Hs _].
            apply PkgFibred.mem_idFibre in HR; destruct HR as [HR _].
            right; exists n1, v1, f1;
              split; [exact Hs | split; [exact HR | exact Hq]].
      Qed.
    End Lookup.
  End Reduction.

End Feature.
