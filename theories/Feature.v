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
      - intros [[[n v] f] [Hs Hq]]; cbn beta iota in Hq.
        destruct (PkgSet.mem (n, v) R) eqn:Em; [| discriminate].
        injection Hq as <-; apply PkgSet.mem_spec in Em; exists n, v, f; auto.
      - intros [n [v [f [Hs [HR ->]]]]]; exists ((n, v), f).
        split; [exact Hs | cbn beta iota].
        apply PkgSet.mem_spec in HR; rewrite HR; reflexivity.
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

    Lemma mem_reduceReal_orig : forall R support n v,
        T.PkgSet.In (Name.Orig n, v) (reduceReal R support) <->
        PkgSet.In (n, v) R.
    Proof.
      intros R support n v; rewrite mem_reduceReal; split.
      - intros [[[pn pv] [HR E]] | [n' [v' [f' [_ [_ E]]]]]]; cbn in E;
          [injection E as -> ->; exact HR | discriminate E].
      - intro HR; left; exists (n, v); split; [exact HR | reflexivity].
    Qed.

    Lemma mem_reduceReal_featPkg : forall R support n f v,
        T.PkgSet.In (Name.FeatPkg n f, v) (reduceReal R support) <->
        SupportSet.In ((n, v), f) support /\ PkgSet.In (n, v) R.
    Proof.
      intros R support n f v; rewrite mem_reduceReal; split.
      - intros [[[pn pv] [_ E]] | [n' [v' [f' [Hs [HR E]]]]]]; cbn in E;
          [discriminate E | injection E as -> -> ->; auto].
      - intros [Hs HR]; right; exists n, v, f; auto.
    Qed.

    Inductive EncodedEdge (R : PkgSet.t) (support : SupportSet.t)
        (Df : FeatDepRel.t) (Da : AddlDepRel.t) : T.DepElt.t -> Prop :=
    | EdgeSupport : forall n v f,
        SupportSet.In ((n, v), f) support -> PkgSet.In (n, v) R ->
        EncodedEdge R support Df Da
          ((Name.FeatPkg n f, v), (Name.Orig n, T.VSet.singleton v))
    | EdgeDepOrig : forall n v m vs,
        FeatDepRel.In ((n, v), (m, (vs, FSet.empty))) Df ->
        EncodedEdge R support Df Da
          ((Name.Orig n, v), (Name.Orig m, embedVS vs))
    | EdgeDepFeatPkg : forall n v m vs fs f,
        FeatDepRel.In ((n, v), (m, (vs, fs))) Df ->
        FSet.is_empty fs = false -> FSet.In f fs ->
        EncodedEdge R support Df Da
          ((Name.Orig n, v), (Name.FeatPkg m f, embedVS vs))
    | EdgeAddlOrig : forall n v f m vs,
        AddlDepRel.In (((n, v), f), (m, (vs, FSet.empty))) Da ->
        EncodedEdge R support Df Da
          ((Name.FeatPkg n f, v), (Name.Orig m, embedVS vs))
    | EdgeAddlFeatPkg : forall n v f m vs fs f',
        AddlDepRel.In (((n, v), f), (m, (vs, fs))) Da ->
        FSet.is_empty fs = false -> FSet.In f' fs ->
        EncodedEdge R support Df Da
          ((Name.FeatPkg n f, v), (Name.FeatPkg m f', embedVS vs)).

    Lemma mem_reduceDeps : forall R support Df Da (y : T.DepElt.t),
        T.DepRel.In y (reduceDeps R support Df Da) <->
        EncodedEdge R support Df Da y.
    Proof.
      intros R support Df Da y; unfold reduceDeps, supportEdges,
        featDepOrigEdges, featDepFeatPkgEdges, addlDepOrigEdges,
        addlDepFeatPkgEdges.
      rewrite !T.DepRel.union_spec, SOsd.mem_filterMap, SOfd.mem_filterMap,
        SOfd.mem_unionMap, SOad.mem_filterMap, SOad.mem_unionMap.
      split.
      - intros [[[[n v] f] [Hs Hy]] | [[[[n v] [m [vs fs]]] [Hd Hy]]
          | [[[[n v] [m [vs fs]]] [Hd Hy]] | [[[[[n v] f] [m [vs fs]]] [Hd Hy]]
          | [[[[n v] f] [m [vs fs]]] [Hd Hy]]]]]];
          cbn beta iota delta [embedPkg] in Hy.
        + destruct (PkgSet.mem (n, v) R) eqn:E; [| discriminate].
          injection Hy as <-; apply PkgSet.mem_spec in E.
          apply EdgeSupport; assumption.
        + destruct (FSet.is_empty fs) eqn:E; [| discriminate].
          injection Hy as <-; apply FSet.is_empty_iff in E; subst fs.
          apply EdgeDepOrig; exact Hd.
        + destruct (FSet.is_empty fs) eqn:E; [destruct (SOfd.empty_in _ Hy) |].
          apply SOfsd.mem_map in Hy as [f [Hf ->]].
          eapply EdgeDepFeatPkg; eassumption.
        + destruct (FSet.is_empty fs) eqn:E; [| discriminate].
          injection Hy as <-; apply FSet.is_empty_iff in E; subst fs.
          apply EdgeAddlOrig; exact Hd.
        + destruct (FSet.is_empty fs) eqn:E; [destruct (SOad.empty_in _ Hy) |].
          apply SOfsd.mem_map in Hy as [f' [Hf' ->]].
          eapply EdgeAddlFeatPkg; eassumption.
      - intros [n v f Hs HR | n v m vs Hd | n v m vs fs f Hd E Hf
          | n v f m vs Hd | n v f m vs fs f' Hd E Hf'].
        + left; exists ((n, v), f); split; [exact Hs | cbn beta iota].
          apply PkgSet.mem_spec in HR; rewrite HR; reflexivity.
        + right; left; exists ((n, v), (m, (vs, FSet.empty))).
          split; [exact Hd | reflexivity].
        + do 2 right; left; exists ((n, v), (m, (vs, fs))).
          split; [exact Hd | cbn beta iota; rewrite E].
          apply SOfsd.mem_map; exists f; split; [exact Hf | reflexivity].
        + do 3 right; left; exists (((n, v), f), (m, (vs, FSet.empty))).
          split; [exact Hd | reflexivity].
        + do 4 right; exists (((n, v), f), (m, (vs, fs))).
          split; [exact Hd | cbn beta iota; rewrite E].
          apply SOfsd.mem_map; exists f'; split; [exact Hf' | reflexivity].
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
          split; [exact HS | cbn beta iota; apply dec_refl].
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

    (* A dependency and an additional dependency are closed over by the same
       argument; only the node their edges leave from differs. *)
    Lemma dep_closure_step : forall RR D r S q n vs fs,
        T.IsResolution RR D r S ->
        (forall m f v, T.PkgSet.In (Name.FeatPkg m f, v) S ->
           T.PkgSet.In (Name.Orig m, v) S) ->
        T.PkgSet.In q S ->
        (fs = FSet.empty -> T.DepRel.In (q, (Name.Orig n, embedVS vs)) D) ->
        (forall f, FSet.is_empty fs = false -> FSet.In f fs ->
           T.DepRel.In (q, (Name.FeatPkg n f, embedVS vs)) D) ->
        exists v, VSet.In v vs /\
          exists fs', FSet.Subset fs fs' /\
            FeaturedSet.In ((n, v), fs') (featureResolution S).
    Proof.
      intros RR D r S q n vs fs [_ _ Hdep Huniq] HfeatOrig HqS Horig Hfeat.
      destruct (FSet.is_empty fs) eqn:E.
      - apply FSet.is_empty_iff in E.
        destruct (Hdep _ HqS _ _ (Horig E)) as [v [Hv HvS]].
        exists v; split; [apply mem_embedVS; exact Hv |].
        exists (featsOf n v S); split.
        + subst fs; intros x Hx; destruct (FSet.empty_spec Hx).
        + apply mem_featureResolution; exists n, v;
            split; [exact HvS | reflexivity].
      - destruct (FSet.choose_nonempty _ E) as [f0 Hf0].
        destruct (Hdep _ HqS _ _ (Hfeat f0 eq_refl Hf0)) as [v [Hv HvS]].
        apply mem_embedVS in Hv; apply HfeatOrig in HvS.
        exists v; split; [exact Hv |].
        exists (featsOf n v S); split.
        + intros f Hf; apply featsOf_spec.
          destruct (Hdep _ HqS _ _ (Hfeat f eq_refl Hf)) as [v' [_ Hv'S]].
          rewrite (Huniq _ _ _ HvS (HfeatOrig _ _ _ Hv'S)); exact Hv'S.
        + apply mem_featureResolution; exists n, v;
            split; [exact HvS | reflexivity].
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
      pose proof Hres as [Hsub Hroot Hdep Huniq].
      destruct r as [rn rv].
      unfold embedPkg in Hroot; simpl in Hroot.
      assert (HorigR : forall n v,
                 T.PkgSet.In (Name.Orig n, v) S -> PkgSet.In (n, v) R)
        by (intros n v HS; exact (proj1 (mem_reduceReal_orig _ _ _ _)
                                    (Hsub _ HS))).
      assert (HfeatR : forall n f v,
                 T.PkgSet.In (Name.FeatPkg n f, v) S ->
                 SupportSet.In ((n, v), f) support /\ PkgSet.In (n, v) R)
        by (intros n f v HS; exact (proj1 (mem_reduceReal_featPkg _ _ _ _ _)
                                      (Hsub _ HS))).
      assert (HfeatOrig : forall n f v,
                 T.PkgSet.In (Name.FeatPkg n f, v) S ->
                 T.PkgSet.In (Name.Orig n, v) S).
      { intros n f v HS; destruct (HfeatR _ _ _ HS) as [Hs HR].
        assert (Hd : T.DepRel.In
                       ((Name.FeatPkg n f, v),
                        (Name.Orig n, T.VSet.singleton v))
                       (reduceDeps R support Df Da))
          by (apply mem_reduceDeps, EdgeSupport; assumption).
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
          + exfalso; exact (Hnosupp f (proj1 (HfeatR _ _ _ H))).
          + exfalso; exact (FSet.empty_spec H). }
        rewrite <- Hfe.
        apply mem_featureResolution; exists rn, rv;
          split; [exact Hroot | reflexivity].
      - intros p fs_p Hmem n vs fs Hdf.
        apply mem_featureResolution in Hmem;
          destruct Hmem as [pn [pv [HpS Heq]]].
        injection Heq as E1 E2; subst p fs_p.
        apply (dep_closure_step _ _ _ S _ n vs fs Hres HfeatOrig HpS);
          [intro; subst fs | intros f E Hf]; apply mem_reduceDeps;
          [apply EdgeDepOrig | eapply EdgeDepFeatPkg]; eassumption.
      - intros p fs_p Hmem f Hf n vs fs Hda.
        apply mem_featureResolution in Hmem;
          destruct Hmem as [pn [pv [HpS Heq]]].
        injection Heq as E1 E2; subst p fs_p.
        rewrite featsOf_spec in Hf.
        apply (dep_closure_step _ _ _ S _ n vs fs Hres HfeatOrig Hf);
          [intro; subst fs | intros f' E Hf']; apply mem_reduceDeps;
          [apply EdgeAddlOrig | eapply EdgeAddlFeatPkg]; eassumption.
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
        exact (proj1 (HfeatR _ _ _ Hf)).
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
      - intros q Hq; rewrite mem_coreResolution in Hq.
        destruct Hq as [[n [v [fs [HS ->]]]] | [n [v [fs [f [HS [Hf ->]]]]]]].
        + apply mem_reduceReal_orig; exact (Hsubset _ _ HS).
        + apply mem_reduceReal_featPkg;
            exact (conj (Hsm n v fs f HS Hf) (Hsubset _ _ HS)).
      - rewrite mem_coreResolution.
        left; exists rn, rv, FSet.empty; split; [exact Hrootm | reflexivity].
      - intros q Hq m vs Hd.
        rewrite mem_coreResolution in Hq; rewrite mem_reduceDeps in Hd.
        destruct Hq as [[pn [pv [fs [HS ->]]]] |
                        [pn [pv [fs [f0 [HS [Hf0 ->]]]]]]];
          inversion Hd; subst.
        + destruct (Hdepc _ _ HS _ _ _ ltac:(eassumption))
            as [v' [Hv' [fs' [_ Hfs']]]].
          exists v'; split; [apply mem_embedVS; exact Hv' |].
          rewrite mem_coreResolution; left.
          do 3 eexists; split; [exact Hfs' | reflexivity].
        + destruct (Hdepc _ _ HS _ _ _ ltac:(eassumption))
            as [v' [Hv' [fs' [Hsub' Hfs']]]].
          exists v'; split; [apply mem_embedVS; exact Hv' |].
          rewrite mem_coreResolution; right.
          do 4 eexists; split; [exact Hfs' |].
          split; [apply Hsub'; eassumption | reflexivity].
        + eexists; split; [apply SOvt.singleton_in; reflexivity |].
          rewrite mem_coreResolution; left.
          do 3 eexists; split; [exact HS | reflexivity].
        + destruct (Haddlc _ _ HS _ Hf0 _ _ _ ltac:(eassumption))
            as [v' [Hv' [fs' [_ Hfs']]]].
          exists v'; split; [apply mem_embedVS; exact Hv' |].
          rewrite mem_coreResolution; left.
          do 3 eexists; split; [exact Hfs' | reflexivity].
        + destruct (Haddlc _ _ HS _ Hf0 _ _ _ ltac:(eassumption))
            as [v' [Hv' [fs' [Hsub' Hfs']]]].
          exists v'; split; [apply mem_embedVS; exact Hv' |].
          rewrite mem_coreResolution; right.
          do 4 eexists; split; [exact Hfs' |].
          split; [apply Hsub'; eassumption | reflexivity].
      - intros n v1 v2 H1 H2.
        rewrite mem_coreResolution in H1, H2.
        destruct H1 as [[n1 [w1 [fs1 [HS1 Hq1]]]] |
                        [n1 [w1 [fs1 [f1 [HS1 [Hf1 Hq1]]]]]]];
          destruct H2 as [[n2 [w2 [fs2 [HS2 Hq2]]]] |
                          [n2 [w2 [fs2 [f2 [HS2 [Hf2 Hq2]]]]]]].
        + injection Hq1 as E1 E2; subst n v1.
          injection Hq2 as E3 E4; subst n2 v2.
          exact (Hvu _ _ _ _ _ HS1 HS2).
        + injection Hq1 as E1 E2; subst n v1.
          discriminate Hq2.
        + injection Hq1 as E1 E2; subst n v1.
          discriminate Hq2.
        + injection Hq1 as E1 E2; subst n v1.
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
      Module PkgFibred := FibredRel N V Pkg PkgSet.
      Module SupportFibred := FibredRel Pkg F PkgF SupportSet.
      Module AddlDepRelFibred :=
        FibredLabelledRel PkgF N VSFS AddlDepElt AddlDepRel.
      (* support is a relation between packages and features, so neither of
         its fibres alone cuts it down to the support pairs that introduce
         one name: those are pinned by the base name and the feature at
         once. *)
      Definition supportFibre (support : SupportSet.t) (n : N.t) (f : F.t)
          : SupportSet.t :=
        SupportSet.filter (fun '((m, _), g) =>
            if N.eq_dec m n then if F.eq_dec g f then true else false
            else false)
          support.

      Lemma mem_supportFibre :
        forall support (n m : N.t) (v : V.t) (f g : F.t),
          SupportSet.In ((m, v), g) (supportFibre support n f) <->
          SupportSet.In ((m, v), g) support /\ m = n /\ g = f.
      Proof.
        intros support n m v f g; unfold supportFibre.
        rewrite SupportSet.filter_spec'; cbn beta iota.
        destruct (N.eq_dec m n); [destruct (F.eq_dec g f) |];
          intuition congruence.
      Qed.

      Theorem versions_lookupOrig :
        forall R support n,
          T.versions (reduceReal R support) (Name.Orig n) =
          T.versions (reduceReal (PkgFibred.tailFibre R n) SupportSet.empty)
            (Name.Orig n).
      Proof.
        intros R support n; apply T.versions_ext; intro v.
        rewrite !mem_reduceReal_orig, PkgFibred.mem_tailFibre; intuition.
      Qed.

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
        inversion H; subst.
        - apply EdgeDepOrig, FeatDepRelFibred.mem_tailFibre;
            split; [eassumption | reflexivity].
        - eapply EdgeDepFeatPkg;
            [apply FeatDepRelFibred.mem_tailFibre;
               split; [eassumption | reflexivity]
            | eassumption | eassumption].
      Qed.

      Theorem versions_lookupFeatPkg : forall R support n f,
          T.versions (reduceReal R support) (Name.FeatPkg n f) =
          T.versions
            (reduceReal (PkgFibred.tailFibre R n) (supportFibre support n f))
            (Name.FeatPkg n f).
      Proof.
        intros R support n f; apply T.versions_ext; intro v.
        rewrite !mem_reduceReal_featPkg, mem_supportFibre,
          PkgFibred.mem_tailFibre; intuition.
      Qed.

      Lemma dependees_lookupFeatPkg_any : forall R support Df Da n v f,
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
        inversion H; subst.
        - apply EdgeSupport;
            [apply SupportFibred.mem_idFibre | apply PkgFibred.mem_idFibre];
            (split; [eassumption | reflexivity]).
        - apply EdgeAddlOrig, AddlDepRelFibred.mem_tailFibre;
            split; [eassumption | reflexivity].
        - eapply EdgeAddlFeatPkg;
            [apply AddlDepRelFibred.mem_tailFibre;
               split; [eassumption | reflexivity]
            | eassumption | eassumption].
      Qed.

      (* The membership premise is what collapses the fibres to singletons. *)
      Theorem dependees_lookupFeatPkg : forall R support Df Da n v f,
          T.PkgSet.In (Name.FeatPkg n f, v) (reduceReal R support) ->
          T.dependees (reduceDeps R support Df Da) (Name.FeatPkg n f, v) =
          T.dependees
            (reduceDeps (PkgSet.singleton (n, v))
               (SupportSet.singleton ((n, v), f)) FeatDepRel.empty
               (AddlDepRelFibred.tailFibre Da ((n, v), f)))
            (Name.FeatPkg n f, v).
      Proof.
        intros R support Df Da n v f Hin.
        apply mem_reduceReal_featPkg in Hin; destruct Hin as [Hs HR].
        assert (PkgFibred.idFibre R (n, v) = PkgSet.singleton (n, v)) as ER.
        { apply PkgSet.ext; intro x.
          rewrite PkgFibred.mem_idFibre, PkgSet.singleton_spec.
          split; [intros [_ E]; exact E
                 | intro E; split; [rewrite E; exact HR | exact E]]. }
        assert (SupportFibred.idFibre support ((n, v), f)
                = SupportSet.singleton ((n, v), f)) as ES.
        { apply SupportSet.ext; intro x.
          rewrite SupportFibred.mem_idFibre, SupportSet.singleton_spec.
          split; [intros [_ E]; exact E
                 | intro E; split; [rewrite E; exact Hs | exact E]]. }
        rewrite dependees_lookupFeatPkg_any, ER, ES; reflexivity.
      Qed.

    End Lookup.
  End Reduction.

End Feature.
