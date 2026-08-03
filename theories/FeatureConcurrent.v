From Stdlib Require Import MSets.
From PackageCalculus Require Import Prelude Core Feature.

Create HintDb cmp_fconc.
Create Rewrite HintDb cmp_fconc.

Module FeatureConcurrent (N V F G : UsualOrderedType).
  Module Feat := Feature N V F.
  Module C := Feat.C.
  Module Pkg := C.Pkg.
  Module PkgSet := C.PkgSet.
  Module VSet := C.VSet.

  Module ParentElt := PairUOT Pkg Pkg.
  Module ParentRel := FSetUOT ParentElt.

  Record IsResolution
      (R : PkgSet.t) (support : Feat.SupportSet.t)
      (Df : Feat.FeatDepRel.t) (Da : Feat.AddlDepRel.t)
      (g : V.t -> G.t) (r : Pkg.t)
      (S : Feat.FeaturedSet.t) (pi : ParentRel.t) : Prop :=
    { res_no_root_support : forall f, ~ Feat.SupportSet.In (r, f) support
    ; res_subset : forall p fs, Feat.FeaturedSet.In (p, fs) S -> PkgSet.In p R
    ; res_root_mem : Feat.FeaturedSet.In (r, Feat.FSet.empty) S
    ; res_feature_unification :
        forall n v fs fs',
          Feat.FeaturedSet.In ((n, v), fs) S ->
          Feat.FeaturedSet.In ((n, v), fs') S -> fs = fs'
    ; res_parent_closure :
        forall p fs_p, Feat.FeaturedSet.In (p, fs_p) S ->
        forall n vs fs, Feat.FeatDepRel.In (p, (n, (vs, fs))) Df ->
        exists! v, VSet.In v vs /\
          (exists fs', Feat.FSet.Subset fs fs' /\
             Feat.FeaturedSet.In ((n, v), fs') S) /\
          ParentRel.In ((n, v), p) pi
    ; res_parent_closure_addl :
        forall p fs_p, Feat.FeaturedSet.In (p, fs_p) S ->
        forall f, Feat.FSet.In f fs_p ->
        forall n vs fs, Feat.AddlDepRel.In ((p, f), (n, (vs, fs))) Da ->
        exists! v, VSet.In v vs /\
          (exists fs', Feat.FSet.Subset fs fs' /\
             Feat.FeaturedSet.In ((n, v), fs') S) /\
          ParentRel.In ((n, v), p) pi
    ; res_pi_functional :
        forall n v v' p,
          ParentRel.In ((n, v), p) pi -> ParentRel.In ((n, v'), p) pi -> v = v'
    ; res_version_granularity :
        forall n v v' fs fs',
          Feat.FeaturedSet.In ((n, v), fs) S ->
          Feat.FeaturedSet.In ((n, v'), fs') S ->
          v <> v' -> g v <> g v'
    ; res_support_mem :
        forall n v fs f,
          Feat.FeaturedSet.In ((n, v), fs) S -> Feat.FSet.In f fs ->
          Feat.SupportSet.In ((n, v), f) support }.

  Module Reduction.
    Module OrigName := PairUOT N G.
    Module OrigNameF := UOTCompareFacts OrigName.
    Module FeatName := TripleUOT N F G.
    Module FeatNameF := UOTCompareFacts FeatName.
    Module InterName := TripleUOT N V N.
    Module InterNameF := UOTCompareFacts InterName.
    Module InterFTail := TripleUOT V N F.
    Module InterFName := PairUOT N InterFTail.
    Module InterFNameF := UOTCompareFacts InterFName.
    Module InterATail := TripleUOT F N F.
    Module InterAName := TripleUOT N V InterATail.
    Module InterANameF := UOTCompareFacts InterAName.
    #[local] Hint Rewrite OrigNameF.compare_eq_iff FeatNameF.compare_eq_iff
      InterNameF.compare_eq_iff InterFNameF.compare_eq_iff
      InterANameF.compare_eq_iff : cmp_fconc.
    #[local] Hint Extern 1 => cmp_by OrigNameF.compare_antisym : cmp_fconc.
    #[local] Hint Extern 1 => cmp_by FeatNameF.compare_antisym : cmp_fconc.
    #[local] Hint Extern 1 => cmp_by InterNameF.compare_antisym : cmp_fconc.
    #[local] Hint Extern 1 => cmp_by InterFNameF.compare_antisym : cmp_fconc.
    #[local] Hint Extern 1 => cmp_by InterANameF.compare_antisym : cmp_fconc.
    #[local] Hint Extern 1 => cmp_by OrigNameF.compare_lt_trans : cmp_fconc.
    #[local] Hint Extern 1 => cmp_by FeatNameF.compare_lt_trans : cmp_fconc.
    #[local] Hint Extern 1 => cmp_by InterNameF.compare_lt_trans : cmp_fconc.
    #[local] Hint Extern 1 => cmp_by InterFNameF.compare_lt_trans : cmp_fconc.
    #[local] Hint Extern 1 => cmp_by InterANameF.compare_lt_trans : cmp_fconc.

    (* A fully abstract name interface would demand four more intermediate*
       constructor families; the encoding never emits them, so Name omits
       them. *)
    Module Name.
      Inductive name : Type :=
      | GranularOrig (n : N.t) (w : G.t)
      | GranularFeatPkg (n : N.t) (f : F.t) (w : G.t)
      | Intermediate (n : N.t) (v : V.t) (m : N.t)
      | IntermediateF (n : N.t) (v : V.t) (m : N.t) (f : F.t)
      | IntermediateA (n : N.t) (v : V.t) (f : F.t) (m : N.t) (f' : F.t).
      Definition t := name.

      Definition compare (x y : t) : comparison :=
        match x, y with
        | GranularOrig n1 w1, GranularOrig n2 w2 =>
            OrigName.compare (n1, w1) (n2, w2)
        | GranularOrig _ _, _ => Lt
        | GranularFeatPkg _ _ _, GranularOrig _ _ => Gt
        | GranularFeatPkg n1 f1 w1, GranularFeatPkg n2 f2 w2 =>
            FeatName.compare (n1, (f1, w1)) (n2, (f2, w2))
        | GranularFeatPkg _ _ _, _ => Lt
        | Intermediate n1 v1 m1, Intermediate n2 v2 m2 =>
            InterName.compare (n1, (v1, m1)) (n2, (v2, m2))
        | Intermediate _ _ _, GranularOrig _ _ => Gt
        | Intermediate _ _ _, GranularFeatPkg _ _ _ => Gt
        | Intermediate _ _ _, _ => Lt
        | IntermediateF n1 v1 m1 f1, IntermediateF n2 v2 m2 f2 =>
            InterFName.compare (n1, (v1, (m1, f1))) (n2, (v2, (m2, f2)))
        | IntermediateF _ _ _ _, IntermediateA _ _ _ _ _ => Lt
        | IntermediateF _ _ _ _, _ => Gt
        | IntermediateA n1 v1 f1 m1 g1, IntermediateA n2 v2 f2 m2 g2 =>
            InterAName.compare (n1, (v1, (f1, (m1, g1))))
              (n2, (v2, (f2, (m2, g2))))
        | IntermediateA _ _ _ _ _, _ => Gt
        end.

      Lemma compare_eq_iff : forall x y, compare x y = Eq <-> x = y.
      Proof. cmp_eq_iff cmp_fconc. Qed.

      Lemma compare_antisym : forall x y, compare y x = CompOpp (compare x y).
      Proof. cmp_antisym cmp_fconc. Qed.

      Lemma compare_lt_trans : forall x y z,
          compare x y = Lt -> compare y z = Lt -> compare x z = Lt.
      Proof. cmp_lt_trans cmp_fconc. Qed.
    End Name.
    Module NameOT := UOTFromCompare Name.

    Module T := Core NameOT V.

    Definition granularOf (g : V.t -> G.t) (q : Feat.Reduction.T.Pkg.t)
        : T.Pkg.t :=
      match q with
      | (Feat.Reduction.Name.Orig n, v) =>
          (Name.GranularOrig n (g v), v)
      | (Feat.Reduction.Name.FeatPkg n f, v) =>
          (Name.GranularFeatPkg n f (g v), v)
      end.

    Definition embedOrigPkg (g : V.t -> G.t) (p : Pkg.t) : T.Pkg.t :=
      let '(n, v) := p in (Name.GranularOrig n (g v), v).

    Definition singVS (u : V.t) : T.VSet.t := T.VSet.singleton u.

    Module SOvv := SetOps V V VSet T.VSet.
    Definition embedVS (vs : VSet.t) : T.VSet.t :=
      SOvv.map (fun v => v) vs.

    Module SOqp :=
      SetOps Feat.Reduction.T.Pkg T.Pkg Feat.Reduction.T.PkgSet T.PkgSet.
    Definition granularReal (R : PkgSet.t) (support : Feat.SupportSet.t)
        (g : V.t -> G.t) : T.PkgSet.t :=
      SOqp.map (granularOf g) (Feat.Reduction.reduceReal R support).

    Module SOvp := SetOps V T.Pkg VSet T.PkgSet.
    Module SOfp := SetOps Feat.FeatDepElt T.Pkg Feat.FeatDepRel T.PkgSet.
    Definition fInterReal (Df : Feat.FeatDepRel.t) : T.PkgSet.t :=
      SOfp.unionMap (fun '((n, v), (m, (vs, _))) =>
          SOvp.map (fun u => (Name.Intermediate n v m, u)) vs)
        Df.

    Module SOfsp := SetOps F T.Pkg Feat.FSet T.PkgSet.
    Definition fInterFeatReal (Df : Feat.FeatDepRel.t) : T.PkgSet.t :=
      SOfp.unionMap (fun '((n, v), (m, (vs, fs))) =>
          SOvp.unionMap (fun u =>
              SOfsp.map (fun f => (Name.IntermediateF n v m f, u)) fs)
            vs)
        Df.

    Module SOap := SetOps Feat.AddlDepElt T.Pkg Feat.AddlDepRel T.PkgSet.
    Definition aInterReal (Da : Feat.AddlDepRel.t) : T.PkgSet.t :=
      SOap.unionMap (fun '(((n, v), _), (m, (vs, _))) =>
          SOvp.map (fun u => (Name.Intermediate n v m, u)) vs)
        Da.

    Definition aInterFeatReal (Da : Feat.AddlDepRel.t) : T.PkgSet.t :=
      SOap.unionMap (fun '(((n, v), f), (m, (vs, fs))) =>
          SOvp.unionMap (fun u =>
              SOfsp.map (fun f' => (Name.IntermediateA n v f m f', u)) fs)
            vs)
        Da.

    Definition reduceReal
        (R : PkgSet.t) (support : Feat.SupportSet.t)
        (Df : Feat.FeatDepRel.t) (Da : Feat.AddlDepRel.t)
        (g : V.t -> G.t) : T.PkgSet.t :=
      T.PkgSet.union (granularReal R support g)
        (T.PkgSet.union (fInterReal Df)
           (T.PkgSet.union (fInterFeatReal Df)
              (T.PkgSet.union (aInterReal Da) (aInterFeatReal Da)))).

    Module SOsd := SetOps Feat.PkgF T.DepElt Feat.SupportSet T.DepRel.
    Definition supportEdges (R : PkgSet.t) (support : Feat.SupportSet.t)
        (g : V.t -> G.t) : T.DepRel.t :=
      SOsd.filterMap (fun '((n, v), f) =>
          if PkgSet.mem (n, v) R
          then Some ((Name.GranularFeatPkg n f (g v), v),
                     (Name.GranularOrig n (g v), singVS v))
          else None)
        support.

    Module SOfd := SetOps Feat.FeatDepElt T.DepElt Feat.FeatDepRel T.DepRel.
    Definition fDepToInterEdges (Df : Feat.FeatDepRel.t)
        (g : V.t -> G.t) : T.DepRel.t :=
      SOfd.map (fun '((n, v), (m, (vs, _))) =>
          ((Name.GranularOrig n (g v), v),
           (Name.Intermediate n v m, embedVS vs)))
        Df.

    Module SOvd := SetOps V T.DepElt VSet T.DepRel.
    Definition fInterToOrigEdges (Df : Feat.FeatDepRel.t)
        (g : V.t -> G.t) : T.DepRel.t :=
      SOfd.unionMap (fun '((n, v), (m, (vs, _))) =>
          SOvd.map (fun u =>
              ((Name.Intermediate n v m, u),
               (Name.GranularOrig m (g u), singVS u)))
            vs)
        Df.

    Module SOfsd := SetOps F T.DepElt Feat.FSet T.DepRel.
    Definition fDepToInterFeatEdges (Df : Feat.FeatDepRel.t)
        (g : V.t -> G.t) : T.DepRel.t :=
      SOfd.unionMap (fun '((n, v), (m, (vs, fs))) =>
          SOfsd.map (fun f =>
              ((Name.GranularOrig n (g v), v),
               (Name.IntermediateF n v m f, embedVS vs)))
            fs)
        Df.

    Definition fInterToFeatEdges (Df : Feat.FeatDepRel.t)
        (g : V.t -> G.t) : T.DepRel.t :=
      SOfd.unionMap (fun '((n, v), (m, (vs, fs))) =>
          SOvd.unionMap (fun u =>
              SOfsd.map (fun f =>
                  ((Name.IntermediateF n v m f, u),
                   (Name.GranularFeatPkg m f (g u), singVS u)))
                fs)
            vs)
        Df.

    Definition fInterFeatToInterEdges (Df : Feat.FeatDepRel.t) : T.DepRel.t :=
      SOfd.unionMap (fun '((n, v), (m, (vs, fs))) =>
          SOfsd.unionMap (fun f =>
              SOvd.map (fun u =>
                  ((Name.IntermediateF n v m f, u),
                   (Name.Intermediate n v m, singVS u)))
                vs)
            fs)
        Df.

    Module SOad := SetOps Feat.AddlDepElt T.DepElt Feat.AddlDepRel T.DepRel.
    Definition aDepToInterEdges (Da : Feat.AddlDepRel.t)
        (g : V.t -> G.t) : T.DepRel.t :=
      SOad.map (fun '(((n, v), f), (m, (vs, _))) =>
          ((Name.GranularFeatPkg n f (g v), v),
           (Name.Intermediate n v m, embedVS vs)))
        Da.

    Definition aInterToOrigEdges (Da : Feat.AddlDepRel.t)
        (g : V.t -> G.t) : T.DepRel.t :=
      SOad.unionMap (fun '(((n, v), _), (m, (vs, _))) =>
          SOvd.map (fun u =>
              ((Name.Intermediate n v m, u),
               (Name.GranularOrig m (g u), singVS u)))
            vs)
        Da.

    Definition aDepToInterFeatEdges (Da : Feat.AddlDepRel.t)
        (g : V.t -> G.t) : T.DepRel.t :=
      SOad.unionMap (fun '(((n, v), f), (m, (vs, fs))) =>
          SOfsd.map (fun f' =>
              ((Name.GranularFeatPkg n f (g v), v),
               (Name.IntermediateA n v f m f', embedVS vs)))
            fs)
        Da.

    Definition aInterToFeatEdges (Da : Feat.AddlDepRel.t)
        (g : V.t -> G.t) : T.DepRel.t :=
      SOad.unionMap (fun '(((n, v), f), (m, (vs, fs))) =>
          SOvd.unionMap (fun u =>
              SOfsd.map (fun f' =>
                  ((Name.IntermediateA n v f m f', u),
                   (Name.GranularFeatPkg m f' (g u), singVS u)))
                fs)
            vs)
        Da.

    Definition aInterFeatToInterEdges (Da : Feat.AddlDepRel.t) : T.DepRel.t :=
      SOad.unionMap (fun '(((n, v), f), (m, (vs, fs))) =>
          SOfsd.unionMap (fun f' =>
              SOvd.map (fun u =>
                  ((Name.IntermediateA n v f m f', u),
                   (Name.Intermediate n v m, singVS u)))
                vs)
            fs)
        Da.

    Definition reduceDeps
        (R : PkgSet.t) (support : Feat.SupportSet.t)
        (Df : Feat.FeatDepRel.t) (Da : Feat.AddlDepRel.t)
        (g : V.t -> G.t) : T.DepRel.t :=
      T.DepRel.union (supportEdges R support g)
        (T.DepRel.union (fDepToInterEdges Df g)
           (T.DepRel.union (fInterToOrigEdges Df g)
              (T.DepRel.union (fDepToInterFeatEdges Df g)
                 (T.DepRel.union (fInterToFeatEdges Df g)
                    (T.DepRel.union (fInterFeatToInterEdges Df)
                       (T.DepRel.union (aDepToInterEdges Da g)
                          (T.DepRel.union (aInterToOrigEdges Da g)
                             (T.DepRel.union (aDepToInterFeatEdges Da g)
                                (T.DepRel.union (aInterToFeatEdges Da g)
                                   (aInterFeatToInterEdges Da)))))))))).

    Lemma mem_embedVS : forall vs w, T.VSet.In w (embedVS vs) <-> VSet.In w vs.
    Proof.
      intros vs w; unfold embedVS.
      exact (SOvv.mem_map_inj (fun v => v) vs w (fun x y H => H)).
    Qed.

    Lemma mem_fInterReal : forall Df (y : T.Pkg.t),
        T.PkgSet.In y (fInterReal Df) <->
        exists n v m vs fs u, Feat.FeatDepRel.In ((n, v), (m, (vs, fs))) Df /\
          VSet.In u vs /\ y = (Name.Intermediate n v m, u).
    Proof.
      intros Df y; unfold fInterReal; rewrite SOfp.mem_unionMap.
      split.
      - intros [[[n v] [m [vs fs]]] [HD Hy]]; cbn beta iota in Hy.
        apply SOvp.mem_map in Hy; destruct Hy as [u [Hu Hy]].
        exists n, v, m, vs, fs, u; auto.
      - intros [n [v [m [vs [fs [u [HD [Hu ->]]]]]]]].
        exists ((n, v), (m, (vs, fs))); split; [exact HD | cbn beta iota].
        apply SOvp.mem_map; exists u; split; [exact Hu | reflexivity].
    Qed.

    Lemma mem_fInterFeatReal : forall Df (y : T.Pkg.t),
        T.PkgSet.In y (fInterFeatReal Df) <->
        exists n v m vs fs u f, Feat.FeatDepRel.In ((n, v), (m, (vs, fs))) Df /\
          VSet.In u vs /\ Feat.FSet.In f fs /\
          y = (Name.IntermediateF n v m f, u).
    Proof.
      intros Df y; unfold fInterFeatReal; rewrite SOfp.mem_unionMap.
      split.
      - intros [[[n v] [m [vs fs]]] [HD Hy]]; cbn beta iota in Hy.
        apply SOvp.mem_unionMap in Hy; destruct Hy as [u [Hu Hy]].
        apply SOfsp.mem_map in Hy; destruct Hy as [f [Hf Hy]].
        exists n, v, m, vs, fs, u, f; auto.
      - intros [n [v [m [vs [fs [u [f [HD [Hu [Hf ->]]]]]]]]]].
        exists ((n, v), (m, (vs, fs))); split; [exact HD | cbn beta iota].
        apply SOvp.mem_unionMap; exists u; split; [exact Hu |].
        apply SOfsp.mem_map; exists f; split; [exact Hf | reflexivity].
    Qed.

    Lemma mem_aInterReal : forall Da (y : T.Pkg.t),
        T.PkgSet.In y (aInterReal Da) <->
        exists n v f m vs fs u,
          Feat.AddlDepRel.In (((n, v), f), (m, (vs, fs))) Da /\
          VSet.In u vs /\ y = (Name.Intermediate n v m, u).
    Proof.
      intros Da y; unfold aInterReal; rewrite SOap.mem_unionMap.
      split.
      - intros [[[[n v] f] [m [vs fs]]] [HD Hy]]; cbn beta iota in Hy.
        apply SOvp.mem_map in Hy; destruct Hy as [u [Hu Hy]].
        exists n, v, f, m, vs, fs, u; auto.
      - intros [n [v [f [m [vs [fs [u [HD [Hu ->]]]]]]]]].
        exists (((n, v), f), (m, (vs, fs))); split; [exact HD | cbn beta iota].
        apply SOvp.mem_map; exists u; split; [exact Hu | reflexivity].
    Qed.

    Lemma mem_aInterFeatReal : forall Da (y : T.Pkg.t),
        T.PkgSet.In y (aInterFeatReal Da) <->
        exists n v f m vs fs u f',
          Feat.AddlDepRel.In (((n, v), f), (m, (vs, fs))) Da /\
          VSet.In u vs /\ Feat.FSet.In f' fs /\
          y = (Name.IntermediateA n v f m f', u).
    Proof.
      intros Da y; unfold aInterFeatReal; rewrite SOap.mem_unionMap.
      split.
      - intros [[[[n v] f] [m [vs fs]]] [HD Hy]]; cbn beta iota in Hy.
        apply SOvp.mem_unionMap in Hy; destruct Hy as [u [Hu Hy]].
        apply SOfsp.mem_map in Hy; destruct Hy as [f' [Hf' Hy]].
        exists n, v, f, m, vs, fs, u, f'; auto.
      - intros [n [v [f [m [vs [fs [u [f' [HD [Hu [Hf' ->]]]]]]]]]]].
        exists (((n, v), f), (m, (vs, fs))); split; [exact HD | cbn beta iota].
        apply SOvp.mem_unionMap; exists u; split; [exact Hu |].
        apply SOfsp.mem_map; exists f'; split; [exact Hf' | reflexivity].
    Qed.

    Lemma mem_reduceReal : forall R support Df Da g (y : T.Pkg.t),
        T.PkgSet.In y (reduceReal R support Df Da g) <->
        (exists q,
           Feat.Reduction.T.PkgSet.In q
             (Feat.Reduction.reduceReal R support) /\
           y = granularOf g q) \/
        (exists n v m vs fs u, Feat.FeatDepRel.In ((n, v), (m, (vs, fs))) Df /\
           VSet.In u vs /\ y = (Name.Intermediate n v m, u)) \/
        (exists n v m vs fs u f,
           Feat.FeatDepRel.In ((n, v), (m, (vs, fs))) Df /\
           VSet.In u vs /\ Feat.FSet.In f fs /\
           y = (Name.IntermediateF n v m f, u)) \/
        (exists n v f m vs fs u,
           Feat.AddlDepRel.In (((n, v), f), (m, (vs, fs))) Da /\
           VSet.In u vs /\ y = (Name.Intermediate n v m, u)) \/
        (exists n v f m vs fs u f',
           Feat.AddlDepRel.In (((n, v), f), (m, (vs, fs))) Da /\
           VSet.In u vs /\ Feat.FSet.In f' fs /\
           y = (Name.IntermediateA n v f m f', u)).
    Proof.
      intros R support Df Da g y; unfold reduceReal, granularReal.
      rewrite !T.PkgSet.union_spec, SOqp.mem_map, mem_fInterReal,
        mem_fInterFeatReal, mem_aInterReal, mem_aInterFeatReal.
      tauto.
    Qed.

    Lemma mem_supportEdges : forall R support g (y : T.DepElt.t),
        T.DepRel.In y (supportEdges R support g) <->
        exists n v f, Feat.SupportSet.In ((n, v), f) support /\
          PkgSet.In (n, v) R /\
          y = ((Name.GranularFeatPkg n f (g v), v),
               (Name.GranularOrig n (g v), singVS v)).
    Proof.
      intros R support g y; unfold supportEdges; rewrite SOsd.mem_filterMap.
      split.
      - intros [[[n v] f] [Hs Hy]]; cbn beta iota in Hy.
        destruct (PkgSet.mem (n, v) R) eqn:Em; [| discriminate].
        injection Hy as <-.
        exists n, v, f; repeat split;
          [exact Hs | apply PkgSet.mem_spec; exact Em].
      - intros [n [v [f [Hs [HR ->]]]]].
        exists ((n, v), f); split; [exact Hs | cbn beta iota].
        rewrite <- PkgSet.mem_spec in HR; rewrite HR; reflexivity.
    Qed.

    Lemma mem_fDepToInterEdges : forall Df g (y : T.DepElt.t),
        T.DepRel.In y (fDepToInterEdges Df g) <->
        exists n v m vs fs, Feat.FeatDepRel.In ((n, v), (m, (vs, fs))) Df /\
          y = ((Name.GranularOrig n (g v), v),
               (Name.Intermediate n v m, embedVS vs)).
    Proof.
      intros Df g y; unfold fDepToInterEdges; rewrite SOfd.mem_map.
      split.
      - intros [[[n v] [m [vs fs]]] [HD Hy]]; cbn beta iota in Hy.
        exists n, v, m, vs, fs; auto.
      - intros [n [v [m [vs [fs [HD ->]]]]]].
        exists ((n, v), (m, (vs, fs))); split; [exact HD | reflexivity].
    Qed.

    Lemma mem_fInterToOrigEdges : forall Df g (y : T.DepElt.t),
        T.DepRel.In y (fInterToOrigEdges Df g) <->
        exists n v m vs fs u, Feat.FeatDepRel.In ((n, v), (m, (vs, fs))) Df /\
          VSet.In u vs /\
          y = ((Name.Intermediate n v m, u),
               (Name.GranularOrig m (g u), singVS u)).
    Proof.
      intros Df g y; unfold fInterToOrigEdges; rewrite SOfd.mem_unionMap.
      split.
      - intros [[[n v] [m [vs fs]]] [HD Hy]]; cbn beta iota in Hy.
        apply SOvd.mem_map in Hy; destruct Hy as [u [Hu Hy]].
        exists n, v, m, vs, fs, u; auto.
      - intros [n [v [m [vs [fs [u [HD [Hu ->]]]]]]]].
        exists ((n, v), (m, (vs, fs))); split; [exact HD | cbn beta iota].
        apply SOvd.mem_map; exists u; split; [exact Hu | reflexivity].
    Qed.

    Lemma mem_fDepToInterFeatEdges : forall Df g (y : T.DepElt.t),
        T.DepRel.In y (fDepToInterFeatEdges Df g) <->
        exists n v m vs fs f, Feat.FeatDepRel.In ((n, v), (m, (vs, fs))) Df /\
          Feat.FSet.In f fs /\
          y = ((Name.GranularOrig n (g v), v),
               (Name.IntermediateF n v m f, embedVS vs)).
    Proof.
      intros Df g y; unfold fDepToInterFeatEdges; rewrite SOfd.mem_unionMap.
      split.
      - intros [[[n v] [m [vs fs]]] [HD Hy]]; cbn beta iota in Hy.
        apply SOfsd.mem_map in Hy; destruct Hy as [f [Hf Hy]].
        exists n, v, m, vs, fs, f; auto.
      - intros [n [v [m [vs [fs [f [HD [Hf ->]]]]]]]].
        exists ((n, v), (m, (vs, fs))); split; [exact HD | cbn beta iota].
        apply SOfsd.mem_map; exists f; split; [exact Hf | reflexivity].
    Qed.

    Lemma mem_fInterToFeatEdges : forall Df g (y : T.DepElt.t),
        T.DepRel.In y (fInterToFeatEdges Df g) <->
        exists n v m vs fs u f, Feat.FeatDepRel.In ((n, v), (m, (vs, fs))) Df /\
          VSet.In u vs /\ Feat.FSet.In f fs /\
          y = ((Name.IntermediateF n v m f, u),
               (Name.GranularFeatPkg m f (g u), singVS u)).
    Proof.
      intros Df g y; unfold fInterToFeatEdges; rewrite SOfd.mem_unionMap.
      split.
      - intros [[[n v] [m [vs fs]]] [HD Hy]]; cbn beta iota in Hy.
        apply SOvd.mem_unionMap in Hy; destruct Hy as [u [Hu Hy]].
        apply SOfsd.mem_map in Hy; destruct Hy as [f [Hf Hy]].
        exists n, v, m, vs, fs, u, f; auto.
      - intros [n [v [m [vs [fs [u [f [HD [Hu [Hf ->]]]]]]]]]].
        exists ((n, v), (m, (vs, fs))); split; [exact HD | cbn beta iota].
        apply SOvd.mem_unionMap; exists u; split; [exact Hu |].
        apply SOfsd.mem_map; exists f; split; [exact Hf | reflexivity].
    Qed.

    Lemma mem_fInterFeatToInterEdges : forall Df (y : T.DepElt.t),
        T.DepRel.In y (fInterFeatToInterEdges Df) <->
        exists n v m vs fs f u, Feat.FeatDepRel.In ((n, v), (m, (vs, fs))) Df /\
          Feat.FSet.In f fs /\ VSet.In u vs /\
          y = ((Name.IntermediateF n v m f, u),
               (Name.Intermediate n v m, singVS u)).
    Proof.
      intros Df y; unfold fInterFeatToInterEdges; rewrite SOfd.mem_unionMap.
      split.
      - intros [[[n v] [m [vs fs]]] [HD Hy]]; cbn beta iota in Hy.
        apply SOfsd.mem_unionMap in Hy; destruct Hy as [f [Hf Hy]].
        apply SOvd.mem_map in Hy; destruct Hy as [u [Hu Hy]].
        exists n, v, m, vs, fs, f, u; auto.
      - intros [n [v [m [vs [fs [f [u [HD [Hf [Hu ->]]]]]]]]]].
        exists ((n, v), (m, (vs, fs))); split; [exact HD | cbn beta iota].
        apply SOfsd.mem_unionMap; exists f; split; [exact Hf |].
        apply SOvd.mem_map; exists u; split; [exact Hu | reflexivity].
    Qed.

    Lemma mem_aDepToInterEdges : forall Da g (y : T.DepElt.t),
        T.DepRel.In y (aDepToInterEdges Da g) <->
        exists n v f m vs fs,
          Feat.AddlDepRel.In (((n, v), f), (m, (vs, fs))) Da /\
          y = ((Name.GranularFeatPkg n f (g v), v),
               (Name.Intermediate n v m, embedVS vs)).
    Proof.
      intros Da g y; unfold aDepToInterEdges; rewrite SOad.mem_map.
      split.
      - intros [[[[n v] f] [m [vs fs]]] [HD Hy]]; cbn beta iota in Hy.
        exists n, v, f, m, vs, fs; auto.
      - intros [n [v [f [m [vs [fs [HD ->]]]]]]].
        exists (((n, v), f), (m, (vs, fs))); split; [exact HD | reflexivity].
    Qed.

    Lemma mem_aInterToOrigEdges : forall Da g (y : T.DepElt.t),
        T.DepRel.In y (aInterToOrigEdges Da g) <->
        exists n v f m vs fs u,
          Feat.AddlDepRel.In (((n, v), f), (m, (vs, fs))) Da /\
          VSet.In u vs /\
          y = ((Name.Intermediate n v m, u),
               (Name.GranularOrig m (g u), singVS u)).
    Proof.
      intros Da g y; unfold aInterToOrigEdges; rewrite SOad.mem_unionMap.
      split.
      - intros [[[[n v] f] [m [vs fs]]] [HD Hy]]; cbn beta iota in Hy.
        apply SOvd.mem_map in Hy; destruct Hy as [u [Hu Hy]].
        exists n, v, f, m, vs, fs, u; auto.
      - intros [n [v [f [m [vs [fs [u [HD [Hu ->]]]]]]]]].
        exists (((n, v), f), (m, (vs, fs))); split; [exact HD | cbn beta iota].
        apply SOvd.mem_map; exists u; split; [exact Hu | reflexivity].
    Qed.

    Lemma mem_aDepToInterFeatEdges : forall Da g (y : T.DepElt.t),
        T.DepRel.In y (aDepToInterFeatEdges Da g) <->
        exists n v f m vs fs f',
          Feat.AddlDepRel.In (((n, v), f), (m, (vs, fs))) Da /\
          Feat.FSet.In f' fs /\
          y = ((Name.GranularFeatPkg n f (g v), v),
               (Name.IntermediateA n v f m f', embedVS vs)).
    Proof.
      intros Da g y; unfold aDepToInterFeatEdges; rewrite SOad.mem_unionMap.
      split.
      - intros [[[[n v] f] [m [vs fs]]] [HD Hy]]; cbn beta iota in Hy.
        apply SOfsd.mem_map in Hy; destruct Hy as [f' [Hf' Hy]].
        exists n, v, f, m, vs, fs, f'; auto.
      - intros [n [v [f [m [vs [fs [f' [HD [Hf' ->]]]]]]]]].
        exists (((n, v), f), (m, (vs, fs))); split; [exact HD | cbn beta iota].
        apply SOfsd.mem_map; exists f'; split; [exact Hf' | reflexivity].
    Qed.

    Lemma mem_aInterToFeatEdges : forall Da g (y : T.DepElt.t),
        T.DepRel.In y (aInterToFeatEdges Da g) <->
        exists n v f m vs fs u f',
          Feat.AddlDepRel.In (((n, v), f), (m, (vs, fs))) Da /\
          VSet.In u vs /\ Feat.FSet.In f' fs /\
          y = ((Name.IntermediateA n v f m f', u),
               (Name.GranularFeatPkg m f' (g u), singVS u)).
    Proof.
      intros Da g y; unfold aInterToFeatEdges; rewrite SOad.mem_unionMap.
      split.
      - intros [[[[n v] f] [m [vs fs]]] [HD Hy]]; cbn beta iota in Hy.
        apply SOvd.mem_unionMap in Hy; destruct Hy as [u [Hu Hy]].
        apply SOfsd.mem_map in Hy; destruct Hy as [f' [Hf' Hy]].
        exists n, v, f, m, vs, fs, u, f'; auto.
      - intros [n [v [f [m [vs [fs [u [f' [HD [Hu [Hf' ->]]]]]]]]]]].
        exists (((n, v), f), (m, (vs, fs))); split; [exact HD | cbn beta iota].
        apply SOvd.mem_unionMap; exists u; split; [exact Hu |].
        apply SOfsd.mem_map; exists f'; split; [exact Hf' | reflexivity].
    Qed.

    Lemma mem_aInterFeatToInterEdges : forall Da (y : T.DepElt.t),
        T.DepRel.In y (aInterFeatToInterEdges Da) <->
        exists n v f m vs fs f' u,
          Feat.AddlDepRel.In (((n, v), f), (m, (vs, fs))) Da /\
          Feat.FSet.In f' fs /\ VSet.In u vs /\
          y = ((Name.IntermediateA n v f m f', u),
               (Name.Intermediate n v m, singVS u)).
    Proof.
      intros Da y; unfold aInterFeatToInterEdges; rewrite SOad.mem_unionMap.
      split.
      - intros [[[[n v] f] [m [vs fs]]] [HD Hy]]; cbn beta iota in Hy.
        apply SOfsd.mem_unionMap in Hy; destruct Hy as [f' [Hf' Hy]].
        apply SOvd.mem_map in Hy; destruct Hy as [u [Hu Hy]].
        exists n, v, f, m, vs, fs, f', u; auto.
      - intros [n [v [f [m [vs [fs [f' [u [HD [Hf' [Hu ->]]]]]]]]]]].
        exists (((n, v), f), (m, (vs, fs))); split; [exact HD | cbn beta iota].
        apply SOfsd.mem_unionMap; exists f'; split; [exact Hf' |].
        apply SOvd.mem_map; exists u; split; [exact Hu | reflexivity].
    Qed.

    (* One constructor per edge family emitted by reduceDeps: the tailFibre
       proofs invert on the depender, so the families must be named rather
       than positions in an eleven-way disjunction. *)
    Inductive EncodedEdge (R : PkgSet.t) (support : Feat.SupportSet.t)
        (Df : Feat.FeatDepRel.t) (Da : Feat.AddlDepRel.t) (g : V.t -> G.t) :
        T.DepElt.t -> Prop :=
    | EdgeSupport : forall n v f,
        Feat.SupportSet.In ((n, v), f) support -> PkgSet.In (n, v) R ->
        EncodedEdge R support Df Da g
          ((Name.GranularFeatPkg n f (g v), v),
           (Name.GranularOrig n (g v), singVS v))
    | EdgeFDepToInter : forall n v m vs fs,
        Feat.FeatDepRel.In ((n, v), (m, (vs, fs))) Df ->
        EncodedEdge R support Df Da g
          ((Name.GranularOrig n (g v), v),
           (Name.Intermediate n v m, embedVS vs))
    | EdgeFInterToOrig : forall n v m vs fs u,
        Feat.FeatDepRel.In ((n, v), (m, (vs, fs))) Df -> VSet.In u vs ->
        EncodedEdge R support Df Da g
          ((Name.Intermediate n v m, u),
           (Name.GranularOrig m (g u), singVS u))
    | EdgeFDepToInterFeat : forall n v m vs fs f,
        Feat.FeatDepRel.In ((n, v), (m, (vs, fs))) Df -> Feat.FSet.In f fs ->
        EncodedEdge R support Df Da g
          ((Name.GranularOrig n (g v), v),
           (Name.IntermediateF n v m f, embedVS vs))
    | EdgeFInterToFeat : forall n v m vs fs u f,
        Feat.FeatDepRel.In ((n, v), (m, (vs, fs))) Df -> VSet.In u vs ->
        Feat.FSet.In f fs ->
        EncodedEdge R support Df Da g
          ((Name.IntermediateF n v m f, u),
           (Name.GranularFeatPkg m f (g u), singVS u))
    | EdgeFInterFeatToInter : forall n v m vs fs f u,
        Feat.FeatDepRel.In ((n, v), (m, (vs, fs))) Df -> Feat.FSet.In f fs ->
        VSet.In u vs ->
        EncodedEdge R support Df Da g
          ((Name.IntermediateF n v m f, u),
           (Name.Intermediate n v m, singVS u))
    | EdgeADepToInter : forall n v f m vs fs,
        Feat.AddlDepRel.In (((n, v), f), (m, (vs, fs))) Da ->
        EncodedEdge R support Df Da g
          ((Name.GranularFeatPkg n f (g v), v),
           (Name.Intermediate n v m, embedVS vs))
    | EdgeAInterToOrig : forall n v f m vs fs u,
        Feat.AddlDepRel.In (((n, v), f), (m, (vs, fs))) Da -> VSet.In u vs ->
        EncodedEdge R support Df Da g
          ((Name.Intermediate n v m, u),
           (Name.GranularOrig m (g u), singVS u))
    | EdgeADepToInterFeat : forall n v f m vs fs f',
        Feat.AddlDepRel.In (((n, v), f), (m, (vs, fs))) Da ->
        Feat.FSet.In f' fs ->
        EncodedEdge R support Df Da g
          ((Name.GranularFeatPkg n f (g v), v),
           (Name.IntermediateA n v f m f', embedVS vs))
    | EdgeAInterToFeat : forall n v f m vs fs u f',
        Feat.AddlDepRel.In (((n, v), f), (m, (vs, fs))) Da -> VSet.In u vs ->
        Feat.FSet.In f' fs ->
        EncodedEdge R support Df Da g
          ((Name.IntermediateA n v f m f', u),
           (Name.GranularFeatPkg m f' (g u), singVS u))
    | EdgeAInterFeatToInter : forall n v f m vs fs f' u,
        Feat.AddlDepRel.In (((n, v), f), (m, (vs, fs))) Da ->
        Feat.FSet.In f' fs -> VSet.In u vs ->
        EncodedEdge R support Df Da g
          ((Name.IntermediateA n v f m f', u),
           (Name.Intermediate n v m, singVS u)).

    Lemma mem_reduceDeps : forall R support Df Da g (y : T.DepElt.t),
        T.DepRel.In y (reduceDeps R support Df Da g) <->
        EncodedEdge R support Df Da g y.
    Proof.
      intros R support Df Da g y; unfold reduceDeps.
      rewrite !T.DepRel.union_spec, mem_supportEdges, mem_fDepToInterEdges,
        mem_fInterToOrigEdges, mem_fDepToInterFeatEdges, mem_fInterToFeatEdges,
        mem_fInterFeatToInterEdges, mem_aDepToInterEdges, mem_aInterToOrigEdges,
        mem_aDepToInterFeatEdges, mem_aInterToFeatEdges,
        mem_aInterFeatToInterEdges.
      split.
      - intros [H1 | [H2 | [H3 | [H4 | [H5 | [H6 | [H7 | [H8 | [H9 |
                [H10 | H11]]]]]]]]]].
        + destruct H1 as [n [v [f [Hs [HR ->]]]]].
          apply EdgeSupport; assumption.
        + destruct H2 as [n [v [m [vs [fs [HD ->]]]]]].
          eapply EdgeFDepToInter; exact HD.
        + destruct H3 as [n [v [m [vs [fs [u [HD [Hu ->]]]]]]]].
          eapply EdgeFInterToOrig; [exact HD | exact Hu].
        + destruct H4 as [n [v [m [vs [fs [f [HD [Hf ->]]]]]]]].
          eapply EdgeFDepToInterFeat; [exact HD | exact Hf].
        + destruct H5 as [n [v [m [vs [fs [u [f [HD [Hu [Hf ->]]]]]]]]]].
          eapply EdgeFInterToFeat; [exact HD | exact Hu | exact Hf].
        + destruct H6 as [n [v [m [vs [fs [f [u [HD [Hf [Hu ->]]]]]]]]]].
          eapply EdgeFInterFeatToInter; [exact HD | exact Hf | exact Hu].
        + destruct H7 as [n [v [f [m [vs [fs [HD ->]]]]]]].
          eapply EdgeADepToInter; exact HD.
        + destruct H8 as [n [v [f [m [vs [fs [u [HD [Hu ->]]]]]]]]].
          eapply EdgeAInterToOrig; [exact HD | exact Hu].
        + destruct H9 as [n [v [f [m [vs [fs [f' [HD [Hf' ->]]]]]]]]].
          eapply EdgeADepToInterFeat; [exact HD | exact Hf'].
        + destruct H10 as [n [v [f [m [vs [fs [u [f' [HD [Hu [Hf' ->]]]]]]]]]]].
          eapply EdgeAInterToFeat; [exact HD | exact Hu | exact Hf'].
        + destruct H11 as [n [v [f [m [vs [fs [f' [u [HD [Hf' [Hu ->]]]]]]]]]]].
          eapply EdgeAInterFeatToInter; [exact HD | exact Hf' | exact Hu].
      - intro Hy; destruct Hy as
          [n v f0 Hs HR | n v m vs fs HD | n v m vs fs u HD Hu
          | n v m vs fs f HD Hf | n v m vs fs u f HD Hu Hf
          | n v m vs fs f u HD Hf Hu | n v f0 m vs fs HD
          | n v f0 m vs fs u HD Hu | n v f0 m vs fs f' HD Hf'
          | n v f0 m vs fs u f' HD Hu Hf' | n v f0 m vs fs f' u HD Hf' Hu].
        + left; exists n, v, f0; auto.
        + right; left; exists n, v, m, vs, fs; auto.
        + do 2 right; left; exists n, v, m, vs, fs, u; auto.
        + do 3 right; left; exists n, v, m, vs, fs, f; auto.
        + do 4 right; left; exists n, v, m, vs, fs, u, f; auto.
        + do 5 right; left; exists n, v, m, vs, fs, f, u; auto.
        + do 6 right; left; exists n, v, f0, m, vs, fs; auto.
        + do 7 right; left; exists n, v, f0, m, vs, fs, u; auto.
        + do 8 right; left; exists n, v, f0, m, vs, fs, f'; auto.
        + do 9 right; left; exists n, v, f0, m, vs, fs, u, f'; auto.
        + do 10 right; exists n, v, f0, m, vs, fs, f', u; auto.
    Qed.

    Lemma mem_reduceDeps_f_depToInter : forall R support Df Da g n v m vs fs,
        Feat.FeatDepRel.In ((n, v), (m, (vs, fs))) Df ->
        T.DepRel.In ((Name.GranularOrig n (g v), v),
                     (Name.Intermediate n v m, embedVS vs))
          (reduceDeps R support Df Da g).
    Proof.
      intros R support Df Da g n v m vs fs H.
      rewrite mem_reduceDeps; eapply EdgeFDepToInter; exact H.
    Qed.

    Lemma mem_reduceDeps_f_interToOrig : forall R support Df Da g n v m vs fs u,
        Feat.FeatDepRel.In ((n, v), (m, (vs, fs))) Df -> VSet.In u vs ->
        T.DepRel.In ((Name.Intermediate n v m, u),
                     (Name.GranularOrig m (g u), singVS u))
          (reduceDeps R support Df Da g).
    Proof.
      intros R support Df Da g n v m vs fs u H Hu.
      rewrite mem_reduceDeps; eapply EdgeFInterToOrig; [exact H | exact Hu].
    Qed.

    Lemma mem_reduceDeps_f_depToInterFeat :
        forall R support Df Da g n v m vs fs f,
        Feat.FeatDepRel.In ((n, v), (m, (vs, fs))) Df -> Feat.FSet.In f fs ->
        T.DepRel.In ((Name.GranularOrig n (g v), v),
                     (Name.IntermediateF n v m f, embedVS vs))
          (reduceDeps R support Df Da g).
    Proof.
      intros R support Df Da g n v m vs fs f H Hf.
      rewrite mem_reduceDeps; eapply EdgeFDepToInterFeat; [exact H | exact Hf].
    Qed.

    Lemma mem_reduceDeps_f_interToFeat :
      forall R support Df Da g n v m vs fs u f,
        Feat.FeatDepRel.In ((n, v), (m, (vs, fs))) Df ->
        VSet.In u vs -> Feat.FSet.In f fs ->
        T.DepRel.In ((Name.IntermediateF n v m f, u),
                     (Name.GranularFeatPkg m f (g u), singVS u))
          (reduceDeps R support Df Da g).
    Proof.
      intros R support Df Da g n v m vs fs u f H Hu Hf.
      rewrite mem_reduceDeps;
        eapply EdgeFInterToFeat; [exact H | exact Hu | exact Hf].
    Qed.

    Lemma mem_reduceDeps_f_interFeatToInter :
        forall R support Df Da g n v m vs fs u f,
        Feat.FeatDepRel.In ((n, v), (m, (vs, fs))) Df ->
        VSet.In u vs -> Feat.FSet.In f fs ->
        T.DepRel.In ((Name.IntermediateF n v m f, u),
                     (Name.Intermediate n v m, singVS u))
          (reduceDeps R support Df Da g).
    Proof.
      intros R support Df Da g n v m vs fs u f H Hu Hf.
      rewrite mem_reduceDeps;
        eapply EdgeFInterFeatToInter; [exact H | exact Hf | exact Hu].
    Qed.

    Lemma mem_reduceDeps_a_depToInter : forall R support Df Da g n v f m vs fs,
        Feat.AddlDepRel.In (((n, v), f), (m, (vs, fs))) Da ->
        T.DepRel.In ((Name.GranularFeatPkg n f (g v), v),
                     (Name.Intermediate n v m, embedVS vs))
          (reduceDeps R support Df Da g).
    Proof.
      intros R support Df Da g n v f m vs fs H.
      rewrite mem_reduceDeps; eapply EdgeADepToInter; exact H.
    Qed.

    Lemma mem_reduceDeps_a_interToOrig :
      forall R support Df Da g n v f m vs fs u,
        Feat.AddlDepRel.In (((n, v), f), (m, (vs, fs))) Da -> VSet.In u vs ->
        T.DepRel.In ((Name.Intermediate n v m, u),
                     (Name.GranularOrig m (g u), singVS u))
          (reduceDeps R support Df Da g).
    Proof.
      intros R support Df Da g n v f m vs fs u H Hu.
      rewrite mem_reduceDeps; eapply EdgeAInterToOrig; [exact H | exact Hu].
    Qed.

    Lemma mem_reduceDeps_a_depToInterFeat :
        forall R support Df Da g n v f m vs fs f',
        Feat.AddlDepRel.In (((n, v), f), (m, (vs, fs))) Da ->
        Feat.FSet.In f' fs ->
        T.DepRel.In ((Name.GranularFeatPkg n f (g v), v),
                     (Name.IntermediateA n v f m f', embedVS vs))
          (reduceDeps R support Df Da g).
    Proof.
      intros R support Df Da g n v f m vs fs f' H Hf'.
      rewrite mem_reduceDeps; eapply EdgeADepToInterFeat; [exact H | exact Hf'].
    Qed.

    Lemma mem_reduceDeps_a_interToFeat :
        forall R support Df Da g n v f m vs fs u f',
        Feat.AddlDepRel.In (((n, v), f), (m, (vs, fs))) Da -> VSet.In u vs ->
        Feat.FSet.In f' fs ->
        T.DepRel.In ((Name.IntermediateA n v f m f', u),
                     (Name.GranularFeatPkg m f' (g u), singVS u))
          (reduceDeps R support Df Da g).
    Proof.
      intros R support Df Da g n v f m vs fs u f' H Hu Hf'.
      rewrite mem_reduceDeps;
        eapply EdgeAInterToFeat; [exact H | exact Hu | exact Hf'].
    Qed.

    Lemma mem_reduceDeps_a_interFeatToInter :
        forall R support Df Da g n v f m vs fs u f',
        Feat.AddlDepRel.In (((n, v), f), (m, (vs, fs))) Da -> VSet.In u vs ->
        Feat.FSet.In f' fs ->
        T.DepRel.In ((Name.IntermediateA n v f m f', u),
                     (Name.Intermediate n v m, singVS u))
          (reduceDeps R support Df Da g).
    Proof.
      intros R support Df Da g n v f m vs fs u f' H Hu Hf'.
      rewrite mem_reduceDeps;
        eapply EdgeAInterFeatToInter; [exact H | exact Hf' | exact Hu].
    Qed.

    Module SOtf := SetOps T.Pkg F T.PkgSet Feat.FSet.
    (* As in Feature: decode by scanning the resolution, so nothing here needs
       the feature universe to be enumerable. *)
    Definition featsOf (g : V.t -> G.t) (n : N.t) (v : V.t)
        (S : T.PkgSet.t) : Feat.FSet.t :=
      SOtf.filterMap (fun q =>
          match q with
          | (Name.GranularFeatPkg n' f w, v') =>
              if T.Pkg.eq_dec (Name.GranularFeatPkg n' f w, v')
                   (Name.GranularFeatPkg n f (g v), v)
              then Some f
              else None
          | _ => None
          end)
        S.

    Module SOts := SetOps T.Pkg Feat.Featured T.PkgSet Feat.FeaturedSet.
    Definition featureConcurrentResolution (g : V.t -> G.t)
        (S : T.PkgSet.t) : Feat.FeaturedSet.t :=
      SOts.filterMap (fun p' =>
          match p' with
          | (Name.GranularOrig n w, v) =>
              if G.eq_dec w (g v) then Some ((n, v), featsOf g n v S) else None
          | _ => None
          end)
        S.

    Module SOtpp := SetOps T.Pkg ParentElt T.PkgSet ParentRel.
    Definition parents (S : T.PkgSet.t) : ParentRel.t :=
      SOtpp.filterMap (fun q =>
          match q with
          | (Name.Intermediate n v m, u) => Some ((m, u), (n, v))
          | _ => None
          end)
        S.

    Lemma featsOf_spec : forall g n v S f,
        Feat.FSet.In f (featsOf g n v S) <->
        T.PkgSet.In (Name.GranularFeatPkg n f (g v), v) S.
    Proof.
      intros g n v S f; unfold featsOf; rewrite SOtf.mem_filterMap.
      split.
      - intros [[[n' w | n' f' w | n' v' m | n' v' m f' | n' v' f' m f''] u]
                 [HS He]]; cbn beta iota in He; try discriminate.
        destruct (T.Pkg.eq_dec (Name.GranularFeatPkg n' f' w, u)
                    (Name.GranularFeatPkg n f' (g v), v)) as [E | NE];
          [| discriminate].
        injection He as <-; rewrite <- E; exact HS.
      - intro HS; exists (Name.GranularFeatPkg n f (g v), v);
          split; [exact HS | cbn beta iota].
        destruct (T.Pkg.eq_dec (Name.GranularFeatPkg n f (g v), v)
                    (Name.GranularFeatPkg n f (g v), v)) as [_ | NE];
          [reflexivity | exfalso; exact (NE eq_refl)].
    Qed.

    Lemma mem_featureConcurrentResolution :
      forall g (S : T.PkgSet.t) (y : Feat.Featured.t),
        Feat.FeaturedSet.In y (featureConcurrentResolution g S) <->
        exists n v, T.PkgSet.In (Name.GranularOrig n (g v), v) S /\
          y = ((n, v), featsOf g n v S).
    Proof.
      intros g S y; unfold featureConcurrentResolution;
        rewrite SOts.mem_filterMap.
      split.
      - intros [[[n w | n f w | n v m | n v m f | n v f m f'] v0] [HeS Hy]];
          cbn beta iota in Hy; try discriminate.
        destruct (G.eq_dec w (g v0)) as [-> | NE]; [| discriminate].
        injection Hy as <-; exists n, v0; split; [exact HeS | reflexivity].
      - intros [n [v [HS ->]]].
        exists (Name.GranularOrig n (g v), v);
          split; [exact HS | cbn beta iota].
        destruct (G.eq_dec (g v) (g v)) as [_ | NE];
          [reflexivity | contradiction NE; reflexivity].
    Qed.

    Lemma mem_parents : forall (S : T.PkgSet.t) m u n v,
        ParentRel.In ((m, u), (n, v)) (parents S) <->
        T.PkgSet.In (Name.Intermediate n v m, u) S.
    Proof.
      intros S m u n v; unfold parents; rewrite SOtpp.mem_filterMap.
      split.
      - intros [[[n0 w0 | n0 f0 w0 | n0 v0 m0 | n0 v0 m0 f0 | n0 v0 f0 m0 f1]
                 u0] [HqS Hy]]; cbn beta iota in Hy; try discriminate.
        injection Hy as E1 E2 E3 E4; subst m0 u0 n0 v0; exact HqS.
      - intro HS.
        exists (Name.Intermediate n v m, u); split; [exact HS | reflexivity].
    Qed.

    Theorem feature_concurrent_soundness :
      forall (R : PkgSet.t) (support : Feat.SupportSet.t)
             (Df : Feat.FeatDepRel.t) (Da : Feat.AddlDepRel.t)
             (g : V.t -> G.t) (r : Pkg.t) (S : T.PkgSet.t),
        T.IsResolution (reduceReal R support Df Da g)
          (reduceDeps R support Df Da g)
          (embedOrigPkg g r) S ->
        (forall f, ~ Feat.SupportSet.In (r, f) support) ->
        IsResolution R support Df Da g r
          (featureConcurrentResolution g S) (parents S).
    Proof.
      intros R support Df Da g r S Hres Hnosupp.
      destruct Hres as [Hsub Hroot Hdep Huniq].
      destruct r as [rn rv].
      unfold embedOrigPkg in Hroot; simpl in Hroot.
      assert (HorigR : forall n v,
                 T.PkgSet.In (Name.GranularOrig n (g v), v) S ->
                 PkgSet.In (n, v) R).
      { intros n v HS.
        pose proof (Hsub _ HS) as HF; rewrite mem_reduceReal in HF.
        destruct HF as [[q [Hq Hy]] | [H2 | [H3 | [H4 | H5]]]].
        - destruct q as [fn qv]; destruct fn as [qn | qn qf];
            unfold granularOf in Hy; simpl in Hy.
          + injection Hy as E1 E2 E3; subst qn qv.
            rewrite Feat.Reduction.mem_reduceReal in Hq.
            destruct Hq as [[p0 [HpR Hq]] | [n' [v' [f' [_ [_ Hq]]]]]].
            * destruct p0 as [p0n p0v];
                unfold Feat.Reduction.embedPkg in Hq; simpl in Hq.
              injection Hq as E4 E5; subst p0n p0v; exact HpR.
            * discriminate Hq.
          + discriminate Hy.
        - destruct H2 as [n0 [v0 [m [vs [fs [u [_ [_ Hy]]]]]]]];
            discriminate Hy.
        - destruct H3 as [n0 [v0 [m [vs [fs [u [f [_ [_ [_ Hy]]]]]]]]]];
            discriminate Hy.
        - destruct H4 as [n0 [v0 [f [m [vs [fs [u [_ [_ Hy]]]]]]]]];
            discriminate Hy.
        - destruct H5 as [n0 [v0 [f [m [vs [fs [u [f' [_ [_ [_ Hy]]]]]]]]]]];
            discriminate Hy. }
      assert (HfeatSup : forall n f v,
                 T.PkgSet.In
                   (Name.GranularFeatPkg n f (g v), v) S ->
                 Feat.SupportSet.In ((n, v), f) support /\ PkgSet.In (n, v) R).
      { intros n f v HS.
        pose proof (Hsub _ HS) as HF; rewrite mem_reduceReal in HF.
        destruct HF as [[q [Hq Hy]] | [H2 | [H3 | [H4 | H5]]]].
        - destruct q as [fn qv]; destruct fn as [qn | qn qf];
            unfold granularOf in Hy; simpl in Hy.
          + discriminate Hy.
          + injection Hy as E1 E2 E3 E4; subst qn qf qv.
            rewrite Feat.Reduction.mem_reduceReal in Hq.
            destruct Hq as [[p0 [HpR Hq]] | [n' [v' [f' [Hsupp [HR Hq]]]]]].
            * destruct p0 as [p0n p0v];
                unfold Feat.Reduction.embedPkg in Hq; simpl in Hq;
                discriminate Hq.
            * injection Hq as E5 E6 E7; subst n' f' v'; split; assumption.
        - destruct H2 as [n0 [v0 [m [vs [fs [u [_ [_ Hy]]]]]]]];
            discriminate Hy.
        - destruct H3 as [n0 [v0 [m [vs [fs [u [f0 [_ [_ [_ Hy]]]]]]]]]];
            discriminate Hy.
        - destruct H4 as [n0 [v0 [f0 [m [vs [fs [u [_ [_ Hy]]]]]]]]];
            discriminate Hy.
        - destruct H5 as [n0 [v0 [f0 [m [vs [fs [u [f' [_ [_ [_ Hy]]]]]]]]]]];
            discriminate Hy. }
      constructor.
      - exact Hnosupp.
      - intros p fs Hmem.
        rewrite mem_featureConcurrentResolution in Hmem.
        destruct Hmem as [n [v [HS Heq]]].
        injection Heq as E1 E2; subst p.
        exact (HorigR n v HS).
      - assert (Hfe : featsOf g rn rv S = Feat.FSet.empty).
        { apply Feat.FSet.ext; intro f; rewrite featsOf_spec; split; intro H.
          - exfalso; exact (Hnosupp f (proj1 (HfeatSup rn f rv H))).
          - exfalso; exact (Feat.FSet.empty_spec H). }
        rewrite <- Hfe.
        rewrite mem_featureConcurrentResolution; exists rn, rv; split;
          [exact Hroot | reflexivity].
      - intros n v fs fs' H1 H2.
        rewrite mem_featureConcurrentResolution in H1, H2.
        destruct H1 as [n1 [v1 [HS1 Heq1]]];
          destruct H2 as [n2 [v2 [HS2 Heq2]]].
        injection Heq1 as E1 E2 E3; subst n1 v1 fs.
        injection Heq2 as E4 E5 E6; subst n2 v2 fs'.
        reflexivity.
      - intros p fs_p Hmem m vs fs Hdf.
        rewrite mem_featureConcurrentResolution in Hmem.
        destruct Hmem as [n [v [HpS Heq]]].
        injection Heq as E1 E2; subst p fs_p.
        pose proof (Hdep _ HpS _ _
          (mem_reduceDeps_f_depToInter R support Df Da g n v m vs fs Hdf))
          as [u0 [Hu0 HwS]].
        rewrite mem_embedVS in Hu0.
        pose proof (Hdep _ HwS _ _
          (mem_reduceDeps_f_interToOrig R support Df Da g n v m vs fs u0
             Hdf Hu0))
          as [w' [Hw' Hw'S]].
        unfold singVS in Hw'; rewrite SOvv.singleton_in in Hw'; subst w'.
        assert (Hsubfs : Feat.FSet.Subset fs (featsOf g m u0 S)).
        { intros f Hf; rewrite featsOf_spec.
          pose proof (Hdep _ HpS _ _
            (mem_reduceDeps_f_depToInterFeat R support Df Da g n v m vs fs f
               Hdf Hf)) as [u1 [Hu1 Hw1S]].
          rewrite mem_embedVS in Hu1.
          pose proof (Hdep _ Hw1S _ _
            (mem_reduceDeps_f_interFeatToInter
               R support Df Da g n v m vs fs u1 f
               Hdf Hu1 Hf)) as [w2 [Hw2 Hw2S]].
          unfold singVS in Hw2; rewrite SOvv.singleton_in in Hw2; subst w2.
          assert (Eu : u1 = u0)
            by exact (Huniq (Name.Intermediate n v m) _ _ Hw2S HwS).
          subst u1.
          pose proof (Hdep _ Hw1S _ _
            (mem_reduceDeps_f_interToFeat R support Df Da g n v m vs fs u0 f
               Hdf Hu0 Hf)) as [w3 [Hw3 Hw3S]].
          unfold singVS in Hw3; rewrite SOvv.singleton_in in Hw3; subst w3.
          exact Hw3S. }
        exists u0; split.
        + split; [exact Hu0 | split].
          * exists (featsOf g m u0 S); split; [exact Hsubfs |].
            rewrite mem_featureConcurrentResolution; exists m, u0; split;
              [exact Hw'S | reflexivity].
          * exact (proj2 (mem_parents S m u0 n v) HwS).
        + intros u' [Hu' [_ Hpi']].
          pose proof (proj1 (mem_parents S m u' n v) Hpi') as HS'.
          assert (E : u0 = u')
            by exact (Huniq (Name.Intermediate n v m) _ _ HwS HS').
          exact E.
      - intros p fs_p Hmem f Hf m vs fs Hda.
        rewrite mem_featureConcurrentResolution in Hmem.
        destruct Hmem as [n [v [HpS Heq]]].
        injection Heq as E1 E2; subst p fs_p.
        rewrite featsOf_spec in Hf.
        pose proof (Hdep _ Hf _ _
          (mem_reduceDeps_a_depToInter R support Df Da g n v f m vs fs Hda))
          as [u0 [Hu0 HwS]].
        rewrite mem_embedVS in Hu0.
        pose proof (Hdep _ HwS _ _
          (mem_reduceDeps_a_interToOrig R support Df Da g n v f m vs fs u0
             Hda Hu0)) as [w' [Hw' Hw'S]].
        unfold singVS in Hw'; rewrite SOvv.singleton_in in Hw'; subst w'.
        assert (Hsubfs : Feat.FSet.Subset fs (featsOf g m u0 S)).
        { intros f' Hf'; rewrite featsOf_spec.
          pose proof (Hdep _ Hf _ _
            (mem_reduceDeps_a_depToInterFeat R support Df Da g n v f m vs fs f'
               Hda Hf')) as [u1 [Hu1 Hw1S]].
          rewrite mem_embedVS in Hu1.
          pose proof (Hdep _ Hw1S _ _
            (mem_reduceDeps_a_interFeatToInter R support Df Da g n v f m vs fs
               u1 f' Hda Hu1 Hf')) as [w2 [Hw2 Hw2S]].
          unfold singVS in Hw2; rewrite SOvv.singleton_in in Hw2; subst w2.
          assert (Eu : u1 = u0)
            by exact (Huniq (Name.Intermediate n v m) _ _ Hw2S HwS).
          subst u1.
          pose proof (Hdep _ Hw1S _ _
            (mem_reduceDeps_a_interToFeat R support Df Da g n v f m vs fs u0 f'
               Hda Hu0 Hf')) as [w3 [Hw3 Hw3S]].
          unfold singVS in Hw3; rewrite SOvv.singleton_in in Hw3; subst w3.
          exact Hw3S. }
        exists u0; split.
        + split; [exact Hu0 | split].
          * exists (featsOf g m u0 S); split; [exact Hsubfs |].
            rewrite mem_featureConcurrentResolution; exists m, u0; split;
              [exact Hw'S | reflexivity].
          * exact (proj2 (mem_parents S m u0 n v) HwS).
        + intros u' [Hu' [_ Hpi']].
          pose proof (proj1 (mem_parents S m u' n v) Hpi') as HS'.
          assert (E : u0 = u')
            by exact (Huniq (Name.Intermediate n v m) _ _ HwS HS').
          exact E.
      - intros m u u' p H1 H2.
        destruct p as [pn pv].
        pose proof (proj1 (mem_parents S m u pn pv) H1) as HS1.
        pose proof (proj1 (mem_parents S m u' pn pv) H2) as HS2.
        assert (E : u = u')
          by exact (Huniq (Name.Intermediate pn pv m) _ _ HS1 HS2).
        exact E.
      - intros n v v' fs fs' H1 H2 Hne Hg.
        rewrite mem_featureConcurrentResolution in H1, H2.
        destruct H1 as [n1 [v1 [HS1 Heq1]]];
          destruct H2 as [n2 [v2 [HS2 Heq2]]].
        injection Heq1 as E1 E2 E3; subst n1 v1 fs.
        injection Heq2 as E4 E5 E6; subst n2 v2 fs'.
        rewrite Hg in HS1.
        assert (E : v = v')
          by exact (Huniq (Name.GranularOrig n (g v')) _ _ HS1 HS2).
        exact (Hne E).
      - intros n v fs f Hmem Hf.
        rewrite mem_featureConcurrentResolution in Hmem.
        destruct Hmem as [n1 [v1 [HS1 Heq]]].
        injection Heq as E1 E2 E3; subst n1 v1 fs.
        rewrite featsOf_spec in Hf.
        exact (proj1 (HfeatSup n f v Hf)).
    Qed.

    Module PkgEqb := UOTEqb Pkg.

    Definition inSb (S_CF : Feat.FeaturedSet.t) (p : Pkg.t) : bool :=
      Feat.FeaturedSet.exists_ (fun '(q, _) => PkgEqb.eqb q p) S_CF.

    Definition takenWithb
        (S_CF : Feat.FeaturedSet.t) (fs : Feat.FSet.t) (q : Pkg.t) : bool :=
      Feat.FeaturedSet.exists_ (fun '(q', fs') =>
          andb (PkgEqb.eqb q' q) (Feat.FSet.subset fs fs'))
        S_CF.

    Definition witnessCondb (S_CF : Feat.FeaturedSet.t) (pi : ParentRel.t)
        (p : Pkg.t) (fs : Feat.FSet.t) (m : N.t) (u : V.t) : bool :=
      andb (inSb S_CF p)
        (andb (takenWithb S_CF fs (m, u)) (ParentRel.mem ((m, u), p) pi)).

    Module SOsw := SetOps Feat.Featured T.Pkg Feat.FeaturedSet T.PkgSet.
    Definition coreResolution (S_CF : Feat.FeaturedSet.t) (pi : ParentRel.t)
        (Df : Feat.FeatDepRel.t) (Da : Feat.AddlDepRel.t) (g : V.t -> G.t) :
        T.PkgSet.t :=
      T.PkgSet.union
        (SOsw.map (fun '((n, v), _) => (Name.GranularOrig n (g v), v)) S_CF)
        (T.PkgSet.union
           (SOsw.unionMap (fun '((n, v), fs) =>
                SOfsp.map (fun f => (Name.GranularFeatPkg n f (g v), v)) fs)
              S_CF)
           (T.PkgSet.union
              (SOfp.unionMap (fun '((n, v), (m, (vs, fs))) =>
                   SOvp.filterMap (fun u =>
                       if witnessCondb S_CF pi (n, v) fs m u
                       then Some (Name.Intermediate n v m, u)
                       else None)
                     vs)
                 Df)
              (T.PkgSet.union
                 (SOap.unionMap (fun '(((n, v), _), (m, (vs, fs))) =>
                      SOvp.filterMap (fun u =>
                          if witnessCondb S_CF pi (n, v) fs m u
                          then Some (Name.Intermediate n v m, u)
                          else None)
                        vs)
                    Da)
                 (T.PkgSet.union
                    (SOfp.unionMap (fun '((n, v), (m, (vs, fs))) =>
                         SOfsp.unionMap (fun f =>
                             SOvp.filterMap (fun u =>
                                 if witnessCondb S_CF pi (n, v) fs m u
                                 then Some (Name.IntermediateF n v m f, u)
                                 else None)
                               vs)
                           fs)
                       Df)
                    (SOap.unionMap (fun '(((n, v), f), (m, (vs, fs))) =>
                         SOfsp.unionMap (fun f' =>
                             SOvp.filterMap (fun u =>
                                 if witnessCondb S_CF pi (n, v) fs m u
                                 then Some (Name.IntermediateA n v f m f', u)
                                 else None)
                               vs)
                           fs)
                       Da))))).

    Lemma inSb_iff : forall S_CF p,
        inSb S_CF p = true <-> exists fs_p, Feat.FeaturedSet.In (p, fs_p) S_CF.
    Proof.
      intros S_CF p; unfold inSb.
      rewrite Feat.FeaturedSet.exists_spec'.
      unfold Feat.FeaturedSet.Exists; split.
      - intros [[q fsq] [Hq Hb]]; cbn beta iota in Hb.
        apply PkgEqb.eqb_true_iff in Hb as ->; exists fsq; exact Hq.
      - intros [fs_p H]; exists (p, fs_p); split;
          [exact H | apply PkgEqb.eqb_refl].
    Qed.

    Lemma takenWithb_iff : forall S_CF fs q,
        takenWithb S_CF fs q = true <->
        exists fs',
          Feat.FSet.Subset fs fs' /\ Feat.FeaturedSet.In (q, fs') S_CF.
    Proof.
      intros S_CF fs q; unfold takenWithb.
      rewrite Feat.FeaturedSet.exists_spec'.
      unfold Feat.FeaturedSet.Exists; split.
      - intros [[q' fs'] [Hq Hb]]; cbn beta iota in Hb.
        apply Bool.andb_true_iff in Hb; destruct Hb as [Hb1 Hb2].
        apply PkgEqb.eqb_true_iff in Hb1 as ->.
        apply Feat.FSet.subset_spec in Hb2.
        exists fs'; split; assumption.
      - intros [fs' [Hsub H]]; exists (q, fs'); split;
          [exact H | cbn beta iota].
        apply Bool.andb_true_iff; split;
          [apply PkgEqb.eqb_refl | apply Feat.FSet.subset_spec; exact Hsub].
    Qed.

    Lemma witnessCondb_iff : forall S_CF pi p fs m u,
        witnessCondb S_CF pi p fs m u = true <->
        (exists fs_p, Feat.FeaturedSet.In (p, fs_p) S_CF) /\
        (exists fs', Feat.FSet.Subset fs fs' /\
           Feat.FeaturedSet.In ((m, u), fs') S_CF) /\
        ParentRel.In ((m, u), p) pi.
    Proof.
      intros S_CF pi p fs m u; unfold witnessCondb.
      rewrite !Bool.andb_true_iff, inSb_iff, takenWithb_iff,
        ParentRel.mem_spec.
      tauto.
    Qed.

    Lemma mem_coreResolution : forall S_CF pi Df Da g (q : T.Pkg.t),
        T.PkgSet.In q (coreResolution S_CF pi Df Da g) <->
        (exists n v fs, Feat.FeaturedSet.In ((n, v), fs) S_CF /\
           q = (Name.GranularOrig n (g v), v)) \/
        (exists n v fs f, Feat.FeaturedSet.In ((n, v), fs) S_CF /\
           Feat.FSet.In f fs /\
           q = (Name.GranularFeatPkg n f (g v), v)) \/
        (exists n v m vs fs u, Feat.FeatDepRel.In ((n, v), (m, (vs, fs))) Df /\
           VSet.In u vs /\ witnessCondb S_CF pi (n, v) fs m u = true /\
           q = (Name.Intermediate n v m, u)) \/
        (exists n v f m vs fs u,
           Feat.AddlDepRel.In (((n, v), f), (m, (vs, fs))) Da /\
           VSet.In u vs /\ witnessCondb S_CF pi (n, v) fs m u = true /\
           q = (Name.Intermediate n v m, u)) \/
        (exists n v m vs fs f u,
           Feat.FeatDepRel.In ((n, v), (m, (vs, fs))) Df /\
           Feat.FSet.In f fs /\ VSet.In u vs /\
           witnessCondb S_CF pi (n, v) fs m u = true /\
           q = (Name.IntermediateF n v m f, u)) \/
        (exists n v f m vs fs f' u,
           Feat.AddlDepRel.In (((n, v), f), (m, (vs, fs))) Da /\
           Feat.FSet.In f' fs /\ VSet.In u vs /\
           witnessCondb S_CF pi (n, v) fs m u = true /\
           q = (Name.IntermediateA n v f m f', u)).
    Proof.
      intros S_CF pi Df Da g q; unfold coreResolution.
      rewrite !T.PkgSet.union_spec, SOsw.mem_map, SOsw.mem_unionMap,
        !SOfp.mem_unionMap, !SOap.mem_unionMap.
      split.
      - intros [H1 | [H2 | [H3 | [H4 | [H5 | H6]]]]].
        + destruct H1 as [[[n v] fs0] [HxS Hy]]; cbn beta iota in Hy.
          left; exists n, v, fs0; auto.
        + destruct H2 as [[[n v] fs0] [HxS Hy]]; cbn beta iota in Hy.
          apply SOfsp.mem_map in Hy; destruct Hy as [f [Hf Hy]].
          right; left; exists n, v, fs0, f; auto.
        + destruct H3 as [[[n v] [m [vs fs]]] [HeD Hy]]; cbn beta iota in Hy.
          apply SOvp.mem_filterMap in Hy; destruct Hy as [u [Hu Hc]];
            cbn beta iota in Hc.
          destruct (witnessCondb S_CF pi (n, v) fs m u) eqn:Hw;
            [| discriminate].
          injection Hc as <-.
          right; right; left; exists n, v, m, vs, fs, u; auto 7.
        + destruct H4 as [[[[n v] f] [m [vs fs]]] [HeD Hy]];
            cbn beta iota in Hy.
          apply SOvp.mem_filterMap in Hy; destruct Hy as [u [Hu Hc]];
            cbn beta iota in Hc.
          destruct (witnessCondb S_CF pi (n, v) fs m u) eqn:Hw;
            [| discriminate].
          injection Hc as <-.
          do 3 right; left; exists n, v, f, m, vs, fs, u; auto 7.
        + destruct H5 as [[[n v] [m [vs fs]]] [HeD Hy]]; cbn beta iota in Hy.
          apply SOfsp.mem_unionMap in Hy; destruct Hy as [f [Hf Hy]].
          apply SOvp.mem_filterMap in Hy; destruct Hy as [u [Hu Hc]];
            cbn beta iota in Hc.
          destruct (witnessCondb S_CF pi (n, v) fs m u) eqn:Hw;
            [| discriminate].
          injection Hc as <-.
          do 4 right; left; exists n, v, m, vs, fs, f, u; auto 8.
        + destruct H6 as [[[[n v] f] [m [vs fs]]] [HeD Hy]];
            cbn beta iota in Hy.
          apply SOfsp.mem_unionMap in Hy; destruct Hy as [f' [Hf' Hy]].
          apply SOvp.mem_filterMap in Hy; destruct Hy as [u [Hu Hc]];
            cbn beta iota in Hc.
          destruct (witnessCondb S_CF pi (n, v) fs m u) eqn:Hw;
            [| discriminate].
          injection Hc as <-.
          do 5 right; exists n, v, f, m, vs, fs, f', u; auto 8.
      - intros [W1 | [W2 | [W3 | [W4 | [W5 | W6]]]]].
        + destruct W1 as [n [v [fs [HS ->]]]].
          left; exists ((n, v), fs); split; [exact HS | reflexivity].
        + destruct W2 as [n [v [fs [f [HS [Hf ->]]]]]].
          right; left; exists ((n, v), fs); split; [exact HS | cbn beta iota].
          apply SOfsp.mem_map; exists f; split; [exact Hf | reflexivity].
        + destruct W3 as [n [v [m [vs [fs [u [HD [Hu [Hc ->]]]]]]]]].
          right; right; left; exists ((n, v), (m, (vs, fs)));
            split; [exact HD | cbn beta iota].
          apply SOvp.mem_filterMap; exists u;
            split; [exact Hu | cbn beta iota].
          rewrite Hc; reflexivity.
        + destruct W4 as [n [v [f [m [vs [fs [u [HD [Hu [Hc ->]]]]]]]]]].
          do 3 right; left; exists (((n, v), f), (m, (vs, fs)));
            split; [exact HD | cbn beta iota].
          apply SOvp.mem_filterMap; exists u;
            split; [exact Hu | cbn beta iota].
          rewrite Hc; reflexivity.
        + destruct W5 as [n [v [m [vs [fs [f [u [HD [Hf [Hu [Hc ->]]]]]]]]]]].
          do 4 right; left; exists ((n, v), (m, (vs, fs)));
            split; [exact HD | cbn beta iota].
          apply SOfsp.mem_unionMap; exists f; split; [exact Hf |].
          apply SOvp.mem_filterMap; exists u;
            split; [exact Hu | cbn beta iota].
          rewrite Hc; reflexivity.
        + destruct W6 as
            [n [v [f [m [vs [fs [f' [u [HD [Hf' [Hu [Hc ->]]]]]]]]]]]].
          do 5 right; exists (((n, v), f), (m, (vs, fs)));
            split; [exact HD | cbn beta iota].
          apply SOfsp.mem_unionMap; exists f'; split; [exact Hf' |].
          apply SOvp.mem_filterMap; exists u;
            split; [exact Hu | cbn beta iota].
          rewrite Hc; reflexivity.
    Qed.

    Lemma witnessCondb_intro : forall S_CF pi (p : Pkg.t) fs m u,
        (exists fs_p, Feat.FeaturedSet.In (p, fs_p) S_CF) ->
        (exists fs', Feat.FSet.Subset fs fs' /\
           Feat.FeaturedSet.In ((m, u), fs') S_CF) ->
        ParentRel.In ((m, u), p) pi ->
        witnessCondb S_CF pi p fs m u = true.
    Proof.
      intros S_CF pi p fs m u H1 H2 H3.
      rewrite witnessCondb_iff; auto.
    Qed.

    Lemma mem_coreResolution_orig : forall S_CF pi Df Da g n v fs,
        Feat.FeaturedSet.In ((n, v), fs) S_CF ->
        T.PkgSet.In (Name.GranularOrig n (g v), v)
          (coreResolution S_CF pi Df Da g).
    Proof.
      intros S_CF pi Df Da g n v fs H.
      rewrite mem_coreResolution; left; exists n, v, fs; auto.
    Qed.

    Lemma mem_coreResolution_featured : forall S_CF pi Df Da g n v fs f,
        Feat.FeaturedSet.In ((n, v), fs) S_CF -> Feat.FSet.In f fs ->
        T.PkgSet.In (Name.GranularFeatPkg n f (g v), v)
          (coreResolution S_CF pi Df Da g).
    Proof.
      intros S_CF pi Df Da g n v fs f H Hf.
      rewrite mem_coreResolution; right; left; exists n, v, fs, f; auto.
    Qed.

    Lemma mem_coreResolution_f_inter : forall S_CF pi Df Da g n v m vs fs u,
        Feat.FeatDepRel.In ((n, v), (m, (vs, fs))) Df -> VSet.In u vs ->
        (exists fs_p, Feat.FeaturedSet.In ((n, v), fs_p) S_CF) ->
        (exists fs', Feat.FSet.Subset fs fs' /\
           Feat.FeaturedSet.In ((m, u), fs') S_CF) ->
        ParentRel.In ((m, u), (n, v)) pi ->
        T.PkgSet.In (Name.Intermediate n v m, u)
          (coreResolution S_CF pi Df Da g).
    Proof.
      intros S_CF pi Df Da g n v m vs fs u HD Hu H1 H2 H3.
      rewrite mem_coreResolution; right; right; left;
        exists n, v, m, vs, fs, u.
      repeat split; try assumption.
      apply witnessCondb_intro; assumption.
    Qed.

    Lemma mem_coreResolution_a_inter :
        forall S_CF pi Df Da g n v f m vs fs u,
        Feat.AddlDepRel.In (((n, v), f), (m, (vs, fs))) Da -> VSet.In u vs ->
        (exists fs_p, Feat.FeaturedSet.In ((n, v), fs_p) S_CF) ->
        (exists fs', Feat.FSet.Subset fs fs' /\
           Feat.FeaturedSet.In ((m, u), fs') S_CF) ->
        ParentRel.In ((m, u), (n, v)) pi ->
        T.PkgSet.In (Name.Intermediate n v m, u)
          (coreResolution S_CF pi Df Da g).
    Proof.
      intros S_CF pi Df Da g n v f m vs fs u HD Hu H1 H2 H3.
      rewrite mem_coreResolution; do 3 right; left;
        exists n, v, f, m, vs, fs, u.
      repeat split; try assumption.
      apply witnessCondb_intro; assumption.
    Qed.

    Lemma mem_coreResolution_f_interF :
        forall S_CF pi Df Da g n v m vs fs f u,
        Feat.FeatDepRel.In ((n, v), (m, (vs, fs))) Df ->
        Feat.FSet.In f fs -> VSet.In u vs ->
        (exists fs_p, Feat.FeaturedSet.In ((n, v), fs_p) S_CF) ->
        (exists fs', Feat.FSet.Subset fs fs' /\
           Feat.FeaturedSet.In ((m, u), fs') S_CF) ->
        ParentRel.In ((m, u), (n, v)) pi ->
        T.PkgSet.In (Name.IntermediateF n v m f, u)
          (coreResolution S_CF pi Df Da g).
    Proof.
      intros S_CF pi Df Da g n v m vs fs f u HD Hf Hu H1 H2 H3.
      rewrite mem_coreResolution; do 4 right; left;
        exists n, v, m, vs, fs, f, u.
      repeat split; try assumption.
      apply witnessCondb_intro; assumption.
    Qed.

    Lemma mem_coreResolution_a_interA :
        forall S_CF pi Df Da g n v f m vs fs f' u,
        Feat.AddlDepRel.In (((n, v), f), (m, (vs, fs))) Da ->
        Feat.FSet.In f' fs -> VSet.In u vs ->
        (exists fs_p, Feat.FeaturedSet.In ((n, v), fs_p) S_CF) ->
        (exists fs', Feat.FSet.Subset fs fs' /\
           Feat.FeaturedSet.In ((m, u), fs') S_CF) ->
        ParentRel.In ((m, u), (n, v)) pi ->
        T.PkgSet.In (Name.IntermediateA n v f m f', u)
          (coreResolution S_CF pi Df Da g).
    Proof.
      intros S_CF pi Df Da g n v f m vs fs f' u HD Hf' Hu H1 H2 H3.
      rewrite mem_coreResolution; do 5 right;
        exists n, v, f, m, vs, fs, f', u.
      repeat split; try assumption.
      apply witnessCondb_intro; assumption.
    Qed.

    Theorem feature_concurrent_completeness :
      forall (R : PkgSet.t) (support : Feat.SupportSet.t)
             (Df : Feat.FeatDepRel.t) (Da : Feat.AddlDepRel.t)
             (g : V.t -> G.t) (r : Pkg.t)
             (S_CF : Feat.FeaturedSet.t) (pi : ParentRel.t),
        IsResolution R support Df Da g r S_CF pi ->
        T.IsResolution (reduceReal R support Df Da g)
          (reduceDeps R support Df Da g)
          (embedOrigPkg g r) (coreResolution S_CF pi Df Da g).
    Proof.
      intros R support Df Da g r S_CF pi Hres.
      destruct Hres as [Hnrs Hsubset Hrootm Hfu Hpc Hpca Hpif Hvg Hsm].
      destruct r as [rn rv].
      constructor.
      - intros q Hq.
        rewrite mem_coreResolution in Hq; rewrite mem_reduceReal.
        destruct Hq as [W1 | [W2 | [W3 | [W4 | [W5 | W6]]]]].
        + destruct W1 as [n [v [fs [HS ->]]]].
          left; exists (Feat.Reduction.Name.Orig n, v); split; [| reflexivity].
          rewrite Feat.Reduction.mem_reduceReal; left; exists (n, v); split;
            [exact (Hsubset _ _ HS) | reflexivity].
        + destruct W2 as [n [v [fs [f [HS [Hf ->]]]]]].
          left; exists (Feat.Reduction.Name.FeatPkg n f, v);
            split; [| reflexivity].
          rewrite Feat.Reduction.mem_reduceReal; right; exists n, v, f.
          split; [exact (Hsm n v fs f HS Hf) |].
          split; [exact (Hsubset _ _ HS) | reflexivity].
        + destruct W3 as [n [v [m [vs [fs [u [HD [Hu [Hc ->]]]]]]]]].
          right; left; exists n, v, m, vs, fs, u; auto.
        + destruct W4 as [n [v [f0 [m [vs [fs [u [HD [Hu [Hc ->]]]]]]]]]].
          do 3 right; left; exists n, v, f0, m, vs, fs, u; auto.
        + destruct W5 as [n [v [m [vs [fs [f [u [HD [Hf [Hu [Hc ->]]]]]]]]]]].
          right; right; left; exists n, v, m, vs, fs, u, f; auto.
        + destruct W6
            as [n [v [f0 [m [vs [fs [f' [u [HD [Hf' [Hu [Hc ->]]]]]]]]]]]].
          do 4 right; exists n, v, f0, m, vs, fs, u, f'; auto.
      - unfold embedOrigPkg; simpl.
        exact (mem_coreResolution_orig S_CF pi Df Da g rn rv
                 Feat.FSet.empty Hrootm).
      - intros q Hq m' ws Hd.
        apply mem_reduceDeps in Hd; remember (q, (m', ws)) as y eqn:Hy.
        destruct Hd as
          [n v f Hsupp HR | n v m vs fs Hdf | n v m vs fs u Hdf Hu
          | n v m vs fs f Hdf Hf | n v m vs fs u f Hdf Hu Hf
          | n v m vs fs f u Hdf Hf Hu | n v f m vs fs Hda
          | n v f m vs fs u Hda Hu | n v f m vs fs f' Hda Hf'
          | n v f m vs fs u f' Hda Hu Hf' | n v f m vs fs f' u Hda Hf' Hu].
        + injection Hy as Eq Em Ews; subst q m' ws.
          rewrite mem_coreResolution in Hq.
          destruct Hq as
            [[n1 [v1 [fs1 [HS1 Hqe]]]] |
            [[n1 [v1 [fs1 [f1 [HS1 [Hf1 Hqe]]]]]] |
            [[n1 [v1 [m1 [vs1 [fs1 [u1 [HD1 [Hu1 [Hc1 Hqe]]]]]]]]] |
            [[n1 [v1 [f1 [m1 [vs1 [fs1
               [u1 [HD1 [Hu1 [Hc1 Hqe]]]]]]]]]] |
            [[n1 [v1 [m1 [vs1 [fs1 [f1
               [u1 [HD1 [Hf1 [Hu1 [Hc1 Hqe]]]]]]]]]]] |
             [n1 [v1 [f1 [m1 [vs1 [fs1
                [f1' [u1 [HD1 [Hf1' [Hu1 [Hc1 Hqe]]]]]]]]]]]]]]]]];
            try discriminate Hqe.
          injection Hqe as E1 E2 E3 E4; subst n1 f1 v1.
          exists v; split;
            [unfold singVS; rewrite SOvv.singleton_in; reflexivity |].
          exact (mem_coreResolution_orig S_CF pi Df Da g n v fs1 HS1).
        + injection Hy as Eq Em Ews; subst q m' ws.
          rewrite mem_coreResolution in Hq.
          destruct Hq as
            [[n1 [v1 [fs1 [HS1 Hqe]]]] |
            [[n1 [v1 [fs1 [f1 [HS1 [Hf1 Hqe]]]]]] |
            [[n1 [v1 [m1 [vs1 [fs1 [u1 [HD1 [Hu1 [Hc1 Hqe]]]]]]]]] |
            [[n1 [v1 [f1 [m1 [vs1 [fs1
               [u1 [HD1 [Hu1 [Hc1 Hqe]]]]]]]]]] |
            [[n1 [v1 [m1 [vs1 [fs1 [f1
               [u1 [HD1 [Hf1 [Hu1 [Hc1 Hqe]]]]]]]]]]] |
             [n1 [v1 [f1 [m1 [vs1 [fs1
                [f1' [u1 [HD1 [Hf1' [Hu1 [Hc1 Hqe]]]]]]]]]]]]]]]]];
            try discriminate Hqe.
          injection Hqe as E1 E2 E3; subst n1 v1.
          destruct (Hpc (n, v) fs1 HS1 m vs fs Hdf) as [u [[Hu [Htk Hpi]] _]].
          exists u; split;
            [rewrite mem_embedVS; exact Hu |].
          apply (mem_coreResolution_f_inter S_CF pi Df Da g n v m vs fs u
                   Hdf Hu); [exists fs1; exact HS1 | exact Htk | exact Hpi].
        + injection Hy as Eq Em Ews; subst q m' ws.
          rewrite mem_coreResolution in Hq.
          destruct Hq as
            [[n1 [v1 [fs1 [HS1 Hqe]]]] |
            [[n1 [v1 [fs1 [f1 [HS1 [Hf1 Hqe]]]]]] |
            [[n1 [v1 [m1 [vs1 [fs1 [u1 [HD1 [Hu1 [Hc1 Hqe]]]]]]]]] |
            [[n1 [v1 [f1 [m1 [vs1 [fs1
               [u1 [HD1 [Hu1 [Hc1 Hqe]]]]]]]]]] |
            [[n1 [v1 [m1 [vs1 [fs1 [f1
               [u1 [HD1 [Hf1 [Hu1 [Hc1 Hqe]]]]]]]]]]] |
             [n1 [v1 [f1 [m1 [vs1 [fs1
                [f1' [u1 [HD1 [Hf1' [Hu1 [Hc1 Hqe]]]]]]]]]]]]]]]]];
            try discriminate Hqe.
          * injection Hqe as E1 E2 E3 E4; subst n1 v1 m1 u1.
            apply witnessCondb_iff in Hc1.
            destruct Hc1 as [_ [[fs' [Hsub' HS']] _]].
            exists u; split;
              [unfold singVS; rewrite SOvv.singleton_in; reflexivity |].
            exact (mem_coreResolution_orig S_CF pi Df Da g m u fs' HS').
          * injection Hqe as E1 E2 E3 E4; subst n1 v1 m1 u1.
            apply witnessCondb_iff in Hc1.
            destruct Hc1 as [_ [[fs' [Hsub' HS']] _]].
            exists u; split;
              [unfold singVS; rewrite SOvv.singleton_in; reflexivity |].
            exact (mem_coreResolution_orig S_CF pi Df Da g m u fs' HS').
        + injection Hy as Eq Em Ews; subst q m' ws.
          rewrite mem_coreResolution in Hq.
          destruct Hq as
            [[n1 [v1 [fs1 [HS1 Hqe]]]] |
            [[n1 [v1 [fs1 [f1 [HS1 [Hf1 Hqe]]]]]] |
            [[n1 [v1 [m1 [vs1 [fs1 [u1 [HD1 [Hu1 [Hc1 Hqe]]]]]]]]] |
            [[n1 [v1 [f1 [m1 [vs1 [fs1
               [u1 [HD1 [Hu1 [Hc1 Hqe]]]]]]]]]] |
            [[n1 [v1 [m1 [vs1 [fs1 [f1
               [u1 [HD1 [Hf1 [Hu1 [Hc1 Hqe]]]]]]]]]]] |
             [n1 [v1 [f1 [m1 [vs1 [fs1
                [f1' [u1 [HD1 [Hf1' [Hu1 [Hc1 Hqe]]]]]]]]]]]]]]]]];
            try discriminate Hqe.
          injection Hqe as E1 E2 E3; subst n1 v1.
          destruct (Hpc (n, v) fs1 HS1 m vs fs Hdf) as [u [[Hu [Htk Hpi]] _]].
          exists u; split;
            [rewrite mem_embedVS; exact Hu |].
          apply (mem_coreResolution_f_interF S_CF pi Df Da g n v m vs fs f u
                   Hdf Hf Hu); [exists fs1; exact HS1 | exact Htk | exact Hpi].
        + injection Hy as Eq Em Ews; subst q m' ws.
          rewrite mem_coreResolution in Hq.
          destruct Hq as
            [[n1 [v1 [fs1 [HS1 Hqe]]]] |
            [[n1 [v1 [fs1 [f1 [HS1 [Hf1 Hqe]]]]]] |
            [[n1 [v1 [m1 [vs1 [fs1 [u1 [HD1 [Hu1 [Hc1 Hqe]]]]]]]]] |
            [[n1 [v1 [f1 [m1 [vs1 [fs1
               [u1 [HD1 [Hu1 [Hc1 Hqe]]]]]]]]]] |
            [[n1 [v1 [m1 [vs1 [fs1 [f1
               [u1 [HD1 [Hf1 [Hu1 [Hc1 Hqe]]]]]]]]]]] |
             [n1 [v1 [f1 [m1 [vs1 [fs1
                [f1' [u1 [HD1 [Hf1' [Hu1 [Hc1 Hqe]]]]]]]]]]]]]]]]];
            try discriminate Hqe.
          injection Hqe as E1 E2 E3 E4 E5; subst n1 v1 m1 f1 u1.
          apply witnessCondb_iff in Hc1.
          destruct Hc1 as [_ [[fs' [Hsub' HS']] _]].
          exists u; split;
            [unfold singVS; rewrite SOvv.singleton_in; reflexivity |].
          exact (mem_coreResolution_featured S_CF pi Df Da g m u fs' f HS'
                   (Hsub' f Hf1)).
        + injection Hy as Eq Em Ews; subst q m' ws.
          rewrite mem_coreResolution in Hq.
          destruct Hq as
            [[n1 [v1 [fs1 [HS1 Hqe]]]] |
            [[n1 [v1 [fs1 [f1 [HS1 [Hf1 Hqe]]]]]] |
            [[n1 [v1 [m1 [vs1 [fs1 [u1 [HD1 [Hu1 [Hc1 Hqe]]]]]]]]] |
            [[n1 [v1 [f1 [m1 [vs1 [fs1
               [u1 [HD1 [Hu1 [Hc1 Hqe]]]]]]]]]] |
            [[n1 [v1 [m1 [vs1 [fs1 [f1
               [u1 [HD1 [Hf1 [Hu1 [Hc1 Hqe]]]]]]]]]]] |
             [n1 [v1 [f1 [m1 [vs1 [fs1
                [f1' [u1 [HD1 [Hf1' [Hu1 [Hc1 Hqe]]]]]]]]]]]]]]]]];
            try discriminate Hqe.
          injection Hqe as E1 E2 E3 E4 E5; subst n1 v1 m1 f1 u1.
          apply witnessCondb_iff in Hc1.
          destruct Hc1 as [HinS [Htk Hpi]].
          exists u; split;
            [unfold singVS; rewrite SOvv.singleton_in; reflexivity |].
          exact (mem_coreResolution_f_inter S_CF pi Df Da g n v m vs1 fs1 u
                   HD1 Hu1 HinS Htk Hpi).
        + injection Hy as Eq Em Ews; subst q m' ws.
          rewrite mem_coreResolution in Hq.
          destruct Hq as
            [[n1 [v1 [fs1 [HS1 Hqe]]]] |
            [[n1 [v1 [fs1 [f1 [HS1 [Hf1 Hqe]]]]]] |
            [[n1 [v1 [m1 [vs1 [fs1 [u1 [HD1 [Hu1 [Hc1 Hqe]]]]]]]]] |
            [[n1 [v1 [f1 [m1 [vs1 [fs1
               [u1 [HD1 [Hu1 [Hc1 Hqe]]]]]]]]]] |
            [[n1 [v1 [m1 [vs1 [fs1 [f1
               [u1 [HD1 [Hf1 [Hu1 [Hc1 Hqe]]]]]]]]]]] |
             [n1 [v1 [f1 [m1 [vs1 [fs1
                [f1' [u1 [HD1 [Hf1' [Hu1 [Hc1 Hqe]]]]]]]]]]]]]]]]];
            try discriminate Hqe.
          injection Hqe as E1 E2 E3 E4; subst n1 f1 v1.
          destruct (Hpca (n, v) fs1 HS1 f Hf1 m vs fs Hda)
            as [u [[Hu [Htk Hpi]] _]].
          exists u; split;
            [rewrite mem_embedVS; exact Hu |].
          apply (mem_coreResolution_a_inter S_CF pi Df Da g n v f m vs fs u
                   Hda Hu); [exists fs1; exact HS1 | exact Htk | exact Hpi].
        + injection Hy as Eq Em Ews; subst q m' ws.
          rewrite mem_coreResolution in Hq.
          destruct Hq as
            [[n1 [v1 [fs1 [HS1 Hqe]]]] |
            [[n1 [v1 [fs1 [f1 [HS1 [Hf1 Hqe]]]]]] |
            [[n1 [v1 [m1 [vs1 [fs1 [u1 [HD1 [Hu1 [Hc1 Hqe]]]]]]]]] |
            [[n1 [v1 [f1 [m1 [vs1 [fs1
               [u1 [HD1 [Hu1 [Hc1 Hqe]]]]]]]]]] |
            [[n1 [v1 [m1 [vs1 [fs1 [f1
               [u1 [HD1 [Hf1 [Hu1 [Hc1 Hqe]]]]]]]]]]] |
             [n1 [v1 [f1 [m1 [vs1 [fs1
                [f1' [u1 [HD1 [Hf1' [Hu1 [Hc1 Hqe]]]]]]]]]]]]]]]]];
            try discriminate Hqe.
          * injection Hqe as E1 E2 E3 E4; subst n1 v1 m1 u1.
            apply witnessCondb_iff in Hc1.
            destruct Hc1 as [_ [[fs' [Hsub' HS']] _]].
            exists u; split;
              [unfold singVS; rewrite SOvv.singleton_in; reflexivity |].
            exact (mem_coreResolution_orig S_CF pi Df Da g m u fs' HS').
          * injection Hqe as E1 E2 E3 E4; subst n1 v1 m1 u1.
            apply witnessCondb_iff in Hc1.
            destruct Hc1 as [_ [[fs' [Hsub' HS']] _]].
            exists u; split;
              [unfold singVS; rewrite SOvv.singleton_in; reflexivity |].
            exact (mem_coreResolution_orig S_CF pi Df Da g m u fs' HS').
        + injection Hy as Eq Em Ews; subst q m' ws.
          rewrite mem_coreResolution in Hq.
          destruct Hq as
            [[n1 [v1 [fs1 [HS1 Hqe]]]] |
            [[n1 [v1 [fs1 [f1 [HS1 [Hf1 Hqe]]]]]] |
            [[n1 [v1 [m1 [vs1 [fs1 [u1 [HD1 [Hu1 [Hc1 Hqe]]]]]]]]] |
            [[n1 [v1 [f1 [m1 [vs1 [fs1
               [u1 [HD1 [Hu1 [Hc1 Hqe]]]]]]]]]] |
            [[n1 [v1 [m1 [vs1 [fs1 [f1
               [u1 [HD1 [Hf1 [Hu1 [Hc1 Hqe]]]]]]]]]]] |
             [n1 [v1 [f1 [m1 [vs1 [fs1
                [f1' [u1 [HD1 [Hf1' [Hu1 [Hc1 Hqe]]]]]]]]]]]]]]]]];
            try discriminate Hqe.
          injection Hqe as E1 E2 E3 E4; subst n1 f1 v1.
          destruct (Hpca (n, v) fs1 HS1 f Hf1 m vs fs Hda)
            as [u [[Hu [Htk Hpi]] _]].
          exists u; split;
            [rewrite mem_embedVS; exact Hu |].
          apply (mem_coreResolution_a_interA S_CF pi Df Da g n v f m vs fs
                   f' u Hda Hf' Hu);
            [exists fs1; exact HS1 | exact Htk | exact Hpi].
        + injection Hy as Eq Em Ews; subst q m' ws.
          rewrite mem_coreResolution in Hq.
          destruct Hq as
            [[n1 [v1 [fs1 [HS1 Hqe]]]] |
            [[n1 [v1 [fs1 [f1 [HS1 [Hf1 Hqe]]]]]] |
            [[n1 [v1 [m1 [vs1 [fs1 [u1 [HD1 [Hu1 [Hc1 Hqe]]]]]]]]] |
            [[n1 [v1 [f1 [m1 [vs1 [fs1
               [u1 [HD1 [Hu1 [Hc1 Hqe]]]]]]]]]] |
            [[n1 [v1 [m1 [vs1 [fs1 [f1
               [u1 [HD1 [Hf1 [Hu1 [Hc1 Hqe]]]]]]]]]]] |
             [n1 [v1 [f1 [m1 [vs1 [fs1
                [f1' [u1 [HD1 [Hf1' [Hu1 [Hc1 Hqe]]]]]]]]]]]]]]]]];
            try discriminate Hqe.
          injection Hqe as E1 E2 E3 E4 E5 E6; subst n1 v1 f1 m1 f1' u1.
          apply witnessCondb_iff in Hc1.
          destruct Hc1 as [_ [[fs'' [Hsub'' HS'']] _]].
          exists u; split;
            [unfold singVS; rewrite SOvv.singleton_in; reflexivity |].
          exact (mem_coreResolution_featured S_CF pi Df Da g m u fs'' f'
                   HS'' (Hsub'' f' Hf1')).
        + injection Hy as Eq Em Ews; subst q m' ws.
          rewrite mem_coreResolution in Hq.
          destruct Hq as
            [[n1 [v1 [fs1 [HS1 Hqe]]]] |
            [[n1 [v1 [fs1 [f1 [HS1 [Hf1 Hqe]]]]]] |
            [[n1 [v1 [m1 [vs1 [fs1 [u1 [HD1 [Hu1 [Hc1 Hqe]]]]]]]]] |
            [[n1 [v1 [f1 [m1 [vs1 [fs1
               [u1 [HD1 [Hu1 [Hc1 Hqe]]]]]]]]]] |
            [[n1 [v1 [m1 [vs1 [fs1 [f1
               [u1 [HD1 [Hf1 [Hu1 [Hc1 Hqe]]]]]]]]]]] |
             [n1 [v1 [f1 [m1 [vs1 [fs1
                [f1' [u1 [HD1 [Hf1' [Hu1 [Hc1 Hqe]]]]]]]]]]]]]]]]];
            try discriminate Hqe.
          injection Hqe as E1 E2 E3 E4 E5 E6; subst n1 v1 f1 m1 f1' u1.
          apply witnessCondb_iff in Hc1.
          destruct Hc1 as [HinS [Htk Hpi]].
          exists u; split;
            [unfold singVS; rewrite SOvv.singleton_in; reflexivity |].
          exact (mem_coreResolution_a_inter S_CF pi Df Da g n v f m vs1 fs1
                   u HD1 Hu1 HinS Htk Hpi).
      - intros nm cv1 cv2 H1 H2.
        rewrite mem_coreResolution in H1, H2.
        destruct H1 as [[n1 [v1 [fs1 [HS1 Hq1]]]] |
                        [[n1 [v1 [fs1 [f1 [HS1 [Hf1 Hq1]]]]]] |
                        [[n1 [v1 [m1 [vs1 [fs1 [u1 [HD1 [Hu1 [Hc1 Hq1]]]]]]]]] |
                        [[n1 [v1 [f1 [m1 [vs1 [fs1
                           [u1 [HD1 [Hu1 [Hc1 Hq1]]]]]]]]]] |
                        [[n1 [v1 [m1 [vs1 [fs1 [f1
                           [u1 [HD1 [Hf1 [Hu1 [Hc1 Hq1]]]]]]]]]]] |
                         [n1 [v1 [f1 [m1 [vs1 [fs1
                            [f1' [u1 [HD1 [Hf1' [Hu1 [Hc1 Hq1]]]]]]]]]]]]]]]]];
          injection Hq1 as E1 E2; subst nm cv1;
          (destruct H2 as
            [[n2 [v2 [fs2 [HS2 Hq2]]]] |
            [[n2 [v2 [fs2 [f2 [HS2 [Hf2 Hq2]]]]]] |
            [[n2 [v2 [m2 [vs2 [fs2 [u2 [HD2 [Hu2 [Hc2 Hq2]]]]]]]]] |
            [[n2 [v2 [f2 [m2 [vs2 [fs2
               [u2 [HD2 [Hu2 [Hc2 Hq2]]]]]]]]]] |
            [[n2 [v2 [m2 [vs2 [fs2 [f2
               [u2 [HD2 [Hf2 [Hu2 [Hc2 Hq2]]]]]]]]]]] |
             [n2 [v2 [f2 [m2 [vs2 [fs2
                [f2' [u2 [HD2 [Hf2' [Hu2 [Hc2 Hq2]]]]]]]]]]]]]]]]];
           try discriminate Hq2).
        + injection Hq2 as E3 E4 E5; subst n2 cv2.
          destruct (V.eq_dec v1 v2) as [-> | NE]; [reflexivity |].
          exfalso; exact (Hvg n1 v1 v2 fs1 fs2 HS1 HS2 NE E4).
        + injection Hq2 as E3 E4 E5 E6; subst n2 f2 cv2.
          destruct (V.eq_dec v1 v2) as [-> | NE]; [reflexivity |].
          exfalso; exact (Hvg n1 v1 v2 fs1 fs2 HS1 HS2 NE E5).
        + injection Hq2 as E3 E4 E5 E6; subst n2 v2 m2 cv2.
          apply witnessCondb_iff in Hc1; destruct Hc1 as [_ [_ Hpi1]].
          apply witnessCondb_iff in Hc2; destruct Hc2 as [_ [_ Hpi2]].
          rewrite (Hpif m1 u1 u2 (n1, v1) Hpi1 Hpi2); reflexivity.
        + injection Hq2 as E3 E4 E5 E6; subst n2 v2 m2 cv2.
          apply witnessCondb_iff in Hc1; destruct Hc1 as [_ [_ Hpi1]].
          apply witnessCondb_iff in Hc2; destruct Hc2 as [_ [_ Hpi2]].
          rewrite (Hpif m1 u1 u2 (n1, v1) Hpi1 Hpi2); reflexivity.
        + injection Hq2 as E3 E4 E5 E6; subst n2 v2 m2 cv2.
          apply witnessCondb_iff in Hc1; destruct Hc1 as [_ [_ Hpi1]].
          apply witnessCondb_iff in Hc2; destruct Hc2 as [_ [_ Hpi2]].
          rewrite (Hpif m1 u1 u2 (n1, v1) Hpi1 Hpi2); reflexivity.
        + injection Hq2 as E3 E4 E5 E6; subst n2 v2 m2 cv2.
          apply witnessCondb_iff in Hc1; destruct Hc1 as [_ [_ Hpi1]].
          apply witnessCondb_iff in Hc2; destruct Hc2 as [_ [_ Hpi2]].
          rewrite (Hpif m1 u1 u2 (n1, v1) Hpi1 Hpi2); reflexivity.
        + injection Hq2 as E3 E4 E5 E6 E7; subst n2 v2 m2 f2 cv2.
          apply witnessCondb_iff in Hc1; destruct Hc1 as [_ [_ Hpi1]].
          apply witnessCondb_iff in Hc2; destruct Hc2 as [_ [_ Hpi2]].
          rewrite (Hpif m1 u1 u2 (n1, v1) Hpi1 Hpi2); reflexivity.
        + injection Hq2 as E3 E4 E5 E6 E7 E8; subst n2 v2 f2 m2 f2' cv2.
          apply witnessCondb_iff in Hc1; destruct Hc1 as [_ [_ Hpi1]].
          apply witnessCondb_iff in Hc2; destruct Hc2 as [_ [_ Hpi2]].
          rewrite (Hpif m1 u1 u2 (n1, v1) Hpi1 Hpi2); reflexivity.
    Qed.

    Module Lookup.
      Module NEqb := UOTEqb N.
      Definition pkgNodeFibre (Da : Feat.AddlDepRel.t) (p : Pkg.t) (m : N.t) :
          Feat.AddlDepRel.t :=
        Feat.AddlDepRel.filter
          (fun '((q, _), (m', _)) => andb (PkgEqb.eqb q p) (NEqb.eqb m' m))
          Da.

      Lemma mem_pkgNodeFibre :
        forall Da (p q : Pkg.t) (f : F.t) (m m' : N.t) (d : Feat.VSFS.t),
          Feat.AddlDepRel.In ((q, f), (m', d)) (pkgNodeFibre Da p m) <->
          Feat.AddlDepRel.In ((q, f), (m', d)) Da /\ q = p /\ m' = m.
      Proof.
        intros Da p q f m m' d; unfold pkgNodeFibre.
        rewrite Feat.AddlDepRel.filter_spec'; cbn beta iota.
        rewrite Bool.andb_true_iff, PkgEqb.eqb_true_iff, NEqb.eqb_true_iff.
        tauto.
      Qed.

      Lemma reduceDeps_mono :
        forall R R' support support' Df Df' Da Da' g (y : T.DepElt.t),
          PkgSet.Subset R' R -> Feat.SupportSet.Subset support' support ->
          Feat.FeatDepRel.Subset Df' Df -> Feat.AddlDepRel.Subset Da' Da ->
          T.DepRel.In y (reduceDeps R' support' Df' Da' g) ->
          T.DepRel.In y (reduceDeps R support Df Da g).
      Proof.
        intros R R' support support' Df Df' Da Da' g y HR Hsup HDf HDa;
          revert y.
        unfold reduceDeps, supportEdges, fDepToInterEdges, fInterToOrigEdges,
          fDepToInterFeatEdges, fInterToFeatEdges, fInterFeatToInterEdges,
          aDepToInterEdges, aInterToOrigEdges, aDepToInterFeatEdges,
          aInterToFeatEdges, aInterFeatToInterEdges.
        repeat apply SOsd.union_subset.
        - apply SOsd.filterMap_mono; [exact Hsup |].
          intros [[n v] f] z Hz; cbn beta iota in Hz |- *.
          destruct (PkgSet.mem (n, v) R') eqn:Em; [| discriminate Hz].
          rewrite PkgSet.mem_spec in Em; apply HR in Em.
          rewrite <- PkgSet.mem_spec in Em; rewrite Em; exact Hz.
        - apply SOfd.map_mono; [exact HDf | intros x; reflexivity].
        - apply SOfd.unionMap_mono; [exact HDf | intros x z Hz; exact Hz].
        - apply SOfd.unionMap_mono; [exact HDf | intros x z Hz; exact Hz].
        - apply SOfd.unionMap_mono; [exact HDf | intros x z Hz; exact Hz].
        - apply SOfd.unionMap_mono; [exact HDf | intros x z Hz; exact Hz].
        - apply SOad.map_mono; [exact HDa | intros x; reflexivity].
        - apply SOad.unionMap_mono; [exact HDa | intros x z Hz; exact Hz].
        - apply SOad.unionMap_mono; [exact HDa | intros x z Hz; exact Hz].
        - apply SOad.unionMap_mono; [exact HDa | intros x z Hz; exact Hz].
        - apply SOad.unionMap_mono; [exact HDa | intros x z Hz; exact Hz].
      Qed.

      Module FeatDepRelFibred := Feat.Reduction.Lookup.FeatDepRelFibred.
      Theorem dependees_lookupGranularOrig : forall R support Df Da g n v,
          T.dependees (reduceDeps R support Df Da g)
            (Name.GranularOrig n (g v), v) =
          T.dependees
            (reduceDeps PkgSet.empty Feat.SupportSet.empty
               (FeatDepRelFibred.tailFibre Df (n, v))
               Feat.AddlDepRel.empty g)
            (Name.GranularOrig n (g v), v).
      Proof.
        intros R support Df Da g n v; apply T.dependees_ext; intros [m ws].
        split; [| apply reduceDeps_mono;
                  [apply PkgSet.empty_subset
                  | apply Feat.SupportSet.empty_subset
                  | apply FeatDepRelFibred.tailFibre_subset
                  | apply Feat.AddlDepRel.empty_subset]].
        intro H; apply mem_reduceDeps in H; apply mem_reduceDeps.
        inversion H; subst.
        - eapply EdgeFDepToInter; apply FeatDepRelFibred.mem_tailFibre;
            split; [eassumption | reflexivity].
        - eapply EdgeFDepToInterFeat;
            [apply FeatDepRelFibred.mem_tailFibre;
               split; [eassumption | reflexivity]
            | eassumption].
      Qed.

      Module PkgFibred := Feat.Reduction.Lookup.PkgFibred.
      Module SupportFibred := Feat.Reduction.Lookup.SupportFibred.
      Module AddlDepRelFibred := Feat.Reduction.Lookup.AddlDepRelFibred.
      Theorem dependees_lookupGranularFeatPkg : forall R support Df Da g n v f,
          T.dependees (reduceDeps R support Df Da g)
            (Name.GranularFeatPkg n f (g v), v) =
          T.dependees
            (reduceDeps (PkgFibred.idFibre R (n, v))
               (SupportFibred.idFibre support ((n, v), f))
               Feat.FeatDepRel.empty
               (AddlDepRelFibred.tailFibre Da ((n, v), f)) g)
            (Name.GranularFeatPkg n f (g v), v).
      Proof.
        intros R support Df Da g n v f; apply T.dependees_ext; intros [m ws].
        split; [| apply reduceDeps_mono;
                  [apply PkgFibred.idFibre_subset
                  | apply SupportFibred.idFibre_subset
                  | apply Feat.FeatDepRel.empty_subset
                  | apply AddlDepRelFibred.tailFibre_subset]].
        intro H; apply mem_reduceDeps in H; apply mem_reduceDeps.
        inversion H; subst.
        - apply EdgeSupport;
            [apply SupportFibred.mem_idFibre;
               split; [eassumption | reflexivity]
            | apply PkgFibred.mem_idFibre; split; [eassumption | reflexivity]].
        - eapply EdgeADepToInter; apply AddlDepRelFibred.mem_tailFibre;
            split; [eassumption | reflexivity].
        - eapply EdgeADepToInterFeat;
            [apply AddlDepRelFibred.mem_tailFibre;
               split; [eassumption | reflexivity]
            | eassumption].
      Qed.

      Theorem dependees_lookupIntermediate : forall R support Df Da g n v m u,
          T.dependees (reduceDeps R support Df Da g)
            (Name.Intermediate n v m, u) =
          T.dependees
            (reduceDeps PkgSet.empty Feat.SupportSet.empty
               (FeatDepRelFibred.endsFibre Df (n, v) m)
               (pkgNodeFibre Da (n, v) m) g)
            (Name.Intermediate n v m, u).
      Proof.
        intros R support Df Da g n v m u.
        apply T.dependees_ext; intros [m' ws].
        split; [| apply reduceDeps_mono;
                  [apply PkgSet.empty_subset
                  | apply Feat.SupportSet.empty_subset
                  | apply FeatDepRelFibred.endsFibre_subset
                  | intros [[q f0] [m0 d]] Hq; apply mem_pkgNodeFibre in Hq;
                    destruct Hq as [Hq _]; exact Hq]].
        intro H; apply mem_reduceDeps in H; apply mem_reduceDeps.
        inversion H; subst.
        - eapply EdgeFInterToOrig;
            [apply FeatDepRelFibred.mem_endsFibre;
               split; [eassumption | split; reflexivity]
            | eassumption].
        - eapply EdgeAInterToOrig;
            [apply mem_pkgNodeFibre; split; [eassumption | split; reflexivity]
            | eassumption].
      Qed.

      Theorem dependees_lookupIntermediateF :
        forall R support Df Da g n v m f u,
          T.dependees (reduceDeps R support Df Da g)
            (Name.IntermediateF n v m f, u) =
          T.dependees
            (reduceDeps PkgSet.empty Feat.SupportSet.empty
               (FeatDepRelFibred.endsFibre Df (n, v) m)
               Feat.AddlDepRel.empty g)
            (Name.IntermediateF n v m f, u).
      Proof.
        intros R support Df Da g n v m f u.
        apply T.dependees_ext; intros [m' ws].
        split; [| apply reduceDeps_mono;
                  [apply PkgSet.empty_subset
                  | apply Feat.SupportSet.empty_subset
                  | apply FeatDepRelFibred.endsFibre_subset
                  | apply Feat.AddlDepRel.empty_subset]].
        intro H; apply mem_reduceDeps in H; apply mem_reduceDeps.
        inversion H; subst.
        - eapply EdgeFInterToFeat;
            [apply FeatDepRelFibred.mem_endsFibre;
               split; [eassumption | split; reflexivity]
            | eassumption | eassumption].
        - eapply EdgeFInterFeatToInter;
            [apply FeatDepRelFibred.mem_endsFibre;
               split; [eassumption | split; reflexivity]
            | eassumption | eassumption].
      Qed.

      Theorem dependees_lookupIntermediateA :
        forall R support Df Da g n v f m f' u,
          T.dependees (reduceDeps R support Df Da g)
            (Name.IntermediateA n v f m f', u) =
          T.dependees
            (reduceDeps PkgSet.empty Feat.SupportSet.empty Feat.FeatDepRel.empty
               (AddlDepRelFibred.endsFibre Da ((n, v), f) m) g)
            (Name.IntermediateA n v f m f', u).
      Proof.
        intros R support Df Da g n v f m f' u.
        apply T.dependees_ext; intros [m' ws].
        split; [| apply reduceDeps_mono;
                  [apply PkgSet.empty_subset
                  | apply Feat.SupportSet.empty_subset
                  | apply Feat.FeatDepRel.empty_subset
                  | apply AddlDepRelFibred.endsFibre_subset]].
        intro H; apply mem_reduceDeps in H; apply mem_reduceDeps.
        inversion H; subst.
        - eapply EdgeAInterToFeat;
            [apply AddlDepRelFibred.mem_endsFibre;
               split; [eassumption | split; reflexivity]
            | eassumption | eassumption].
        - eapply EdgeAInterFeatToInter;
            [apply AddlDepRelFibred.mem_endsFibre;
               split; [eassumption | split; reflexivity]
            | eassumption | eassumption].
      Qed.

    End Lookup.
  End Reduction.
End FeatureConcurrent.
