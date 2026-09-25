From Stdlib Require Import MSets.
From PackageCalculus Require Import Prelude Core Feature.

Create HintDb cmp_fconc.
Create Rewrite HintDb cmp_fconc.
Create HintDb fc_mem.

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

    Lemma mem_singVS : forall u w, T.VSet.In w (singVS u) <-> w = u.
    Proof. intros u w; exact (SOvv.singleton_in u w). Qed.

    (* The encodings are unions of map, unionMap and guarded filterMap over
       tuples.  mem_open takes a membership apart into its witnesses;
       mem_close rebuilds one disjunct of a union from the hypotheses and
       fails on any other, so pick_close finds the component by what it
       contains rather than by its position in the union. *)
    Ltac split_pairs :=
      repeat match goal with
      | x : ?T |- _ =>
          lazymatch eval hnf in T with
          | prod _ _ => destruct x
          | Feat.Reduction.Name.name => destruct x
          end
      end.

    Ltac mem_open :=
      repeat progress (
        mem_destruct; split_pairs; cbn beta iota delta [granularOf] in *;
        rewrite ?SOvp.mem_map, ?SOvp.mem_unionMap, ?SOvp.mem_filterMap,
          ?SOfsp.mem_map, ?SOfsp.mem_unionMap, ?SOvd.mem_map,
          ?SOvd.mem_unionMap, ?SOfsd.mem_map, ?SOfsd.mem_unionMap in *;
        try match goal with
            | H : (if ?b then _ else _) = Some _ |- _ =>
                destruct b eqn:?; [| discriminate H]
            | H : PkgSet.mem _ _ = true |- _ => apply PkgSet.mem_spec in H
            end).

    Ltac mem_close :=
      repeat first
        [ reflexivity
        | progress cbn beta iota delta [granularOf]
        | rewrite SOvp.mem_map | rewrite SOvp.mem_unionMap
        | rewrite SOvp.mem_filterMap | rewrite SOfsp.mem_map
        | rewrite SOfsp.mem_unionMap | rewrite SOvd.mem_map
        | rewrite SOvd.mem_unionMap | rewrite SOfsd.mem_map
        | rewrite SOfsd.mem_unionMap
        | match goal with
          | H : ?b = true |- context [if ?b then _ else _] => rewrite H
          | |- context [PkgSet.mem ?x ?s] =>
              replace (PkgSet.mem x s) with true
                by (symmetry; apply PkgSet.mem_spec; assumption)
          end
        | eexists; split; [eassumption |] ].

    Ltac pick_close :=
      first [ solve [mem_close] | left; solve [mem_close]
            | right; pick_close ].

    Inductive RealMember (R : PkgSet.t) (support : Feat.SupportSet.t)
        (Df : Feat.FeatDepRel.t) (Da : Feat.AddlDepRel.t) (g : V.t -> G.t) :
        T.Pkg.t -> Prop :=
    | RealOrig : forall n v,
        Feat.Reduction.T.PkgSet.In (Feat.Reduction.Name.Orig n, v)
          (Feat.Reduction.reduceReal R support) ->
        RealMember R support Df Da g (Name.GranularOrig n (g v), v)
    | RealFeatPkg : forall n f v,
        Feat.Reduction.T.PkgSet.In (Feat.Reduction.Name.FeatPkg n f, v)
          (Feat.Reduction.reduceReal R support) ->
        RealMember R support Df Da g (Name.GranularFeatPkg n f (g v), v)
    | RealFInter : forall n v m vs fs u,
        Feat.FeatDepRel.In ((n, v), (m, (vs, fs))) Df -> VSet.In u vs ->
        RealMember R support Df Da g (Name.Intermediate n v m, u)
    | RealFInterF : forall n v m vs fs u f,
        Feat.FeatDepRel.In ((n, v), (m, (vs, fs))) Df -> VSet.In u vs ->
        Feat.FSet.In f fs ->
        RealMember R support Df Da g (Name.IntermediateF n v m f, u)
    | RealAInter : forall n v f m vs fs u,
        Feat.AddlDepRel.In (((n, v), f), (m, (vs, fs))) Da -> VSet.In u vs ->
        RealMember R support Df Da g (Name.Intermediate n v m, u)
    | RealAInterA : forall n v f m vs fs u f',
        Feat.AddlDepRel.In (((n, v), f), (m, (vs, fs))) Da -> VSet.In u vs ->
        Feat.FSet.In f' fs ->
        RealMember R support Df Da g (Name.IntermediateA n v f m f', u).
    #[local] Hint Constructors RealMember : fc_mem.

    Lemma mem_reduceReal : forall R support Df Da g (y : T.Pkg.t),
        T.PkgSet.In y (reduceReal R support Df Da g) <->
        RealMember R support Df Da g y.
    Proof.
      intros R support Df Da g y; unfold reduceReal, granularReal,
        fInterReal, fInterFeatReal, aInterReal, aInterFeatReal.
      rewrite !T.PkgSet.union_spec, SOqp.mem_map, !SOfp.mem_unionMap,
        !SOap.mem_unionMap.
      split.
      - intro H;
          repeat match goal with H : _ \/ _ |- _ => destruct H as [H | H] end;
          mem_open; eauto with fc_mem.
      - destruct 1; pick_close.
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
    #[local] Hint Constructors EncodedEdge : fc_mem.

    Lemma mem_reduceDeps : forall R support Df Da g (y : T.DepElt.t),
        T.DepRel.In y (reduceDeps R support Df Da g) <->
        EncodedEdge R support Df Da g y.
    Proof.
      intros R support Df Da g y; unfold reduceDeps, supportEdges,
        fDepToInterEdges, fInterToOrigEdges, fDepToInterFeatEdges,
        fInterToFeatEdges, fInterFeatToInterEdges, aDepToInterEdges,
        aInterToOrigEdges, aDepToInterFeatEdges, aInterToFeatEdges,
        aInterFeatToInterEdges.
      rewrite !T.DepRel.union_spec, SOsd.mem_filterMap, SOfd.mem_map,
        !SOfd.mem_unionMap, SOad.mem_map, !SOad.mem_unionMap.
      split.
      - intro H;
          repeat match goal with H : _ \/ _ |- _ => destruct H as [H | H] end;
          mem_open; eauto with fc_mem.
      - destruct 1; pick_close.
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
          split; [exact HS | cbn beta iota; apply dec_refl].
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
          split; [exact HS | cbn beta iota; apply dec_refl].
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

    (* A dependency and an additional dependency are closed over by the same
       argument; they differ only in the node their edges leave from and in
       how its intermediate feature nodes are named. *)
    Lemma parent_closure_step :
      forall RR D r g S (q : T.Pkg.t) n v m vs fs (iF : F.t -> Name.t),
        T.IsResolution RR D r S -> T.PkgSet.In q S ->
        T.DepRel.In (q, (Name.Intermediate n v m, embedVS vs)) D ->
        (forall u, VSet.In u vs ->
           T.DepRel.In ((Name.Intermediate n v m, u),
                        (Name.GranularOrig m (g u), singVS u)) D) ->
        (forall f, Feat.FSet.In f fs ->
           T.DepRel.In (q, (iF f, embedVS vs)) D) ->
        (forall f u, Feat.FSet.In f fs -> VSet.In u vs ->
           T.DepRel.In ((iF f, u), (Name.Intermediate n v m, singVS u)) D) ->
        (forall f u, Feat.FSet.In f fs -> VSet.In u vs ->
           T.DepRel.In ((iF f, u),
                        (Name.GranularFeatPkg m f (g u), singVS u)) D) ->
        exists! u, VSet.In u vs /\
          (exists fs', Feat.FSet.Subset fs fs' /\
             Feat.FeaturedSet.In ((m, u), fs')
               (featureConcurrentResolution g S)) /\
          ParentRel.In ((m, u), (n, v)) (parents S).
    Proof.
      intros RR D r g S q n v m vs fs iF [_ _ Hdep Huniq] HqS Hd Hto Hfd
        Hback Hfwd.
      destruct (Hdep _ HqS _ _ Hd) as [u [Hu HiS]]; rewrite mem_embedVS in Hu.
      destruct (Hdep _ HiS _ _ (Hto u Hu)) as [w [Hw HoS]].
      apply mem_singVS in Hw; subst w.
      exists u; split; [split; [exact Hu | split] |].
      - exists (featsOf g m u S); split.
        + intros f Hf; apply featsOf_spec.
          destruct (Hdep _ HqS _ _ (Hfd f Hf)) as [u1 [Hu1 HfS]].
          rewrite mem_embedVS in Hu1.
          destruct (Hdep _ HfS _ _ (Hback f u1 Hf Hu1)) as [w [Hw Hi1S]].
          apply mem_singVS in Hw; subst w.
          assert (u1 = u) as -> by exact (Huniq _ _ _ Hi1S HiS).
          destruct (Hdep _ HfS _ _ (Hfwd f u Hf Hu)) as [w [Hw HgS]].
          apply mem_singVS in Hw; subst w; exact HgS.
        + apply mem_featureConcurrentResolution; exists m, u;
            split; [exact HoS | reflexivity].
      - apply mem_parents; exact HiS.
      - intros u' [_ [_ Hpi]]; apply mem_parents in Hpi.
        exact (Huniq _ _ _ HiS Hpi).
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
      pose proof Hres as [Hsub Hroot Hdep Huniq].
      destruct r as [rn rv].
      unfold embedOrigPkg in Hroot; simpl in Hroot.
      assert (HorigR : forall n v,
                 T.PkgSet.In (Name.GranularOrig n (g v), v) S ->
                 PkgSet.In (n, v) R).
      { intros n v HS; pose proof (Hsub _ HS) as HF.
        apply mem_reduceReal in HF; inversion HF; subst.
        eapply Feat.Reduction.mem_reduceReal_orig; eassumption. }
      assert (HfeatSup : forall n f v,
                 T.PkgSet.In
                   (Name.GranularFeatPkg n f (g v), v) S ->
                 Feat.SupportSet.In ((n, v), f) support /\ PkgSet.In (n, v) R).
      { intros n f v HS; pose proof (Hsub _ HS) as HF.
        apply mem_reduceReal in HF; inversion HF; subst.
        eapply Feat.Reduction.mem_reduceReal_featPkg; eassumption. }
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
        apply (parent_closure_step _ _ _ g S _ n v m vs fs
                 (Name.IntermediateF n v m) Hres HpS);
          intros; apply mem_reduceDeps;
          [eapply EdgeFDepToInter | eapply EdgeFInterToOrig
          | eapply EdgeFDepToInterFeat | eapply EdgeFInterFeatToInter
          | eapply EdgeFInterToFeat]; eassumption.
      - intros p fs_p Hmem f Hf m vs fs Hda.
        rewrite mem_featureConcurrentResolution in Hmem.
        destruct Hmem as [n [v [HpS Heq]]].
        injection Heq as E1 E2; subst p fs_p.
        rewrite featsOf_spec in Hf.
        apply (parent_closure_step _ _ _ g S _ n v m vs fs
                 (Name.IntermediateA n v f m) Hres Hf);
          intros; apply mem_reduceDeps;
          [eapply EdgeADepToInter | eapply EdgeAInterToOrig
          | eapply EdgeADepToInterFeat | eapply EdgeAInterFeatToInter
          | eapply EdgeAInterToFeat]; eassumption.
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

    Inductive CoreMember (S_CF : Feat.FeaturedSet.t) (pi : ParentRel.t)
        (Df : Feat.FeatDepRel.t) (Da : Feat.AddlDepRel.t) (g : V.t -> G.t) :
        T.Pkg.t -> Prop :=
    | CoreOrig : forall n v fs,
        Feat.FeaturedSet.In ((n, v), fs) S_CF ->
        CoreMember S_CF pi Df Da g (Name.GranularOrig n (g v), v)
    | CoreFeatPkg : forall n v fs f,
        Feat.FeaturedSet.In ((n, v), fs) S_CF -> Feat.FSet.In f fs ->
        CoreMember S_CF pi Df Da g (Name.GranularFeatPkg n f (g v), v)
    | CoreFInter : forall n v m vs fs u,
        Feat.FeatDepRel.In ((n, v), (m, (vs, fs))) Df -> VSet.In u vs ->
        witnessCondb S_CF pi (n, v) fs m u = true ->
        CoreMember S_CF pi Df Da g (Name.Intermediate n v m, u)
    | CoreAInter : forall n v f m vs fs u,
        Feat.AddlDepRel.In (((n, v), f), (m, (vs, fs))) Da -> VSet.In u vs ->
        witnessCondb S_CF pi (n, v) fs m u = true ->
        CoreMember S_CF pi Df Da g (Name.Intermediate n v m, u)
    | CoreFInterF : forall n v m vs fs f u,
        Feat.FeatDepRel.In ((n, v), (m, (vs, fs))) Df -> Feat.FSet.In f fs ->
        VSet.In u vs -> witnessCondb S_CF pi (n, v) fs m u = true ->
        CoreMember S_CF pi Df Da g (Name.IntermediateF n v m f, u)
    | CoreAInterA : forall n v f m vs fs f' u,
        Feat.AddlDepRel.In (((n, v), f), (m, (vs, fs))) Da ->
        Feat.FSet.In f' fs -> VSet.In u vs ->
        witnessCondb S_CF pi (n, v) fs m u = true ->
        CoreMember S_CF pi Df Da g (Name.IntermediateA n v f m f', u).
    #[local] Hint Constructors CoreMember : fc_mem.

    Lemma mem_coreResolution : forall S_CF pi Df Da g (q : T.Pkg.t),
        T.PkgSet.In q (coreResolution S_CF pi Df Da g) <->
        CoreMember S_CF pi Df Da g q.
    Proof.
      intros S_CF pi Df Da g q; unfold coreResolution.
      rewrite !T.PkgSet.union_spec, SOsw.mem_map, SOsw.mem_unionMap,
        !SOfp.mem_unionMap, !SOap.mem_unionMap.
      split.
      - intro H;
          repeat match goal with H : _ \/ _ |- _ => destruct H as [H | H] end;
          mem_open; eauto with fc_mem.
      - destruct 1; pick_close.
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
      - intros q Hq; apply mem_coreResolution in Hq; apply mem_reduceReal.
        destruct Hq as [n v fs HS | n v fs f HS Hf | n v m vs fs u HD Hu _
          | n v f m vs fs u HD Hu _ | n v m vs fs f u HD Hf Hu _
          | n v f m vs fs f' u HD Hf' Hu _].
        + apply RealOrig, Feat.Reduction.mem_reduceReal_orig.
          exact (Hsubset _ _ HS).
        + apply RealFeatPkg, Feat.Reduction.mem_reduceReal_featPkg.
          exact (conj (Hsm n v fs f HS Hf) (Hsubset _ _ HS)).
        + eapply RealFInter; eassumption.
        + eapply RealAInter; eassumption.
        + eapply RealFInterF; eassumption.
        + eapply RealAInterA; eassumption.
      - apply mem_coreResolution; unfold embedOrigPkg.
        eapply CoreOrig; exact Hrootm.
      - intros q Hq m' ws Hd.
        apply mem_coreResolution in Hq; apply mem_reduceDeps in Hd.
        destruct Hq as [n v fs HS | n v fs f HS Hf
          | n v m vs fs u HD Hu Hc | n v f m vs fs u HD Hu Hc
          | n v m vs fs f u HD Hf Hu Hc | n v f m vs fs f' u HD Hf' Hu Hc].
        + inversion Hd; subst.
          * destruct (Hpc _ _ HS _ _ _ ltac:(eassumption))
              as [u [[Hu [Htk Hpi]] _]].
            exists u; split; [apply mem_embedVS; exact Hu |].
            apply mem_coreResolution; eapply CoreFInter;
              [eassumption | exact Hu | apply witnessCondb_iff; eauto].
          * destruct (Hpc _ _ HS _ _ _ ltac:(eassumption))
              as [u [[Hu [Htk Hpi]] _]].
            exists u; split; [apply mem_embedVS; exact Hu |].
            apply mem_coreResolution; eapply CoreFInterF;
              [eassumption | eassumption | exact Hu
              | apply witnessCondb_iff; eauto].
        + inversion Hd; subst.
          * eexists; split; [apply mem_singVS; reflexivity |].
            apply mem_coreResolution; eapply CoreOrig; exact HS.
          * destruct (Hpca _ _ HS _ Hf _ _ _ ltac:(eassumption))
              as [u [[Hu [Htk Hpi]] _]].
            exists u; split; [apply mem_embedVS; exact Hu |].
            apply mem_coreResolution; eapply CoreAInter;
              [eassumption | exact Hu | apply witnessCondb_iff; eauto].
          * destruct (Hpca _ _ HS _ Hf _ _ _ ltac:(eassumption))
              as [u [[Hu [Htk Hpi]] _]].
            exists u; split; [apply mem_embedVS; exact Hu |].
            apply mem_coreResolution; eapply CoreAInterA;
              [eassumption | eassumption | exact Hu
              | apply witnessCondb_iff; eauto].
        + inversion Hd; subst;
            apply witnessCondb_iff in Hc as [_ [[fs' [_ HS']] _]];
            eexists; (split; [apply mem_singVS; reflexivity |]);
            apply mem_coreResolution; eapply CoreOrig; exact HS'.
        + inversion Hd; subst;
            apply witnessCondb_iff in Hc as [_ [[fs' [_ HS']] _]];
            eexists; (split; [apply mem_singVS; reflexivity |]);
            apply mem_coreResolution; eapply CoreOrig; exact HS'.
        + inversion Hd; subst;
            eexists; (split; [apply mem_singVS; reflexivity |]);
            apply mem_coreResolution.
          * apply witnessCondb_iff in Hc as [_ [[fs' [Hsub' HS']] _]].
            eapply CoreFeatPkg; [exact HS' | exact (Hsub' _ Hf)].
          * eapply CoreFInter; [exact HD | exact Hu | exact Hc].
        + inversion Hd; subst;
            eexists; (split; [apply mem_singVS; reflexivity |]);
            apply mem_coreResolution.
          * apply witnessCondb_iff in Hc as [_ [[fs' [Hsub' HS']] _]].
            eapply CoreFeatPkg; [exact HS' | exact (Hsub' _ Hf')].
          * eapply CoreAInter; [exact HD | exact Hu | exact Hc].
      - intros n cv1 cv2 H1 H2.
        apply mem_coreResolution in H1, H2.
        inversion H1; subst; inversion H2; subst;
          repeat match goal with
                 | H : witnessCondb _ _ _ _ _ _ = true |- _ =>
                     apply witnessCondb_iff in H; destruct H as [_ [_ ?]]
                 end;
          try (eapply Hpif; eassumption).
        all: match goal with |- ?a = ?b =>
               destruct (V.eq_dec a b) as [| NE]; [assumption | exfalso];
               eapply (Hvg _ a b);
                 [eassumption | eassumption | exact NE | congruence]
             end.
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
      Lemma dependees_lookupGranularFeatPkg_any :
        forall R support Df Da g n v f,
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

      (* The membership premise is what collapses the fibres to singletons. *)
      Theorem dependees_lookupGranularFeatPkg : forall R support Df Da g n v f,
          T.PkgSet.In (Name.GranularFeatPkg n f (g v), v)
            (reduceReal R support Df Da g) ->
          T.dependees (reduceDeps R support Df Da g)
            (Name.GranularFeatPkg n f (g v), v) =
          T.dependees
            (reduceDeps (PkgSet.singleton (n, v))
               (Feat.SupportSet.singleton ((n, v), f))
               Feat.FeatDepRel.empty
               (AddlDepRelFibred.tailFibre Da ((n, v), f)) g)
            (Name.GranularFeatPkg n f (g v), v).
      Proof.
        intros R support Df Da g n v f Hin.
        assert (Feat.SupportSet.In ((n, v), f) support /\ PkgSet.In (n, v) R)
          as [Hs HR].
        { apply mem_reduceReal in Hin; inversion Hin; subst.
          eapply Feat.Reduction.mem_reduceReal_featPkg; eassumption. }
        assert (PkgFibred.idFibre R (n, v) = PkgSet.singleton (n, v)) as ER.
        { apply PkgSet.ext; intro x.
          rewrite PkgFibred.mem_idFibre, PkgSet.singleton_spec.
          split; [intros [_ E]; exact E
                 | intro E; split; [rewrite E; exact HR | exact E]]. }
        assert (SupportFibred.idFibre support ((n, v), f)
                = Feat.SupportSet.singleton ((n, v), f)) as ES.
        { apply Feat.SupportSet.ext; intro x.
          rewrite SupportFibred.mem_idFibre, Feat.SupportSet.singleton_spec.
          split; [intros [_ E]; exact E
                 | intro E; split; [rewrite E; exact Hs | exact E]]. }
        rewrite dependees_lookupGranularFeatPkg_any, ER, ES; reflexivity.
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
