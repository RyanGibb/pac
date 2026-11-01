From Stdlib Require Import MSets.
From PackageCalculus Require Import Prelude Core Feature.

Create HintDb cmp_fconc.
Create Rewrite HintDb cmp_fconc.
Create HintDb fc_mem.

Module ConcurrentFeature (N V F G : UsualOrderedType).
  Module Feature := Feature N V F.
  Module Source := Feature.Source.
  Module Package := Source.Package.
  Module PackageSet := Source.PackageSet.
  Module VSet := Source.VSet.

  Module ParentElt := PairUOT Package Package.
  Module ParentRel := FSetUOT ParentElt.

  Record IsResolution
      (R : PackageSet.t) (support : Feature.SupportRel.t)
      (Df : Feature.ParameterisedDependencyRel.t)
        (Da : Feature.AdditionalDependencyRel.t)
      (g : V.t -> G.t) (r : Package.t)
      (S : Feature.FeaturedSet.t) (pi : ParentRel.t) : Prop :=
    { res_subset : forall p fs, Feature.FeaturedSet.In (p, fs) S ->
        PackageSet.In p R
    ; res_root_mem : Feature.FeaturedSet.In (r, Feature.FSet.empty) S
    ; res_parent_closure :
        (forall p fs_p, Feature.FeaturedSet.In (p, fs_p) S ->
         forall n vs fs,
           Feature.ParameterisedDependencyRel.In (p, (n, (vs, fs))) Df ->
         exists v, VSet.In v vs /\
           (exists fs', Feature.FSet.Subset fs fs' /\
              Feature.FeaturedSet.In ((n, v), fs') S) /\
           ParentRel.In ((n, v), p) pi) /\
        (forall p fs_p, Feature.FeaturedSet.In (p, fs_p) S ->
         forall f, Feature.FSet.In f fs_p ->
         forall n vs fs,
           Feature.AdditionalDependencyRel.In ((p, f), (n, (vs, fs))) Da ->
         exists v, VSet.In v vs /\
           (exists fs', Feature.FSet.Subset fs fs' /\
              Feature.FeaturedSet.In ((n, v), fs') S) /\
           ParentRel.In ((n, v), p) pi)
    ; res_pi_functional :
        forall n v v' p,
          ParentRel.In ((n, v), p) pi -> ParentRel.In ((n, v'), p) pi -> v = v'
    ; res_version_granularity :
        forall n v v' fs fs',
          Feature.FeaturedSet.In ((n, v), fs) S ->
          Feature.FeaturedSet.In ((n, v'), fs') S ->
          v <> v' -> g v <> g v'
    ; res_feature_unification :
        forall n v fs fs',
          Feature.FeaturedSet.In ((n, v), fs) S ->
          Feature.FeaturedSet.In ((n, v), fs') S -> fs = fs'
    ; res_support_mem :
        forall p fs f,
          Feature.FeaturedSet.In (p, fs) S -> Feature.FSet.In f fs ->
          Feature.SupportRel.In (p, f) support
    ; res_parent_subset :
        forall q p, ParentRel.In (q, p) pi ->
          (exists fs_q, Feature.FeaturedSet.In (q, fs_q) S) /\
          (exists fs_p, Feature.FeaturedSet.In (p, fs_p) S) }.

  Definition ParentDependency (Df : Feature.ParameterisedDependencyRel.t)
      (Da : Feature.AdditionalDependencyRel.t) (S : Feature.FeaturedSet.t)
        (pi : ParentRel.t)
      : Prop :=
    forall m u n v, ParentRel.In ((m, u), (n, v)) pi ->
      (exists vs fs,
        Feature.ParameterisedDependencyRel.In ((n, v), (m, (vs, fs))) Df) \/
      (exists fs_p f vs fs, Feature.FeaturedSet.In ((n, v), fs_p) S /\
         Feature.FSet.In f fs_p /\
         Feature.AdditionalDependencyRel.In (((n, v), f), (m, (vs, fs))) Da).

  Module Reduction.
    Module GranularOriginalName := PairUOT N G.
    Module GranularOriginalNameFacts := UOTCompareFacts GranularOriginalName.
    Module GranularFeaturePackageName := TripleUOT N F G.
    Module GranularFeaturePackageNameFacts :=
      UOTCompareFacts GranularFeaturePackageName.
    Module IntermediateName := TripleUOT N V N.
    Module IntermediateNameFacts := UOTCompareFacts IntermediateName.
    Module ParameterisedIntermediateNameTail := TripleUOT V N F.
    Module ParameterisedIntermediateName :=
      PairUOT N ParameterisedIntermediateNameTail.
    Module ParameterisedIntermediateNameFacts :=
      UOTCompareFacts ParameterisedIntermediateName.
    Module AdditionalIntermediateNameTail := TripleUOT F N F.
    Module AdditionalIntermediateName :=
      TripleUOT N V AdditionalIntermediateNameTail.
    Module AdditionalIntermediateNameFacts :=
      UOTCompareFacts AdditionalIntermediateName.
    #[local] Hint Rewrite GranularOriginalNameFacts.compare_eq_iff
      GranularFeaturePackageNameFacts.compare_eq_iff
      IntermediateNameFacts.compare_eq_iff
        ParameterisedIntermediateNameFacts.compare_eq_iff
      AdditionalIntermediateNameFacts.compare_eq_iff : cmp_fconc.
    #[local] Hint Extern 1 =>
      cmp_by GranularOriginalNameFacts.compare_antisym : cmp_fconc.
    #[local] Hint Extern 1 =>
      cmp_by GranularFeaturePackageNameFacts.compare_antisym : cmp_fconc.
    #[local] Hint Extern 1 =>
      cmp_by IntermediateNameFacts.compare_antisym : cmp_fconc.
    #[local] Hint Extern 1 =>
      cmp_by ParameterisedIntermediateNameFacts.compare_antisym : cmp_fconc.
    #[local] Hint Extern 1 =>
      cmp_by AdditionalIntermediateNameFacts.compare_antisym : cmp_fconc.
    #[local] Hint Extern 1 =>
      cmp_by GranularOriginalNameFacts.compare_lt_trans : cmp_fconc.
    #[local] Hint Extern 1 =>
      cmp_by GranularFeaturePackageNameFacts.compare_lt_trans : cmp_fconc.
    #[local] Hint Extern 1 =>
      cmp_by IntermediateNameFacts.compare_lt_trans : cmp_fconc.
    #[local] Hint Extern 1 =>
      cmp_by ParameterisedIntermediateNameFacts.compare_lt_trans : cmp_fconc.
    #[local] Hint Extern 1 =>
      cmp_by AdditionalIntermediateNameFacts.compare_lt_trans : cmp_fconc.

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
            GranularOriginalName.compare (n1, w1) (n2, w2)
        | GranularOrig _ _, _ => Lt
        | GranularFeatPkg _ _ _, GranularOrig _ _ => Gt
        | GranularFeatPkg n1 f1 w1, GranularFeatPkg n2 f2 w2 =>
            GranularFeaturePackageName.compare (n1, (f1, w1)) (n2, (f2, w2))
        | GranularFeatPkg _ _ _, _ => Lt
        | Intermediate n1 v1 m1, Intermediate n2 v2 m2 =>
            IntermediateName.compare (n1, (v1, m1)) (n2, (v2, m2))
        | Intermediate _ _ _, GranularOrig _ _ => Gt
        | Intermediate _ _ _, GranularFeatPkg _ _ _ => Gt
        | Intermediate _ _ _, _ => Lt
        | IntermediateF n1 v1 m1 f1, IntermediateF n2 v2 m2 f2 =>
            ParameterisedIntermediateName.compare (n1, (v1, (m1, f1)))
              (n2, (v2, (m2, f2)))
        | IntermediateF _ _ _ _, IntermediateA _ _ _ _ _ => Lt
        | IntermediateF _ _ _ _, _ => Gt
        | IntermediateA n1 v1 f1 m1 g1, IntermediateA n2 v2 f2 m2 g2 =>
            AdditionalIntermediateName.compare (n1, (v1, (f1, (m1, g1))))
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

    Module Reduced := Core NameOT V.

    Definition granularOf (g : V.t -> G.t)
        (q : Feature.Reduction.Reduced.Package.t)
        : Reduced.Package.t :=
      match q with
      | (Feature.Reduction.Name.Orig n, v) =>
          (Name.GranularOrig n (g v), v)
      | (Feature.Reduction.Name.FeatPkg n f, v) =>
          (Name.GranularFeatPkg n f (g v), v)
      end.

    Definition embedOrigPkg (g : V.t -> G.t) (p : Package.t) :
        Reduced.Package.t :=
      let '(n, v) := p in (Name.GranularOrig n (g v), v).

    Definition singVS (v : V.t) : Reduced.VSet.t := Reduced.VSet.singleton v.

    Module SOvv := SetOps V V VSet Reduced.VSet.
    Definition embedVS (vs : VSet.t) : Reduced.VSet.t :=
      SOvv.map (fun v => v) vs.

    Module SOqp :=
      SetOps Feature.Reduction.Reduced.Package Reduced.Package
        Feature.Reduction.Reduced.PackageSet Reduced.PackageSet.
    Definition granularReal (R : PackageSet.t) (support : Feature.SupportRel.t)
        (g : V.t -> G.t) : Reduced.PackageSet.t :=
      SOqp.map (granularOf g) (Feature.Reduction.reduceReal R support).

    Module SOvp := SetOps V Reduced.Package VSet Reduced.PackageSet.
    Module SOfp :=
      SetOps Feature.ParameterisedDependencyElt Reduced.Package
      Feature.ParameterisedDependencyRel Reduced.PackageSet.
    Definition fInterReal (Df : Feature.ParameterisedDependencyRel.t) :
        Reduced.PackageSet.t :=
      SOfp.unionMap (fun '((n, v), (m, (vs, _))) =>
          SOvp.map (fun u => (Name.Intermediate n v m, u)) vs)
        Df.

    Module SOfsp := SetOps F Reduced.Package Feature.FSet Reduced.PackageSet.
    Definition fInterFeatReal (Df : Feature.ParameterisedDependencyRel.t) :
        Reduced.PackageSet.t :=
      SOfp.unionMap (fun '((n, v), (m, (vs, fs))) =>
          SOvp.unionMap (fun u =>
              SOfsp.map (fun f => (Name.IntermediateF n v m f, u)) fs)
            vs)
        Df.

    Module SOap :=
      SetOps Feature.AdditionalDependencyElt Reduced.Package
      Feature.AdditionalDependencyRel Reduced.PackageSet.
    Definition aInterReal (Da : Feature.AdditionalDependencyRel.t) :
        Reduced.PackageSet.t :=
      SOap.unionMap (fun '(((n, v), _), (m, (vs, _))) =>
          SOvp.map (fun u => (Name.Intermediate n v m, u)) vs)
        Da.

    Definition aInterFeatReal (Da : Feature.AdditionalDependencyRel.t) :
        Reduced.PackageSet.t :=
      SOap.unionMap (fun '(((n, v), f), (m, (vs, fs))) =>
          SOvp.unionMap (fun u =>
              SOfsp.map (fun f' => (Name.IntermediateA n v f m f', u)) fs)
            vs)
        Da.

    Definition reduceReal
        (R : PackageSet.t) (support : Feature.SupportRel.t)
        (Df : Feature.ParameterisedDependencyRel.t)
          (Da : Feature.AdditionalDependencyRel.t)
        (g : V.t -> G.t) : Reduced.PackageSet.t :=
      Reduced.PackageSet.union (granularReal R support g)
        (Reduced.PackageSet.union (fInterReal Df)
           (Reduced.PackageSet.union (fInterFeatReal Df)
              (Reduced.PackageSet.union (aInterReal Da) (aInterFeatReal Da)))).

    Module SOsd :=
      SetOps Feature.PackageF Reduced.DependencyElt Feature.SupportRel
      Reduced.DependencyRel.
    Definition supportEdges (R : PackageSet.t) (support : Feature.SupportRel.t)
        (g : V.t -> G.t) : Reduced.DependencyRel.t :=
      SOsd.filterMap (fun '((n, v), f) =>
          if PackageSet.mem (n, v) R
          then Some ((Name.GranularFeatPkg n f (g v), v),
                     (Name.GranularOrig n (g v), singVS v))
          else None)
        support.

    Module SOfd :=
      SetOps Feature.ParameterisedDependencyElt Reduced.DependencyElt
      Feature.ParameterisedDependencyRel Reduced.DependencyRel.
    Definition fDepToInterEdges (Df : Feature.ParameterisedDependencyRel.t)
        (g : V.t -> G.t) : Reduced.DependencyRel.t :=
      SOfd.map (fun '((n, v), (m, (vs, _))) =>
          ((Name.GranularOrig n (g v), v),
           (Name.Intermediate n v m, embedVS vs)))
        Df.

    Module SOvd := SetOps V Reduced.DependencyElt VSet Reduced.DependencyRel.
    Definition fInterToOrigEdges (Df : Feature.ParameterisedDependencyRel.t)
        (g : V.t -> G.t) : Reduced.DependencyRel.t :=
      SOfd.unionMap (fun '((n, v), (m, (vs, _))) =>
          SOvd.map (fun u =>
              ((Name.Intermediate n v m, u),
               (Name.GranularOrig m (g u), singVS u)))
            vs)
        Df.

    Module SOfsd :=
      SetOps F Reduced.DependencyElt Feature.FSet Reduced.DependencyRel.
    Definition fDepToInterFeatEdges (Df : Feature.ParameterisedDependencyRel.t)
        (g : V.t -> G.t) : Reduced.DependencyRel.t :=
      SOfd.unionMap (fun '((n, v), (m, (vs, fs))) =>
          SOfsd.map (fun f =>
              ((Name.GranularOrig n (g v), v),
               (Name.IntermediateF n v m f, embedVS vs)))
            fs)
        Df.

    Definition fInterToFeatEdges (Df : Feature.ParameterisedDependencyRel.t)
        (g : V.t -> G.t) : Reduced.DependencyRel.t :=
      SOfd.unionMap (fun '((n, v), (m, (vs, fs))) =>
          SOvd.unionMap (fun u =>
              SOfsd.map (fun f =>
                  ((Name.IntermediateF n v m f, u),
                   (Name.GranularFeatPkg m f (g u), singVS u)))
                fs)
            vs)
        Df.

    Definition fInterFeatToInterEdges
        (Df : Feature.ParameterisedDependencyRel.t) : Reduced.DependencyRel.t :=
      SOfd.unionMap (fun '((n, v), (m, (vs, fs))) =>
          SOfsd.unionMap (fun f =>
              SOvd.map (fun u =>
                  ((Name.IntermediateF n v m f, u),
                   (Name.Intermediate n v m, singVS u)))
                vs)
            fs)
        Df.

    Module SOad :=
      SetOps Feature.AdditionalDependencyElt Reduced.DependencyElt
      Feature.AdditionalDependencyRel Reduced.DependencyRel.
    Definition aDepToInterEdges (Da : Feature.AdditionalDependencyRel.t)
        (g : V.t -> G.t) : Reduced.DependencyRel.t :=
      SOad.map (fun '(((n, v), f), (m, (vs, _))) =>
          ((Name.GranularFeatPkg n f (g v), v),
           (Name.Intermediate n v m, embedVS vs)))
        Da.

    Definition aInterToOrigEdges (Da : Feature.AdditionalDependencyRel.t)
        (g : V.t -> G.t) : Reduced.DependencyRel.t :=
      SOad.unionMap (fun '(((n, v), _), (m, (vs, _))) =>
          SOvd.map (fun u =>
              ((Name.Intermediate n v m, u),
               (Name.GranularOrig m (g u), singVS u)))
            vs)
        Da.

    Definition aDepToInterFeatEdges (Da : Feature.AdditionalDependencyRel.t)
        (g : V.t -> G.t) : Reduced.DependencyRel.t :=
      SOad.unionMap (fun '(((n, v), f), (m, (vs, fs))) =>
          SOfsd.map (fun f' =>
              ((Name.GranularFeatPkg n f (g v), v),
               (Name.IntermediateA n v f m f', embedVS vs)))
            fs)
        Da.

    Definition aInterToFeatEdges (Da : Feature.AdditionalDependencyRel.t)
        (g : V.t -> G.t) : Reduced.DependencyRel.t :=
      SOad.unionMap (fun '(((n, v), f), (m, (vs, fs))) =>
          SOvd.unionMap (fun u =>
              SOfsd.map (fun f' =>
                  ((Name.IntermediateA n v f m f', u),
                   (Name.GranularFeatPkg m f' (g u), singVS u)))
                fs)
            vs)
        Da.

    Definition aInterFeatToInterEdges (Da : Feature.AdditionalDependencyRel.t) :
        Reduced.DependencyRel.t :=
      SOad.unionMap (fun '(((n, v), f), (m, (vs, fs))) =>
          SOfsd.unionMap (fun f' =>
              SOvd.map (fun u =>
                  ((Name.IntermediateA n v f m f', u),
                   (Name.Intermediate n v m, singVS u)))
                vs)
            fs)
        Da.

    Definition reduceDeps
        (R : PackageSet.t) (support : Feature.SupportRel.t)
        (Df : Feature.ParameterisedDependencyRel.t)
          (Da : Feature.AdditionalDependencyRel.t)
        (g : V.t -> G.t) : Reduced.DependencyRel.t :=
      Reduced.DependencyRel.union (supportEdges R support g)
        (Reduced.DependencyRel.union (fDepToInterEdges Df g)
           (Reduced.DependencyRel.union (fInterToOrigEdges Df g)
              (Reduced.DependencyRel.union (fDepToInterFeatEdges Df g)
                 (Reduced.DependencyRel.union (fInterToFeatEdges Df g)
                    (Reduced.DependencyRel.union (fInterFeatToInterEdges Df)
                       (Reduced.DependencyRel.union (aDepToInterEdges Da g)
                          (Reduced.DependencyRel.union (aInterToOrigEdges Da g)
                             (Reduced.DependencyRel.union
                               (aDepToInterFeatEdges Da g)
                                (Reduced.DependencyRel.union
                                  (aInterToFeatEdges Da g)
                                   (aInterFeatToInterEdges Da)))))))))).

    Lemma mem_embedVS : forall vs v, Reduced.VSet.In v (embedVS vs) <->
        VSet.In v vs.
    Proof.
      intros vs v; unfold embedVS.
      exact (SOvv.mem_map_inj (fun u => u) vs v (fun x y H => H)).
    Qed.

    Lemma mem_singVS : forall v u, Reduced.VSet.In u (singVS v) <-> u = v.
    Proof. intros v u; exact (SOvv.singleton_in v u). Qed.

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
          | Feature.Reduction.Name.name => destruct x
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
            | H : PackageSet.mem _ _ = true |- _ =>
                apply PackageSet.mem_spec in H
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
          | |- context [PackageSet.mem ?x ?s] =>
              replace (PackageSet.mem x s) with true
                by (symmetry; apply PackageSet.mem_spec; assumption)
          end
        | eexists; split; [eassumption |] ].

    Ltac pick_close :=
      first [ solve [mem_close] | left; solve [mem_close]
            | right; pick_close ].

    Inductive RealMember (R : PackageSet.t) (support : Feature.SupportRel.t)
        (Df : Feature.ParameterisedDependencyRel.t)
          (Da : Feature.AdditionalDependencyRel.t) (g : V.t -> G.t) :
        Reduced.Package.t -> Prop :=
    | RealOrig : forall n v,
        Feature.Reduction.Reduced.PackageSet.In
          (Feature.Reduction.Name.Orig n, v)
          (Feature.Reduction.reduceReal R support) ->
        RealMember R support Df Da g (Name.GranularOrig n (g v), v)
    | RealFeatPkg : forall n f v,
        Feature.Reduction.Reduced.PackageSet.In
          (Feature.Reduction.Name.FeatPkg n f, v)
          (Feature.Reduction.reduceReal R support) ->
        RealMember R support Df Da g (Name.GranularFeatPkg n f (g v), v)
    | RealFInter : forall n v m vs fs u,
        Feature.ParameterisedDependencyRel.In ((n, v), (m, (vs, fs))) Df ->
          VSet.In u vs ->
        RealMember R support Df Da g (Name.Intermediate n v m, u)
    | RealFInterF : forall n v m vs fs u f,
        Feature.ParameterisedDependencyRel.In ((n, v), (m, (vs, fs))) Df ->
          VSet.In u vs ->
        Feature.FSet.In f fs ->
        RealMember R support Df Da g (Name.IntermediateF n v m f, u)
    | RealAInter : forall n v f m vs fs u,
        Feature.AdditionalDependencyRel.In (((n, v), f), (m, (vs, fs))) Da ->
          VSet.In u vs ->
        RealMember R support Df Da g (Name.Intermediate n v m, u)
    | RealAInterA : forall n v f m vs fs u f',
        Feature.AdditionalDependencyRel.In (((n, v), f), (m, (vs, fs))) Da ->
          VSet.In u vs ->
        Feature.FSet.In f' fs ->
        RealMember R support Df Da g (Name.IntermediateA n v f m f', u).
    #[local] Hint Constructors RealMember : fc_mem.

    Lemma mem_reduceReal : forall R support Df Da g (p : Reduced.Package.t),
        Reduced.PackageSet.In p (reduceReal R support Df Da g) <->
        RealMember R support Df Da g p.
    Proof.
      intros R support Df Da g p; unfold reduceReal, granularReal,
        fInterReal, fInterFeatReal, aInterReal, aInterFeatReal.
      rewrite !Reduced.PackageSet.union_spec, SOqp.mem_map, !SOfp.mem_unionMap,
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
    Inductive EncodedEdge (R : PackageSet.t) (support : Feature.SupportRel.t)
        (Df : Feature.ParameterisedDependencyRel.t)
          (Da : Feature.AdditionalDependencyRel.t) (g : V.t -> G.t) :
        Reduced.DependencyElt.t -> Prop :=
    | EdgeSupport : forall n v f,
        Feature.SupportRel.In ((n, v), f) support -> PackageSet.In (n, v) R ->
        EncodedEdge R support Df Da g
          ((Name.GranularFeatPkg n f (g v), v),
           (Name.GranularOrig n (g v), singVS v))
    | EdgeFDepToInter : forall n v m vs fs,
        Feature.ParameterisedDependencyRel.In ((n, v), (m, (vs, fs))) Df ->
        EncodedEdge R support Df Da g
          ((Name.GranularOrig n (g v), v),
           (Name.Intermediate n v m, embedVS vs))
    | EdgeFInterToOrig : forall n v m vs fs u,
        Feature.ParameterisedDependencyRel.In ((n, v), (m, (vs, fs))) Df ->
          VSet.In u vs ->
        EncodedEdge R support Df Da g
          ((Name.Intermediate n v m, u),
           (Name.GranularOrig m (g u), singVS u))
    | EdgeFDepToInterFeat : forall n v m vs fs f,
        Feature.ParameterisedDependencyRel.In ((n, v), (m, (vs, fs))) Df ->
          Feature.FSet.In f fs ->
        EncodedEdge R support Df Da g
          ((Name.GranularOrig n (g v), v),
           (Name.IntermediateF n v m f, embedVS vs))
    | EdgeFInterToFeat : forall n v m vs fs u f,
        Feature.ParameterisedDependencyRel.In ((n, v), (m, (vs, fs))) Df ->
          VSet.In u vs ->
        Feature.FSet.In f fs ->
        EncodedEdge R support Df Da g
          ((Name.IntermediateF n v m f, u),
           (Name.GranularFeatPkg m f (g u), singVS u))
    | EdgeFInterFeatToInter : forall n v m vs fs f u,
        Feature.ParameterisedDependencyRel.In ((n, v), (m, (vs, fs))) Df ->
          Feature.FSet.In f fs ->
        VSet.In u vs ->
        EncodedEdge R support Df Da g
          ((Name.IntermediateF n v m f, u),
           (Name.Intermediate n v m, singVS u))
    | EdgeADepToInter : forall n v f m vs fs,
        Feature.AdditionalDependencyRel.In (((n, v), f), (m, (vs, fs))) Da ->
        EncodedEdge R support Df Da g
          ((Name.GranularFeatPkg n f (g v), v),
           (Name.Intermediate n v m, embedVS vs))
    | EdgeAInterToOrig : forall n v f m vs fs u,
        Feature.AdditionalDependencyRel.In (((n, v), f), (m, (vs, fs))) Da ->
          VSet.In u vs ->
        EncodedEdge R support Df Da g
          ((Name.Intermediate n v m, u),
           (Name.GranularOrig m (g u), singVS u))
    | EdgeADepToInterFeat : forall n v f m vs fs f',
        Feature.AdditionalDependencyRel.In (((n, v), f), (m, (vs, fs))) Da ->
        Feature.FSet.In f' fs ->
        EncodedEdge R support Df Da g
          ((Name.GranularFeatPkg n f (g v), v),
           (Name.IntermediateA n v f m f', embedVS vs))
    | EdgeAInterToFeat : forall n v f m vs fs u f',
        Feature.AdditionalDependencyRel.In (((n, v), f), (m, (vs, fs))) Da ->
          VSet.In u vs ->
        Feature.FSet.In f' fs ->
        EncodedEdge R support Df Da g
          ((Name.IntermediateA n v f m f', u),
           (Name.GranularFeatPkg m f' (g u), singVS u))
    | EdgeAInterFeatToInter : forall n v f m vs fs f' u,
        Feature.AdditionalDependencyRel.In (((n, v), f), (m, (vs, fs))) Da ->
        Feature.FSet.In f' fs -> VSet.In u vs ->
        EncodedEdge R support Df Da g
          ((Name.IntermediateA n v f m f', u),
           (Name.Intermediate n v m, singVS u)).
    #[local] Hint Constructors EncodedEdge : fc_mem.

    Lemma mem_reduceDeps :
        forall R support Df Da g (y : Reduced.DependencyElt.t),
        Reduced.DependencyRel.In y (reduceDeps R support Df Da g) <->
        EncodedEdge R support Df Da g y.
    Proof.
      intros R support Df Da g y; unfold reduceDeps, supportEdges,
        fDepToInterEdges, fInterToOrigEdges, fDepToInterFeatEdges,
        fInterToFeatEdges, fInterFeatToInterEdges, aDepToInterEdges,
        aInterToOrigEdges, aDepToInterFeatEdges, aInterToFeatEdges,
        aInterFeatToInterEdges.
      rewrite !Reduced.DependencyRel.union_spec, SOsd.mem_filterMap,
        SOfd.mem_map,
        !SOfd.mem_unionMap, SOad.mem_map, !SOad.mem_unionMap.
      split.
      - intro H;
          repeat match goal with H : _ \/ _ |- _ => destruct H as [H | H] end;
          mem_open; eauto with fc_mem.
      - destruct 1; pick_close.
    Qed.

    Module SOtf := SetOps Reduced.Package F Reduced.PackageSet Feature.FSet.
    (* As in Feature: decode by scanning the resolution, so nothing here needs
       the feature universe to be enumerable. *)
    Definition featsOf (g : V.t -> G.t) (n : N.t) (v : V.t)
        (S : Reduced.PackageSet.t) : Feature.FSet.t :=
      SOtf.filterMap (fun q =>
          match q with
          | (Name.GranularFeatPkg n' f w, v') =>
              if Reduced.Package.eq_dec (Name.GranularFeatPkg n' f w, v')
                   (Name.GranularFeatPkg n f (g v), v)
              then Some f
              else None
          | _ => None
          end)
        S.

    Module SOts :=
      SetOps Reduced.Package Feature.Featured Reduced.PackageSet
      Feature.FeaturedSet.
    Definition concurrentFeatureResolution (g : V.t -> G.t)
        (S : Reduced.PackageSet.t) : Feature.FeaturedSet.t :=
      SOts.filterMap (fun p' =>
          match p' with
          | (Name.GranularOrig n w, v) =>
              if G.eq_dec w (g v) then Some ((n, v), featsOf g n v S) else None
          | _ => None
          end)
        S.

    Module SOvpp := SetOps V ParentElt VSet ParentRel.
    Definition parentsOf (S : Reduced.PackageSet.t) (n : N.t)
        (v : V.t) (m : N.t)
        (vs : VSet.t) : ParentRel.t :=
      SOvpp.filterMap (fun u =>
          if Reduced.PackageSet.mem (Name.Intermediate n v m, u) S
          then Some ((m, u), (n, v))
          else None)
        vs.

    Module SOfpp :=
      SetOps Feature.ParameterisedDependencyElt ParentElt
      Feature.ParameterisedDependencyRel ParentRel.
    Module SOapp :=
      SetOps Feature.AdditionalDependencyElt ParentElt
      Feature.AdditionalDependencyRel ParentRel.
    Definition parents (Df : Feature.ParameterisedDependencyRel.t)
        (Da : Feature.AdditionalDependencyRel.t)
        (g : V.t -> G.t) (S : Reduced.PackageSet.t) : ParentRel.t :=
      ParentRel.union
        (SOfpp.unionMap (fun '((n, v), (m, (vs, _))) =>
             if Reduced.PackageSet.mem (Name.GranularOrig n (g v), v) S
             then parentsOf S n v m vs
             else ParentRel.empty)
           Df)
        (SOapp.unionMap (fun '(((n, v), f), (m, (vs, _))) =>
             if Reduced.PackageSet.mem (Name.GranularFeatPkg n f (g v), v) S
             then parentsOf S n v m vs
             else ParentRel.empty)
           Da).

    Lemma featsOf_spec : forall g n v S f,
        Feature.FSet.In f (featsOf g n v S) <->
        Reduced.PackageSet.In (Name.GranularFeatPkg n f (g v), v) S.
    Proof.
      intros g n v S f; unfold featsOf; rewrite SOtf.mem_filterMap.
      split.
      - intros [[[n' w | n' f' w | n' v' m | n' v' m f' | n' v' f' m f''] u]
                 [HS He]]; cbn beta iota in He; try discriminate.
        destruct (Reduced.Package.eq_dec (Name.GranularFeatPkg n' f' w, u)
                    (Name.GranularFeatPkg n f' (g v), v)) as [E | NE];
          [| discriminate].
        injection He as <-; rewrite <- E; exact HS.
      - intro HS; exists (Name.GranularFeatPkg n f (g v), v);
          split; [exact HS | cbn beta iota; apply dec_refl].
    Qed.

    Lemma mem_concurrentFeatureResolution :
      forall g (S : Reduced.PackageSet.t) n v fs,
        Feature.FeaturedSet.In ((n, v), fs)
          (concurrentFeatureResolution g S) <->
        Reduced.PackageSet.In (Name.GranularOrig n (g v), v) S /\ fs =
          featsOf g n v S.
    Proof.
      intros g S n v fs; unfold concurrentFeatureResolution;
        rewrite SOts.mem_filterMap.
      split.
      - intros [[[n0 w | n0 f w | n0 v1 m | n0 v1 m f | n0 v1 f m f'] v0]
                  [HeS Hy]];
          cbn beta iota in Hy; try discriminate.
        destruct (G.eq_dec w (g v0)) as [-> | NE]; [| discriminate].
        injection Hy as <- <- <-; split; [exact HeS | reflexivity].
      - intros [HS ->].
        exists (Name.GranularOrig n (g v), v);
          split; [exact HS | cbn beta iota; apply dec_refl].
    Qed.

    Lemma mem_parentsOf : forall S n v m vs m' u n' v',
        ParentRel.In ((m', u), (n', v')) (parentsOf S n v m vs) <->
        VSet.In u vs /\ Reduced.PackageSet.In (Name.Intermediate n v m, u) S /\
        m' = m /\ n' = n /\ v' = v.
    Proof.
      intros S n v m vs m' u n' v'; unfold parentsOf.
      rewrite SOvpp.mem_filterMap_if;
        setoid_rewrite Reduced.PackageSet.mem_spec; split.
      - intros (u' & Hu & Hi & E); injection E as -> -> -> ->; auto.
      - intros (Hu & Hi & -> & -> & ->); exists u; auto.
    Qed.

    Lemma mem_parents : forall Df Da g (S : Reduced.PackageSet.t) m u n v,
        ParentRel.In ((m, u), (n, v)) (parents Df Da g S) <->
        Reduced.PackageSet.In (Name.Intermediate n v m, u) S /\
        ((exists vs fs,
          Feature.ParameterisedDependencyRel.In ((n, v), (m, (vs, fs))) Df /\
            VSet.In u vs /\
              Reduced.PackageSet.In (Name.GranularOrig n (g v), v) S) \/
         (exists f vs fs,
           Feature.AdditionalDependencyRel.In (((n, v), f), (m, (vs, fs))) Da /\
            VSet.In u vs /\
            Reduced.PackageSet.In (Name.GranularFeatPkg n f (g v), v) S)).
    Proof.
      intros Df Da g S m u n v; unfold parents.
      rewrite ParentRel.union_spec, SOfpp.mem_unionMap, SOapp.mem_unionMap.
      split.
      - intros [([[n' v'] [m' [vs fs]]] & HD & Hh)
               | ([[[n' v'] f] [m' [vs fs]]] & HA & Hh)];
          cbn beta iota in Hh; apply SOvpp.in_if_empty in Hh;
          rewrite Reduced.PackageSet.mem_spec, mem_parentsOf in Hh;
          destruct Hh as (Hs & Hu & Hi & -> & -> & ->);
          (split; [exact Hi |]);
          [left; exists vs, fs | right; exists f, vs, fs]; auto.
      - intros [Hi [(vs & fs & HD & Hu & Hs) | (f & vs & fs & HA & Hu & Hs)]];
          [left; exists ((n, v), (m, (vs, fs)))
          | right; exists (((n, v), f), (m, (vs, fs)))];
          (split; [assumption | cbn beta iota]);
          apply SOvpp.in_if_empty;
            rewrite Reduced.PackageSet.mem_spec, mem_parentsOf;
          repeat split; assumption.
    Qed.

    Lemma parent_closure_step :
      forall RR D r g S P (q : Reduced.Package.t) n v m vs fs
        (iF : F.t -> Name.t),
        Reduced.IsResolution RR D r S -> Reduced.PackageSet.In q S ->
        (forall u, VSet.In u vs ->
           Reduced.PackageSet.In (Name.Intermediate n v m, u) S ->
           ParentRel.In ((m, u), (n, v)) P) ->
        Reduced.DependencyRel.In (q, (Name.Intermediate n v m, embedVS vs)) D ->
        (forall u, VSet.In u vs ->
           Reduced.DependencyRel.In ((Name.Intermediate n v m, u),
                        (Name.GranularOrig m (g u), singVS u)) D) ->
        (forall f, Feature.FSet.In f fs ->
           Reduced.DependencyRel.In (q, (iF f, embedVS vs)) D) ->
        (forall f u, Feature.FSet.In f fs -> VSet.In u vs ->
           Reduced.DependencyRel.In
             ((iF f, u), (Name.Intermediate n v m, singVS u)) D) ->
        (forall f u, Feature.FSet.In f fs -> VSet.In u vs ->
           Reduced.DependencyRel.In ((iF f, u),
                        (Name.GranularFeatPkg m f (g u), singVS u)) D) ->
        exists u, VSet.In u vs /\
          (exists fs', Feature.FSet.Subset fs fs' /\
             Feature.FeaturedSet.In ((m, u), fs')
               (concurrentFeatureResolution g S)) /\
          ParentRel.In ((m, u), (n, v)) P.
    Proof.
      intros RR D r g S P q n v m vs fs iF [_ _ Hdep Huniq] HqS Hin Hd
        Hto Hfd Hback Hfwd.
      destruct (Hdep _ HqS _ _ Hd) as [u [Hu HiS]]; rewrite mem_embedVS in Hu.
      destruct (Hdep _ HiS _ _ (Hto u Hu)) as [w [Hw HoS]].
      apply mem_singVS in Hw; subst w.
      exists u; split; [exact Hu | split].
      - exists (featsOf g m u S); split.
        + intros f Hf; apply featsOf_spec.
          destruct (Hdep _ HqS _ _ (Hfd f Hf)) as [u1 [Hu1 HfS]].
          rewrite mem_embedVS in Hu1.
          destruct (Hdep _ HfS _ _ (Hback f u1 Hf Hu1)) as [w [Hw Hi1S]].
          apply mem_singVS in Hw; subst w.
          assert (u1 = u) as -> by exact (Huniq _ _ _ Hi1S HiS).
          destruct (Hdep _ HfS _ _ (Hfwd f u Hf Hu)) as [w [Hw HgS]].
          apply mem_singVS in Hw; subst w; exact HgS.
        + apply mem_concurrentFeatureResolution;
            split; [exact HoS | reflexivity].
      - exact (Hin u Hu HiS).
    Qed.

    Theorem concurrent_feature_soundness :
      forall (R : PackageSet.t) (support : Feature.SupportRel.t)
             (Df : Feature.ParameterisedDependencyRel.t)
               (Da : Feature.AdditionalDependencyRel.t)
             (g : V.t -> G.t) (r : Package.t) (S : Reduced.PackageSet.t),
        (forall f, ~ Feature.SupportRel.In (r, f) support) ->
        Reduced.IsResolution (reduceReal R support Df Da g)
          (reduceDeps R support Df Da g)
          (embedOrigPkg g r) S ->
        IsResolution R support Df Da g r
          (concurrentFeatureResolution g S) (parents Df Da g S).
    Proof.
      intros R support Df Da g r S Hnosupp Hres.
      pose proof Hres as [Hsub Hroot Hdep Huniq].
      destruct r as [rn rv].
      unfold embedOrigPkg in Hroot; simpl in Hroot.
      assert (HorigR : forall n v,
                 Reduced.PackageSet.In (Name.GranularOrig n (g v), v) S ->
                 PackageSet.In (n, v) R).
      { intros n v HS; pose proof (Hsub _ HS) as HF.
        apply mem_reduceReal in HF; inversion HF; subst.
        eapply Feature.Reduction.mem_reduceReal_orig; eassumption. }
      assert (HfeatSup : forall n f v,
                 Reduced.PackageSet.In
                   (Name.GranularFeatPkg n f (g v), v) S ->
                 Feature.SupportRel.In ((n, v), f) support /\
                   PackageSet.In (n, v) R).
      { intros n f v HS; pose proof (Hsub _ HS) as HF.
        apply mem_reduceReal in HF; inversion HF; subst.
        eapply Feature.Reduction.mem_reduceReal_featPkg; eassumption. }
      constructor.
      - intros [n v] fs Hmem.
        rewrite mem_concurrentFeatureResolution in Hmem.
        destruct Hmem as [HS _].
        exact (HorigR n v HS).
      - assert (Hfe : featsOf g rn rv S = Feature.FSet.empty).
        { apply Feature.FSet.ext; intro f; rewrite featsOf_spec; split; intro H.
          - exfalso; exact (Hnosupp f (proj1 (HfeatSup rn f rv H))).
          - exfalso; exact (Feature.FSet.empty_spec H). }
        rewrite <- Hfe.
        rewrite mem_concurrentFeatureResolution; split;
          [exact Hroot | reflexivity].
      - split.
        + intros [n v] fs_p Hmem m vs fs Hdf.
          rewrite mem_concurrentFeatureResolution in Hmem.
          destruct Hmem as [HpS ->].
          apply (parent_closure_step _ _ _ g S _ _ n v m vs fs
                   (Name.IntermediateF n v m) Hres HpS
                   (fun u Hu Hi => proj2 (mem_parents Df Da g S m u n v)
                      (conj Hi (or_introl (ex_intro _ vs (ex_intro _ fs
                         (conj Hdf (conj Hu HpS))))))));
            intros; apply mem_reduceDeps;
            [eapply EdgeFDepToInter | eapply EdgeFInterToOrig
            | eapply EdgeFDepToInterFeat | eapply EdgeFInterFeatToInter
            | eapply EdgeFInterToFeat]; eassumption.
        + intros [n v] fs_p Hmem f Hf m vs fs Hda.
          rewrite mem_concurrentFeatureResolution in Hmem.
          destruct Hmem as [HpS ->].
          rewrite featsOf_spec in Hf.
          apply (parent_closure_step _ _ _ g S _ _ n v m vs fs
                   (Name.IntermediateA n v f m) Hres Hf
                   (fun u Hu Hi => proj2 (mem_parents Df Da g S m u n v)
                      (conj Hi (or_intror (ex_intro _ f (ex_intro _ vs
                         (ex_intro _ fs (conj Hda (conj Hu Hf)))))))));
            intros; apply mem_reduceDeps;
            [eapply EdgeADepToInter | eapply EdgeAInterToOrig
            | eapply EdgeADepToInterFeat | eapply EdgeAInterFeatToInter
            | eapply EdgeAInterToFeat]; eassumption.
      - intros m u u' p H1 H2.
        destruct p as [pn pv].
        apply mem_parents in H1, H2.
        exact (Huniq (Name.Intermediate pn pv m) _ _ (proj1 H1) (proj1 H2)).
      - intros n v v' fs fs' H1 H2 Hne Hg.
        rewrite mem_concurrentFeatureResolution in H1, H2.
        destruct H1 as [HS1 _]; destruct H2 as [HS2 _].
        rewrite Hg in HS1.
        assert (E : v = v')
          by exact (Huniq (Name.GranularOrig n (g v')) _ _ HS1 HS2).
        exact (Hne E).
      - intros n v fs fs' H1 H2.
        rewrite mem_concurrentFeatureResolution in H1, H2.
        destruct H1 as [HS1 ->]; destruct H2 as [HS2 ->].
        reflexivity.
      - intros [n v] fs f Hmem Hf.
        rewrite mem_concurrentFeatureResolution in Hmem.
        destruct Hmem as [HS1 ->].
        rewrite featsOf_spec in Hf.
        exact (proj1 (HfeatSup n f v Hf)).
      - intros [m u] [n v] Hpi; apply mem_parents in Hpi.
        assert (Hin : forall n' v',
                  Reduced.PackageSet.In (Name.GranularOrig n' (g v'), v') S ->
                  exists fs, Feature.FeaturedSet.In ((n', v'), fs)
                               (concurrentFeatureResolution g S))
          by (intros n' v' HS; exists (featsOf g n' v' S);
              apply mem_concurrentFeatureResolution; auto).
        destruct Hpi as [Hi [(vs & fs & HD & Hu & Hp)
                             | (f & vs & fs & HA & Hu & Hf)]];
          split; apply Hin.
        + destruct (Hdep _ Hi _ _ (proj2 (mem_reduceDeps _ _ _ _ _ _)
                     (EdgeFInterToOrig _ _ _ _ _ n v m vs fs u HD Hu)))
            as [w [Hw HwS]].
          apply mem_singVS in Hw; subst w; exact HwS.
        + exact Hp.
        + destruct (Hdep _ Hi _ _ (proj2 (mem_reduceDeps _ _ _ _ _ _)
                     (EdgeAInterToOrig _ _ _ _ _ n v f m vs fs u HA Hu)))
            as [w [Hw HwS]].
          apply mem_singVS in Hw; subst w; exact HwS.
        + destruct (HfeatSup _ _ _ Hf) as [Hs HR].
          destruct (Hdep _ Hf _ _ (proj2 (mem_reduceDeps _ _ _ _ _ _)
                     (EdgeSupport _ _ _ _ _ n v f Hs HR)))
            as [w [Hw HwS]].
          apply mem_singVS in Hw; subst w; exact HwS.
    Qed.

    Module PackageEqb := UOTEqb Package.

    Definition inSb (S_CF : Feature.FeaturedSet.t) (p : Package.t) : bool :=
      Feature.FeaturedSet.exists_ (fun '(q, _) => PackageEqb.eqb q p) S_CF.

    Definition takenWithb
        (S_CF : Feature.FeaturedSet.t) (fs : Feature.FSet.t)
          (q : Package.t) : bool :=
      Feature.FeaturedSet.exists_ (fun '(q', fs') =>
          andb (PackageEqb.eqb q' q) (Feature.FSet.subset fs fs'))
        S_CF.

    Definition activeb (S_CF : Feature.FeaturedSet.t) (pi : ParentRel.t)
        (p : Package.t) (fs : Feature.FSet.t) (m : N.t) (u : V.t) : bool :=
      andb (inSb S_CF p)
        (andb (takenWithb S_CF fs (m, u)) (ParentRel.mem ((m, u), p) pi)).

    Module SOsw :=
      SetOps Feature.Featured Reduced.Package Feature.FeaturedSet
      Reduced.PackageSet.
    Definition coreResolution (Df : Feature.ParameterisedDependencyRel.t)
        (Da : Feature.AdditionalDependencyRel.t)
        (g : V.t -> G.t) (S_CF : Feature.FeaturedSet.t) (pi : ParentRel.t) :
        Reduced.PackageSet.t :=
      Reduced.PackageSet.union
        (SOsw.map (fun '((n, v), _) => (Name.GranularOrig n (g v), v)) S_CF)
        (Reduced.PackageSet.union
           (SOsw.unionMap (fun '((n, v), fs) =>
                SOfsp.map (fun f => (Name.GranularFeatPkg n f (g v), v)) fs)
              S_CF)
           (Reduced.PackageSet.union
              (SOfp.unionMap (fun '((n, v), (m, (vs, fs))) =>
                   SOvp.filterMap (fun u =>
                       if activeb S_CF pi (n, v) fs m u
                       then Some (Name.Intermediate n v m, u)
                       else None)
                     vs)
                 Df)
              (Reduced.PackageSet.union
                 (SOap.unionMap (fun '(((n, v), _), (m, (vs, fs))) =>
                      SOvp.filterMap (fun u =>
                          if activeb S_CF pi (n, v) fs m u
                          then Some (Name.Intermediate n v m, u)
                          else None)
                        vs)
                    Da)
                 (Reduced.PackageSet.union
                    (SOfp.unionMap (fun '((n, v), (m, (vs, fs))) =>
                         SOfsp.unionMap (fun f =>
                             SOvp.filterMap (fun u =>
                                 if activeb S_CF pi (n, v) fs m u
                                 then Some (Name.IntermediateF n v m f, u)
                                 else None)
                               vs)
                           fs)
                       Df)
                    (SOap.unionMap (fun '(((n, v), f), (m, (vs, fs))) =>
                         SOfsp.unionMap (fun f' =>
                             SOvp.filterMap (fun u =>
                                 if activeb S_CF pi (n, v) fs m u
                                 then Some (Name.IntermediateA n v f m f', u)
                                 else None)
                               vs)
                           fs)
                       Da))))).

    Lemma inSb_iff : forall S_CF p,
        inSb S_CF p = true <-> exists fs_p,
          Feature.FeaturedSet.In (p, fs_p) S_CF.
    Proof.
      intros S_CF p; unfold inSb.
      rewrite Feature.FeaturedSet.exists_spec'.
      unfold Feature.FeaturedSet.Exists; split.
      - intros [[q fsq] [Hq Hb]]; cbn beta iota in Hb.
        apply PackageEqb.eqb_true_iff in Hb as ->; exists fsq; exact Hq.
      - intros [fs_p H]; exists (p, fs_p); split;
          [exact H | apply PackageEqb.eqb_refl].
    Qed.

    Lemma takenWithb_iff : forall S_CF fs q,
        takenWithb S_CF fs q = true <->
        exists fs',
          Feature.FSet.Subset fs fs' /\ Feature.FeaturedSet.In (q, fs') S_CF.
    Proof.
      intros S_CF fs q; unfold takenWithb.
      rewrite Feature.FeaturedSet.exists_spec'.
      unfold Feature.FeaturedSet.Exists; split.
      - intros [[q' fs'] [Hq Hb]]; cbn beta iota in Hb.
        apply Bool.andb_true_iff in Hb; destruct Hb as [Hb1 Hb2].
        apply PackageEqb.eqb_true_iff in Hb1 as ->.
        apply Feature.FSet.subset_spec in Hb2.
        exists fs'; split; assumption.
      - intros [fs' [Hsub H]]; exists (q, fs'); split;
          [exact H | cbn beta iota].
        apply Bool.andb_true_iff; split;
          [apply PackageEqb.eqb_refl | apply Feature.FSet.subset_spec;
            exact Hsub].
    Qed.

    Lemma activeb_iff : forall S_CF pi p fs m u,
        activeb S_CF pi p fs m u = true <->
        (exists fs_p, Feature.FeaturedSet.In (p, fs_p) S_CF) /\
        (exists fs', Feature.FSet.Subset fs fs' /\
           Feature.FeaturedSet.In ((m, u), fs') S_CF) /\
        ParentRel.In ((m, u), p) pi.
    Proof.
      intros S_CF pi p fs m u; unfold activeb.
      rewrite !Bool.andb_true_iff, inSb_iff, takenWithb_iff,
        ParentRel.mem_spec.
      tauto.
    Qed.

    Inductive CoreMember (S_CF : Feature.FeaturedSet.t) (pi : ParentRel.t)
        (Df : Feature.ParameterisedDependencyRel.t)
          (Da : Feature.AdditionalDependencyRel.t) (g : V.t -> G.t) :
        Reduced.Package.t -> Prop :=
    | CoreOrig : forall n v fs,
        Feature.FeaturedSet.In ((n, v), fs) S_CF ->
        CoreMember S_CF pi Df Da g (Name.GranularOrig n (g v), v)
    | CoreFeatPkg : forall n v fs f,
        Feature.FeaturedSet.In ((n, v), fs) S_CF -> Feature.FSet.In f fs ->
        CoreMember S_CF pi Df Da g (Name.GranularFeatPkg n f (g v), v)
    | CoreFInter : forall n v m vs fs u,
        Feature.ParameterisedDependencyRel.In ((n, v), (m, (vs, fs))) Df ->
          VSet.In u vs ->
        activeb S_CF pi (n, v) fs m u = true ->
        CoreMember S_CF pi Df Da g (Name.Intermediate n v m, u)
    | CoreAInter : forall n v f m vs fs u,
        Feature.AdditionalDependencyRel.In (((n, v), f), (m, (vs, fs))) Da ->
          VSet.In u vs ->
        activeb S_CF pi (n, v) fs m u = true ->
        CoreMember S_CF pi Df Da g (Name.Intermediate n v m, u)
    | CoreFInterF : forall n v m vs fs f u,
        Feature.ParameterisedDependencyRel.In ((n, v), (m, (vs, fs))) Df ->
          Feature.FSet.In f fs ->
        VSet.In u vs -> activeb S_CF pi (n, v) fs m u = true ->
        CoreMember S_CF pi Df Da g (Name.IntermediateF n v m f, u)
    | CoreAInterA : forall n v f m vs fs f' u,
        Feature.AdditionalDependencyRel.In (((n, v), f), (m, (vs, fs))) Da ->
        Feature.FSet.In f' fs -> VSet.In u vs ->
        activeb S_CF pi (n, v) fs m u = true ->
        CoreMember S_CF pi Df Da g (Name.IntermediateA n v f m f', u).
    #[local] Hint Constructors CoreMember : fc_mem.

    Lemma mem_coreResolution : forall S_CF pi Df Da g (q : Reduced.Package.t),
        Reduced.PackageSet.In q (coreResolution Df Da g S_CF pi) <->
        CoreMember S_CF pi Df Da g q.
    Proof.
      intros S_CF pi Df Da g q; unfold coreResolution.
      rewrite !Reduced.PackageSet.union_spec, SOsw.mem_map, SOsw.mem_unionMap,
        !SOfp.mem_unionMap, !SOap.mem_unionMap.
      split.
      - intro H;
          repeat match goal with H : _ \/ _ |- _ => destruct H as [H | H] end;
          mem_open; eauto with fc_mem.
      - destruct 1; pick_close.
    Qed.

    Theorem concurrent_feature_completeness :
      forall (R : PackageSet.t) (support : Feature.SupportRel.t)
             (Df : Feature.ParameterisedDependencyRel.t)
               (Da : Feature.AdditionalDependencyRel.t)
             (g : V.t -> G.t) (r : Package.t)
             (S_CF : Feature.FeaturedSet.t) (pi : ParentRel.t),
        IsResolution R support Df Da g r S_CF pi ->
        Reduced.IsResolution (reduceReal R support Df Da g)
          (reduceDeps R support Df Da g)
          (embedOrigPkg g r) (coreResolution Df Da g S_CF pi).
    Proof.
      intros R support Df Da g r S_CF pi Hres.
      destruct Hres as [Hsubset Hrootm [Hpc Hpca] Hpif Hvg Hfu Hsm _].
      destruct r as [rn rv].
      constructor.
      - intros q Hq; apply mem_coreResolution in Hq; apply mem_reduceReal.
        destruct Hq as [n v fs HS | n v fs f HS Hf | n v m vs fs u HD Hu _
          | n v f m vs fs u HD Hu _ | n v m vs fs f u HD Hf Hu _
          | n v f m vs fs f' u HD Hf' Hu _].
        + apply RealOrig, Feature.Reduction.mem_reduceReal_orig.
          exact (Hsubset _ _ HS).
        + apply RealFeatPkg, Feature.Reduction.mem_reduceReal_featPkg.
          exact (conj (Hsm _ fs f HS Hf) (Hsubset _ _ HS)).
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
              as [u [Hu [Htk Hpi]]].
            exists u; split; [apply mem_embedVS; exact Hu |].
            apply mem_coreResolution; eapply CoreFInter;
              [eassumption | exact Hu | apply activeb_iff; eauto].
          * destruct (Hpc _ _ HS _ _ _ ltac:(eassumption))
              as [u [Hu [Htk Hpi]]].
            exists u; split; [apply mem_embedVS; exact Hu |].
            apply mem_coreResolution; eapply CoreFInterF;
              [eassumption | eassumption | exact Hu
              | apply activeb_iff; eauto].
        + inversion Hd; subst.
          * eexists; split; [apply mem_singVS; reflexivity |].
            apply mem_coreResolution; eapply CoreOrig; exact HS.
          * destruct (Hpca _ _ HS _ Hf _ _ _ ltac:(eassumption))
              as [u [Hu [Htk Hpi]]].
            exists u; split; [apply mem_embedVS; exact Hu |].
            apply mem_coreResolution; eapply CoreAInter;
              [eassumption | exact Hu | apply activeb_iff; eauto].
          * destruct (Hpca _ _ HS _ Hf _ _ _ ltac:(eassumption))
              as [u [Hu [Htk Hpi]]].
            exists u; split; [apply mem_embedVS; exact Hu |].
            apply mem_coreResolution; eapply CoreAInterA;
              [eassumption | eassumption | exact Hu
              | apply activeb_iff; eauto].
        + inversion Hd; subst;
            apply activeb_iff in Hc as [_ [[fs' [_ HS']] _]];
            eexists; (split; [apply mem_singVS; reflexivity |]);
            apply mem_coreResolution; eapply CoreOrig; exact HS'.
        + inversion Hd; subst;
            apply activeb_iff in Hc as [_ [[fs' [_ HS']] _]];
            eexists; (split; [apply mem_singVS; reflexivity |]);
            apply mem_coreResolution; eapply CoreOrig; exact HS'.
        + inversion Hd; subst;
            eexists; (split; [apply mem_singVS; reflexivity |]);
            apply mem_coreResolution.
          * apply activeb_iff in Hc as [_ [[fs' [Hsub' HS']] _]].
            eapply CoreFeatPkg; [exact HS' | exact (Hsub' _ Hf)].
          * eapply CoreFInter; [exact HD | exact Hu | exact Hc].
        + inversion Hd; subst;
            eexists; (split; [apply mem_singVS; reflexivity |]);
            apply mem_coreResolution.
          * apply activeb_iff in Hc as [_ [[fs' [Hsub' HS']] _]].
            eapply CoreFeatPkg; [exact HS' | exact (Hsub' _ Hf')].
          * eapply CoreAInter; [exact HD | exact Hu | exact Hc].
      - intros n cv1 cv2 H1 H2.
        apply mem_coreResolution in H1, H2.
        inversion H1; subst; inversion H2; subst;
          repeat match goal with
                 | H : activeb _ _ _ _ _ _ = true |- _ =>
                     apply activeb_iff in H; destruct H as [_ [_ ?]]
                 end;
          try (eapply Hpif; eassumption).
        all: match goal with |- ?a = ?b =>
               destruct (V.eq_dec a b) as [| NE]; [assumption | exfalso];
               eapply (Hvg _ a b);
                 [eassumption | eassumption | exact NE | congruence]
             end.
    Qed.

    Lemma concurrentFeatureResolution_coreResolution :
      forall R support Df Da g r S_CF pi,
        IsResolution R support Df Da g r S_CF pi ->
        concurrentFeatureResolution g (coreResolution Df Da g S_CF pi) = S_CF.
    Proof.
      intros R support Df Da g r S_CF pi Hres.
      assert (Hfeats : forall n v fs,
        Feature.FeaturedSet.In ((n, v), fs) S_CF ->
                 featsOf g n v (coreResolution Df Da g S_CF pi) = fs).
      { intros n v fs HS; apply Feature.FSet.ext; intro f.
        rewrite featsOf_spec, mem_coreResolution; split.
        - intro Hc; inversion Hc; subst.
          match goal with
          | H1 : Feature.FeaturedSet.In (?p, ?fs1) S_CF,
            H2 : Feature.FeaturedSet.In (?p, ?fs2) S_CF,
            Hf : Feature.FSet.In ?x ?fs2 |- Feature.FSet.In ?x ?fs1 =>
              rewrite <- (res_feature_unification _ _ _ _ _ _ _ _ Hres
                            _ _ _ _ H1 H2) in Hf; exact Hf
          end.
        - intro Hf; exact (CoreFeatPkg _ _ _ _ _ n v fs f HS Hf). }
      apply Feature.FeaturedSet.ext; intros [[n v] fs].
      rewrite mem_concurrentFeatureResolution; split.
      - intros [Hc ->].
        rewrite mem_coreResolution in Hc; inversion Hc; subst.
        match goal with
        | HS : Feature.FeaturedSet.In ((_, _), _) S_CF |- _ =>
            rewrite (Hfeats _ _ _ HS); exact HS
        end.
      - intro HS; split.
        + apply mem_coreResolution; exact (CoreOrig _ _ _ _ _ n v fs HS).
        + rewrite (Hfeats _ _ _ HS); reflexivity.
    Qed.

    Lemma parents_coreResolution_iff :
      forall R support Df Da g r S_CF pi,
        IsResolution R support Df Da g r S_CF pi ->
        forall m u n v,
          ParentRel.In ((m, u), (n, v))
            (parents Df Da g (coreResolution Df Da g S_CF pi))
          <-> ParentRel.In ((m, u), (n, v)) pi /\
          ((exists vs fs,
            Feature.ParameterisedDependencyRel.In ((n, v), (m, (vs, fs))) Df) \/
           (exists fs_p f vs fs, Feature.FeaturedSet.In ((n, v), fs_p) S_CF /\
              Feature.FSet.In f fs_p /\
              Feature.AdditionalDependencyRel.In
                (((n, v), f), (m, (vs, fs))) Da)).
    Proof.
      intros R support Df Da g r S_CF pi Hres m u n v; rewrite mem_parents.
      split.
      - intros [H Hdep]; split.
        { apply mem_coreResolution in H; inversion H; subst;
            match goal with
            | Hw : activeb _ _ _ _ _ _ = true |- _ =>
                apply activeb_iff in Hw; destruct Hw as (_ & _ & Hpi);
                exact Hpi
            end. }
        destruct Hdep
          as [(vs & fs & HD & _ & Hs) | (f & vs & fs & HA & _ & Hs)].
        + left; exists vs, fs; exact HD.
        + apply mem_coreResolution in Hs; inversion Hs; subst.
          right; do 4 eexists; split; [eassumption |].
          split; [| exact HA]; eassumption.
      - intros [Hpi [(vs & fs & HD) | (fs_p & f & vs & fs & Hp & Hf & HA)]].
        + destruct (proj2 (res_parent_subset _ _ _ _ _ _ _ _ Hres _ _ Hpi))
            as [fs_p Hp].
          destruct (proj1 (res_parent_closure _ _ _ _ _ _ _ _ Hres)
                      _ _ Hp _ _ _ HD)
            as (w & Hw & Htk & Hpiw).
          assert (w = u) as ->
            by exact (res_pi_functional _ _ _ _ _ _ _ _ Hres _ _ _ _ Hpiw Hpi).
          split.
          * apply mem_coreResolution,
              (CoreFInter _ _ _ _ _ n v m vs fs u HD Hw).
            apply activeb_iff; split; [exists fs_p; exact Hp |].
            split; [exact Htk | exact Hpi].
          * left; exists vs, fs; split; [exact HD | split; [exact Hw |]].
            apply mem_coreResolution; exact (CoreOrig _ _ _ _ _ n v fs_p Hp).
        + destruct (proj2 (res_parent_closure _ _ _ _ _ _ _ _ Hres)
                      _ _ Hp _ Hf _ _ _ HA)
            as (w & Hw & Htk & Hpiw).
          assert (w = u) as ->
            by exact (res_pi_functional _ _ _ _ _ _ _ _ Hres _ _ _ _ Hpiw Hpi).
          split.
          * apply mem_coreResolution,
              (CoreAInter _ _ _ _ _ n v f m vs fs u HA Hw).
            apply activeb_iff; split; [exists fs_p; exact Hp |].
            split; [exact Htk | exact Hpi].
          * right; exists f, vs, fs; split; [exact HA | split; [exact Hw |]].
            apply mem_coreResolution.
            exact (CoreFeatPkg _ _ _ _ _ n v fs_p f Hp Hf).
    Qed.

    Theorem concurrent_feature_retraction :
      forall R support Df Da g r S_CF pi,
        IsResolution R support Df Da g r S_CF pi ->
        ParentDependency Df Da S_CF pi ->
        concurrentFeatureResolution g (coreResolution Df Da g S_CF pi) = S_CF
        /\ parents Df Da g (coreResolution Df Da g S_CF pi) = pi.
    Proof.
      intros R support Df Da g r S_CF pi Hres Hdep.
      split; [exact (concurrentFeatureResolution_coreResolution
                       _ _ _ _ _ _ _ _ Hres) |].
      apply ParentRel.ext; intros [[m u] [n v]].
      rewrite (parents_coreResolution_iff _ _ _ _ _ _ _ _ Hres).
      split; [intros [H _]; exact H | intro H; exact (conj H (Hdep _ _ _ _ H))].
    Qed.

    Module Lookup.
      Module NEqb := UOTEqb N.
      Definition pkgNodeFibre (Da : Feature.AdditionalDependencyRel.t)
          (p : Package.t) (m : N.t) :
          Feature.AdditionalDependencyRel.t :=
        Feature.AdditionalDependencyRel.filter
          (fun '((q, _), (m', _)) => andb (PackageEqb.eqb q p) (NEqb.eqb m' m))
          Da.

      Lemma mem_pkgNodeFibre :
        forall Da (p q : Package.t) (f : F.t) (m m' : N.t)
          (d : Feature.DependeeTail.t),
          Feature.AdditionalDependencyRel.In ((q, f), (m', d))
            (pkgNodeFibre Da p m) <->
          Feature.AdditionalDependencyRel.In ((q, f), (m', d)) Da /\ q =
            p /\ m' = m.
      Proof.
        intros Da p q f m m' d; unfold pkgNodeFibre.
        rewrite Feature.AdditionalDependencyRel.filter_spec'; cbn beta iota.
        rewrite Bool.andb_true_iff, PackageEqb.eqb_true_iff, NEqb.eqb_true_iff.
        tauto.
      Qed.

      Lemma reduceDeps_mono :
        forall R R' support support' Df Df' Da Da' g
          (y : Reduced.DependencyElt.t),
          PackageSet.Subset R' R ->
            Feature.SupportRel.Subset support' support ->
          Feature.ParameterisedDependencyRel.Subset Df' Df ->
            Feature.AdditionalDependencyRel.Subset Da' Da ->
          Reduced.DependencyRel.In y (reduceDeps R' support' Df' Da' g) ->
          Reduced.DependencyRel.In y (reduceDeps R support Df Da g).
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
          destruct (PackageSet.mem (n, v) R') eqn:Em; [| discriminate Hz].
          rewrite PackageSet.mem_spec in Em; apply HR in Em.
          rewrite <- PackageSet.mem_spec in Em; rewrite Em; exact Hz.
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

      Include GranularityFibre N V G Package PackageSet.

      Theorem versions_lookupGranularOrig : forall R support Df Da g n w,
          Reduced.versions (reduceReal R support Df Da g)
            (Name.GranularOrig n w) =
          Reduced.versions
            (reduceReal (granFibre g R n w) Feature.SupportRel.empty
               Feature.ParameterisedDependencyRel.empty
                 Feature.AdditionalDependencyRel.empty g)
            (Name.GranularOrig n w).
      Proof.
        intros R support Df Da g n w; apply Reduced.versions_ext; intro v.
        rewrite !mem_reduceReal.
        split; intro H; inversion H; subst; apply RealOrig;
          rewrite Feature.Reduction.mem_reduceReal_orig in *;
          rewrite mem_granFibre in *; intuition.
      Qed.

      Module ParameterisedDependencyRelFibred :=
        Feature.Reduction.Lookup.ParameterisedDependencyRelFibred.
      Theorem dependees_lookupGranularOrig : forall R support Df Da g n v,
          Reduced.dependees (reduceDeps R support Df Da g)
            (Name.GranularOrig n (g v), v) =
          Reduced.dependees
            (reduceDeps PackageSet.empty Feature.SupportRel.empty
               (ParameterisedDependencyRelFibred.tailFibre Df (n, v))
               Feature.AdditionalDependencyRel.empty g)
            (Name.GranularOrig n (g v), v).
      Proof.
        intros R support Df Da g n v; apply Reduced.dependees_ext;
          intros [m ws].
        split; [| apply reduceDeps_mono;
                  [apply PackageSet.empty_subset
                  | apply Feature.SupportRel.empty_subset
                  | apply ParameterisedDependencyRelFibred.tailFibre_subset
                  | apply Feature.AdditionalDependencyRel.empty_subset]].
        intro H; apply mem_reduceDeps in H; apply mem_reduceDeps.
        inversion H; subst.
        - eapply EdgeFDepToInter;
            apply ParameterisedDependencyRelFibred.mem_tailFibre;
            split; [eassumption | reflexivity].
        - eapply EdgeFDepToInterFeat;
            [apply ParameterisedDependencyRelFibred.mem_tailFibre;
               split; [eassumption | reflexivity]
            | eassumption].
      Qed.

      Module PackageSetFibred := Feature.Reduction.Lookup.PackageSetFibred.
      Module SupportRelFibred := Feature.Reduction.Lookup.SupportRelFibred.
      Module AdditionalDependencyRelFibred :=
        Feature.Reduction.Lookup.AdditionalDependencyRelFibred.
      Theorem versions_lookupGranularFeatPkg : forall R support Df Da g n f w,
          Reduced.versions (reduceReal R support Df Da g)
            (Name.GranularFeatPkg n f w) =
          Reduced.versions
            (reduceReal (granFibre g R n w)
               (Feature.Reduction.Lookup.supportFibre support n f)
               Feature.ParameterisedDependencyRel.empty
                 Feature.AdditionalDependencyRel.empty g)
            (Name.GranularFeatPkg n f w).
      Proof.
        intros R support Df Da g n f w; apply Reduced.versions_ext; intro v.
        rewrite !mem_reduceReal.
        split; intro H; inversion H; subst; apply RealFeatPkg;
          rewrite Feature.Reduction.mem_reduceReal_featPkg in *;
          rewrite mem_granFibre, Feature.Reduction.Lookup.mem_supportFibre in *;
          intuition.
      Qed.

      Lemma dependees_lookupGranularFeatPkg_any :
        forall R support Df Da g n v f,
          Reduced.dependees (reduceDeps R support Df Da g)
            (Name.GranularFeatPkg n f (g v), v) =
          Reduced.dependees
            (reduceDeps (PackageSetFibred.idFibre R (n, v))
               (SupportRelFibred.idFibre support ((n, v), f))
               Feature.ParameterisedDependencyRel.empty
               (AdditionalDependencyRelFibred.tailFibre Da ((n, v), f)) g)
            (Name.GranularFeatPkg n f (g v), v).
      Proof.
        intros R support Df Da g n v f; apply Reduced.dependees_ext;
          intros [m ws].
        split; [| apply reduceDeps_mono;
                  [apply PackageSetFibred.idFibre_subset
                  | apply SupportRelFibred.idFibre_subset
                  | apply Feature.ParameterisedDependencyRel.empty_subset
                  | apply AdditionalDependencyRelFibred.tailFibre_subset]].
        intro H; apply mem_reduceDeps in H; apply mem_reduceDeps.
        inversion H; subst.
        - apply EdgeSupport;
            [apply SupportRelFibred.mem_idFibre;
               split; [eassumption | reflexivity]
            | apply PackageSetFibred.mem_idFibre; split;
                [eassumption | reflexivity]].
        - eapply EdgeADepToInter;
            apply AdditionalDependencyRelFibred.mem_tailFibre;
            split; [eassumption | reflexivity].
        - eapply EdgeADepToInterFeat;
            [apply AdditionalDependencyRelFibred.mem_tailFibre;
               split; [eassumption | reflexivity]
            | eassumption].
      Qed.

      (* The membership premise is what collapses the fibres to singletons. *)
      Theorem dependees_lookupGranularFeatPkg : forall R support Df Da g n v f,
          Reduced.PackageSet.In (Name.GranularFeatPkg n f (g v), v)
            (reduceReal R support Df Da g) ->
          Reduced.dependees (reduceDeps R support Df Da g)
            (Name.GranularFeatPkg n f (g v), v) =
          Reduced.dependees
            (reduceDeps (PackageSet.singleton (n, v))
               (Feature.SupportRel.singleton ((n, v), f))
               Feature.ParameterisedDependencyRel.empty
               (AdditionalDependencyRelFibred.tailFibre Da ((n, v), f)) g)
            (Name.GranularFeatPkg n f (g v), v).
      Proof.
        intros R support Df Da g n v f Hin.
        assert (Feature.SupportRel.In ((n, v), f) support /\
          PackageSet.In (n, v) R)
          as [Hs HR].
        { apply mem_reduceReal in Hin; inversion Hin; subst.
          eapply Feature.Reduction.mem_reduceReal_featPkg; eassumption. }
        assert (PackageSetFibred.idFibre R (n, v) =
          PackageSet.singleton (n, v)) as ER.
        { apply PackageSet.ext; intro x.
          rewrite PackageSetFibred.mem_idFibre, PackageSet.singleton_spec.
          split; [intros [_ E]; exact E
                 | intro E; split; [rewrite E; exact HR | exact E]]. }
        assert (SupportRelFibred.idFibre support ((n, v), f)
                = Feature.SupportRel.singleton ((n, v), f)) as ES.
        { apply Feature.SupportRel.ext; intro x.
          rewrite SupportRelFibred.mem_idFibre,
            Feature.SupportRel.singleton_spec.
          split; [intros [_ E]; exact E
                 | intro E; split; [rewrite E; exact Hs | exact E]]. }
        rewrite dependees_lookupGranularFeatPkg_any, ER, ES; reflexivity.
      Qed.

      Theorem versions_lookupIntermediate : forall R support Df Da g n v m,
          Reduced.versions (reduceReal R support Df Da g)
            (Name.Intermediate n v m) =
          Reduced.versions
            (reduceReal PackageSet.empty Feature.SupportRel.empty
               (ParameterisedDependencyRelFibred.endsFibre Df (n, v) m)
               (pkgNodeFibre Da (n, v) m) g)
            (Name.Intermediate n v m).
      Proof.
        intros R support Df Da g n v m; apply Reduced.versions_ext; intro u.
        rewrite !mem_reduceReal.
        split; intro H; inversion H; subst.
        - eapply RealFInter; [| eassumption].
          apply ParameterisedDependencyRelFibred.mem_endsFibre;
            split; [eassumption | split; reflexivity].
        - eapply RealAInter; [| eassumption].
          apply mem_pkgNodeFibre; split; [eassumption | split; reflexivity].
        - match goal with
          | Hx : Feature.ParameterisedDependencyRel.In _
              (ParameterisedDependencyRelFibred.endsFibre _ _ _) |- _ =>
              apply ParameterisedDependencyRelFibred.mem_endsFibre in Hx;
                destruct Hx as [Hx _]
          end.
          eapply RealFInter; eassumption.
        - match goal with
          | Hx : Feature.AdditionalDependencyRel.In _
              (pkgNodeFibre _ _ _) |- _ =>
              apply mem_pkgNodeFibre in Hx; destruct Hx as [Hx _]
          end.
          eapply RealAInter; eassumption.
      Qed.

      Theorem dependees_lookupIntermediate : forall R support Df Da g n v m u,
          Reduced.dependees (reduceDeps R support Df Da g)
            (Name.Intermediate n v m, u) =
          Reduced.dependees
            (reduceDeps PackageSet.empty Feature.SupportRel.empty
               (ParameterisedDependencyRelFibred.endsFibre Df (n, v) m)
               (pkgNodeFibre Da (n, v) m) g)
            (Name.Intermediate n v m, u).
      Proof.
        intros R support Df Da g n v m u.
        apply Reduced.dependees_ext; intros [m' ws].
        split; [| apply reduceDeps_mono;
                  [apply PackageSet.empty_subset
                  | apply Feature.SupportRel.empty_subset
                  | apply ParameterisedDependencyRelFibred.endsFibre_subset
                  | intros [[q f0] [m0 d]] Hq; apply mem_pkgNodeFibre in Hq;
                    destruct Hq as [Hq _]; exact Hq]].
        intro H; apply mem_reduceDeps in H; apply mem_reduceDeps.
        inversion H; subst.
        - eapply EdgeFInterToOrig;
            [apply ParameterisedDependencyRelFibred.mem_endsFibre;
               split; [eassumption | split; reflexivity]
            | eassumption].
        - eapply EdgeAInterToOrig;
            [apply mem_pkgNodeFibre; split; [eassumption | split; reflexivity]
            | eassumption].
      Qed.

      Theorem versions_lookupIntermediateF : forall R support Df Da g n v m f',
          Reduced.versions (reduceReal R support Df Da g)
            (Name.IntermediateF n v m f') =
          Reduced.versions
            (reduceReal PackageSet.empty Feature.SupportRel.empty
               (ParameterisedDependencyRelFibred.endsFibre Df (n, v) m)
               Feature.AdditionalDependencyRel.empty g)
            (Name.IntermediateF n v m f').
      Proof.
        intros R support Df Da g n v m f'; apply Reduced.versions_ext; intro u.
        rewrite !mem_reduceReal.
        split; intro H; inversion H; subst.
        - eapply RealFInterF; [| eassumption | eassumption].
          apply ParameterisedDependencyRelFibred.mem_endsFibre;
            split; [eassumption | split; reflexivity].
        - match goal with
          | Hx : Feature.ParameterisedDependencyRel.In _
              (ParameterisedDependencyRelFibred.endsFibre _ _ _) |- _ =>
              apply ParameterisedDependencyRelFibred.mem_endsFibre in Hx;
                destruct Hx as [Hx _]
          end.
          eapply RealFInterF; eassumption.
      Qed.

      Theorem dependees_lookupIntermediateF :
        forall R support Df Da g n v m f' u,
          Reduced.dependees (reduceDeps R support Df Da g)
            (Name.IntermediateF n v m f', u) =
          Reduced.dependees
            (reduceDeps PackageSet.empty Feature.SupportRel.empty
               (ParameterisedDependencyRelFibred.endsFibre Df (n, v) m)
               Feature.AdditionalDependencyRel.empty g)
            (Name.IntermediateF n v m f', u).
      Proof.
        intros R support Df Da g n v m f' u.
        apply Reduced.dependees_ext; intros [m' ws].
        split; [| apply reduceDeps_mono;
                  [apply PackageSet.empty_subset
                  | apply Feature.SupportRel.empty_subset
                  | apply ParameterisedDependencyRelFibred.endsFibre_subset
                  | apply Feature.AdditionalDependencyRel.empty_subset]].
        intro H; apply mem_reduceDeps in H; apply mem_reduceDeps.
        inversion H; subst.
        - eapply EdgeFInterToFeat;
            [apply ParameterisedDependencyRelFibred.mem_endsFibre;
               split; [eassumption | split; reflexivity]
            | eassumption | eassumption].
        - eapply EdgeFInterFeatToInter;
            [apply ParameterisedDependencyRelFibred.mem_endsFibre;
               split; [eassumption | split; reflexivity]
            | eassumption | eassumption].
      Qed.

      Theorem versions_lookupIntermediateA :
        forall R support Df Da g n v f m f',
          Reduced.versions (reduceReal R support Df Da g)
            (Name.IntermediateA n v f m f') =
          Reduced.versions
            (reduceReal PackageSet.empty Feature.SupportRel.empty
              Feature.ParameterisedDependencyRel.empty
               (AdditionalDependencyRelFibred.endsFibre Da ((n, v), f) m) g)
            (Name.IntermediateA n v f m f').
      Proof.
        intros R support Df Da g n v f m f';
          apply Reduced.versions_ext; intro u.
        rewrite !mem_reduceReal.
        split; intro H; inversion H; subst.
        - eapply RealAInterA; [| eassumption | eassumption].
          apply AdditionalDependencyRelFibred.mem_endsFibre;
            split; [eassumption | split; reflexivity].
        - match goal with
          | Hx : Feature.AdditionalDependencyRel.In _
              (AdditionalDependencyRelFibred.endsFibre _ _ _) |- _ =>
              apply AdditionalDependencyRelFibred.mem_endsFibre in Hx;
                destruct Hx as [Hx _]
          end.
          eapply RealAInterA; eassumption.
      Qed.

      Theorem dependees_lookupIntermediateA :
        forall R support Df Da g n v f m f' u,
          Reduced.dependees (reduceDeps R support Df Da g)
            (Name.IntermediateA n v f m f', u) =
          Reduced.dependees
            (reduceDeps PackageSet.empty Feature.SupportRel.empty
              Feature.ParameterisedDependencyRel.empty
               (AdditionalDependencyRelFibred.endsFibre Da ((n, v), f) m) g)
            (Name.IntermediateA n v f m f', u).
      Proof.
        intros R support Df Da g n v f m f' u.
        apply Reduced.dependees_ext; intros [m' ws].
        split; [| apply reduceDeps_mono;
                  [apply PackageSet.empty_subset
                  | apply Feature.SupportRel.empty_subset
                  | apply Feature.ParameterisedDependencyRel.empty_subset
                  | apply AdditionalDependencyRelFibred.endsFibre_subset]].
        intro H; apply mem_reduceDeps in H; apply mem_reduceDeps.
        inversion H; subst.
        - eapply EdgeAInterToFeat;
            [apply AdditionalDependencyRelFibred.mem_endsFibre;
               split; [eassumption | split; reflexivity]
            | eassumption | eassumption].
        - eapply EdgeAInterFeatToInter;
            [apply AdditionalDependencyRelFibred.mem_endsFibre;
               split; [eassumption | split; reflexivity]
            | eassumption | eassumption].
      Qed.

    End Lookup.
  End Reduction.
End ConcurrentFeature.
