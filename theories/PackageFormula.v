From Stdlib Require Import MSets.
From PackageCalculus Require Import Prelude Core.

Create HintDb cmp_pkgf.
Create Rewrite HintDb cmp_pkgf.

Module PackageFormula (N V : UsualOrderedType).
  Module C := Core N V.
  Module Pkg := C.Pkg.
  Module PkgSet := C.PkgSet.
  Module VSet := C.VSet.

  Inductive Formula : Type :=
  | FDep (n : N.t) (vs : VSet.t)
  | FConj (f1 f2 : Formula)
  | FDisj (f1 f2 : Formula)
  | FNeg (f : Formula).

  Fixpoint Satisfies (S : PkgSet.t) (f : Formula) : Prop :=
    match f with
    | FDep n vs => exists v, VSet.In v vs /\ PkgSet.In (n, v) S
    | FConj f1 f2 => Satisfies S f1 /\ Satisfies S f2
    | FDisj f1 f2 => Satisfies S f1 \/ Satisfies S f2
    | FNeg f1 => ~ Satisfies S f1
    end.

  Fixpoint satisfiesb (S : PkgSet.t) (f : Formula) : bool :=
    match f with
    | FDep n vs => VSet.exists_ (fun v => PkgSet.mem (n, v) S) vs
    | FConj f1 f2 => andb (satisfiesb S f1) (satisfiesb S f2)
    | FDisj f1 f2 => orb (satisfiesb S f1) (satisfiesb S f2)
    | FNeg f1 => negb (satisfiesb S f1)
    end.

  Lemma satisfiesb_iff : forall S f, satisfiesb S f = true <-> Satisfies S f.
  Proof.
    intros S f; induction f as [n vs | a IHa b IHb | a IHa b IHb | a IHa];
      simpl.
    - rewrite VSet.exists_spec'.
      split; intros [v [Hv Hm]]; exists v; split; try assumption;
        apply PkgSet.mem_spec; assumption.
    - rewrite Bool.andb_true_iff, IHa, IHb; reflexivity.
    - rewrite Bool.orb_true_iff, IHa, IHb; reflexivity.
    - rewrite Bool.negb_true_iff; split.
      + intros E Hs; apply IHa in Hs; congruence.
      + intro Hn; destruct (satisfiesb S a) eqn:E; [| reflexivity].
        exfalso; apply Hn, IHa; reflexivity.
  Qed.

  Lemma satisfiesb_false_iff : forall S f,
      satisfiesb S f = false <-> ~ Satisfies S f.
  Proof.
    intros S f; split.
    - intros E Hs; apply satisfiesb_iff in Hs; congruence.
    - intro Hn; destruct (satisfiesb S f) eqn:E; [| reflexivity].
      exfalso; apply Hn, satisfiesb_iff; exact E.
  Qed.

  Lemma satisfies_double_neg : forall S f, ~ ~ Satisfies S f -> Satisfies S f.
  Proof.
    intros S f Hnn; destruct (satisfiesb S f) eqn:E.
    - apply satisfiesb_iff; exact E.
    - exfalso; apply Hnn, satisfiesb_false_iff; exact E.
  Qed.

  Module NF := UOTCompareFacts N.
  Module VSF := UOTCompareFacts VSet.AsUOT.
  #[local] Hint Rewrite NF.compare_eq_iff : cmp_pkgf.
  #[local] Hint Extern 1 => cmp_by NF.compare_antisym : cmp_pkgf.
  #[local] Hint Extern 1 => cmp_by NF.compare_lt_trans : cmp_pkgf.

  Module FComp <: ComparableType.
    Definition t := Formula.
    Definition rank (f : Formula) : nat :=
      match f with
      | FDep _ _ => 0 | FConj _ _ => 1 | FDisj _ _ => 2 | FNeg _ => 3
      end.

    Fixpoint compare (x y : Formula) : comparison :=
      match Nat.compare (rank x) (rank y) with
      | Eq =>
          match x, y with
          | FDep n1 vs1, FDep n2 vs2 =>
              lex (N.compare n1 n2) (VSet.AsUOT.compare vs1 vs2)
          | FConj a1 b1, FConj a2 b2 => lex (compare a1 a2) (compare b1 b2)
          | FDisj a1 b1, FDisj a2 b2 => lex (compare a1 a2) (compare b1 b2)
          | FNeg a1, FNeg a2 => compare a1 a2
          | _, _ => Eq
          end
      | c => c
      end.

    Lemma compare_eq_iff : forall x y, compare x y = Eq <-> x = y.
    Proof.
      intros x; induction x as [n1 vs1 | a IHa b IHb | a IHa b IHb | a IHa];
        intros y; destruct y as [n2 vs2 | a2 b2 | a2 b2 | a2]; simpl;
        try (split; intro H; congruence).
      - rewrite lex_eq_iff, NF.compare_eq_iff, VSF.compare_eq_iff;
          split; intro H; [destruct H; congruence | injection H as -> ->; auto].
      - rewrite lex_eq_iff, IHa, IHb;
          split; intro H; [destruct H; congruence | injection H as -> ->; auto].
      - rewrite lex_eq_iff, IHa, IHb;
          split; intro H; [destruct H; congruence | injection H as -> ->; auto].
      - rewrite IHa; split; intro H; congruence.
    Qed.

    Lemma compare_antisym : forall x y, compare y x = CompOpp (compare x y).
    Proof.
      intros x; induction x as [n1 vs1 | a IHa b IHb | a IHa b IHb | a IHa];
        intros y; destruct y as [n2 vs2 | a2 b2 | a2 b2 | a2]; simpl;
        try reflexivity.
      - rewrite lex_opp, NF.compare_antisym, VSF.compare_antisym; reflexivity.
      - rewrite lex_opp, IHa, IHb; reflexivity.
      - rewrite lex_opp, IHa, IHb; reflexivity.
      - apply IHa.
    Qed.

    Lemma compare_lt_trans : forall x y z,
        compare x y = Lt -> compare y z = Lt -> compare x z = Lt.
    Proof.
      intros x;
        induction x as [n1 vs1 | a1 IHa b1 IHb | a1 IHa b1 IHb | a1 IHa];
        intros y z; destruct y as [n2 vs2 | a2 b2 | a2 b2 | a2],
          z as [n3 vs3 | a3 b3 | a3 b3 | a3]; simpl; intros H1 H2;
        try congruence.
      - exact (lex_lt_trans NF.compare_eq_iff (NF.compare_lt_trans _ _ _)
                 (VSF.compare_lt_trans _ _ _) H1 H2).
      - exact (lex_lt_trans compare_eq_iff (IHa _ _) (IHb _ _) H1 H2).
      - exact (lex_lt_trans compare_eq_iff (IHa _ _) (IHb _ _) H1 H2).
      - exact (IHa _ _ H1 H2).
    Qed.
  End FComp.
  Module FOT := UOTFromCompare FComp.

  Module Dependees := FOT.
  Module DepElt := PairUOT Pkg Dependees.
  Module DepRel := FSetUOT DepElt.

  Record IsResolution
      (R : PkgSet.t) (D : DepRel.t) (r : Pkg.t) (S : PkgSet.t) : Prop :=
    { res_subset : PkgSet.Subset S R
    ; res_root_mem : PkgSet.In r S
    ; res_formula_closure :
        forall p, PkgSet.In p S ->
        forall f : Formula, DepRel.In (p, f) D -> Satisfies S f
    ; res_version_unique : C.VersionUnique S }.

  Module Reduction.
    Module DepF := UOTCompareFacts C.Dependees.
    Module DPair := PairUOT FOT FOT.
    Module DPairF := UOTCompareFacts DPair.
    #[local] Hint Rewrite DepF.compare_eq_iff DPairF.compare_eq_iff : cmp_pkgf.
    #[local] Hint Extern 1 => cmp_by DepF.compare_antisym : cmp_pkgf.
    #[local] Hint Extern 1 => cmp_by DPairF.compare_antisym : cmp_pkgf.
    #[local] Hint Extern 1 => cmp_by DepF.compare_lt_trans : cmp_pkgf.
    #[local] Hint Extern 1 => cmp_by DPairF.compare_lt_trans : cmp_pkgf.

    Module Name.
      Inductive name : Type :=
      | Orig (n : N.t)
      | Disjunct (f1 f2 : Formula)
      | NegDep (n : N.t) (vs : VSet.t).
      Definition t := name.

      Definition compare (x y : t) : comparison :=
        match x, y with
        | Orig n1, Orig n2 => N.compare n1 n2
        | Orig _, _ => Lt
        | Disjunct _ _, Orig _ => Gt
        | Disjunct f1 g1, Disjunct f2 g2 => DPair.compare (f1, g1) (f2, g2)
        | Disjunct _ _, NegDep _ _ => Lt
        | NegDep n1 vs1, NegDep n2 vs2 =>
            C.Dependees.compare (n1, vs1) (n2, vs2)
        | NegDep _ _, _ => Gt
        end.

      Lemma compare_eq_iff : forall x y, compare x y = Eq <-> x = y.
      Proof. cmp_eq_iff cmp_pkgf. Qed.

      Lemma compare_antisym : forall x y, compare y x = CompOpp (compare x y).
      Proof. cmp_antisym cmp_pkgf. Qed.

      Lemma compare_lt_trans : forall x y z,
          compare x y = Lt -> compare y z = Lt -> compare x z = Lt.
      Proof. cmp_lt_trans cmp_pkgf. Qed.
    End Name.

    Module VF := UOTCompareFacts V.
    #[local] Hint Rewrite VF.compare_eq_iff : cmp_pkgf.
    #[local] Hint Extern 1 => cmp_by VF.compare_antisym : cmp_pkgf.
    #[local] Hint Extern 1 => cmp_by VF.compare_lt_trans : cmp_pkgf.

    Module Version.
      Inductive version : Type :=
      | Orig (v : V.t)
      | Zero
      | One.
      Definition t := version.

      Definition compare (x y : t) : comparison :=
        match x, y with
        | Orig v1, Orig v2 => V.compare v1 v2
        | Orig _, _ => Lt
        | Zero, Orig _ => Gt
        | Zero, Zero => Eq
        | Zero, One => Lt
        | One, One => Eq
        | One, _ => Gt
        end.

      Lemma compare_eq_iff : forall x y, compare x y = Eq <-> x = y.
      Proof. cmp_eq_iff cmp_pkgf. Qed.

      Lemma compare_antisym : forall x y, compare y x = CompOpp (compare x y).
      Proof. cmp_antisym cmp_pkgf. Qed.

      Lemma compare_lt_trans : forall x y z,
          compare x y = Lt -> compare y z = Lt -> compare x z = Lt.
      Proof. cmp_lt_trans cmp_pkgf. Qed.
    End Version.

    Module NameOT := UOTFromCompare Name.
    Module VersionOT := UOTFromCompare Version.
    Module T := Core NameOT VersionOT.

    Definition embedPkg (p : Pkg.t) : T.Pkg.t :=
      let '(n, v) := p in (Name.Orig n, Version.Orig v).

    Module SOvv := SetOps V VersionOT VSet T.VSet.
    Definition embedVS (vs : VSet.t) : T.VSet.t :=
      SOvv.map Version.Orig vs.

    Definition zeroOne : T.VSet.t :=
      T.VSet.add Version.Zero (T.VSet.singleton Version.One).

    Module SOvd := SetOps V T.DepElt VSet T.DepRel.
    (* A De Morgan case would recurse on a rewritten term, demanding
       well-founded recursion on a measure under which negation strictly
       decreases; fusing one unfolding step keeps this pair structural. *)
    Fixpoint encodeNNF (p : T.Pkg.t) (f : Formula) : T.DepRel.t :=
      match f with
      | FDep n vs =>
          T.DepRel.singleton (p, (Name.Orig n, embedVS vs))
      | FConj a b =>
          T.DepRel.union (encodeNNF p a) (encodeNNF p b)
      | FDisj a b =>
          T.DepRel.add (p, (Name.Disjunct a b, zeroOne))
            (T.DepRel.union
               (encodeNNF (Name.Disjunct a b, Version.Zero) a)
               (encodeNNF (Name.Disjunct a b, Version.One) b))
      | FNeg a => encodeNNFneg p a
      end
    with encodeNNFneg (p : T.Pkg.t) (f : Formula) : T.DepRel.t :=
      match f with
      | FDep n vs =>
          T.DepRel.add (p, (Name.NegDep n vs, T.VSet.singleton Version.One))
            (SOvd.map (fun u =>
                 ((Name.Orig n, Version.Orig u),
                  (Name.NegDep n vs, T.VSet.singleton Version.Zero)))
               vs)
      | FConj a b =>
          T.DepRel.add (p, (Name.Disjunct (FNeg a) (FNeg b), zeroOne))
            (T.DepRel.union
               (encodeNNFneg (Name.Disjunct (FNeg a) (FNeg b), Version.Zero) a)
               (encodeNNFneg (Name.Disjunct (FNeg a) (FNeg b), Version.One) b))
      | FDisj a b =>
          T.DepRel.union (encodeNNFneg p a) (encodeNNFneg p b)
      | FNeg a => encodeNNF p a
      end.

    Fixpoint witnessSet (p : T.Pkg.t) (f : Formula) : T.PkgSet.t :=
      match f with
      | FDep _ _ => T.PkgSet.empty
      | FConj a b => T.PkgSet.union (witnessSet p a) (witnessSet p b)
      | FDisj a b =>
          T.PkgSet.add (Name.Disjunct a b, Version.Zero)
            (T.PkgSet.add (Name.Disjunct a b, Version.One)
               (T.PkgSet.union
                  (witnessSet (Name.Disjunct a b, Version.Zero) a)
                  (witnessSet (Name.Disjunct a b, Version.One) b)))
      | FNeg a => witnessSetNeg p a
      end
    with witnessSetNeg (p : T.Pkg.t) (f : Formula) : T.PkgSet.t :=
      match f with
      | FDep n vs =>
          T.PkgSet.add (Name.NegDep n vs, Version.Zero)
            (T.PkgSet.singleton (Name.NegDep n vs, Version.One))
      | FConj a b =>
          T.PkgSet.add (Name.Disjunct (FNeg a) (FNeg b), Version.Zero)
            (T.PkgSet.add (Name.Disjunct (FNeg a) (FNeg b), Version.One)
               (T.PkgSet.union
                  (witnessSetNeg
                     (Name.Disjunct (FNeg a) (FNeg b), Version.Zero) a)
                  (witnessSetNeg
                     (Name.Disjunct (FNeg a) (FNeg b), Version.One) b)))
      | FDisj a b =>
          T.PkgSet.union (witnessSetNeg p a) (witnessSetNeg p b)
      | FNeg a => witnessSet p a
      end.

    Module SOpt := SetOps Pkg T.Pkg PkgSet T.PkgSet.
    Module SOet := SetOps DepElt T.Pkg DepRel T.PkgSet.
    Definition reduceReal (R : PkgSet.t) (D : DepRel.t) : T.PkgSet.t :=
      T.PkgSet.union (SOpt.map embedPkg R)
        (SOet.unionMap (fun '(p, f) => witnessSet (embedPkg p) f) D).

    Module SOed := SetOps DepElt T.DepElt DepRel T.DepRel.
    Definition reduceDeps (D : DepRel.t) : T.DepRel.t :=
      SOed.unionMap (fun '(p, f) => encodeNNF (embedPkg p) f) D.

    Lemma mem_zeroOne : forall w,
        T.VSet.In w zeroOne <-> w = Version.Zero \/ w = Version.One.
    Proof.
      intro w; unfold zeroOne; rewrite SOvv.add_in, SOvv.singleton_in; tauto.
    Qed.

    Lemma mem_reduceReal : forall R D (y : T.Pkg.t),
        T.PkgSet.In y (reduceReal R D) <->
        (exists p, PkgSet.In p R /\ y = embedPkg p) \/
        (exists p f, DepRel.In (p, f) D /\
                     T.PkgSet.In y (witnessSet (embedPkg p) f)).
    Proof.
      intros R D y; unfold reduceReal.
      rewrite T.PkgSet.union_spec, SOpt.mem_map, SOet.mem_unionMap.
      split.
      - intros [H | [[q g] [He Hy]]]; [left; exact H |].
        right; exists q, g; split; [exact He | exact Hy].
      - intros [H | [q [g [Hd Hy]]]]; [left; exact H |].
        right; exists (q, g); split; [exact Hd | exact Hy].
    Qed.

    Lemma mem_reduceDeps : forall D (d : T.DepElt.t),
        T.DepRel.In d (reduceDeps D) <->
        exists p f, DepRel.In (p, f) D /\
                    T.DepRel.In d (encodeNNF (embedPkg p) f).
    Proof.
      intros D d; unfold reduceDeps; rewrite SOed.mem_unionMap.
      split.
      - intros [[q g] [He Hd]]; exists q, g; split; [exact He | exact Hd].
      - intros [q [g [Hq Hd]]]; exists (q, g); split; [exact Hq | exact Hd].
    Qed.

    Definition tryInvPkg (p' : T.Pkg.t) : option Pkg.t :=
      match p' with
      | (Name.Orig n, Version.Orig v) => Some (n, v)
      | _ => None
      end.

    Lemma tryInvPkg_embed : forall p, tryInvPkg (embedPkg p) = Some p.
    Proof. intros [n v]; reflexivity. Qed.

    Lemma tryInvPkg_some : forall (p' : T.Pkg.t) (p : Pkg.t),
        tryInvPkg p' = Some p -> embedPkg p = p'.
    Proof.
      intros [n' v'] p H; destruct n', v'; cbn [tryInvPkg] in H;
        try discriminate.
      injection H as <-; reflexivity.
    Qed.

    Module SOtp := SetOps T.Pkg Pkg T.PkgSet PkgSet.
    Lemma embedPkg_injective : forall p q : Pkg.t,
        embedPkg p = embedPkg q -> p = q.
    Proof. exact (SOtp.emb_injective tryInvPkg embedPkg tryInvPkg_embed). Qed.
    Definition packageFormulaResolution (S : T.PkgSet.t) : PkgSet.t :=
      SOtp.filterMap tryInvPkg S.

    Lemma mem_packageFormulaResolution : forall (S : T.PkgSet.t) (p : Pkg.t),
        PkgSet.In p (packageFormulaResolution S) <-> T.PkgSet.In (embedPkg p) S.
    Proof.
      unfold packageFormulaResolution.
      exact (SOtp.mem_filterMap_inv tryInvPkg embedPkg tryInvPkg_embed
               tryInvPkg_some).
    Qed.

    Lemma witnessSet_name_classify_aux : forall f : Formula,
        (forall (p : T.Pkg.t) (n : Name.t) (v : Version.t),
            T.PkgSet.In (n, v) (witnessSet p f) ->
            (exists n' vs, n = Name.NegDep n' vs) \/
            (exists f1 f2, n = Name.Disjunct f1 f2)) /\
        (forall (p : T.Pkg.t) (n : Name.t) (v : Version.t),
            T.PkgSet.In (n, v) (witnessSetNeg p f) ->
            (exists n' vs, n = Name.NegDep n' vs) \/
            (exists f1 f2, n = Name.Disjunct f1 f2)).
    Proof.
      induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa];
        split; intros p n v H; simpl in H.
      - exfalso; exact (SOpt.empty_in _ H).
      - rewrite SOpt.add_in, SOpt.singleton_in in H.
        destruct H as [H | H]; injection H as -> _; left; eauto.
      - apply T.PkgSet.union_spec in H; destruct H as [H | H];
          [exact (proj1 IHa _ _ _ H) | exact (proj1 IHb _ _ _ H)].
      - rewrite !SOpt.add_in in H.
        destruct H as [H | [H | H]]; try (injection H as -> _; right; eauto).
        apply T.PkgSet.union_spec in H; destruct H as [H | H];
          [exact (proj2 IHa _ _ _ H) | exact (proj2 IHb _ _ _ H)].
      - rewrite !SOpt.add_in in H.
        destruct H as [H | [H | H]]; try (injection H as -> _; right; eauto).
        apply T.PkgSet.union_spec in H; destruct H as [H | H];
          [exact (proj1 IHa _ _ _ H) | exact (proj1 IHb _ _ _ H)].
      - apply T.PkgSet.union_spec in H; destruct H as [H | H];
          [exact (proj2 IHa _ _ _ H) | exact (proj2 IHb _ _ _ H)].
      - exact (proj2 IHa _ _ _ H).
      - exact (proj1 IHa _ _ _ H).
    Qed.

    Lemma witnessSet_not_orig : forall (p : T.Pkg.t) (f : Formula) n v,
        ~ T.PkgSet.In (Name.Orig n, v) (witnessSet p f).
    Proof.
      intros p f n v H.
      destruct (proj1 (witnessSet_name_classify_aux f) _ _ _ H)
        as [[n' [vs E]] | [f1 [f2 E]]]; discriminate.
    Qed.

    Lemma embedPkg_mem_reduceReal : forall (p : Pkg.t) R D,
        T.PkgSet.In (embedPkg p) (reduceReal R D) -> PkgSet.In p R.
    Proof.
      intros [pn pv] R D H; apply mem_reduceReal in H.
      destruct H as [[q [HqR Hq]] | [q [g [_ Hy]]]].
      - apply embedPkg_injective in Hq as ->; exact HqR.
      - exfalso; exact (witnessSet_not_orig _ _ _ _ Hy).
    Qed.

    Lemma encodeNNF_satisfies : forall (R : T.PkgSet.t) (D : T.DepRel.t)
                                    (r : T.Pkg.t) (S : T.PkgSet.t),
        T.IsResolution R D r S ->
        forall (q : T.Pkg.t) (f : Formula),
          (forall d, T.DepRel.In d (encodeNNF q f) -> T.DepRel.In d D) ->
          T.PkgSet.In q S ->
          Satisfies (packageFormulaResolution S) f.
    Proof.
      intros R D r S Hres; destruct Hres as [Hsub Hroot Hdep Huniq].
      cut (forall f : Formula,
        (forall q : T.Pkg.t,
            (forall d, T.DepRel.In d (encodeNNF q f) -> T.DepRel.In d D) ->
            T.PkgSet.In q S -> Satisfies (packageFormulaResolution S) f) /\
        (forall q : T.Pkg.t,
            (forall d, T.DepRel.In d (encodeNNFneg q f) -> T.DepRel.In d D) ->
            T.PkgSet.In q S -> ~ Satisfies (packageFormulaResolution S) f)).
      { intros H q f; exact (proj1 (H f) q). }
      induction f as [n vs | a IHa b IHb | a IHa b IHb | a IHa];
        split; intros q Henc HqS; simpl.
      - assert (Hd : T.DepRel.In (q, (Name.Orig n, embedVS vs)) D).
        { apply Henc; simpl; apply SOed.singleton_in; reflexivity. }
        destruct (Hdep q HqS _ _ Hd) as [w [Hw HwS]].
        unfold embedVS in Hw; apply SOvv.mem_map in Hw;
          destruct Hw as [v [Hv ->]].
        exists v; split; [exact Hv |].
        apply mem_packageFormulaResolution; exact HwS.
      - assert
          (Hd1 : T.DepRel.In
                   (q, (Name.NegDep n vs, T.VSet.singleton Version.One)) D).
        { apply Henc; simpl; apply SOed.add_in; left; reflexivity. }
        destruct (Hdep q HqS _ _ Hd1) as [w [Hw HwS]].
        apply SOvv.singleton_in in Hw; subst w.
        intros [v [Hv HvS]].
        apply mem_packageFormulaResolution in HvS.
        assert (Hd2 : T.DepRel.In ((Name.Orig n, Version.Orig v),
                        (Name.NegDep n vs, T.VSet.singleton Version.Zero)) D).
        { apply Henc; simpl; apply SOed.add_in; right.
          apply SOvd.mem_map; exists v; split; [exact Hv | reflexivity]. }
        destruct (Hdep _ HvS _ _ Hd2) as [w2 [Hw2 Hw2S]].
        apply SOvv.singleton_in in Hw2; subst w2.
        assert (E := Huniq _ _ _ HwS Hw2S); discriminate.
      - split.
        + apply (proj1 IHa q); [| exact HqS].
          intros d Hd; apply Henc; simpl;
            apply T.DepRel.union_spec; left; exact Hd.
        + apply (proj1 IHb q); [| exact HqS].
          intros d Hd; apply Henc; simpl;
            apply T.DepRel.union_spec; right; exact Hd.
      - assert (Hd : T.DepRel.In
          (q, (Name.Disjunct (FNeg a) (FNeg b), zeroOne)) D).
        { apply Henc; simpl; apply SOed.add_in; left; reflexivity. }
        destruct (Hdep q HqS _ _ Hd) as [w [Hw HwS]].
        apply mem_zeroOne in Hw.
        intros [HsatA HsatB].
        destruct Hw as [-> | ->].
        + refine (proj2 IHa (Name.Disjunct (FNeg a) (FNeg b), Version.Zero)
                    _ HwS HsatA).
          intros d Hd'; apply Henc; simpl; apply SOed.add_in; right;
            apply T.DepRel.union_spec; left; exact Hd'.
        + refine (proj2 IHb (Name.Disjunct (FNeg a) (FNeg b), Version.One)
                    _ HwS HsatB).
          intros d Hd'; apply Henc; simpl; apply SOed.add_in; right;
            apply T.DepRel.union_spec; right; exact Hd'.
      - assert (Hd : T.DepRel.In (q, (Name.Disjunct a b, zeroOne)) D).
        { apply Henc; simpl; apply SOed.add_in; left; reflexivity. }
        destruct (Hdep q HqS _ _ Hd) as [w [Hw HwS]].
        apply mem_zeroOne in Hw; destruct Hw as [-> | ->].
        + left;
            apply (proj1 IHa (Name.Disjunct a b, Version.Zero)); [| exact HwS].
          intros d Hd'; apply Henc; simpl; apply SOed.add_in; right;
            apply T.DepRel.union_spec; left; exact Hd'.
        + right;
            apply (proj1 IHb (Name.Disjunct a b, Version.One)); [| exact HwS].
          intros d Hd'; apply Henc; simpl; apply SOed.add_in; right;
            apply T.DepRel.union_spec; right; exact Hd'.
      - intros [HsatA | HsatB].
        + refine (proj2 IHa q _ HqS HsatA).
          intros d Hd'; apply Henc; simpl;
            apply T.DepRel.union_spec; left; exact Hd'.
        + refine (proj2 IHb q _ HqS HsatB).
          intros d Hd'; apply Henc; simpl;
            apply T.DepRel.union_spec; right; exact Hd'.
      - exact (proj2 IHa q Henc HqS).
      - intro Hn; exact (Hn (proj1 IHa q Henc HqS)).
    Qed.

    Theorem package_formula_soundness :
      forall (R : PkgSet.t) (D : DepRel.t) (r : Pkg.t) (S : T.PkgSet.t),
        T.IsResolution (reduceReal R D) (reduceDeps D) (embedPkg r) S ->
        IsResolution R D r (packageFormulaResolution S).
    Proof.
      intros R D r S Hres.
      assert (H := Hres); destruct H as [Hsub Hroot Hdep Huniq].
      constructor.
      - intros p Hp; apply mem_packageFormulaResolution in Hp.
        exact (embedPkg_mem_reduceReal p R D (Hsub _ Hp)).
      - apply mem_packageFormulaResolution; exact Hroot.
      - intros p Hp f Hdf.
        apply mem_packageFormulaResolution in Hp.
        apply (encodeNNF_satisfies _ _ _ _ Hres (embedPkg p) f); [| exact Hp].
        intros d Hd; apply mem_reduceDeps;
          exists p, f; split; [exact Hdf | exact Hd].
      - intros n v v' Hv Hv'.
        apply mem_packageFormulaResolution in Hv, Hv'.
        unfold embedPkg in Hv, Hv'; simpl in Hv, Hv'.
        assert (E := Huniq _ _ _ Hv Hv').
        injection E as E; exact E.
    Qed.

    Definition depTakenb (S : PkgSet.t) (n : N.t) (vs : VSet.t) : bool :=
      VSet.exists_ (fun u => PkgSet.mem (n, u) S) vs.

    Lemma depTakenb_iff : forall S n vs,
        depTakenb S n vs = true <->
        exists u, VSet.In u vs /\ PkgSet.In (n, u) S.
    Proof.
      intros S n vs; unfold depTakenb.
      rewrite VSet.exists_spec'.
      split; intros [u [Hu Hm]]; exists u; split; try assumption;
        apply PkgSet.mem_spec; assumption.
    Qed.

    Fixpoint witnessSetUntaken (S : PkgSet.t) (f : Formula) : T.PkgSet.t :=
      match f with
      | FDep _ _ => T.PkgSet.empty
      | FConj a b =>
          T.PkgSet.union (witnessSetUntaken S a) (witnessSetUntaken S b)
      | FDisj a b =>
          T.PkgSet.union (witnessSetUntaken S a) (witnessSetUntaken S b)
      | FNeg a => witnessSetUntakenNeg S a
      end
    with witnessSetUntakenNeg (S : PkgSet.t) (f : Formula) : T.PkgSet.t :=
      match f with
      | FDep n vs =>
          if depTakenb S n vs
          then T.PkgSet.singleton (Name.NegDep n vs, Version.Zero)
          else T.PkgSet.empty
      | FConj a b =>
          T.PkgSet.union (witnessSetUntakenNeg S a) (witnessSetUntakenNeg S b)
      | FDisj a b =>
          T.PkgSet.union (witnessSetUntakenNeg S a) (witnessSetUntakenNeg S b)
      | FNeg a => witnessSetUntaken S a
      end.

    Fixpoint witnessSetTaken (S : PkgSet.t) (f : Formula) : T.PkgSet.t :=
      match f with
      | FDep _ _ => T.PkgSet.empty
      | FConj a b =>
          T.PkgSet.union (witnessSetTaken S a) (witnessSetTaken S b)
      | FDisj a b =>
          if satisfiesb S a
          then T.PkgSet.add (Name.Disjunct a b, Version.Zero)
                 (T.PkgSet.union (witnessSetTaken S a) (witnessSetUntaken S b))
          else T.PkgSet.add (Name.Disjunct a b, Version.One)
                 (T.PkgSet.union (witnessSetUntaken S a) (witnessSetTaken S b))
      | FNeg a => witnessSetTakenNeg S a
      end
    with witnessSetTakenNeg (S : PkgSet.t) (f : Formula) : T.PkgSet.t :=
      match f with
      | FDep n vs => T.PkgSet.singleton (Name.NegDep n vs, Version.One)
      | FConj a b =>
          if negb (satisfiesb S a)
          then T.PkgSet.add (Name.Disjunct (FNeg a) (FNeg b), Version.Zero)
                 (T.PkgSet.union (witnessSetTakenNeg S a)
                    (witnessSetUntakenNeg S b))
          else T.PkgSet.add (Name.Disjunct (FNeg a) (FNeg b), Version.One)
                 (T.PkgSet.union (witnessSetUntakenNeg S a)
                    (witnessSetTakenNeg S b))
      | FDisj a b =>
          T.PkgSet.union (witnessSetTakenNeg S a) (witnessSetTakenNeg S b)
      | FNeg a => witnessSetTaken S a
      end.

    Definition coreResolution (S : PkgSet.t) (D : DepRel.t) : T.PkgSet.t :=
      T.PkgSet.union (SOpt.map embedPkg S)
        (SOet.unionMap (fun '(p, f) =>
             if PkgSet.mem p S
             then witnessSetTaken S f
             else witnessSetUntaken S f)
           D).

    Lemma witnessSetUntaken_subset_witnessSet_aux : forall S f,
        (forall p : T.Pkg.t,
            T.PkgSet.Subset (witnessSetUntaken S f) (witnessSet p f)) /\
        (forall p : T.Pkg.t,
            T.PkgSet.Subset (witnessSetUntakenNeg S f) (witnessSetNeg p f)).
    Proof.
      intros S f; induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa];
        split; intros p y; simpl.
      - intro H; exfalso; exact (SOpt.empty_in _ H).
      - destruct (depTakenb S m ws); intro H.
        + apply SOpt.singleton_in in H; subst y;
            apply SOpt.add_in; left; reflexivity.
        + exfalso; exact (SOpt.empty_in _ H).
      - intro H; apply T.PkgSet.union_spec in H; apply T.PkgSet.union_spec;
          destruct H as [H | H];
          [left; exact (proj1 IHa p _ H) | right; exact (proj1 IHb p _ H)].
      - intro H; apply T.PkgSet.union_spec in H;
          apply SOpt.add_in; right; apply SOpt.add_in; right;
          apply T.PkgSet.union_spec; destruct H as [H | H];
          [left; exact (proj2 IHa _ _ H) | right; exact (proj2 IHb _ _ H)].
      - intro H; apply T.PkgSet.union_spec in H;
          apply SOpt.add_in; right; apply SOpt.add_in; right;
          apply T.PkgSet.union_spec; destruct H as [H | H];
          [left; exact (proj1 IHa _ _ H) | right; exact (proj1 IHb _ _ H)].
      - intro H; apply T.PkgSet.union_spec in H; apply T.PkgSet.union_spec;
          destruct H as [H | H];
          [left; exact (proj2 IHa p _ H) | right; exact (proj2 IHb p _ H)].
      - exact (proj2 IHa p y).
      - exact (proj1 IHa p y).
    Qed.

    Lemma witnessSetUntaken_subset_witnessSet : forall S (p : T.Pkg.t) f,
        T.PkgSet.Subset (witnessSetUntaken S f) (witnessSet p f).
    Proof.
      intros S p f;
        exact (proj1 (witnessSetUntaken_subset_witnessSet_aux S f) p).
    Qed.

    Lemma witnessSetTaken_subset_witnessSet_aux : forall S f,
        (forall p : T.Pkg.t,
            T.PkgSet.Subset (witnessSetTaken S f) (witnessSet p f)) /\
        (forall p : T.Pkg.t,
            T.PkgSet.Subset (witnessSetTakenNeg S f) (witnessSetNeg p f)).
    Proof.
      intros S f; induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa];
        split; intros p y; simpl.
      - intro H; exfalso; exact (SOpt.empty_in _ H).
      - intro H; apply SOpt.singleton_in in H; subst y;
          apply SOpt.add_in; right; apply SOpt.singleton_in; reflexivity.
      - intro H; apply T.PkgSet.union_spec in H; apply T.PkgSet.union_spec;
          destruct H as [H | H];
          [left; exact (proj1 IHa p _ H) | right; exact (proj1 IHb p _ H)].
      - destruct (satisfiesb S a); intro H; apply SOpt.add_in in H;
          (destruct H as [H | H];
           [| apply T.PkgSet.union_spec in H; destruct H as [H | H]]).
        + subst y; apply SOpt.add_in; right; apply SOpt.add_in; left;
            reflexivity.
        + apply SOpt.add_in; right; apply SOpt.add_in; right;
            apply T.PkgSet.union_spec; left;
            exact (proj2 (witnessSetUntaken_subset_witnessSet_aux S a)
                     _ _ H).
        + apply SOpt.add_in; right; apply SOpt.add_in; right;
            apply T.PkgSet.union_spec; right; exact (proj2 IHb _ _ H).
        + subst y; apply SOpt.add_in; left; reflexivity.
        + apply SOpt.add_in; right; apply SOpt.add_in; right;
            apply T.PkgSet.union_spec; left; exact (proj2 IHa _ _ H).
        + apply SOpt.add_in; right; apply SOpt.add_in; right;
            apply T.PkgSet.union_spec; right;
            exact (proj2 (witnessSetUntaken_subset_witnessSet_aux S b)
                     _ _ H).
      - destruct (satisfiesb S a); intro H; apply SOpt.add_in in H;
          (destruct H as [H | H];
           [| apply T.PkgSet.union_spec in H; destruct H as [H | H]]).
        + subst y; apply SOpt.add_in; left; reflexivity.
        + apply SOpt.add_in; right; apply SOpt.add_in; right;
            apply T.PkgSet.union_spec; left; exact (proj1 IHa _ _ H).
        + apply SOpt.add_in; right; apply SOpt.add_in; right;
            apply T.PkgSet.union_spec; right;
            exact (proj1 (witnessSetUntaken_subset_witnessSet_aux S b)
                     _ _ H).
        + subst y; apply SOpt.add_in; right; apply SOpt.add_in; left;
            reflexivity.
        + apply SOpt.add_in; right; apply SOpt.add_in; right;
            apply T.PkgSet.union_spec; left;
            exact (proj1 (witnessSetUntaken_subset_witnessSet_aux S a)
                     _ _ H).
        + apply SOpt.add_in; right; apply SOpt.add_in; right;
            apply T.PkgSet.union_spec; right; exact (proj1 IHb _ _ H).
      - intro H; apply T.PkgSet.union_spec in H; apply T.PkgSet.union_spec;
          destruct H as [H | H];
          [left; exact (proj2 IHa p _ H) | right; exact (proj2 IHb p _ H)].
      - exact (proj2 IHa p y).
      - exact (proj1 IHa p y).
    Qed.

    Lemma witnessSetTaken_subset_witnessSet : forall S (p : T.Pkg.t) f,
        T.PkgSet.Subset (witnessSetTaken S f) (witnessSet p f).
    Proof.
      intros S p f;
        exact (proj1 (witnessSetTaken_subset_witnessSet_aux S f) p).
    Qed.

    Lemma witnessSetUntaken_negDep_det_aux : forall S f,
        (forall n vs v,
            T.PkgSet.In (Name.NegDep n vs, v) (witnessSetUntaken S f) ->
            v = Version.Zero) /\
        (forall n vs v,
            T.PkgSet.In (Name.NegDep n vs, v) (witnessSetUntakenNeg S f) ->
            v = Version.Zero).
    Proof.
      intros S f; induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa];
        split; intros n vs v; simpl.
      - intro H; exfalso; exact (SOpt.empty_in _ H).
      - destruct (depTakenb S m ws); intro H.
        + apply SOpt.singleton_in in H; congruence.
        + exfalso; exact (SOpt.empty_in _ H).
      - intro H; apply T.PkgSet.union_spec in H; destruct H as [H | H];
          [exact (proj1 IHa _ _ _ H) | exact (proj1 IHb _ _ _ H)].
      - intro H; apply T.PkgSet.union_spec in H; destruct H as [H | H];
          [exact (proj2 IHa _ _ _ H) | exact (proj2 IHb _ _ _ H)].
      - intro H; apply T.PkgSet.union_spec in H; destruct H as [H | H];
          [exact (proj1 IHa _ _ _ H) | exact (proj1 IHb _ _ _ H)].
      - intro H; apply T.PkgSet.union_spec in H; destruct H as [H | H];
          [exact (proj2 IHa _ _ _ H) | exact (proj2 IHb _ _ _ H)].
      - exact (proj2 IHa n vs v).
      - exact (proj1 IHa n vs v).
    Qed.

    Lemma witnessSetUntaken_negDep_det : forall S f n vs v,
        T.PkgSet.In (Name.NegDep n vs, v) (witnessSetUntaken S f) ->
        v = Version.Zero.
    Proof.
      intros S f; exact (proj1 (witnessSetUntaken_negDep_det_aux S f)).
    Qed.

    Lemma witnessSetUntaken_negDep_exists_aux : forall S f,
        (forall n vs v,
            T.PkgSet.In (Name.NegDep n vs, v) (witnessSetUntaken S f) ->
            exists u, VSet.In u vs /\ PkgSet.In (n, u) S) /\
        (forall n vs v,
            T.PkgSet.In (Name.NegDep n vs, v) (witnessSetUntakenNeg S f) ->
            exists u, VSet.In u vs /\ PkgSet.In (n, u) S).
    Proof.
      intros S f; induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa];
        split; intros n vs v; simpl.
      - intro H; exfalso; exact (SOpt.empty_in _ H).
      - destruct (depTakenb S m ws) eqn:E; intro H.
        + apply SOpt.singleton_in in H; injection H as -> -> _.
          apply depTakenb_iff; exact E.
        + exfalso; exact (SOpt.empty_in _ H).
      - intro H; apply T.PkgSet.union_spec in H; destruct H as [H | H];
          [exact (proj1 IHa _ _ _ H) | exact (proj1 IHb _ _ _ H)].
      - intro H; apply T.PkgSet.union_spec in H; destruct H as [H | H];
          [exact (proj2 IHa _ _ _ H) | exact (proj2 IHb _ _ _ H)].
      - intro H; apply T.PkgSet.union_spec in H; destruct H as [H | H];
          [exact (proj1 IHa _ _ _ H) | exact (proj1 IHb _ _ _ H)].
      - intro H; apply T.PkgSet.union_spec in H; destruct H as [H | H];
          [exact (proj2 IHa _ _ _ H) | exact (proj2 IHb _ _ _ H)].
      - exact (proj2 IHa n vs v).
      - exact (proj1 IHa n vs v).
    Qed.

    Lemma witnessSetUntaken_negDep_exists : forall S f n vs v,
        T.PkgSet.In (Name.NegDep n vs, v) (witnessSetUntaken S f) ->
        exists u, VSet.In u vs /\ PkgSet.In (n, u) S.
    Proof.
      intros S f; exact (proj1 (witnessSetUntaken_negDep_exists_aux S f)).
    Qed.

    Lemma witnessSetUntaken_disjunct_det_aux : forall S f,
        (forall f1 f2 v,
            T.PkgSet.In (Name.Disjunct f1 f2, v) (witnessSetUntaken S f) ->
            False) /\
        (forall f1 f2 v,
            T.PkgSet.In (Name.Disjunct f1 f2, v) (witnessSetUntakenNeg S f) ->
            False).
    Proof.
      intros S f; induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa];
        split; intros f1 f2 v; simpl.
      - intro H; exact (SOpt.empty_in _ H).
      - destruct (depTakenb S m ws); intro H.
        + apply SOpt.singleton_in in H; congruence.
        + exact (SOpt.empty_in _ H).
      - intro H; apply T.PkgSet.union_spec in H; destruct H as [H | H];
          [exact (proj1 IHa _ _ _ H) | exact (proj1 IHb _ _ _ H)].
      - intro H; apply T.PkgSet.union_spec in H; destruct H as [H | H];
          [exact (proj2 IHa _ _ _ H) | exact (proj2 IHb _ _ _ H)].
      - intro H; apply T.PkgSet.union_spec in H; destruct H as [H | H];
          [exact (proj1 IHa _ _ _ H) | exact (proj1 IHb _ _ _ H)].
      - intro H; apply T.PkgSet.union_spec in H; destruct H as [H | H];
          [exact (proj2 IHa _ _ _ H) | exact (proj2 IHb _ _ _ H)].
      - exact (proj2 IHa f1 f2 v).
      - exact (proj1 IHa f1 f2 v).
    Qed.

    Lemma witnessSetUntaken_disjunct_det : forall S f f1 f2 v,
        T.PkgSet.In (Name.Disjunct f1 f2, v) (witnessSetUntaken S f) -> False.
    Proof.
      intros S f; exact (proj1 (witnessSetUntaken_disjunct_det_aux S f)).
    Qed.

    Lemma witnessSetTaken_disjunct_det_aux : forall S f,
        (forall f1 f2 v,
            T.PkgSet.In (Name.Disjunct f1 f2, v) (witnessSetTaken S f) ->
            v = (if satisfiesb S f1 then Version.Zero else Version.One)) /\
        (forall f1 f2 v,
            T.PkgSet.In (Name.Disjunct f1 f2, v) (witnessSetTakenNeg S f) ->
            v = (if satisfiesb S f1 then Version.Zero else Version.One)).
    Proof.
      intros S f; induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa];
        split; intros f1 f2 v; simpl.
      - intro H; exfalso; exact (SOpt.empty_in _ H).
      - intro H; apply SOpt.singleton_in in H; congruence.
      - intro H; apply T.PkgSet.union_spec in H; destruct H as [H | H];
          [exact (proj1 IHa _ _ _ H) | exact (proj1 IHb _ _ _ H)].
      - destruct (satisfiesb S a) eqn:Ea; intro H;
          apply SOpt.add_in in H;
          (destruct H as [H | H];
           [| apply T.PkgSet.union_spec in H; destruct H as [H | H]]).
        + injection H as -> -> ->; simpl; rewrite Ea; reflexivity.
        + exfalso;
            exact (proj2 (witnessSetUntaken_disjunct_det_aux S a) _ _ _ H).
        + exact (proj2 IHb _ _ _ H).
        + injection H as -> -> ->; simpl; rewrite Ea; reflexivity.
        + exact (proj2 IHa _ _ _ H).
        + exfalso;
            exact (proj2 (witnessSetUntaken_disjunct_det_aux S b) _ _ _ H).
      - destruct (satisfiesb S a) eqn:Ea; intro H;
          apply SOpt.add_in in H;
          (destruct H as [H | H];
           [| apply T.PkgSet.union_spec in H; destruct H as [H | H]]).
        + injection H as -> -> ->; rewrite Ea; reflexivity.
        + exact (proj1 IHa _ _ _ H).
        + exfalso; exact (witnessSetUntaken_disjunct_det _ _ _ _ _ H).
        + injection H as -> -> ->; rewrite Ea; reflexivity.
        + exfalso; exact (witnessSetUntaken_disjunct_det _ _ _ _ _ H).
        + exact (proj1 IHb _ _ _ H).
      - intro H; apply T.PkgSet.union_spec in H; destruct H as [H | H];
          [exact (proj2 IHa _ _ _ H) | exact (proj2 IHb _ _ _ H)].
      - exact (proj2 IHa f1 f2 v).
      - exact (proj1 IHa f1 f2 v).
    Qed.

    Lemma witnessSetTaken_disjunct_det : forall S f f1 f2 v,
        T.PkgSet.In (Name.Disjunct f1 f2, v) (witnessSetTaken S f) ->
        v = (if satisfiesb S f1 then Version.Zero else Version.One).
    Proof.
      intros S f; exact (proj1 (witnessSetTaken_disjunct_det_aux S f)).
    Qed.

    Lemma witnessSetTaken_negDep_det_aux : forall S f,
        (Satisfies S f ->
         forall n vs v,
           T.PkgSet.In (Name.NegDep n vs, v) (witnessSetTaken S f) ->
           v = (if depTakenb S n vs then Version.Zero else Version.One)) /\
        (~ Satisfies S f ->
         forall n vs v,
           T.PkgSet.In (Name.NegDep n vs, v) (witnessSetTakenNeg S f) ->
           v = (if depTakenb S n vs then Version.Zero else Version.One)).
    Proof.
      intros S f; induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa];
        split; intros Hyp n vs v; simpl.
      - intro H; exfalso; exact (SOpt.empty_in _ H).
      - intro H; apply SOpt.singleton_in in H; injection H as -> -> ->.
        destruct (depTakenb S m ws) eqn:E; [| reflexivity].
        exfalso; apply Hyp, depTakenb_iff; exact E.
      - intro H; apply T.PkgSet.union_spec in H; destruct H as [H | H];
          [exact (proj1 IHa (proj1 Hyp) _ _ _ H)
          | exact (proj1 IHb (proj2 Hyp) _ _ _ H)].
      - destruct (satisfiesb S a) eqn:Ea; intro H; apply SOpt.add_in in H;
          (destruct H as [H | H];
           [congruence
           | apply T.PkgSet.union_spec in H; destruct H as [H | H]]).
        + assert (E2 : depTakenb S n vs = true).
          { apply depTakenb_iff;
              exact (proj2 (witnessSetUntaken_negDep_exists_aux S a) _ _ _ H). }
          rewrite E2;
            exact (proj2 (witnessSetUntaken_negDep_det_aux S a) _ _ _ H).
        + apply (proj2 IHb); [| exact H].
          intro Hb'; apply Hyp; split;
            [apply satisfiesb_iff; exact Ea | exact Hb'].
        + apply (proj2 IHa); [| exact H].
          apply satisfiesb_false_iff; exact Ea.
        + assert (E2 : depTakenb S n vs = true).
          { apply depTakenb_iff;
              exact (proj2 (witnessSetUntaken_negDep_exists_aux S b) _ _ _ H). }
          rewrite E2;
            exact (proj2 (witnessSetUntaken_negDep_det_aux S b) _ _ _ H).
      - destruct (satisfiesb S a) eqn:Ea; intro H; apply SOpt.add_in in H;
          (destruct H as [H | H];
           [congruence
           | apply T.PkgSet.union_spec in H; destruct H as [H | H]]).
        + apply (proj1 IHa); [apply satisfiesb_iff; exact Ea | exact H].
        + assert (E2 : depTakenb S n vs = true).
          { apply depTakenb_iff;
              exact (proj1 (witnessSetUntaken_negDep_exists_aux S b) _ _ _ H). }
          rewrite E2;
            exact (proj1 (witnessSetUntaken_negDep_det_aux S b) _ _ _ H).
        + assert (E2 : depTakenb S n vs = true).
          { apply depTakenb_iff;
              exact (proj1 (witnessSetUntaken_negDep_exists_aux S a) _ _ _ H). }
          rewrite E2;
            exact (proj1 (witnessSetUntaken_negDep_det_aux S a) _ _ _ H).
        + apply (proj1 IHb); [| exact H].
          destruct Hyp as [Ha | Hb]; [| exact Hb].
          exfalso; exact (proj1 (satisfiesb_false_iff S a) Ea Ha).
      - intro H; apply T.PkgSet.union_spec in H; destruct H as [H | H];
          [apply (proj2 IHa); [intro Ha; exact (Hyp (or_introl Ha)) | exact H]
          | apply (proj2 IHb);
              [intro Hb; exact (Hyp (or_intror Hb)) | exact H]].
      - exact (proj2 IHa Hyp n vs v).
      - exact (proj1 IHa (satisfies_double_neg S a Hyp) n vs v).
    Qed.

    Lemma witnessSetTaken_negDep_det : forall S f,
        Satisfies S f ->
        forall n vs v,
          T.PkgSet.In (Name.NegDep n vs, v) (witnessSetTaken S f) ->
          v = (if depTakenb S n vs then Version.Zero else Version.One).
    Proof. intros S f; exact (proj1 (witnessSetTaken_negDep_det_aux S f)). Qed.

    Lemma witnessSetUntaken_name_classify_aux : forall S f,
        (forall (n : Name.t) (v : Version.t),
            T.PkgSet.In (n, v) (witnessSetUntaken S f) ->
            (exists n' vs, n = Name.NegDep n' vs) \/
            (exists f1 f2, n = Name.Disjunct f1 f2)) /\
        (forall (n : Name.t) (v : Version.t),
            T.PkgSet.In (n, v) (witnessSetUntakenNeg S f) ->
            (exists n' vs, n = Name.NegDep n' vs) \/
            (exists f1 f2, n = Name.Disjunct f1 f2)).
    Proof.
      intros S f; induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa];
        split; intros n v; simpl.
      - intro H; exfalso; exact (SOpt.empty_in _ H).
      - destruct (depTakenb S m ws); intro H.
        + apply SOpt.singleton_in in H; injection H as -> _.
          left; exists m, ws; reflexivity.
        + exfalso; exact (SOpt.empty_in _ H).
      - intro H; apply T.PkgSet.union_spec in H; destruct H as [H | H];
          [exact (proj1 IHa _ _ H) | exact (proj1 IHb _ _ H)].
      - intro H; apply T.PkgSet.union_spec in H; destruct H as [H | H];
          [exact (proj2 IHa _ _ H) | exact (proj2 IHb _ _ H)].
      - intro H; apply T.PkgSet.union_spec in H; destruct H as [H | H];
          [exact (proj1 IHa _ _ H) | exact (proj1 IHb _ _ H)].
      - intro H; apply T.PkgSet.union_spec in H; destruct H as [H | H];
          [exact (proj2 IHa _ _ H) | exact (proj2 IHb _ _ H)].
      - exact (proj2 IHa n v).
      - exact (proj1 IHa n v).
    Qed.

    Lemma witnessSetUntaken_name_classify :
      forall S f (n : Name.t) (v : Version.t),
        T.PkgSet.In (n, v) (witnessSetUntaken S f) ->
        (exists n' vs, n = Name.NegDep n' vs) \/
        (exists f1 f2, n = Name.Disjunct f1 f2).
    Proof.
      intros S f; exact (proj1 (witnessSetUntaken_name_classify_aux S f)).
    Qed.

    Lemma witnessSetTaken_name_classify_aux : forall S f,
        (forall (n : Name.t) (v : Version.t),
            T.PkgSet.In (n, v) (witnessSetTaken S f) ->
            (exists n' vs, n = Name.NegDep n' vs) \/
            (exists f1 f2, n = Name.Disjunct f1 f2)) /\
        (forall (n : Name.t) (v : Version.t),
            T.PkgSet.In (n, v) (witnessSetTakenNeg S f) ->
            (exists n' vs, n = Name.NegDep n' vs) \/
            (exists f1 f2, n = Name.Disjunct f1 f2)).
    Proof.
      intros S f; induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa];
        split; intros n v; simpl.
      - intro H; exfalso; exact (SOpt.empty_in _ H).
      - intro H; apply SOpt.singleton_in in H; injection H as -> _.
        left; exists m, ws; reflexivity.
      - intro H; apply T.PkgSet.union_spec in H; destruct H as [H | H];
          [exact (proj1 IHa _ _ H) | exact (proj1 IHb _ _ H)].
      - destruct (satisfiesb S a); intro H; apply SOpt.add_in in H;
          (destruct H as [H | H];
           [injection H as -> _; right; eauto
           | apply T.PkgSet.union_spec in H; destruct H as [H | H]]).
        + exact (proj2 (witnessSetUntaken_name_classify_aux S a) _ _ H).
        + exact (proj2 IHb _ _ H).
        + exact (proj2 IHa _ _ H).
        + exact (proj2 (witnessSetUntaken_name_classify_aux S b) _ _ H).
      - destruct (satisfiesb S a); intro H; apply SOpt.add_in in H;
          (destruct H as [H | H];
           [injection H as -> _; right; eauto
           | apply T.PkgSet.union_spec in H; destruct H as [H | H]]).
        + exact (proj1 IHa _ _ H).
        + exact (proj1 (witnessSetUntaken_name_classify_aux S b) _ _ H).
        + exact (proj1 (witnessSetUntaken_name_classify_aux S a) _ _ H).
        + exact (proj1 IHb _ _ H).
      - intro H; apply T.PkgSet.union_spec in H; destruct H as [H | H];
          [exact (proj2 IHa _ _ H) | exact (proj2 IHb _ _ H)].
      - exact (proj2 IHa n v).
      - exact (proj1 IHa n v).
    Qed.

    Lemma witnessSetTaken_name_classify :
      forall S f (n : Name.t) (v : Version.t),
        T.PkgSet.In (n, v) (witnessSetTaken S f) ->
        (exists n' vs, n = Name.NegDep n' vs) \/
        (exists f1 f2, n = Name.Disjunct f1 f2).
    Proof.
      intros S f; exact (proj1 (witnessSetTaken_name_classify_aux S f)).
    Qed.

    Lemma witnessSetUntaken_not_orig : forall S f n v,
        ~ T.PkgSet.In (Name.Orig n, v) (witnessSetUntaken S f).
    Proof.
      intros S f n v H.
      destruct (witnessSetUntaken_name_classify S f _ _ H)
        as [[n' [vs E]] | [f1 [f2 E]]]; discriminate.
    Qed.

    Lemma witnessSetTaken_not_orig : forall S f n v,
        ~ T.PkgSet.In (Name.Orig n, v) (witnessSetTaken S f).
    Proof.
      intros S f n v H.
      destruct (witnessSetTaken_name_classify S f _ _ H)
        as [[n' [vs E]] | [f1 [f2 E]]]; discriminate.
    Qed.

    Lemma mem_coreResolution : forall S D (y : T.Pkg.t),
        T.PkgSet.In y (coreResolution S D) <->
        (exists p, PkgSet.In p S /\ y = embedPkg p) \/
        (exists p f, DepRel.In (p, f) D /\
           T.PkgSet.In y (if PkgSet.mem p S
                          then witnessSetTaken S f
                          else witnessSetUntaken S f)).
    Proof.
      intros S D y; unfold coreResolution.
      rewrite T.PkgSet.union_spec, SOpt.mem_map, SOet.mem_unionMap.
      split.
      - intros [H | [[q g] [He Hy]]]; [left; exact H |].
        right; exists q, g; split; [exact He | exact Hy].
      - intros [H | [q [g [Hd Hy]]]]; [left; exact H |].
        right; exists (q, g); split; [exact Hd | exact Hy].
    Qed.

    Lemma witnessSet_subset_coreResolution : forall S D p f,
        DepRel.In (p, f) D ->
        T.PkgSet.Subset
          (if PkgSet.mem p S
           then witnessSetTaken S f
           else witnessSetUntaken S f)
          (coreResolution S D).
    Proof.
      intros S D p f Hd y Hy; apply mem_coreResolution; right.
      exists p, f; split; [exact Hd | exact Hy].
    Qed.

    Lemma witnessSetTaken_disj_zero_mono_aux : forall S f,
        (forall f1 f2,
            T.PkgSet.In (Name.Disjunct f1 f2, Version.Zero)
              (witnessSetTaken S f) ->
            Satisfies S f1 /\
            T.PkgSet.Subset (witnessSetTaken S f1) (witnessSetTaken S f) /\
            T.PkgSet.Subset (witnessSetUntaken S f2) (witnessSetTaken S f)) /\
        (forall f1 f2,
            T.PkgSet.In (Name.Disjunct f1 f2, Version.Zero)
              (witnessSetTakenNeg S f) ->
            Satisfies S f1 /\
            T.PkgSet.Subset (witnessSetTaken S f1) (witnessSetTakenNeg S f) /\
            T.PkgSet.Subset (witnessSetUntaken S f2) (witnessSetTakenNeg S f)).
    Proof.
      intros S f; induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa];
        split; intros f1 f2; simpl.
      - intro H; exfalso; exact (SOpt.empty_in _ H).
      - intro H; apply SOpt.singleton_in in H; congruence.
      - intro H; apply T.PkgSet.union_spec in H; destruct H as [H | H].
        + destruct (proj1 IHa f1 f2 H) as (Hs & H1 & H2).
          split; [exact Hs |]; split; intros y Hy;
            apply T.PkgSet.union_spec; left; [apply H1 | apply H2]; exact Hy.
        + destruct (proj1 IHb f1 f2 H) as (Hs & H1 & H2).
          split; [exact Hs |]; split; intros y Hy;
            apply T.PkgSet.union_spec; right; [apply H1 | apply H2]; exact Hy.
      - destruct (satisfiesb S a) eqn:Ea; intro H; apply SOpt.add_in in H;
          (destruct H as [H | H];
           [| apply T.PkgSet.union_spec in H; destruct H as [H | H]]).
        + congruence.
        + exfalso;
            exact (proj2 (witnessSetUntaken_disjunct_det_aux S a) _ _ _ H).
        + destruct (proj2 IHb f1 f2 H) as (Hs & H1 & H2).
          split; [exact Hs |]; split; intros y Hy;
            apply SOpt.add_in; right; apply T.PkgSet.union_spec; right;
            [apply H1 | apply H2]; exact Hy.
        + injection H as -> ->.
          split; [apply satisfiesb_false_iff; exact Ea |].
          split; intros y Hy; apply SOpt.add_in; right;
            apply T.PkgSet.union_spec; [left | right]; exact Hy.
        + destruct (proj2 IHa f1 f2 H) as (Hs & H1 & H2).
          split; [exact Hs |]; split; intros y Hy;
            apply SOpt.add_in; right; apply T.PkgSet.union_spec; left;
            [apply H1 | apply H2]; exact Hy.
        + exfalso;
            exact (proj2 (witnessSetUntaken_disjunct_det_aux S b) _ _ _ H).
      - destruct (satisfiesb S a) eqn:Ea; intro H; apply SOpt.add_in in H;
          (destruct H as [H | H];
           [| apply T.PkgSet.union_spec in H; destruct H as [H | H]]).
        + injection H as -> ->.
          split; [apply satisfiesb_iff; exact Ea |].
          split; intros y Hy; apply SOpt.add_in; right;
            apply T.PkgSet.union_spec; [left | right]; exact Hy.
        + destruct (proj1 IHa f1 f2 H) as (Hs & H1 & H2).
          split; [exact Hs |]; split; intros y Hy;
            apply SOpt.add_in; right; apply T.PkgSet.union_spec; left;
            [apply H1 | apply H2]; exact Hy.
        + exfalso; exact (witnessSetUntaken_disjunct_det _ _ _ _ _ H).
        + congruence.
        + exfalso; exact (witnessSetUntaken_disjunct_det _ _ _ _ _ H).
        + destruct (proj1 IHb f1 f2 H) as (Hs & H1 & H2).
          split; [exact Hs |]; split; intros y Hy;
            apply SOpt.add_in; right; apply T.PkgSet.union_spec; right;
            [apply H1 | apply H2]; exact Hy.
      - intro H; apply T.PkgSet.union_spec in H; destruct H as [H | H].
        + destruct (proj2 IHa f1 f2 H) as (Hs & H1 & H2).
          split; [exact Hs |]; split; intros y Hy;
            apply T.PkgSet.union_spec; left; [apply H1 | apply H2]; exact Hy.
        + destruct (proj2 IHb f1 f2 H) as (Hs & H1 & H2).
          split; [exact Hs |]; split; intros y Hy;
            apply T.PkgSet.union_spec; right; [apply H1 | apply H2]; exact Hy.
      - exact (proj2 IHa f1 f2).
      - exact (proj1 IHa f1 f2).
    Qed.

    Lemma witnessSetTaken_disj_one_mono_aux : forall S f,
        (Satisfies S f ->
         forall f1 f2,
           T.PkgSet.In (Name.Disjunct f1 f2, Version.One)
             (witnessSetTaken S f) ->
           Satisfies S f2 /\
           T.PkgSet.Subset (witnessSetUntaken S f1) (witnessSetTaken S f) /\
           T.PkgSet.Subset (witnessSetTaken S f2) (witnessSetTaken S f)) /\
        (~ Satisfies S f ->
         forall f1 f2,
           T.PkgSet.In (Name.Disjunct f1 f2, Version.One)
             (witnessSetTakenNeg S f) ->
           Satisfies S f2 /\
           T.PkgSet.Subset (witnessSetUntaken S f1) (witnessSetTakenNeg S f) /\
           T.PkgSet.Subset (witnessSetTaken S f2) (witnessSetTakenNeg S f)).
    Proof.
      intros S f; induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa];
        split; intros Hyp f1 f2; simpl.
      - intro H; exfalso; exact (SOpt.empty_in _ H).
      - intro H; apply SOpt.singleton_in in H; congruence.
      - intro H; apply T.PkgSet.union_spec in H; destruct H as [H | H].
        + destruct (proj1 IHa (proj1 Hyp) f1 f2 H) as (Hs & H1 & H2).
          split; [exact Hs |]; split; intros y Hy;
            apply T.PkgSet.union_spec; left; [apply H1 | apply H2]; exact Hy.
        + destruct (proj1 IHb (proj2 Hyp) f1 f2 H) as (Hs & H1 & H2).
          split; [exact Hs |]; split; intros y Hy;
            apply T.PkgSet.union_spec; right; [apply H1 | apply H2]; exact Hy.
      - destruct (satisfiesb S a) eqn:Ea; intro H; apply SOpt.add_in in H;
          (destruct H as [H | H];
           [| apply T.PkgSet.union_spec in H; destruct H as [H | H]]).
        + injection H as -> ->.
          split.
          { intro Hb'; apply Hyp; split;
              [apply satisfiesb_iff; exact Ea | exact Hb']. }
          split; intros y Hy; apply SOpt.add_in; right;
            apply T.PkgSet.union_spec; [left | right]; exact Hy.
        + exfalso;
            exact (proj2 (witnessSetUntaken_disjunct_det_aux S a) _ _ _ H).
        + assert (Hnb : ~ Satisfies S b).
          { intro Hb'; apply Hyp; split;
              [apply satisfiesb_iff; exact Ea | exact Hb']. }
          destruct (proj2 IHb Hnb f1 f2 H) as (Hs & H1 & H2).
          split; [exact Hs |]; split; intros y Hy;
            apply SOpt.add_in; right; apply T.PkgSet.union_spec; right;
            [apply H1 | apply H2]; exact Hy.
        + congruence.
        + destruct (proj2 IHa (proj1 (satisfiesb_false_iff S a) Ea) f1 f2 H)
            as (Hs & H1 & H2).
          split; [exact Hs |]; split; intros y Hy;
            apply SOpt.add_in; right; apply T.PkgSet.union_spec; left;
            [apply H1 | apply H2]; exact Hy.
        + exfalso;
            exact (proj2 (witnessSetUntaken_disjunct_det_aux S b) _ _ _ H).
      - destruct (satisfiesb S a) eqn:Ea; intro H; apply SOpt.add_in in H;
          (destruct H as [H | H];
           [| apply T.PkgSet.union_spec in H; destruct H as [H | H]]).
        + congruence.
        + destruct (proj1 IHa (proj1 (satisfiesb_iff S a) Ea) f1 f2 H)
            as (Hs & H1 & H2).
          split; [exact Hs |]; split; intros y Hy;
            apply SOpt.add_in; right; apply T.PkgSet.union_spec; left;
            [apply H1 | apply H2]; exact Hy.
        + exfalso; exact (witnessSetUntaken_disjunct_det _ _ _ _ _ H).
        + injection H as -> ->.
          assert (Hb : Satisfies S b).
          { destruct Hyp as [Ha | Hb]; [| exact Hb].
            exfalso; exact (proj1 (satisfiesb_false_iff S a) Ea Ha). }
          split; [exact Hb |].
          split; intros y Hy; apply SOpt.add_in; right;
            apply T.PkgSet.union_spec; [left | right]; exact Hy.
        + exfalso; exact (witnessSetUntaken_disjunct_det _ _ _ _ _ H).
        + assert (Hb : Satisfies S b).
          { destruct Hyp as [Ha | Hb]; [| exact Hb].
            exfalso; exact (proj1 (satisfiesb_false_iff S a) Ea Ha). }
          destruct (proj1 IHb Hb f1 f2 H) as (Hs & H1 & H2).
          split; [exact Hs |]; split; intros y Hy;
            apply SOpt.add_in; right; apply T.PkgSet.union_spec; right;
            [apply H1 | apply H2]; exact Hy.
      - intro H; apply T.PkgSet.union_spec in H; destruct H as [H | H].
        + destruct (proj2 IHa (fun Ha => Hyp (or_introl Ha)) f1 f2 H)
            as (Hs & H1 & H2).
          split; [exact Hs |]; split; intros y Hy;
            apply T.PkgSet.union_spec; left; [apply H1 | apply H2]; exact Hy.
        + destruct (proj2 IHb (fun Hb => Hyp (or_intror Hb)) f1 f2 H)
            as (Hs & H1 & H2).
          split; [exact Hs |]; split; intros y Hy;
            apply T.PkgSet.union_spec; right; [apply H1 | apply H2]; exact Hy.
      - exact (proj2 IHa Hyp f1 f2).
      - exact (proj1 IHa (satisfies_double_neg S a Hyp) f1 f2).
    Qed.

    Lemma coreResolution_disj_zero : forall S D f1 f2,
        T.PkgSet.In (Name.Disjunct f1 f2, Version.Zero)
          (coreResolution S D) ->
        Satisfies S f1 /\
        T.PkgSet.Subset (witnessSetTaken S f1) (coreResolution S D) /\
        T.PkgSet.Subset (witnessSetUntaken S f2) (coreResolution S D).
    Proof.
      intros S D f1 f2 H; apply mem_coreResolution in H.
      destruct H as [[p [_ Hp]] | [p [g [Hd Hw]]]].
      - destruct p as [pn pv]; unfold embedPkg in Hp; discriminate.
      - pose proof (witnessSet_subset_coreResolution S D p g Hd) as Hsub.
        revert Hw Hsub; destruct (PkgSet.mem p S); intros Hw Hsub.
        + destruct (proj1 (witnessSetTaken_disj_zero_mono_aux S g) f1 f2 Hw)
            as (Hs & H1 & H2).
          split; [exact Hs |]; split; intros y Hy; apply Hsub;
            [apply H1 | apply H2]; exact Hy.
        + exfalso; exact (witnessSetUntaken_disjunct_det _ _ _ _ _ Hw).
    Qed.

    Lemma coreResolution_disj_one : forall S D f1 f2,
        (forall p, PkgSet.In p S ->
         forall f, DepRel.In (p, f) D -> Satisfies S f) ->
        T.PkgSet.In (Name.Disjunct f1 f2, Version.One)
          (coreResolution S D) ->
        Satisfies S f2 /\
        T.PkgSet.Subset (witnessSetUntaken S f1) (coreResolution S D) /\
        T.PkgSet.Subset (witnessSetTaken S f2) (coreResolution S D).
    Proof.
      intros S D f1 f2 Hclo H; apply mem_coreResolution in H.
      destruct H as [[p [_ Hp]] | [p [g [Hd Hw]]]].
      - destruct p as [pn pv]; unfold embedPkg in Hp; discriminate.
      - pose proof (witnessSet_subset_coreResolution S D p g Hd) as Hsub.
        revert Hw Hsub; destruct (PkgSet.mem p S) eqn:Ep; intros Hw Hsub.
        + assert (Hsat : Satisfies S g).
          { apply (Hclo p); [apply PkgSet.mem_spec; exact Ep | exact Hd]. }
          destruct (proj1 (witnessSetTaken_disj_one_mono_aux S g) Hsat f1 f2 Hw)
            as (Hs & H1 & H2).
          split; [exact Hs |]; split; intros y Hy; apply Hsub;
            [apply H1 | apply H2]; exact Hy.
        + exfalso; exact (witnessSetUntaken_disjunct_det _ _ _ _ _ Hw).
    Qed.

    Lemma encodeNNF_dep_closure_aux :
      forall (S : PkgSet.t) (w : T.PkgSet.t),
        (forall p, PkgSet.In p S -> T.PkgSet.In (embedPkg p) w) ->
        (forall n v, T.PkgSet.In (Name.Orig n, v) w ->
           exists p, PkgSet.In p S /\ embedPkg p = (Name.Orig n, v)) ->
        (forall f1 f2, T.PkgSet.In (Name.Disjunct f1 f2, Version.Zero) w ->
           Satisfies S f1 /\
           T.PkgSet.Subset (witnessSetTaken S f1) w /\
           T.PkgSet.Subset (witnessSetUntaken S f2) w) ->
        (forall f1 f2, T.PkgSet.In (Name.Disjunct f1 f2, Version.One) w ->
           Satisfies S f2 /\
           T.PkgSet.Subset (witnessSetUntaken S f1) w /\
           T.PkgSet.Subset (witnessSetTaken S f2) w) ->
        forall f : Formula,
          (forall q0 : T.Pkg.t,
              (~ T.PkgSet.In q0 w /\
               T.PkgSet.Subset (witnessSetUntaken S f) w) \/
              (Satisfies S f /\
               T.PkgSet.Subset (witnessSetTaken S f) w) ->
              forall (q : T.Pkg.t) (m : NameOT.t) (ws : T.VSet.t),
                T.DepRel.In (q, (m, ws)) (encodeNNF q0 f) ->
                T.PkgSet.In q w ->
                exists v, T.VSet.In v ws /\ T.PkgSet.In (m, v) w) /\
          (forall q0 : T.Pkg.t,
              (~ T.PkgSet.In q0 w /\
               T.PkgSet.Subset (witnessSetUntakenNeg S f) w) \/
              (~ Satisfies S f /\
               T.PkgSet.Subset (witnessSetTakenNeg S f) w) ->
              forall (q : T.Pkg.t) (m : NameOT.t) (ws : T.VSet.t),
                T.DepRel.In (q, (m, ws)) (encodeNNFneg q0 f) ->
                T.PkgSet.In q w ->
                exists v, T.VSet.In v ws /\ T.PkgSet.In (m, v) w).
    Proof.
      intros S w Hemb Horig Hdz Hdo f.
      induction f as [n vs | a IHa b IHb | a IHa b IHb | a IHa];
        split; intros q0 Hwit q m ws Henc Hqw.
      - apply SOed.singleton_in in Henc; injection Henc as -> -> ->.
        destruct Hwit as [[Hq0 _] | [Hsat _]].
        + exfalso; exact (Hq0 Hqw).
        + destruct Hsat as [u [Hu HuS]].
          exists (Version.Orig u); split.
          * unfold embedVS; apply SOvv.mem_map;
              exists u; split; [exact Hu | reflexivity].
          * exact (Hemb (n, u) HuS).
      - apply SOed.add_in in Henc; destruct Henc as [He | He].
        + injection He as -> -> ->.
          destruct Hwit as [[Hq0 _] | [_ Hsub]].
          * exfalso; exact (Hq0 Hqw).
          * exists Version.One; split; [apply SOvv.singleton_in; reflexivity |].
            apply Hsub, SOpt.singleton_in; reflexivity.
        + apply SOvd.mem_map in He; destruct He as [u [Hu He]];
            injection He as -> -> ->.
          destruct (Horig n (Version.Orig u) Hqw) as [[pn pv] [HpS Hpe]].
          unfold embedPkg in Hpe; simpl in Hpe; injection Hpe as -> ->.
          destruct Hwit as [[_ Hsub] | [Hns _]].
          * assert (E : depTakenb S n vs = true).
            { apply depTakenb_iff; exists u; split; assumption. }
            exists Version.Zero;
              split; [apply SOvv.singleton_in; reflexivity |].
            apply Hsub.
            change (T.PkgSet.In (Name.NegDep n vs, Version.Zero)
                      (if depTakenb S n vs
                       then T.PkgSet.singleton (Name.NegDep n vs, Version.Zero)
                       else T.PkgSet.empty)).
            rewrite E; apply SOpt.singleton_in; reflexivity.
          * exfalso; apply Hns; exists u; split; assumption.
      - apply T.DepRel.union_spec in Henc; destruct Henc as [He | He].
        + refine (proj1 IHa q0 _ q m ws He Hqw).
          destruct Hwit as [[Hq0 Hsub] | [Hsat Hsub]].
          * left; split; [exact Hq0 |].
            intros y Hy; apply Hsub, T.PkgSet.union_spec; left; exact Hy.
          * right; split; [exact (proj1 Hsat) |].
            intros y Hy; apply Hsub, T.PkgSet.union_spec; left; exact Hy.
        + refine (proj1 IHb q0 _ q m ws He Hqw).
          destruct Hwit as [[Hq0 Hsub] | [Hsat Hsub]].
          * left; split; [exact Hq0 |].
            intros y Hy; apply Hsub, T.PkgSet.union_spec; right; exact Hy.
          * right; split; [exact (proj2 Hsat) |].
            intros y Hy; apply Hsub, T.PkgSet.union_spec; right; exact Hy.
      - apply SOed.add_in in Henc; destruct Henc as [He | He].
        + injection He as -> -> ->.
          destruct Hwit as [[Hq0 _] | [_ Hsub]].
          * exfalso; exact (Hq0 Hqw).
          * destruct (satisfiesb S a) eqn:Ea.
            -- exists Version.One;
               split; [apply mem_zeroOne; right; reflexivity |].
               apply Hsub; simpl; rewrite Ea;
                 apply SOpt.add_in; left; reflexivity.
            -- exists Version.Zero;
               split; [apply mem_zeroOne; left; reflexivity |].
               apply Hsub; simpl; rewrite Ea;
                 apply SOpt.add_in; left; reflexivity.
        + apply T.DepRel.union_spec in He; destruct He as [He | He].
          * refine (proj2 IHa (Name.Disjunct (FNeg a) (FNeg b), Version.Zero)
                      _ q m ws He Hqw).
            destruct (T.PkgSet.mem
                        (Name.Disjunct (FNeg a) (FNeg b), Version.Zero) w)
              eqn:EM.
            -- apply T.PkgSet.mem_spec in EM.
               destruct (Hdz _ _ EM) as (HsF & HsubT & _).
               right; split; [exact HsF | exact HsubT].
            -- left; split.
               { intro Hin; apply T.PkgSet.mem_spec in Hin; congruence. }
               destruct Hwit as [[_ Hsub] | [Hns Hsub]].
               ++ intros y Hy; apply Hsub, T.PkgSet.union_spec; left; exact Hy.
               ++ destruct (satisfiesb S a) eqn:Ea.
                  ** intros y Hy; apply Hsub; simpl; rewrite Ea;
                       apply SOpt.add_in; right;
                       apply T.PkgSet.union_spec; left; exact Hy.
                  ** exfalso.
                     assert (Hin : T.PkgSet.In
                         (Name.Disjunct (FNeg a) (FNeg b), Version.Zero) w).
                     { apply Hsub; simpl; rewrite Ea;
                         apply SOpt.add_in; left; reflexivity. }
                     apply T.PkgSet.mem_spec in Hin; congruence.
          * refine (proj2 IHb (Name.Disjunct (FNeg a) (FNeg b), Version.One)
                      _ q m ws He Hqw).
            destruct (T.PkgSet.mem
                        (Name.Disjunct (FNeg a) (FNeg b), Version.One) w)
              eqn:EM.
            -- apply T.PkgSet.mem_spec in EM.
               destruct (Hdo _ _ EM) as (HsF & _ & HsubT).
               right; split; [exact HsF | exact HsubT].
            -- left; split.
               { intro Hin; apply T.PkgSet.mem_spec in Hin; congruence. }
               destruct Hwit as [[_ Hsub] | [Hns Hsub]].
               ++ intros y Hy; apply Hsub, T.PkgSet.union_spec; right; exact Hy.
               ++ destruct (satisfiesb S a) eqn:Ea.
                  ** exfalso.
                     assert (Hin : T.PkgSet.In
                         (Name.Disjunct (FNeg a) (FNeg b), Version.One) w).
                     { apply Hsub; simpl; rewrite Ea;
                         apply SOpt.add_in; left; reflexivity. }
                     apply T.PkgSet.mem_spec in Hin; congruence.
                  ** intros y Hy; apply Hsub; simpl; rewrite Ea;
                       apply SOpt.add_in; right;
                       apply T.PkgSet.union_spec; right; exact Hy.
      - apply SOed.add_in in Henc; destruct Henc as [He | He].
        + injection He as -> -> ->.
          destruct Hwit as [[Hq0 _] | [_ Hsub]].
          * exfalso; exact (Hq0 Hqw).
          * destruct (satisfiesb S a) eqn:Ea.
            -- exists Version.Zero;
               split; [apply mem_zeroOne; left; reflexivity |].
               apply Hsub; simpl; rewrite Ea;
                 apply SOpt.add_in; left; reflexivity.
            -- exists Version.One;
               split; [apply mem_zeroOne; right; reflexivity |].
               apply Hsub; simpl; rewrite Ea;
                 apply SOpt.add_in; left; reflexivity.
        + apply T.DepRel.union_spec in He; destruct He as [He | He].
          * refine (proj1 IHa (Name.Disjunct a b, Version.Zero)
                      _ q m ws He Hqw).
            destruct (T.PkgSet.mem (Name.Disjunct a b, Version.Zero) w) eqn:EM.
            -- apply T.PkgSet.mem_spec in EM.
               destruct (Hdz _ _ EM) as (HsF & HsubT & _).
               right; split; [exact HsF | exact HsubT].
            -- left; split.
               { intro Hin; apply T.PkgSet.mem_spec in Hin; congruence. }
               destruct Hwit as [[_ Hsub] | [Hsat Hsub]].
               ++ intros y Hy; apply Hsub, T.PkgSet.union_spec; left; exact Hy.
               ++ destruct (satisfiesb S a) eqn:Ea.
                  ** exfalso.
                     assert
                       (Hin : T.PkgSet.In (Name.Disjunct a b, Version.Zero) w).
                     { apply Hsub; simpl; rewrite Ea;
                         apply SOpt.add_in; left; reflexivity. }
                     apply T.PkgSet.mem_spec in Hin; congruence.
                  ** intros y Hy; apply Hsub; simpl; rewrite Ea;
                       apply SOpt.add_in; right;
                       apply T.PkgSet.union_spec; left; exact Hy.
          * refine (proj1 IHb (Name.Disjunct a b, Version.One) _ q m ws He Hqw).
            destruct (T.PkgSet.mem (Name.Disjunct a b, Version.One) w) eqn:EM.
            -- apply T.PkgSet.mem_spec in EM.
               destruct (Hdo _ _ EM) as (HsF & _ & HsubT).
               right; split; [exact HsF | exact HsubT].
            -- left; split.
               { intro Hin; apply T.PkgSet.mem_spec in Hin; congruence. }
               destruct Hwit as [[_ Hsub] | [Hsat Hsub]].
               ++ intros y Hy; apply Hsub, T.PkgSet.union_spec; right; exact Hy.
               ++ destruct (satisfiesb S a) eqn:Ea.
                  ** intros y Hy; apply Hsub; simpl; rewrite Ea;
                       apply SOpt.add_in; right;
                       apply T.PkgSet.union_spec; right; exact Hy.
                  ** exfalso.
                     assert
                       (Hin : T.PkgSet.In (Name.Disjunct a b, Version.One) w).
                     { apply Hsub; simpl; rewrite Ea;
                         apply SOpt.add_in; left; reflexivity. }
                     apply T.PkgSet.mem_spec in Hin; congruence.
      - apply T.DepRel.union_spec in Henc; destruct Henc as [He | He].
        + refine (proj2 IHa q0 _ q m ws He Hqw).
          destruct Hwit as [[Hq0 Hsub] | [Hns Hsub]].
          * left; split; [exact Hq0 |].
            intros y Hy; apply Hsub, T.PkgSet.union_spec; left; exact Hy.
          * right; split; [intro Ha; exact (Hns (or_introl Ha)) |].
            intros y Hy; apply Hsub, T.PkgSet.union_spec; left; exact Hy.
        + refine (proj2 IHb q0 _ q m ws He Hqw).
          destruct Hwit as [[Hq0 Hsub] | [Hns Hsub]].
          * left; split; [exact Hq0 |].
            intros y Hy; apply Hsub, T.PkgSet.union_spec; right; exact Hy.
          * right; split; [intro Hb; exact (Hns (or_intror Hb)) |].
            intros y Hy; apply Hsub, T.PkgSet.union_spec; right; exact Hy.
      - exact (proj2 IHa q0 Hwit q m ws Henc Hqw).
      - destruct Hwit as [[Hq0 Hsub] | [Hnn Hsub]].
        + exact (proj1 IHa q0 (or_introl (conj Hq0 Hsub)) q m ws Henc Hqw).
        + exact (proj1 IHa q0
                   (or_intror (conj (satisfies_double_neg S a Hnn) Hsub))
                   q m ws Henc Hqw).
    Qed.

    Theorem package_formula_completeness :
      forall (R : PkgSet.t) (D : DepRel.t) (r : Pkg.t) (S : PkgSet.t),
        IsResolution R D r S ->
        T.IsResolution (reduceReal R D) (reduceDeps D) (embedPkg r)
          (coreResolution S D).
    Proof.
      intros R D r S Hres; destruct Hres as [Hsub Hroot Hclo Huniq].
      assert (Hemb : forall p, PkgSet.In p S ->
          T.PkgSet.In (embedPkg p) (coreResolution S D)).
      { intros p Hp; apply mem_coreResolution; left.
        exists p; split; [exact Hp | reflexivity]. }
      assert (Horig : forall n v,
          T.PkgSet.In (Name.Orig n, v) (coreResolution S D) ->
          exists p, PkgSet.In p S /\ embedPkg p = (Name.Orig n, v)).
      { intros n v Hv; apply mem_coreResolution in Hv.
        destruct Hv as [[p [Hp Hpe]] | [p [g [Hd Hw]]]].
        - exists p; split; [exact Hp | symmetry; exact Hpe].
        - exfalso; revert Hw; destruct (PkgSet.mem p S); intro Hw;
            [exact (witnessSetTaken_not_orig _ _ _ _ Hw)
            | exact (witnessSetUntaken_not_orig _ _ _ _ Hw)]. }
      assert (Hdz := fun f1 f2 => coreResolution_disj_zero S D f1 f2).
      assert (Hdo := fun f1 f2 => coreResolution_disj_one S D f1 f2 Hclo).
      constructor.
      - intros y Hy; apply mem_coreResolution in Hy.
        apply mem_reduceReal.
        destruct Hy as [[p [Hp ->]] | [p [g [Hd Hw]]]].
        + left; exists p; split; [apply Hsub; exact Hp | reflexivity].
        + right; exists p, g; split; [exact Hd |].
          revert Hw; destruct (PkgSet.mem p S); intro Hw;
            [exact (witnessSetTaken_subset_witnessSet
                      S (embedPkg p) g _ Hw)
            | exact (witnessSetUntaken_subset_witnessSet
                       S (embedPkg p) g _ Hw)].
      - exact (Hemb r Hroot).
      - intros q Hq m vs Hd.
        apply mem_reduceDeps in Hd; destruct Hd as [p [g [Hpg Henc]]].
        destruct (PkgSet.mem p S) eqn:Ep.
        + refine (proj1 (encodeNNF_dep_closure_aux S _ Hemb Horig Hdz Hdo g)
            (embedPkg p) _ q m vs Henc Hq).
          right; split.
          * apply (Hclo p); [apply PkgSet.mem_spec; exact Ep | exact Hpg].
          * pose proof (witnessSet_subset_coreResolution S D p g Hpg) as Hs;
              rewrite Ep in Hs; exact Hs.
        + refine (proj1 (encodeNNF_dep_closure_aux S _ Hemb Horig Hdz Hdo g)
            (embedPkg p) _ q m vs Henc Hq).
          left; split.
          * intro Hin; destruct p as [pn pv].
            destruct (Horig pn (Version.Orig pv) Hin) as [[qn qv] [HqS Hqe]].
            unfold embedPkg in Hqe; simpl in Hqe; injection Hqe as -> ->.
            apply PkgSet.mem_spec in HqS; congruence.
          * pose proof (witnessSet_subset_coreResolution S D p g Hpg) as Hs;
              rewrite Ep in Hs; exact Hs.
      - intros n v v' Hv Hv'.
        apply mem_coreResolution in Hv, Hv'.
        destruct Hv as [[p1 [Hp1 He1]] | [p1 [g1 [Hd1 Hw1]]]];
          destruct Hv' as [[p2 [Hp2 He2]] | [p2 [g2 [Hd2 Hw2]]]].
        + destruct p1 as [n1 w1]; destruct p2 as [n2 w2].
          unfold embedPkg in He1, He2; simpl in He1, He2.
          injection He1 as -> ->; injection He2 as -> ->.
          f_equal; exact (Huniq _ _ _ Hp1 Hp2).
        + destruct p1 as [n1 w1]; unfold embedPkg in He1; simpl in He1;
            injection He1 as -> ->.
          exfalso; revert Hw2; destruct (PkgSet.mem p2 S); intro Hw2;
            [exact (witnessSetTaken_not_orig _ _ _ _ Hw2)
            | exact (witnessSetUntaken_not_orig _ _ _ _ Hw2)].
        + destruct p2 as [n2 w2]; unfold embedPkg in He2; simpl in He2;
            injection He2 as -> ->.
          exfalso; revert Hw1; destruct (PkgSet.mem p1 S); intro Hw1;
            [exact (witnessSetTaken_not_orig _ _ _ _ Hw1)
            | exact (witnessSetUntaken_not_orig _ _ _ _ Hw1)].
        + destruct n as [n0 | f1 f2 | n0 vs0].
          * exfalso; revert Hw1; destruct (PkgSet.mem p1 S); intro Hw1;
              [exact (witnessSetTaken_not_orig _ _ _ _ Hw1)
              | exact (witnessSetUntaken_not_orig _ _ _ _ Hw1)].
          * assert (G : forall p g v0, DepRel.In (p, g) D ->
                T.PkgSet.In (Name.Disjunct f1 f2, v0)
                  (if PkgSet.mem p S then witnessSetTaken S g
                   else witnessSetUntaken S g) ->
                v0 = (if satisfiesb S f1 then Version.Zero else Version.One)).
            { intros p g v0 _ Hw; revert Hw;
                destruct (PkgSet.mem p S); intro Hw.
              - exact (witnessSetTaken_disjunct_det _ _ _ _ _ Hw).
              - exfalso;
                  exact (witnessSetUntaken_disjunct_det _ _ _ _ _ Hw). }
            rewrite (G _ _ _ Hd1 Hw1), (G _ _ _ Hd2 Hw2); reflexivity.
          * assert (G : forall p g v0, DepRel.In (p, g) D ->
                T.PkgSet.In (Name.NegDep n0 vs0, v0)
                  (if PkgSet.mem p S then witnessSetTaken S g
                   else witnessSetUntaken S g) ->
                v0 =
                  (if depTakenb S n0 vs0 then Version.Zero else Version.One)).
            { intros p g v0 Hd Hw; revert Hw;
                destruct (PkgSet.mem p S) eqn:Ep; intro Hw.
              - apply (witnessSetTaken_negDep_det S g); [| exact Hw].
                apply (Hclo p); [apply PkgSet.mem_spec; exact Ep | exact Hd].
              - assert (E : depTakenb S n0 vs0 = true).
                { apply depTakenb_iff;
                    exact (witnessSetUntaken_negDep_exists _ _ _ _ _ Hw). }
                rewrite E;
                  exact (witnessSetUntaken_negDep_det _ _ _ _ _ Hw). }
            rewrite (G _ _ _ Hd1 Hw1), (G _ _ _ Hd2 Hw2); reflexivity.
    Qed.
  End Reduction.
End PackageFormula.
