From Stdlib Require Import MSets List.
From PackageCalculus Require Import Prelude Core Versions PackageFormula.

Create HintDb cmp_varf.
Create Rewrite HintDb cmp_varf.

Module VariableFormula (N V : UsualOrderedType)
    (X : FiniteUsualOrderedType) (Y : UsualOrderedType).
  Module C := Core N V.
  Module Pkg := C.Pkg.
  Module PkgSet := C.PkgSet.
  Module VSet := C.VSet.

  Inductive Formula : Type :=
  | FDep (m : N.t) (vs : VSet.t)
  | FConj (f1 f2 : Formula)
  | FDisj (f1 f2 : Formula)
  | FNeg (f : Formula)
  | FVarCmp (x : X.t) (op : CmpOp) (y : Y.t).

  Definition opEvalY (op : CmpOp) (y' y : Y.t) : bool :=
    cmpOpEvalBy Y.compare op y' y.

  Fixpoint Satisfies (S : PkgSet.t) (sigma : X.t -> Y.t) (f : Formula) : Prop :=
    match f with
    | FDep m vs => exists v, VSet.In v vs /\ PkgSet.In (m, v) S
    | FConj f1 f2 => Satisfies S sigma f1 /\ Satisfies S sigma f2
    | FDisj f1 f2 => Satisfies S sigma f1 \/ Satisfies S sigma f2
    | FNeg f1 => ~ Satisfies S sigma f1
    | FVarCmp x op y => opEvalY op (sigma x) y = true
    end.

  Fixpoint satisfiesb (S : PkgSet.t) (sigma : X.t -> Y.t) (f : Formula) :
      bool :=
    match f with
    | FDep m vs => VSet.exists_ (fun v => PkgSet.mem (m, v) S) vs
    | FConj f1 f2 => andb (satisfiesb S sigma f1) (satisfiesb S sigma f2)
    | FDisj f1 f2 => orb (satisfiesb S sigma f1) (satisfiesb S sigma f2)
    | FNeg f1 => negb (satisfiesb S sigma f1)
    | FVarCmp x op y => opEvalY op (sigma x) y
    end.

  Lemma satisfiesb_iff : forall S sigma f,
      satisfiesb S sigma f = true <-> Satisfies S sigma f.
  Proof.
    intros S sigma f;
      induction f as [m vs | a IHa b IHb | a IHa b IHb | a IHa | x op y];
      simpl.
    - rewrite VSet.exists_spec'.
      split; intros [v [Hv Hm]]; exists v; split; try assumption;
        apply PkgSet.mem_spec; assumption.
    - rewrite Bool.andb_true_iff, IHa, IHb; reflexivity.
    - rewrite Bool.orb_true_iff, IHa, IHb; reflexivity.
    - rewrite Bool.negb_true_iff; split.
      + intros E Hs; apply IHa in Hs; congruence.
      + intro Hn; destruct (satisfiesb S sigma a) eqn:E; [| reflexivity].
        exfalso; apply Hn, IHa; reflexivity.
    - reflexivity.
  Qed.

  Lemma satisfiesb_false_iff : forall S sigma f,
      satisfiesb S sigma f = false <-> ~ Satisfies S sigma f.
  Proof.
    intros S sigma f; split.
    - intros E Hs; apply satisfiesb_iff in Hs; congruence.
    - intro Hn; destruct (satisfiesb S sigma f) eqn:E; [| reflexivity].
      exfalso; apply Hn, satisfiesb_iff; exact E.
  Qed.

  Lemma satisfies_double_neg : forall S sigma f,
      ~ ~ Satisfies S sigma f -> Satisfies S sigma f.
  Proof.
    intros S sigma f Hnn; destruct (satisfiesb S sigma f) eqn:E.
    - apply satisfiesb_iff; exact E.
    - exfalso; apply Hnn, satisfiesb_false_iff; exact E.
  Qed.

  Module XOY := TripleUOT X OpOT Y.
  Module XOYF := UOTCompareFacts XOY.
  Module NF := UOTCompareFacts N.
  Module VSF := UOTCompareFacts VSet.AsUOT.
  #[local] Hint Rewrite NF.compare_eq_iff : cmp_varf.
  #[local] Hint Extern 1 => cmp_by NF.compare_antisym : cmp_varf.
  #[local] Hint Extern 1 => cmp_by NF.compare_lt_trans : cmp_varf.

  Module FComp <: ComparableType.
    Definition t := Formula.
    Definition rank (f : Formula) : nat :=
      match f with
      | FDep _ _ => 0 | FConj _ _ => 1 | FDisj _ _ => 2 | FNeg _ => 3
      | FVarCmp _ _ _ => 4
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
          | FVarCmp x1 o1 y1, FVarCmp x2 o2 y2 =>
              XOY.compare (x1, (o1, y1)) (x2, (o2, y2))
          | _, _ => Eq
          end
      | c => c
      end.

    Lemma compare_eq_iff : forall x y, compare x y = Eq <-> x = y.
    Proof.
      intros x; induction x
        as [n1 vs1 | a IHa b IHb | a IHa b IHb | a IHa | x1 o1 y1];
        intros y; destruct y as [n2 vs2 | a2 b2 | a2 b2 | a2 | x2 o2 y2]; simpl;
        try (split; intro H; congruence).
      - rewrite lex_eq_iff, NF.compare_eq_iff, VSF.compare_eq_iff;
          split; intro H; [destruct H; congruence | injection H as -> ->; auto].
      - rewrite lex_eq_iff, IHa, IHb;
          split; intro H; [destruct H; congruence | injection H as -> ->; auto].
      - rewrite lex_eq_iff, IHa, IHb;
          split; intro H; [destruct H; congruence | injection H as -> ->; auto].
      - rewrite IHa; split; intro H; congruence.
      - rewrite XOYF.compare_eq_iff; split; intro H; congruence.
    Qed.

    Lemma compare_antisym : forall x y, compare y x = CompOpp (compare x y).
    Proof.
      intros x; induction x
        as [n1 vs1 | a IHa b IHb | a IHa b IHb | a IHa | x1 o1 y1];
        intros y; destruct y as [n2 vs2 | a2 b2 | a2 b2 | a2 | x2 o2 y2]; simpl;
        try reflexivity.
      - rewrite lex_opp, NF.compare_antisym, VSF.compare_antisym; reflexivity.
      - rewrite lex_opp, IHa, IHb; reflexivity.
      - rewrite lex_opp, IHa, IHb; reflexivity.
      - apply IHa.
      - apply XOYF.compare_antisym.
    Qed.

    Lemma compare_lt_trans : forall x y z,
        compare x y = Lt -> compare y z = Lt -> compare x z = Lt.
    Proof.
      intros x; induction x
        as [n1 vs1 | a1 IHa b1 IHb | a1 IHa b1 IHb | a1 IHa | x1 o1 y1];
        intros y z; destruct y as [n2 vs2 | a2 b2 | a2 b2 | a2 | x2 o2 y2],
          z as [n3 vs3 | a3 b3 | a3 b3 | a3 | x3 o3 y3]; simpl; intros H1 H2;
        try congruence.
      - exact (lex_lt_trans NF.compare_eq_iff (NF.compare_lt_trans _ _ _)
                 (VSF.compare_lt_trans _ _ _) H1 H2).
      - exact (lex_lt_trans compare_eq_iff (IHa _ _) (IHb _ _) H1 H2).
      - exact (lex_lt_trans compare_eq_iff (IHa _ _) (IHb _ _) H1 H2).
      - exact (IHa _ _ H1 H2).
      - exact (XOYF.compare_lt_trans _ _ _ H1 H2).
    Qed.
  End FComp.
  Module FOT := UOTFromCompare FComp.

  Module Dependees := FOT.
  Module DepElt := PairUOT Pkg Dependees.
  Module DepRel := FSetUOT DepElt.

  Record IsResolution
      (R : PkgSet.t) (D : DepRel.t) (r : Pkg.t) (S : PkgSet.t)
      (sigma : X.t -> Y.t) : Prop :=
    { res_subset : PkgSet.Subset S R
    ; res_root_mem : PkgSet.In r S
    ; res_formula_closure :
        forall p, PkgSet.In p S ->
        forall f : Formula, DepRel.In (p, f) D -> Satisfies S sigma f
    ; res_version_unique : C.VersionUnique S }.

  Module NX := SumUOT N X.
  Module VY := SumUOT V Y.

  Module Ab <: AbsentNames NX.
    Definition hasAbsent (n : NX.t) : bool :=
      match n with inl _ => true | inr _ => false end.
  End Ab.

  Module PF := FormulaCalculus NX VY Ab.

  Module Reduction.
    Module T := PF.Reduction.T.
    Module Name := PF.Reduction.Name.
    Module Version := PF.Reduction.Version.
    Module YSet := FSetUOT Y.
    Module NSet := FSetUOT N.

    Definition liftPkg (p : Pkg.t) : PF.Pkg.t := (inl (fst p), inl (snd p)).

    Definition embedPkg (p : Pkg.t) : T.Pkg.t :=
      PF.Reduction.embedPkg (liftPkg p).

    Module SOvl := SetOps V VY VSet PF.VSet.
    Definition liftVS (vs : VSet.t) : PF.VSet.t := SOvl.map inl vs.

    Definition embedVS (vs : VSet.t) : T.VSet.t :=
      PF.Reduction.embedVS (liftVS vs).

    Module SOyl := SetOps Y VY YSet PF.VSet.
    Definition cmpVersionSet (Y_x : X.t -> YSet.t) (x : X.t) (op : CmpOp)
        (y : Y.t) : PF.VSet.t :=
      SOyl.filterMap (fun y' =>
          if opEvalY op y' y then Some (inr y') else None)
        (Y_x x).

    Fixpoint liftFormula (Y_x : X.t -> YSet.t) (f : Formula) : PF.Formula :=
      match f with
      | FDep m vs => PF.FDep (inl m) (liftVS vs)
      | FConj a b => PF.FConj (liftFormula Y_x a) (liftFormula Y_x b)
      | FDisj a b => PF.FDisj (liftFormula Y_x a) (liftFormula Y_x b)
      | FNeg a => PF.FNeg (liftFormula Y_x a)
      | FVarCmp x op y => PF.FDep (inr x) (cmpVersionSet Y_x x op y)
      end.

    Module SOyp := SetOps Y PF.Pkg YSet PF.PkgSet.
    Definition varPkgs (Y_x : X.t -> YSet.t) : PF.PkgSet.t :=
      List.fold_right (fun x acc =>
          PF.PkgSet.union (SOyp.map (fun y => (inr x, inr y)) (Y_x x)) acc)
        PF.PkgSet.empty X.enum.

    Module SOpl := SetOps Pkg PF.Pkg PkgSet PF.PkgSet.
    Definition liftReal (Y_x : X.t -> YSet.t) (R : PkgSet.t) : PF.PkgSet.t :=
      PF.PkgSet.union (SOpl.map liftPkg R) (varPkgs Y_x).

    Module SOdl := SetOps DepElt PF.DepElt DepRel PF.DepRel.
    Definition liftDeps (Y_x : X.t -> YSet.t) (D : DepRel.t) : PF.DepRel.t :=
      SOdl.map (fun e => (liftPkg (fst e), liftFormula Y_x (snd e))) D.

    Definition liftOracle (Y_x : X.t -> YSet.t) (Vq : N.t -> VSet.t)
        (n : NX.t) : PF.VSet.t :=
      match n with
      | inl m => liftVS (Vq m)
      | inr x => SOyl.map inr (Y_x x)
      end.

    Definition reduceReal (Y_x : X.t -> YSet.t) (R : PkgSet.t) (D : DepRel.t)
      : T.PkgSet.t :=
      PF.Reduction.reduceReal (liftReal Y_x R) (liftDeps Y_x D).

    Definition reduceDepsBy (Y_x : X.t -> YSet.t) (Vq : N.t -> VSet.t)
        (D : DepRel.t) : T.DepRel.t :=
      PF.Reduction.reduceDepsBy (liftOracle Y_x Vq) (liftDeps Y_x D).

    Definition reduceDeps (Y_x : X.t -> YSet.t) (R : PkgSet.t) (D : DepRel.t)
      : T.DepRel.t :=
      PF.Reduction.reduceDeps (liftReal Y_x R) (liftDeps Y_x D).

    Lemma mem_liftVS : forall vs w,
        PF.VSet.In w (liftVS vs) <-> exists v, VSet.In v vs /\ w = inl v.
    Proof. intros vs w; unfold liftVS; apply SOvl.mem_map. Qed.

    Lemma mem_cmpVersionSet : forall Y_x x op y w,
        PF.VSet.In w (cmpVersionSet Y_x x op y) <->
        exists y', YSet.In y' (Y_x x) /\ opEvalY op y' y = true /\ w = inr y'.
    Proof.
      intros Y_x x op y w; unfold cmpVersionSet; rewrite SOyl.mem_filterMap.
      split.
      - intros [y' [Hy He]]; destruct (opEvalY op y' y) eqn:Ho;
          [| discriminate He].
        injection He as <-; exists y'; auto.
      - intros [y' [Hy [Ho ->]]]; exists y'; split; [exact Hy |].
        rewrite Ho; reflexivity.
    Qed.

    Lemma mem_varPkgs : forall Y_x q,
        PF.PkgSet.In q (varPkgs Y_x) <->
        exists x y, YSet.In y (Y_x x) /\ q = (inr x, inr y).
    Proof.
      intros Y_x q; unfold varPkgs.
      assert (H : forall l, PF.PkgSet.In q
                    (List.fold_right (fun x acc =>
                        PF.PkgSet.union
                          (SOyp.map (fun y => (inr x, inr y)) (Y_x x)) acc)
                       PF.PkgSet.empty l) <->
                  exists x y, List.In x l /\ YSet.In y (Y_x x) /\
                              q = (inr x, inr y)).
      { induction l as [| x0 l IH]; cbn [List.fold_right].
        - split; [intro Hq; destruct (SOyp.empty_in _ Hq) |].
          intros [x [y [[] _]]].
        - rewrite PF.PkgSet.union_spec, SOyp.mem_map, IH; split.
          + intros [[y [Hy ->]] | [x [y [Hx Hy]]]].
            * exists x0, y; split; [left; reflexivity | auto].
            * exists x, y; split; [right; exact Hx | exact Hy].
          + intros [x [y [[<- | Hx] [Hy ->]]]].
            * left; exists y; auto.
            * right; exists x, y; auto. }
      rewrite H; split.
      - intros [x [y [_ Hy]]]; exists x, y; exact Hy.
      - intros [x [y Hy]]; exists x, y; split; [apply X.enum_complete | ].
        exact Hy.
    Qed.

    Lemma mem_liftReal : forall Y_x R q,
        PF.PkgSet.In q (liftReal Y_x R) <->
        (exists m v, PkgSet.In (m, v) R /\ q = (inl m, inl v)) \/
        (exists x y, YSet.In y (Y_x x) /\ q = (inr x, inr y)).
    Proof.
      intros Y_x R q; unfold liftReal.
      rewrite PF.PkgSet.union_spec, SOpl.mem_map, mem_varPkgs.
      apply or_iff_compat_r; split.
      - intros [[m v] [Hp ->]]; exists m, v; split; [exact Hp | reflexivity].
      - intros [m [v [Hp ->]]]; exists (m, v); split; [exact Hp | reflexivity].
    Qed.

    Lemma mem_liftDeps : forall Y_x D e,
        PF.DepRel.In e (liftDeps Y_x D) <->
        exists p f, DepRel.In (p, f) D /\ e = (liftPkg p, liftFormula Y_x f).
    Proof.
      intros Y_x D e; unfold liftDeps; rewrite SOdl.mem_map; split.
      - intros [[p f] [He ->]]; exists p, f; split; [exact He | reflexivity].
      - intros [p [f [He ->]]]; exists (p, f); split; [exact He | reflexivity].
    Qed.

    Lemma versions_liftReal : forall Y_x R n,
        PF.C.versions (liftReal Y_x R) n = liftOracle Y_x (C.versions R) n.
    Proof.
      intros Y_x R n; apply PF.VSet.ext; intro w.
      rewrite PF.C.mem_versions, mem_liftReal.
      destruct n as [m | x]; cbn [liftOracle].
      - rewrite mem_liftVS; split.
        + intros [[m' [v [Hp E]]] | [x [y [_ E]]]]; [| discriminate E].
          injection E as -> ->; exists v; split; [| reflexivity].
          apply C.mem_versions; exact Hp.
        + intros [v [Hv ->]]; left; exists m, v; split; [| reflexivity].
          apply C.mem_versions; exact Hv.
      - rewrite SOyl.mem_map; split.
        + intros [[m' [v [_ E]]] | [x' [y [Hy E]]]]; [discriminate E |].
          injection E as -> ->; exists y; auto.
        + intros [y [Hy ->]]; right; exists x, y; auto.
    Qed.

    Lemma reduceDeps_by : forall Y_x R D,
        reduceDeps Y_x R D = reduceDepsBy Y_x (C.versions R) D.
    Proof.
      intros Y_x R D; unfold reduceDeps, reduceDepsBy, PF.Reduction.reduceDeps.
      apply PF.Reduction.Lookup.reduceDepsBy_agree; intros n _.
      apply versions_liftReal.
    Qed.

    Definition tryInvPkg (p' : T.Pkg.t) : option Pkg.t :=
      match p' with
      | (Name.Orig (inl m), Version.Orig (inl v)) => Some (m, v)
      | _ => None
      end.

    Lemma tryInvPkg_embed : forall p, tryInvPkg (embedPkg p) = Some p.
    Proof. intros [m v]; reflexivity. Qed.

    Lemma tryInvPkg_some : forall (p' : T.Pkg.t) (p : Pkg.t),
        tryInvPkg p' = Some p -> embedPkg p = p'.
    Proof.
      intros [[[n' | x'] | fs] [[v' | y'] | i |]] p H; cbn [tryInvPkg] in H;
        try discriminate.
      injection H as <-; reflexivity.
    Qed.

    Module SOtp := SetOps T.Pkg Pkg T.PkgSet PkgSet.
    Definition variableFormulaResolution (S : T.PkgSet.t) : PkgSet.t :=
      SOtp.filterMap tryInvPkg S.

    Lemma mem_variableFormulaResolution : forall (S : T.PkgSet.t) (p : Pkg.t),
        PkgSet.In p (variableFormulaResolution S) <->
        T.PkgSet.In (embedPkg p) S.
    Proof.
      unfold variableFormulaResolution.
      exact (SOtp.mem_filterMap_inv tryInvPkg embedPkg tryInvPkg_embed
               tryInvPkg_some).
    Qed.

    Module SOty := SetOps T.Pkg Y T.PkgSet YSet.
    Definition assignCand (S : T.PkgSet.t) (x : X.t) : YSet.t :=
      SOty.filterMap (fun p' =>
          match p' with
          | (Name.Orig (inr x'), Version.Orig (inr y)) =>
              if X.eq_dec x' x then Some y else None
          | _ => None
          end)
        S.

    Definition extractAssignment (y0 : Y.t) (Y_x : X.t -> YSet.t)
        (S : T.PkgSet.t) (x : X.t) : Y.t :=
      match YSet.min_elt (assignCand S x) with
      | Some y => y
      | None =>
          match YSet.min_elt (Y_x x) with
          | Some y => y
          | None => y0
          end
      end.

    Lemma mem_assignCand : forall S x y,
        YSet.In y (assignCand S x) <->
        T.PkgSet.In (Name.Orig (inr x), Version.Orig (inr y)) S.
    Proof.
      intros S x y; unfold assignCand; rewrite SOty.mem_filterMap.
      split.
      - intros [[[[n' | x'] | fs] [[v' | y'] | i |]] [Hp' Hin]];
          cbn beta iota in Hin; try discriminate.
        destruct (X.eq_dec x' x) as [-> | NE]; [| discriminate].
        injection Hin as <-; exact Hp'.
      - intro H; exists (Name.Orig (inr x), Version.Orig (inr y));
          split; [exact H | cbn beta iota].
        destruct (X.eq_dec x x) as [_ | NE];
          [reflexivity | contradiction NE; reflexivity].
    Qed.

    Lemma extractAssignment_at : forall y0 Y_x S x y,
        T.VersionUnique S ->
        T.PkgSet.In (Name.Orig (inr x), Version.Orig (inr y)) S ->
        extractAssignment y0 Y_x S x = y.
    Proof.
      intros y0 Y_x S x y Huniq Hin; unfold extractAssignment.
      destruct (YSet.min_elt (assignCand S x)) as [y' |] eqn:E.
      - apply YSet.min_elt_spec1, mem_assignCand in E.
        assert (Ev := Huniq _ _ _ E Hin); injection Ev as ->; reflexivity.
      - exfalso; apply YSet.min_elt_spec3 in E.
        exact (E y (proj2 (mem_assignCand S x y) Hin)).
    Qed.

    Definition assignPkgs (sigma : X.t -> Y.t) : PF.PkgSet.t :=
      List.fold_right (fun x acc => PF.PkgSet.add (inr x, inr (sigma x)) acc)
        PF.PkgSet.empty X.enum.

    Lemma mem_assignPkgs : forall sigma q,
        PF.PkgSet.In q (assignPkgs sigma) <->
        exists x, q = (inr x, inr (sigma x)).
    Proof.
      intros sigma q; unfold assignPkgs.
      assert (H : forall l, PF.PkgSet.In q
                    (List.fold_right (fun x acc =>
                        PF.PkgSet.add (inr x, inr (sigma x)) acc)
                       PF.PkgSet.empty l) <->
                  exists x, List.In x l /\ q = (inr x, inr (sigma x))).
      { induction l as [| x0 l IH]; cbn [List.fold_right].
        - split; [intro Hq; destruct (SOyp.empty_in _ Hq) |].
          intros [x [[] _]].
        - rewrite SOyp.add_in, IH; split.
          + intros [-> | [x [Hx ->]]];
              [exists x0; split; [left |]; reflexivity
              | exists x; split; [right; exact Hx | reflexivity]].
          + intros [x [[<- | Hx] ->]]; [left; reflexivity |].
            right; exists x; auto. }
      rewrite H; split.
      - intros [x [_ ->]]; exists x; reflexivity.
      - intros [x ->]; exists x; split; [apply X.enum_complete | reflexivity].
    Qed.

    Definition liftModel (S : PkgSet.t) (sigma : X.t -> Y.t) : PF.PkgSet.t :=
      PF.PkgSet.union (SOpl.map liftPkg S) (assignPkgs sigma).

    Lemma mem_liftModel_inl : forall S sigma m w,
        PF.PkgSet.In (inl m, w) (liftModel S sigma) <->
        exists v, w = inl v /\ PkgSet.In (m, v) S.
    Proof.
      intros S sigma m w; unfold liftModel.
      rewrite PF.PkgSet.union_spec, SOpl.mem_map, mem_assignPkgs; split.
      - intros [[[m' v] [Hp E]] | [x E]]; [| discriminate E].
        unfold liftPkg in E; cbn [fst snd] in E; injection E as <- ->.
        exists v; split; [reflexivity | exact Hp].
      - intros [v [-> Hp]]; left; exists (m, v); split; [exact Hp |].
        reflexivity.
    Qed.

    Lemma mem_liftModel_inr : forall S sigma x w,
        PF.PkgSet.In (inr x, w) (liftModel S sigma) <-> w = inr (sigma x).
    Proof.
      intros S sigma x w; unfold liftModel.
      rewrite PF.PkgSet.union_spec, SOpl.mem_map, mem_assignPkgs; split.
      - intros [[p [_ E]] | [x' E]]; [unfold liftPkg in E; discriminate E |].
        injection E as <- ->; reflexivity.
      - intros ->; right; exists x; reflexivity.
    Qed.

    Lemma satisfies_liftFormula : forall Y_x S sigma f,
        (forall x, YSet.In (sigma x) (Y_x x)) ->
        (Satisfies S sigma f <->
         PF.Satisfies (liftModel S sigma) (liftFormula Y_x f)).
    Proof.
      intros Y_x S sigma f Hs;
        induction f as [m vs | a IHa b IHb | a IHa b IHb | a IHa | x op y];
        cbn [Satisfies PF.Satisfies liftFormula].
      - split.
        + intros [v [Hv Hm]]; exists (inl v); split;
            [apply mem_liftVS; exists v; auto |].
          apply mem_liftModel_inl; exists v; auto.
        + intros [w [Hw Hm]]; apply mem_liftVS in Hw.
          destruct Hw as [v [Hv ->]]; apply mem_liftModel_inl in Hm.
          destruct Hm as [v' [E Hm]]; injection E as <-.
          exists v; auto.
      - rewrite IHa, IHb; reflexivity.
      - rewrite IHa, IHb; reflexivity.
      - rewrite IHa; reflexivity.
      - split.
        + intro Ho; exists (inr (sigma x)); split;
            [apply mem_cmpVersionSet; exists (sigma x); auto |].
          apply mem_liftModel_inr; reflexivity.
        + intros [w [Hw Hm]]; apply mem_liftModel_inr in Hm; subst w.
          apply mem_cmpVersionSet in Hw.
          destruct Hw as [y' [_ [Ho E]]]; injection E as <-; exact Ho.
    Qed.

    Theorem variable_formula_soundness :
      forall (y0 : Y.t) (Y_x : X.t -> YSet.t),
        (forall x, exists y, YSet.In y (Y_x x)) ->
        forall (R : PkgSet.t) (D : DepRel.t) (r : Pkg.t) (S : T.PkgSet.t),
          T.IsResolution (reduceReal Y_x R D) (reduceDeps Y_x R D)
            (embedPkg r) S ->
          IsResolution R D r (variableFormulaResolution S)
            (extractAssignment y0 Y_x S) /\
          forall x, YSet.In (extractAssignment y0 Y_x S x) (Y_x x).
    Proof.
      intros y0 Y_x Hne R D r S Hres.
      set (sigma := extractAssignment y0 Y_x S).
      assert (Hres' := Hres); destruct Hres' as [Hsub Hroot Hdep Huniq].
      assert (Hreal : forall n w,
                 T.PkgSet.In (Name.Orig n, Version.Orig w) S ->
                 PF.PkgSet.In (n, w) (liftReal Y_x R)).
      { intros n w H.
        exact (PF.Reduction.embedPkg_mem_reduceReal (n, w) _ _ (Hsub _ H)). }
      assert (Hsig : forall x, YSet.In (sigma x) (Y_x x)).
      { intro x; unfold sigma, extractAssignment.
        destruct (YSet.min_elt (assignCand S x)) as [y |] eqn:E.
        - apply YSet.min_elt_spec1, mem_assignCand, Hreal, mem_liftReal in E.
          destruct E as [[m [v [_ E]]] | [x' [y' [Hy E]]]]; [discriminate E |].
          injection E as -> ->; exact Hy.
        - destruct (Hne x) as [y' Hy'].
          destruct (YSet.min_elt (Y_x x)) as [y |] eqn:E2.
          + exact (YSet.min_elt_spec1 E2).
          + exfalso; apply YSet.min_elt_spec3 in E2; exact (E2 y' Hy'). }
      set (M := liftModel (variableFormulaResolution S) sigma).
      assert (HM : PF.Reduction.AgreesOn S M).
      { intros [m | x] w Hn; unfold M.
        - rewrite mem_liftModel_inl; destruct w as [v | y]; split.
          + intros [v' [E Hv]]; injection E as <-.
            apply mem_variableFormulaResolution in Hv; exact Hv.
          + intro Hv; exists v; split; [reflexivity |].
            apply mem_variableFormulaResolution; exact Hv.
          + intros [v' [E _]]; discriminate E.
          + intro H; apply Hreal, mem_liftReal in H.
            destruct H as [[m' [v' [_ E]]] | [x [y' [_ E]]]];
              discriminate E.
        - rewrite mem_liftModel_inr.
          destruct Hn as [Hn | [u Hu]];
            [cbv [Ab.hasAbsent] in Hn; discriminate Hn |].
          assert (Hu' := Hreal _ _ Hu); apply mem_liftReal in Hu'.
          destruct Hu' as [[m' [v' [_ E]]] | [x' [y [_ E]]]];
            [discriminate E |].
          injection E as <- ->.
          assert (Hs : sigma x = y)
            by exact (extractAssignment_at y0 Y_x S x y Huniq Hu).
          rewrite Hs; split.
          + intros ->; exact Hu.
          + intro Hw; assert (E := Huniq _ _ _ Hu Hw).
            injection E as E'; exact (eq_sym E'). }
      split; [| exact Hsig].
      constructor.
      - intros [m v] Hp; apply mem_variableFormulaResolution in Hp.
        apply (Hreal (inl m) (inl v)), mem_liftReal in Hp.
        destruct Hp as [[m' [v' [Hp E]]] | [x [y [_ E]]]]; [| discriminate E].
        injection E as <- <-; exact Hp.
      - apply mem_variableFormulaResolution; exact Hroot.
      - intros p Hp f Hdf.
        apply (satisfies_liftFormula Y_x _ sigma f Hsig).
        apply (PF.Reduction.package_formula_soundness_agree
                 (liftReal Y_x R) (liftDeps Y_x D) (liftPkg r) S M Hres HM
                 (liftPkg p) (liftFormula Y_x f)).
        + apply PF.Reduction.mem_packageFormulaResolution.
          apply mem_variableFormulaResolution in Hp; exact Hp.
        + apply mem_liftDeps; exists p, f; auto.
      - intros m v v' Hv Hv'.
        apply mem_variableFormulaResolution in Hv, Hv'.
        unfold embedPkg, PF.Reduction.embedPkg, liftPkg in Hv, Hv'.
        cbn [fst snd] in Hv, Hv'.
        assert (E := Huniq _ _ _ Hv Hv'); injection E as E; exact E.
    Qed.

    Definition coreResolution (Y_x : X.t -> YSet.t) (S : PkgSet.t)
        (R : PkgSet.t) (D : DepRel.t) (sigma : X.t -> Y.t) : T.PkgSet.t :=
      PF.Reduction.coreResolution (liftModel S sigma) (liftReal Y_x R)
        (liftDeps Y_x D).

    Theorem variable_formula_completeness :
      forall (Y_x : X.t -> YSet.t) (R : PkgSet.t) (D : DepRel.t)
             (r : Pkg.t) (sigma : X.t -> Y.t),
        (forall x, YSet.In (sigma x) (Y_x x)) ->
        forall (S : PkgSet.t),
          IsResolution R D r S sigma ->
          T.IsResolution (reduceReal Y_x R D) (reduceDeps Y_x R D) (embedPkg r)
            (coreResolution Y_x S R D sigma).
    Proof.
      intros Y_x R D r sigma Hs S [Hsub Hroot Hclo Huniq].
      apply PF.Reduction.package_formula_completeness.
      - constructor.
        + intros [[m | x] w] Hq; apply mem_liftReal.
          * apply mem_liftModel_inl in Hq; destruct Hq as [v [-> Hv]].
            left; exists m, v; split; [exact (Hsub _ Hv) | reflexivity].
          * apply mem_liftModel_inr in Hq; subst w.
            right; exists x, (sigma x); auto.
        + apply mem_liftModel_inl; exists (snd r); split; [reflexivity |].
          destruct r as [rn rv]; exact Hroot.
        + intros [[m | x] w] Hq g Hg.
          * apply mem_liftModel_inl in Hq; destruct Hq as [v [-> Hv]].
            apply mem_liftDeps in Hg; destruct Hg as [[m' v'] [f [Hd E]]].
            unfold liftPkg in E; cbn [fst snd] in E.
            injection E as <- <- ->.
            apply (satisfies_liftFormula Y_x S sigma f Hs).
            exact (Hclo _ Hv f Hd).
          * apply mem_liftDeps in Hg; destruct Hg as [p [f [_ E]]].
            unfold liftPkg in E; discriminate E.
        + intros [m | x] w w' Hw Hw'.
          * apply mem_liftModel_inl in Hw, Hw'.
            destruct Hw as [v [-> Hv]]; destruct Hw' as [v' [-> Hv']].
            rewrite (Huniq _ _ _ Hv Hv'); reflexivity.
          * apply mem_liftModel_inr in Hw, Hw'; congruence.
      - intros [m | x] _ Ha; [cbv [Ab.hasAbsent] in Ha; discriminate Ha |].
        exists (inr (sigma x)); apply mem_liftModel_inr; reflexivity.
    Qed.

    Module Lookup.
      Module PkgFibred := FibredRel N V Pkg PkgSet.
      Module DepRelFibred := FibredRel Pkg Dependees DepElt DepRel.
      Module RKeys := PreimageOfKeys N Pkg NSet PkgSet.

      Fixpoint fnames (f : Formula) : NSet.t :=
        match f with
        | FDep m _ => NSet.singleton m
        | FConj a b => NSet.union (fnames a) (fnames b)
        | FDisj a b => NSet.union (fnames a) (fnames b)
        | FNeg a => fnames a
        | FVarCmp _ _ _ => NSet.empty
        end.

      Module SOen := SetOps DepElt N DepRel NSet.
      Definition depNames (D : DepRel.t) : NSet.t :=
        SOen.unionMap (fun e => fnames (snd e)) D.

      Definition realPreimage (R : PkgSet.t) (ns : NSet.t) : PkgSet.t :=
        RKeys.ofKeys fst ns R.

      Definition valuesAt (Y_x : X.t -> YSet.t) (x : X.t) : X.t -> YSet.t :=
        fun x' => if X.eq_dec x x' then Y_x x else YSet.empty.

      Lemma fnames_liftFormula : forall Y_x f m,
          PF.Reduction.NSet.In (inl m) (PF.Reduction.fnames (liftFormula Y_x f))
          -> NSet.In m (fnames f).
      Proof.
        intros Y_x f m;
          induction f as [o vs | a IHa b IHb | a IHa b IHb | a IHa | x op y];
          cbn [liftFormula PF.Reduction.fnames fnames]; intro H.
        - apply PF.Reduction.NSet.singleton_spec in H; injection H as ->.
          apply NSet.singleton_spec; reflexivity.
        - apply PF.Reduction.NSet.union_spec in H; apply NSet.union_spec.
          destruct H as [H | H]; [left; exact (IHa H) | right; exact (IHb H)].
        - apply PF.Reduction.NSet.union_spec in H; apply NSet.union_spec.
          destruct H as [H | H]; [left; exact (IHa H) | right; exact (IHb H)].
        - exact (IHa H).
        - apply PF.Reduction.NSet.singleton_spec in H; discriminate H.
      Qed.

      Lemma liftDeps_tailFibre : forall Y_x D (m : N.t) (v : V.t),
          PF.Reduction.Lookup.DepRelFibred.tailFibre (liftDeps Y_x D)
            (inl m, inl v) =
          liftDeps Y_x (DepRelFibred.tailFibre D (m, v)).
      Proof.
        intros Y_x D m v; apply PF.DepRel.ext; intros [p g].
        rewrite PF.Reduction.Lookup.DepRelFibred.mem_tailFibre, !mem_liftDeps.
        split.
        - intros [[[m' v'] [f [Hd E]]] ->].
          unfold liftPkg in E; cbn [fst snd] in E; injection E as <- <- ->.
          exists (m, v), f; split; [| reflexivity].
          apply DepRelFibred.mem_tailFibre; split; [exact Hd | reflexivity].
        - intros [p' [f [Hd E]]].
          apply DepRelFibred.mem_tailFibre in Hd; destruct Hd as [Hd ->].
          injection E as -> ->.
          split; [exists (m, v), f; split; [exact Hd | reflexivity] |].
          reflexivity.
      Qed.

      Theorem versions_lookupOrig : forall Y_x R D (r : Pkg.t) (m : N.t),
          PkgSet.In r R ->
          (exists p h,
              T.DepRel.In (p, (Name.Orig (inl m), h)) (reduceDeps Y_x R D)) \/
          m = fst r ->
          T.versions (reduceReal Y_x R D) (Name.Orig (inl m)) =
          T.VSet.add Version.Bot
            (embedVS (C.versions (PkgFibred.tailFibre R m) m)).
      Proof.
        intros Y_x R D r m Hr Hreach.
        assert (Hr' : PF.PkgSet.In (liftPkg r) (liftReal Y_x R))
          by (apply mem_liftReal; left; exists (fst r), (snd r);
              destruct r; split; [exact Hr | reflexivity]).
        unfold reduceReal; rewrite (PF.Reduction.Lookup.versions_lookupOrig
                                      _ _ (liftPkg r) (inl m) Hr').
        - unfold embedVS; do 2 f_equal; apply PF.VSet.ext; intro w.
          rewrite PF.C.mem_versions,
            PF.Reduction.Lookup.PkgFibred.mem_tailFibre, mem_liftReal,
            mem_liftVS; split.
          + intros [[[m' [v [Hp E]]] | [x [y [_ E]]]] _]; [| discriminate E].
            injection E as <- ->; exists v; split; [| reflexivity].
            apply C.mem_versions, PkgFibred.mem_tailFibre.
            split; [exact Hp | reflexivity].
          + intros [v [Hv ->]].
            apply C.mem_versions, PkgFibred.mem_tailFibre in Hv.
            destruct Hv as [Hv _]; split; [left; exists m, v; auto |].
            reflexivity.
        - destruct Hreach as [H | ->]; [left; exact H | right; reflexivity].
        - reflexivity.
      Qed.

      Theorem versions_lookupVar : forall Y_x R D (x : X.t),
          T.versions (reduceReal Y_x R D) (Name.Orig (inr x)) =
          T.versions (reduceReal (valuesAt Y_x x) PkgSet.empty DepRel.empty)
            (Name.Orig (inr x)).
      Proof.
        intros Y_x R D x; unfold reduceReal.
        rewrite !PF.Reduction.Lookup.versions_lookupOrigPresent
          by reflexivity.
        f_equal; apply PF.VSet.ext; intro w.
        rewrite !PF.C.mem_versions,
          !PF.Reduction.Lookup.PkgFibred.mem_tailFibre, !mem_liftReal.
        split.
        - intros [[[m [v [_ E]]] | [x' [y [Hy E]]]] _]; [discriminate E |].
          injection E as <- ->; split; [| reflexivity].
          right; exists x, y; split; [| reflexivity].
          unfold valuesAt; destruct (X.eq_dec x x) as [_ | NE];
            [exact Hy | contradiction NE; reflexivity].
        - intros [[[m [v [Hv E]]] | [x' [y [Hy E]]]] _];
            [destruct (PkgSet.empty_spec Hv) |].
          injection E as <- ->; split; [| reflexivity].
          right; exists x, y; split; [| reflexivity].
          revert Hy; unfold valuesAt; destruct (X.eq_dec x x) as [_ | NE];
            [intro Hy; exact Hy | contradiction NE; reflexivity].
      Qed.

      Theorem dependees_lookupOrig : forall Y_x R D m v,
          T.dependees (reduceDeps Y_x R D)
            (Name.Orig (inl m), Version.Orig (inl v)) =
          T.dependees
            (reduceDeps Y_x
               (realPreimage R (depNames (DepRelFibred.tailFibre D (m, v))))
               (DepRelFibred.tailFibre D (m, v)))
            (Name.Orig (inl m), Version.Orig (inl v)).
      Proof.
        intros Y_x R D m v.
        set (Dp := DepRelFibred.tailFibre D (m, v)).
        unfold reduceDeps at 1.
        rewrite (PF.Reduction.Lookup.dependees_lookupOrigBy _ _
                   (liftOracle Y_x
                      (C.versions (realPreimage R (depNames Dp))))).
        - rewrite reduceDeps_by, liftDeps_tailFibre; reflexivity.
        - rewrite liftDeps_tailFibre; intros [m' | x] Hn;
            rewrite versions_liftReal; [| reflexivity].
          cbn [liftOracle]; f_equal; apply C.versions_ext; intro w.
          unfold realPreimage; rewrite RKeys.mem_ofKeys; cbn [fst].
          split; [intros [H _]; exact H | intro H; split; [exact H |]].
          apply PF.Reduction.mem_depNames in Hn.
          destruct Hn as [p [g [Hg Hm]]]; apply mem_liftDeps in Hg.
          destruct Hg as [p' [f [Hf E]]]; injection E as _ ->.
          apply SOen.mem_unionMap; exists (p', f); split; [exact Hf |].
          exact (fnames_liftFormula Y_x f m' Hm).
      Qed.

      Theorem dependees_lookupOrigBy : forall Y_x R D Vq m v,
          (forall n, NSet.In n (depNames (DepRelFibred.tailFibre D (m, v))) ->
                     Vq n = C.versions R n) ->
          T.dependees (reduceDeps Y_x R D)
            (Name.Orig (inl m), Version.Orig (inl v)) =
          T.dependees (reduceDepsBy Y_x Vq (DepRelFibred.tailFibre D (m, v)))
            (Name.Orig (inl m), Version.Orig (inl v)).
      Proof.
        intros Y_x R D Vq m v HVq; rewrite dependees_lookupOrig, reduceDeps_by.
        unfold reduceDepsBy; f_equal.
        apply PF.Reduction.Lookup.reduceDepsBy_agree; intros [m' | x] Hn;
          [| reflexivity].
        cbn [liftOracle]; f_equal.
        apply PF.Reduction.mem_depNames in Hn.
        destruct Hn as [p [g [Hg Hm]]]; apply mem_liftDeps in Hg.
        destruct Hg as [p' [f [Hf E]]]; injection E as _ ->.
        assert (Hin : NSet.In m' (depNames (DepRelFibred.tailFibre D (m, v))))
          by (apply SOen.mem_unionMap; exists (p', f);
              exact (conj Hf (fnames_liftFormula Y_x f m' Hm))).
        rewrite (HVq m' Hin); apply C.versions_ext; intro w.
        unfold realPreimage; rewrite RKeys.mem_ofKeys; cbn [fst]; tauto.
      Qed.

      Theorem dependees_lookupAbsent : forall Y_x R D m,
          T.dependees (reduceDeps Y_x R D) (Name.Orig (inl m), Version.Bot) =
          T.DependeesSet.empty.
      Proof.
        intros Y_x R D m; apply PF.Reduction.Lookup.dependees_lookupAbsent.
      Qed.

      Theorem dependees_lookupVar : forall Y_x R D x (y : Version.t),
          T.dependees (reduceDeps Y_x R D) (Name.Orig (inr x), y) =
          T.DependeesSet.empty.
      Proof.
        intros Y_x R D x y; apply T.dependees_empty_iff; intros h H.
        apply PF.Reduction.mem_reduceDeps in H.
        destruct H as [p [g [Hg He]]].
        assert (E := proj1 (PF.Reduction.Lookup.encodeNNF_src_orig_aux _ g)
                       _ _ _ _ He).
        apply mem_liftDeps in Hg; destruct Hg as [[m v] [f [_ Ep]]].
        injection Ep as -> _.
        unfold PF.Reduction.embedPkg, liftPkg in E; cbn [fst snd] in E.
        discriminate E.
      Qed.

      Theorem versions_lookupDisjunct : forall Y_x R D fs,
          (exists p h, T.DepRel.In (p, (Name.Disjunct fs, h))
                         (reduceDeps Y_x R D)) ->
          T.versions (reduceReal Y_x R D) (Name.Disjunct fs) =
          PF.Reduction.idxSet (List.length fs).
      Proof.
        intros Y_x R D fs H;
          exact (PF.Reduction.Lookup.versions_lookupDisjunct _ _ fs H).
      Qed.

      Theorem dependees_lookupDisjunct : forall Y_x R D fs (i : Version.t),
          T.PkgSet.In (Name.Disjunct fs, i) (reduceReal Y_x R D) ->
          T.dependees (reduceDeps Y_x R D) (Name.Disjunct fs, i) =
          match PF.Reduction.Lookup.disjAlt fs i with
          | Some g =>
              T.dependees
                (PF.Reduction.encodeNNF (liftOracle Y_x (C.versions R))
                   (Name.Disjunct fs, i) g)
                (Name.Disjunct fs, i)
          | None => T.DependeesSet.empty
          end.
      Proof.
        intros Y_x R D fs i H; unfold reduceDeps.
        rewrite (PF.Reduction.Lookup.dependees_lookupDisjunct _ _ fs i H).
        destruct (PF.Reduction.Lookup.disjAlt fs i) as [g |]; [| reflexivity].
        f_equal.
        refine (proj1 (PF.Reduction.Lookup.encodeNNF_agree_aux _ _ g _) _).
        intros n _; apply versions_liftReal.
      Qed.

      Theorem dependees_lookupDisjunctBy : forall Y_x R D R' D' Vq fs i,
          DepRel.Subset D' D ->
          T.PkgSet.In (Name.Disjunct fs, i) (reduceReal Y_x R' D') ->
          (forall p f n, DepRel.In (p, f) D' ->
             PF.Reduction.NSet.In n
               (PF.Reduction.Lookup.negNames (liftFormula Y_x f)) ->
             liftOracle Y_x Vq n = liftOracle Y_x (C.versions R) n) ->
          T.dependees (reduceDeps Y_x R D) (Name.Disjunct fs, i) =
          T.dependees (reduceDepsBy Y_x Vq D') (Name.Disjunct fs, i).
      Proof.
        intros Y_x R D R' D' Vq fs i Hsub Hin HVq.
        unfold reduceDeps, reduceDepsBy.
        apply (PF.Reduction.Lookup.dependees_lookupDisjunctBy _ _
                 (liftReal Y_x R') (liftDeps Y_x D')).
        - intros e He; apply mem_liftDeps in He; apply mem_liftDeps.
          destruct He as [p [f [Hd ->]]]; exists p, f.
          split; [exact (Hsub _ Hd) | reflexivity].
        - exact Hin.
        - intros p g n Hg Hn; apply mem_liftDeps in Hg.
          destruct Hg as [p' [f [Hf E]]]; injection E as _ ->.
          rewrite versions_liftReal; exact (HVq p' f n Hf Hn).
      Qed.
    End Lookup.
  End Reduction.
End VariableFormula.
