From Stdlib Require Import MSets List.
From PackageCalculus Require Import Prelude Core Versions PackageFormula.

Create HintDb cmp_varf.
Create Rewrite HintDb cmp_varf.

Module VariableFormula (N V : UsualOrderedType)
    (X : FiniteUsualOrderedType) (Y : UsualOrderedType).
  Module Source := Core N V.
  Module Package := Source.Package.
  Module PackageSet := Source.PackageSet.
  Module VSet := Source.VSet.

  Inductive Formula : Type :=
  | FAtom (n : N.t) (vs : VSet.t)
  | FConj (psiL psiR : Formula)
  | FDisj (psiL psiR : Formula)
  | FNeg (psi : Formula)
  | FVarCmp (x : X.t) (op : CmpOp) (y : Y.t).

  Definition opEvalY (op : CmpOp) (v y : Y.t) : bool :=
    cmpOpEvalBy Y.compare op v y.

  Fixpoint Satisfies (S : PackageSet.t) (sigma : X.t -> Y.t) (psi : Formula) :
      Prop :=
    match psi with
    | FAtom n vs => exists v, VSet.In v vs /\ PackageSet.In (n, v) S
    | FConj psiL psiR => Satisfies S sigma psiL /\ Satisfies S sigma psiR
    | FDisj psiL psiR => Satisfies S sigma psiL \/ Satisfies S sigma psiR
    | FNeg psi' => ~ Satisfies S sigma psi'
    | FVarCmp x op y => opEvalY op (sigma x) y = true
    end.

  Fixpoint satisfiesb (S : PackageSet.t) (sigma : X.t -> Y.t) (psi : Formula) :
      bool :=
    match psi with
    | FAtom m vs => VSet.exists_ (fun v => PackageSet.mem (m, v) S) vs
    | FConj psiL psiR =>
        andb (satisfiesb S sigma psiL) (satisfiesb S sigma psiR)
    | FDisj psiL psiR => orb (satisfiesb S sigma psiL) (satisfiesb S sigma psiR)
    | FNeg psi' => negb (satisfiesb S sigma psi')
    | FVarCmp x op y => opEvalY op (sigma x) y
    end.

  Lemma satisfiesb_iff : forall S sigma psi,
      satisfiesb S sigma psi = true <-> Satisfies S sigma psi.
  Proof.
    intros S sigma psi;
      induction psi
        as [m vs | psiL IHa psiR IHb | psiL IHa psiR IHb | psi' IHa | x op y];
      simpl.
    - rewrite VSet.exists_spec'.
      split; intros [v [Hv Hm]]; exists v; split; try assumption;
        apply PackageSet.mem_spec; assumption.
    - rewrite Bool.andb_true_iff, IHa, IHb; reflexivity.
    - rewrite Bool.orb_true_iff, IHa, IHb; reflexivity.
    - rewrite Bool.negb_true_iff; split.
      + intros E Hs; apply IHa in Hs; congruence.
      + intro Hn; destruct (satisfiesb S sigma psi') eqn:E; [| reflexivity].
        exfalso; apply Hn, IHa; reflexivity.
    - reflexivity.
  Qed.

  Lemma satisfiesb_false_iff : forall S sigma psi,
      satisfiesb S sigma psi = false <-> ~ Satisfies S sigma psi.
  Proof.
    intros S sigma psi; split.
    - intros E Hs; apply satisfiesb_iff in Hs; congruence.
    - intro Hn; destruct (satisfiesb S sigma psi) eqn:E; [| reflexivity].
      exfalso; apply Hn, satisfiesb_iff; exact E.
  Qed.

  Lemma satisfies_double_neg : forall S sigma psi,
      ~ ~ Satisfies S sigma psi -> Satisfies S sigma psi.
  Proof.
    intros S sigma psi Hnn; destruct (satisfiesb S sigma psi) eqn:E.
    - apply satisfiesb_iff; exact E.
    - exfalso; apply Hnn, satisfiesb_false_iff; exact E.
  Qed.

  Module VariableComparison := TripleUOT X ComparisonOperatorOT Y.
  Module XOYF := UOTCompareFacts VariableComparison.
  Module NF := UOTCompareFacts N.
  Module VSF := UOTCompareFacts VSet.AsUOT.
  #[local] Hint Rewrite NF.compare_eq_iff : cmp_varf.
  #[local] Hint Extern 1 => cmp_by NF.compare_antisym : cmp_varf.
  #[local] Hint Extern 1 => cmp_by NF.compare_lt_trans : cmp_varf.

  Module VariableFormulaComp <: ComparableType.
    Definition t := Formula.
    Definition rank (psi : Formula) : nat :=
      match psi with
      | FAtom _ _ => 0 | FConj _ _ => 1 | FDisj _ _ => 2 | FNeg _ => 3
      | FVarCmp _ _ _ => 4
      end.

    Fixpoint compare (x y : Formula) : comparison :=
      match Nat.compare (rank x) (rank y) with
      | Eq =>
          match x, y with
          | FAtom n1 vs1, FAtom n2 vs2 =>
              lex (N.compare n1 n2) (VSet.AsUOT.compare vs1 vs2)
          | FConj a1 b1, FConj a2 b2 => lex (compare a1 a2) (compare b1 b2)
          | FDisj a1 b1, FDisj a2 b2 => lex (compare a1 a2) (compare b1 b2)
          | FNeg a1, FNeg a2 => compare a1 a2
          | FVarCmp x1 o1 y1, FVarCmp x2 o2 y2 =>
              VariableComparison.compare (x1, (o1, y1)) (x2, (o2, y2))
          | _, _ => Eq
          end
      | c => c
      end.

    Lemma compare_eq_iff : forall x y, compare x y = Eq <-> x = y.
    Proof.
      intros x; induction x
        as [n1 vs1 | psiL IHa psiR IHb | psiL IHa psiR IHb | psi' IHa
           | x1 o1 y1];
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
        as [n1 vs1 | psiL IHa psiR IHb | psiL IHa psiR IHb | psi' IHa
           | x1 o1 y1];
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
  End VariableFormulaComp.
  Module VariableFormulaOT := UOTFromCompare VariableFormulaComp.

  Module Dependee := VariableFormulaOT.
  Module DependencyElt := PairUOT Package Dependee.
  Module DependencyRel := FSetUOT DependencyElt.
  Module YSet := FSetUOT Y.

  Record IsResolution
      (Y_x : X.t -> YSet.t) (R : PackageSet.t) (D : DependencyRel.t) (r : Package.t)
      (S : PackageSet.t) (sigma : X.t -> Y.t) : Prop :=
    { res_subset : PackageSet.Subset S R
    ; res_root_mem : PackageSet.In r S
    ; res_formula_closure :
        forall p, PackageSet.In p S ->
        forall psi : Formula, DependencyRel.In (p, psi) D -> Satisfies S sigma psi
    ; res_version_unique : Source.VersionUnique S
    ; res_assignment_mem : forall x, YSet.In (sigma x) (Y_x x) }.

  Module NX := SumUOT N X.
  Module VY := SumUOT V Y.

  Module Ab <: AbsentNames NX.
    Definition hasAbsent (n : NX.t) : bool :=
      match n with inl _ => true | inr _ => false end.
  End Ab.

  Module PF := FormulaCalculus NX VY Ab.

  Module Reduction.
    Module Reduced := PF.Reduction.Reduced.
    Module Name := PF.Reduction.Name.
    Module Version := PF.Reduction.Version.
    Module NSet := Source.NSet.

    Definition liftPkg (p : Package.t) : PF.Package.t := (inl (fst p), inl (snd p)).

    Definition embedPkg (p : Package.t) : Reduced.Package.t :=
      PF.Reduction.embedPkg (liftPkg p).

    Module SOvl := SetOps V VY VSet PF.VSet.
    Definition liftVS (vs : VSet.t) : PF.VSet.t := SOvl.map inl vs.

    Definition embedVS (vs : VSet.t) : Reduced.VSet.t :=
      PF.Reduction.embedVS (liftVS vs).

    Module SOyl := SetOps Y VY YSet PF.VSet.
    Definition cmpVersionSet (Y_x : X.t -> YSet.t) (x : X.t) (op : CmpOp)
        (y : Y.t) : PF.VSet.t :=
      SOyl.filterMap (fun v =>
          if opEvalY op v y then Some (inr v) else None)
        (Y_x x).

    Fixpoint liftFormula (Y_x : X.t -> YSet.t) (psi : Formula) : PF.Formula :=
      match psi with
      | FAtom m vs => PF.FAtom (inl m) (liftVS vs)
      | FConj psiL psiR =>
          PF.FConj (liftFormula Y_x psiL) (liftFormula Y_x psiR)
      | FDisj psiL psiR =>
          PF.FDisj (liftFormula Y_x psiL) (liftFormula Y_x psiR)
      | FNeg psi' => PF.FNeg (liftFormula Y_x psi')
      | FVarCmp x op y => PF.FAtom (inr x) (cmpVersionSet Y_x x op y)
      end.

    Module SOyp := SetOps Y PF.Package YSet PF.PackageSet.
    Definition varPkgs (Y_x : X.t -> YSet.t) : PF.PackageSet.t :=
      List.fold_right (fun x acc =>
          PF.PackageSet.union (SOyp.map (fun y => (inr x, inr y)) (Y_x x)) acc)
        PF.PackageSet.empty X.enum.

    Module SOpl := SetOps Package PF.Package PackageSet PF.PackageSet.
    Definition liftReal (Y_x : X.t -> YSet.t) (R : PackageSet.t) : PF.PackageSet.t :=
      PF.PackageSet.union (SOpl.map liftPkg R) (varPkgs Y_x).

    Module SOdl := SetOps DependencyElt PF.DependencyElt DependencyRel PF.DependencyRel.
    Definition liftDeps (Y_x : X.t -> YSet.t) (D : DependencyRel.t) : PF.DependencyRel.t :=
      SOdl.map (fun e => (liftPkg (fst e), liftFormula Y_x (snd e))) D.

    Definition liftOracle (Y_x : X.t -> YSet.t) (Vq : N.t -> VSet.t)
        (n : NX.t) : PF.VSet.t :=
      match n with
      | inl m => liftVS (Vq m)
      | inr x => SOyl.map inr (Y_x x)
      end.

    Definition reduceReal (Y_x : X.t -> YSet.t) (R : PackageSet.t) (D : DependencyRel.t)
      : Reduced.PackageSet.t :=
      PF.Reduction.reduceReal (liftReal Y_x R) (liftDeps Y_x D).

    Definition reduceDepsBy (Y_x : X.t -> YSet.t) (Vq : N.t -> VSet.t)
        (D : DependencyRel.t) : Reduced.DependencyRel.t :=
      PF.Reduction.reduceDepsBy (liftOracle Y_x Vq) (liftDeps Y_x D).

    Definition reduceDeps (Y_x : X.t -> YSet.t) (R : PackageSet.t) (D : DependencyRel.t)
      : Reduced.DependencyRel.t :=
      PF.Reduction.reduceDeps (liftReal Y_x R) (liftDeps Y_x D).

    Lemma mem_liftVS : forall vs u,
        PF.VSet.In u (liftVS vs) <-> exists v, VSet.In v vs /\ u = inl v.
    Proof. intros vs u; unfold liftVS; apply SOvl.mem_map. Qed.

    Lemma mem_cmpVersionSet : forall Y_x x op y u,
        PF.VSet.In u (cmpVersionSet Y_x x op y) <->
        exists v, YSet.In v (Y_x x) /\ opEvalY op v y = true /\ u = inr v.
    Proof.
      intros Y_x x op y u; unfold cmpVersionSet; rewrite SOyl.mem_filterMap.
      split.
      - intros [v [Hy He]]; destruct (opEvalY op v y) eqn:Ho;
          [| discriminate He].
        injection He as <-; exists v; auto.
      - intros [v [Hy [Ho ->]]]; exists v; split; [exact Hy |].
        rewrite Ho; reflexivity.
    Qed.

    Lemma mem_varPkgs : forall Y_x q,
        PF.PackageSet.In q (varPkgs Y_x) <->
        exists x y, YSet.In y (Y_x x) /\ q = (inr x, inr y).
    Proof.
      intros Y_x q; unfold varPkgs.
      assert (H : forall l, PF.PackageSet.In q
                    (List.fold_right (fun x acc =>
                        PF.PackageSet.union
                          (SOyp.map (fun y => (inr x, inr y)) (Y_x x)) acc)
                       PF.PackageSet.empty l) <->
                  exists x y, List.In x l /\ YSet.In y (Y_x x) /\
                              q = (inr x, inr y)).
      { induction l as [| x0 l IH]; cbn [List.fold_right].
        - split; [intro Hq; destruct (SOyp.empty_in _ Hq) |].
          intros [x [y [[] _]]].
        - rewrite PF.PackageSet.union_spec, SOyp.mem_map, IH; split.
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
        PF.PackageSet.In q (liftReal Y_x R) <->
        (exists n v, PackageSet.In (n, v) R /\ q = (inl n, inl v)) \/
        (exists x y, YSet.In y (Y_x x) /\ q = (inr x, inr y)).
    Proof.
      intros Y_x R q; unfold liftReal.
      rewrite PF.PackageSet.union_spec, SOpl.mem_map, mem_varPkgs.
      apply or_iff_compat_r; split.
      - intros [[n v] [Hp ->]]; exists n, v; split; [exact Hp | reflexivity].
      - intros [n [v [Hp ->]]]; exists (n, v); split; [exact Hp | reflexivity].
    Qed.

    Lemma mem_liftDeps : forall Y_x D e,
        PF.DependencyRel.In e (liftDeps Y_x D) <->
        exists p psi, DependencyRel.In (p, psi) D /\
          e = (liftPkg p, liftFormula Y_x psi).
    Proof.
      intros Y_x D e; unfold liftDeps; rewrite SOdl.mem_map; split.
      - intros [[p psi] [He ->]]; exists p, psi; split;
          [exact He | reflexivity].
      - intros [p [psi [He ->]]]; exists (p, psi); split;
          [exact He | reflexivity].
    Qed.

    Lemma versions_liftReal : forall Y_x R n,
        PF.Source.versions (liftReal Y_x R) n = liftOracle Y_x (Source.versions R) n.
    Proof.
      intros Y_x R n; apply PF.VSet.ext; intro w.
      rewrite PF.Source.mem_versions, mem_liftReal.
      destruct n as [m | x]; cbn [liftOracle].
      - rewrite mem_liftVS; split.
        + intros [[m' [v [Hp E]]] | [x [y [_ E]]]]; [| discriminate E].
          injection E as -> ->; exists v; split; [| reflexivity].
          apply Source.mem_versions; exact Hp.
        + intros [v [Hv ->]]; left; exists m, v; split; [| reflexivity].
          apply Source.mem_versions; exact Hv.
      - rewrite SOyl.mem_map; split.
        + intros [[m' [v [_ E]]] | [x' [y [Hy E]]]]; [discriminate E |].
          injection E as -> ->; exists y; auto.
        + intros [y [Hy ->]]; right; exists x, y; auto.
    Qed.

    Lemma reduceDeps_by : forall Y_x R D,
        reduceDeps Y_x R D = reduceDepsBy Y_x (Source.versions R) D.
    Proof.
      intros Y_x R D; unfold reduceDeps, reduceDepsBy, PF.Reduction.reduceDeps.
      apply PF.Reduction.Lookup.reduceDepsBy_agree; intros n _.
      apply versions_liftReal.
    Qed.

    Definition tryInvPkg (p' : Reduced.Package.t) : option Package.t :=
      match p' with
      | (Name.Orig (inl m), Version.Orig (inl v)) => Some (m, v)
      | _ => None
      end.

    Lemma tryInvPkg_embed : forall p, tryInvPkg (embedPkg p) = Some p.
    Proof. intros [m v]; reflexivity. Qed.

    Lemma tryInvPkg_some : forall (p' : Reduced.Package.t) (p : Package.t),
        tryInvPkg p' = Some p -> embedPkg p = p'.
    Proof.
      intros [[[n' | x'] | chis] [[v' | v] | i |]] p H; cbn [tryInvPkg] in H;
        try discriminate.
      injection H as <-; reflexivity.
    Qed.

    Module SOtp := SetOps Reduced.Package Package Reduced.PackageSet PackageSet.
    Definition variableFormulaResolution (S : Reduced.PackageSet.t) : PackageSet.t :=
      SOtp.filterMap tryInvPkg S.

    Lemma mem_variableFormulaResolution : forall (S : Reduced.PackageSet.t) (p : Package.t),
        PackageSet.In p (variableFormulaResolution S) <->
        Reduced.PackageSet.In (embedPkg p) S.
    Proof.
      unfold variableFormulaResolution.
      exact (SOtp.mem_filterMap_inv tryInvPkg embedPkg tryInvPkg_embed
               tryInvPkg_some).
    Qed.

    Module SOty := SetOps Reduced.Package Y Reduced.PackageSet YSet.
    Definition assignCand (S : Reduced.PackageSet.t) (x : X.t) : YSet.t :=
      SOty.filterMap (fun p' =>
          match p' with
          | (Name.Orig (inr x'), Version.Orig (inr y)) =>
              if X.eq_dec x' x then Some y else None
          | _ => None
          end)
        S.

    Definition assignment (y0 : Y.t) (Y_x : X.t -> YSet.t)
        (S : Reduced.PackageSet.t) (x : X.t) : Y.t :=
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
        Reduced.PackageSet.In (Name.Orig (inr x), Version.Orig (inr y)) S.
    Proof.
      intros S x y; unfold assignCand; rewrite SOty.mem_filterMap.
      split.
      - intros [[[[n' | x'] | chis] [[v' | v] | i |]] [Hp' Hin]];
          cbn beta iota in Hin; try discriminate.
        destruct (X.eq_dec x' x) as [-> | NE]; [| discriminate].
        injection Hin as <-; exact Hp'.
      - intro H; exists (Name.Orig (inr x), Version.Orig (inr y));
          split; [exact H | cbn beta iota].
        destruct (X.eq_dec x x) as [_ | NE];
          [reflexivity | contradiction NE; reflexivity].
    Qed.

    Lemma assignment_at : forall y0 Y_x S x y,
        Reduced.VersionUnique S ->
        Reduced.PackageSet.In (Name.Orig (inr x), Version.Orig (inr y)) S ->
        assignment y0 Y_x S x = y.
    Proof.
      intros y0 Y_x S x y Huniq Hin; unfold assignment.
      destruct (YSet.min_elt (assignCand S x)) as [v |] eqn:E.
      - apply YSet.min_elt_spec1, mem_assignCand in E.
        assert (Ev := Huniq _ _ _ E Hin); injection Ev as ->; reflexivity.
      - exfalso; apply YSet.min_elt_spec3 in E.
        exact (E y (proj2 (mem_assignCand S x y) Hin)).
    Qed.

    Definition assignPkgs (sigma : X.t -> Y.t) : PF.PackageSet.t :=
      List.fold_right (fun x acc => PF.PackageSet.add (inr x, inr (sigma x)) acc)
        PF.PackageSet.empty X.enum.

    Lemma mem_assignPkgs : forall sigma q,
        PF.PackageSet.In q (assignPkgs sigma) <->
        exists x, q = (inr x, inr (sigma x)).
    Proof.
      intros sigma q; unfold assignPkgs.
      assert (H : forall l, PF.PackageSet.In q
                    (List.fold_right (fun x acc =>
                        PF.PackageSet.add (inr x, inr (sigma x)) acc)
                       PF.PackageSet.empty l) <->
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

    Definition liftModel (S : PackageSet.t) (sigma : X.t -> Y.t) : PF.PackageSet.t :=
      PF.PackageSet.union (SOpl.map liftPkg S) (assignPkgs sigma).

    Lemma mem_liftModel_inl : forall S sigma m w,
        PF.PackageSet.In (inl m, w) (liftModel S sigma) <->
        exists v, w = inl v /\ PackageSet.In (m, v) S.
    Proof.
      intros S sigma m w; unfold liftModel.
      rewrite PF.PackageSet.union_spec, SOpl.mem_map, mem_assignPkgs; split.
      - intros [[[m' v] [Hp E]] | [x E]]; [| discriminate E].
        unfold liftPkg in E; cbn [fst snd] in E; injection E as <- ->.
        exists v; split; [reflexivity | exact Hp].
      - intros [v [-> Hp]]; left; exists (m, v); split; [exact Hp |].
        reflexivity.
    Qed.

    Lemma mem_liftModel_inr : forall S sigma x w,
        PF.PackageSet.In (inr x, w) (liftModel S sigma) <-> w = inr (sigma x).
    Proof.
      intros S sigma x w; unfold liftModel.
      rewrite PF.PackageSet.union_spec, SOpl.mem_map, mem_assignPkgs; split.
      - intros [[p [_ E]] | [x' E]]; [unfold liftPkg in E; discriminate E |].
        injection E as <- ->; reflexivity.
      - intros ->; right; exists x; reflexivity.
    Qed.

    Lemma satisfies_liftFormula : forall Y_x S sigma psi,
        (forall x, YSet.In (sigma x) (Y_x x)) ->
        (Satisfies S sigma psi <->
         PF.Satisfies (liftModel S sigma) (liftFormula Y_x psi)).
    Proof.
      intros Y_x S sigma psi Hs;
        induction psi
          as [m vs | psiL IHa psiR IHb | psiL IHa psiR IHb | psi' IHa | x op y];
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
        forall (R : PackageSet.t) (D : DependencyRel.t) (r : Package.t) (S : Reduced.PackageSet.t),
          Reduced.IsResolution (reduceReal Y_x R D) (reduceDeps Y_x R D)
            (embedPkg r) S ->
          IsResolution Y_x R D r (variableFormulaResolution S)
            (assignment y0 Y_x S).
    Proof.
      intros y0 Y_x Hne R D r S Hres.
      set (sigma := assignment y0 Y_x S).
      assert (Hres' := Hres); destruct Hres' as [Hsub Hroot Hdep Huniq].
      assert (Hreal : forall n w,
                 Reduced.PackageSet.In (Name.Orig n, Version.Orig w) S ->
                 PF.PackageSet.In (n, w) (liftReal Y_x R)).
      { intros n w H.
        exact (PF.Reduction.embedPkg_mem_reduceReal (n, w) _ _ (Hsub _ H)). }
      assert (Hsig : forall x, YSet.In (sigma x) (Y_x x)).
      { intro x; unfold sigma, assignment.
        destruct (YSet.min_elt (assignCand S x)) as [y |] eqn:E.
        - apply YSet.min_elt_spec1, mem_assignCand, Hreal, mem_liftReal in E.
          destruct E as [[m [v [_ E]]] | [x' [y' [Hy E]]]]; [discriminate E |].
          injection E as -> ->; exact Hy.
        - destruct (Hne x) as [y' Hy'].
          destruct (YSet.min_elt (Y_x x)) as [y |] eqn:E2.
          + exact (YSet.min_elt_spec1 E2).
          + exfalso; apply YSet.min_elt_spec3 in E2; exact (E2 y' Hy'). }
      set (ps := liftModel (variableFormulaResolution S) sigma).
      assert (HM : PF.Reduction.AgreesOn S ps).
      { intros [m | x] w Hn; unfold ps.
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
            by exact (assignment_at y0 Y_x S x y Huniq Hu).
          rewrite Hs; split.
          + intros ->; exact Hu.
          + intro Hw; assert (E := Huniq _ _ _ Hu Hw).
            injection E as E'; exact (eq_sym E'). }
      constructor.
      - intros [m v] Hp; apply mem_variableFormulaResolution in Hp.
        apply (Hreal (inl m) (inl v)), mem_liftReal in Hp.
        destruct Hp as [[m' [v' [Hp E]]] | [x [y [_ E]]]]; [| discriminate E].
        injection E as <- <-; exact Hp.
      - apply mem_variableFormulaResolution; exact Hroot.
      - intros p Hp psi Hdf.
        apply (satisfies_liftFormula Y_x _ sigma psi Hsig).
        apply (PF.Reduction.package_formula_soundness_agree
                 (liftReal Y_x R) (liftDeps Y_x D) (liftPkg r) S ps Hres HM
                 (liftPkg p) (liftFormula Y_x psi)).
        + apply PF.Reduction.mem_packageFormulaResolution.
          apply mem_variableFormulaResolution in Hp; exact Hp.
        + apply mem_liftDeps; exists p, psi; auto.
      - intros m v v' Hv Hv'.
        apply mem_variableFormulaResolution in Hv, Hv'.
        unfold embedPkg, PF.Reduction.embedPkg, liftPkg in Hv, Hv'.
        cbn [fst snd] in Hv, Hv'.
        assert (E := Huniq _ _ _ Hv Hv'); injection E as E; exact E.
      - exact Hsig.
    Qed.

    Definition coreResolution (Y_x : X.t -> YSet.t) (R : PackageSet.t)
        (D : DependencyRel.t) (S : PackageSet.t) (sigma : X.t -> Y.t) : Reduced.PackageSet.t :=
      PF.Reduction.coreResolution (liftReal Y_x R) (liftDeps Y_x D)
        (liftModel S sigma).

    Theorem variable_formula_completeness :
      forall (Y_x : X.t -> YSet.t) (R : PackageSet.t) (D : DependencyRel.t)
             (r : Package.t) (S : PackageSet.t) (sigma : X.t -> Y.t),
        IsResolution Y_x R D r S sigma ->
        Reduced.IsResolution (reduceReal Y_x R D) (reduceDeps Y_x R D) (embedPkg r)
          (coreResolution Y_x R D S sigma).
    Proof.
      intros Y_x R D r S sigma [Hsub Hroot Hclo Huniq Hs].
      apply PF.Reduction.formula_calculus_completeness.
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
            apply mem_liftDeps in Hg; destruct Hg as [[m' v'] [psi [Hd E]]].
            unfold liftPkg in E; cbn [fst snd] in E.
            injection E as <- <- ->.
            apply (satisfies_liftFormula Y_x S sigma psi Hs).
            exact (Hclo _ Hv psi Hd).
          * apply mem_liftDeps in Hg; destruct Hg as [p [psi [_ E]]].
            unfold liftPkg in E; discriminate E.
        + intros [m | x] w w' Hw Hw'.
          * apply mem_liftModel_inl in Hw, Hw'.
            destruct Hw as [v [-> Hv]]; destruct Hw' as [v' [-> Hv']].
            rewrite (Huniq _ _ _ Hv Hv'); reflexivity.
          * apply mem_liftModel_inr in Hw, Hw'; congruence.
      - intros [m | x] _ Ha; [cbv [Ab.hasAbsent] in Ha; discriminate Ha |].
        exists (inr (sigma x)); apply mem_liftModel_inr; reflexivity.
    Qed.

    Theorem variable_formula_retraction : forall y0 Y_x S R D sigma,
        variableFormulaResolution (coreResolution Y_x R D S sigma) = S /\
        forall x,
          assignment y0 Y_x (coreResolution Y_x R D S sigma) x = sigma x.
    Proof.
      intros y0 Y_x S R D sigma; split.
      { apply PackageSet.ext; intros [m v].
        rewrite mem_variableFormulaResolution; unfold embedPkg, coreResolution.
        rewrite <- PF.Reduction.mem_packageFormulaResolution,
          PF.Reduction.package_formula_retraction.
        unfold liftPkg; cbn [fst snd]; rewrite mem_liftModel_inl; split.
        - intros [v' [E Hv]]; injection E as <-; exact Hv.
        - intro Hv; exists v; split; [reflexivity | exact Hv]. }
      intro x.
      assert (Hc : forall y,
                 YSet.In y (assignCand (coreResolution Y_x R D S sigma) x) <->
                 y = sigma x).
      { intro y; rewrite mem_assignCand; unfold coreResolution.
        change (Name.Orig (inr x), Version.Orig (inr y))
          with (PF.Reduction.embedPkg (inr x, inr y)).
        rewrite <- PF.Reduction.mem_packageFormulaResolution,
          PF.Reduction.package_formula_retraction,
          mem_liftModel_inr.
        split; [intro E; injection E as -> | intros ->]; reflexivity. }
      unfold assignment.
      destruct (YSet.min_elt (assignCand (coreResolution Y_x R D S sigma) x))
        as [y |] eqn:E.
      - apply YSet.min_elt_spec1, Hc in E; exact E.
      - exfalso; apply YSet.min_elt_spec3 in E.
        exact (E (sigma x) (proj2 (Hc _) eq_refl)).
    Qed.

    Module Lookup.
      Module PackageSetFibred := FibredRel N V Package PackageSet.
      Module DependencyRelFibred := FibredRel Package Dependee DependencyElt DependencyRel.

      Fixpoint ownNegNames (psi : Formula) : NSet.t :=
        match psi with
        | FAtom _ _ => NSet.empty
        | FConj psiL psiR => NSet.union (ownNegNames psiL) (ownNegNames psiR)
        | FDisj _ _ => NSet.empty
        | FNeg psi' => ownNegNamesNeg psi'
        | FVarCmp _ _ _ => NSet.empty
        end
      with ownNegNamesNeg (psi : Formula) : NSet.t :=
        match psi with
        | FAtom m _ => NSet.singleton m
        | FConj _ _ => NSet.empty
        | FDisj psiL psiR =>
            NSet.union (ownNegNamesNeg psiL) (ownNegNamesNeg psiR)
        | FNeg psi' => ownNegNames psi'
        | FVarCmp _ _ _ => NSet.empty
        end.

      Module SOen := SetOps DependencyElt N DependencyRel NSet.
      Definition ownNegDepNames (D : DependencyRel.t) : NSet.t :=
        SOen.unionMap (fun e => ownNegNames (snd e)) D.

      Definition valuesAt (Y_x : X.t -> YSet.t) (x : X.t) : X.t -> YSet.t :=
        fun x' => if X.eq_dec x x' then Y_x x else YSet.empty.

      Lemma ownNegNames_liftFormula : forall Y_x psi m,
          (PF.Reduction.NSet.In (inl m)
             (PF.Reduction.Lookup.ownNegNames (liftFormula Y_x psi)) ->
           NSet.In m (ownNegNames psi)) /\
          (PF.Reduction.NSet.In (inl m)
             (PF.Reduction.Lookup.ownNegNamesNeg (liftFormula Y_x psi)) ->
           NSet.In m (ownNegNamesNeg psi)).
      Proof.
        intros Y_x psi m;
          induction psi
            as [o vs | psiL IHa psiR IHb | psiL IHa psiR IHb | psi' IHa
               | x op y];
          cbn [liftFormula PF.Reduction.Lookup.ownNegNames
               PF.Reduction.Lookup.ownNegNamesNeg ownNegNames ownNegNamesNeg];
          split; intro H;
          try (destruct (PF.Reduction.NSet.empty_spec H)).
        - apply PF.Reduction.NSet.singleton_spec in H; injection H as ->.
          apply NSet.singleton_spec; reflexivity.
        - apply PF.Reduction.NSet.union_spec in H; apply NSet.union_spec.
          destruct H as [H | H];
            [left; exact (proj1 IHa H) | right; exact (proj1 IHb H)].
        - apply PF.Reduction.NSet.union_spec in H; apply NSet.union_spec.
          destruct H as [H | H];
            [left; exact (proj2 IHa H) | right; exact (proj2 IHb H)].
        - exact (proj2 IHa H).
        - exact (proj1 IHa H).
        - apply PF.Reduction.NSet.singleton_spec in H; discriminate H.
      Qed.

      Lemma ownNegDepNames_liftDeps : forall Y_x D m,
          PF.Reduction.NSet.In (inl m)
            (PF.Reduction.Lookup.ownNegDepNames (liftDeps Y_x D)) ->
          NSet.In m (ownNegDepNames D).
      Proof.
        intros Y_x D m Hn.
        apply PF.Reduction.Lookup.mem_ownNegDepNames in Hn.
        destruct Hn as [p [g [Hg Hm]]]; apply mem_liftDeps in Hg.
        destruct Hg as [p' [psi [Hf E]]]; injection E as _ ->.
        apply SOen.mem_unionMap; exists (p', psi); split; [exact Hf |].
        exact (proj1 (ownNegNames_liftFormula Y_x psi m) Hm).
      Qed.

      Lemma liftDeps_tailFibre : forall Y_x D (m : N.t) (v : V.t),
          PF.Reduction.Lookup.DependencyRelFibred.tailFibre (liftDeps Y_x D)
            (inl m, inl v) =
          liftDeps Y_x (DependencyRelFibred.tailFibre D (m, v)).
      Proof.
        intros Y_x D m v; apply PF.DependencyRel.ext; intros [p g].
        rewrite PF.Reduction.Lookup.DependencyRelFibred.mem_tailFibre, !mem_liftDeps.
        split.
        - intros [[[m' v'] [psi [Hd E]]] ->].
          unfold liftPkg in E; cbn [fst snd] in E; injection E as <- <- ->.
          exists (m, v), psi; split; [| reflexivity].
          apply DependencyRelFibred.mem_tailFibre; split; [exact Hd | reflexivity].
        - intros [p' [psi [Hd E]]].
          apply DependencyRelFibred.mem_tailFibre in Hd; destruct Hd as [Hd ->].
          injection E as -> ->.
          split; [exists (m, v), psi; split; [exact Hd | reflexivity] |].
          reflexivity.
      Qed.

      Theorem versions_lookupOrig :
        forall Y_x R D (m : N.t) (u : V.t) (n : N.t),
          PackageSet.In (m, u) R ->
          (exists p h,
              Reduced.DependencyRel.In (p, (Name.Orig (inl n), h)) (reduceDeps Y_x R D)) \/
          n = m ->
          Reduced.versions (reduceReal Y_x R D) (Name.Orig (inl n)) =
          Reduced.VSet.add Version.Bot
            (Reduced.versions
               (reduceReal (fun _ => YSet.empty) (PackageSetFibred.tailFibre R n)
                  DependencyRel.empty)
               (Name.Orig (inl n))).
      Proof.
        intros Y_x R D m u n Hr Hreach.
        assert (Hr' : PF.PackageSet.In (inl m, inl u) (liftReal Y_x R))
          by (apply mem_liftReal; left; exists m, u;
              split; [exact Hr | reflexivity]).
        unfold reduceReal; rewrite (PF.Reduction.Lookup.versions_lookupOrig
                                      _ _ (inl m) (inl u) (inl n) Hr').
        - rewrite !PF.Reduction.Lookup.versions_reduceReal_bot.
          do 2 f_equal; apply PF.Source.versions_ext; intro w.
          rewrite PF.Reduction.Lookup.PackageSetFibred.mem_tailFibre, !mem_liftReal.
          split.
          + intros [[[m' [v [Hp E]]] | [x [y [_ E]]]] _]; [| discriminate E].
            injection E as <- ->; left; exists n, v; split; [| reflexivity].
            apply PackageSetFibred.mem_tailFibre; split; [exact Hp | reflexivity].
          + intros [[m' [v [Hp E]]] | [x [y [Hy _]]]];
              [| destruct (YSet.empty_spec Hy)].
            apply PackageSetFibred.mem_tailFibre in Hp; destruct Hp as [Hp Hm].
            cbn [fst] in Hm; subst m'; injection E as ->.
            split; [left; exists n, v; split; [exact Hp | reflexivity] |].
            reflexivity.
        - destruct Hreach as [H | ->]; [left; exact H | right; reflexivity].
        - reflexivity.
      Qed.

      Theorem versions_lookupVar : forall Y_x R D (x : X.t),
          Reduced.versions (reduceReal Y_x R D) (Name.Orig (inr x)) =
          Reduced.versions (reduceReal (valuesAt Y_x x) PackageSet.empty DependencyRel.empty)
            (Name.Orig (inr x)).
      Proof.
        intros Y_x R D x; unfold reduceReal.
        rewrite !PF.Reduction.Lookup.versions_lookupOrigPresent
          by reflexivity.
        f_equal; apply PF.VSet.ext; intro w.
        rewrite !PF.Source.mem_versions,
          !PF.Reduction.Lookup.PackageSetFibred.mem_tailFibre, !mem_liftReal.
        split.
        - intros [[[m [v [_ E]]] | [x' [y [Hy E]]]] _]; [discriminate E |].
          injection E as <- ->; split; [| reflexivity].
          right; exists x, y; split; [| reflexivity].
          unfold valuesAt; destruct (X.eq_dec x x) as [_ | NE];
            [exact Hy | contradiction NE; reflexivity].
        - intros [[[m [v [Hv E]]] | [x' [y [Hy E]]]] _];
            [destruct (PackageSet.empty_spec Hv) |].
          injection E as <- ->; split; [| reflexivity].
          right; exists x, y; split; [| reflexivity].
          revert Hy; unfold valuesAt; destruct (X.eq_dec x x) as [_ | NE];
            [intro Hy; exact Hy | contradiction NE; reflexivity].
      Qed.

      Theorem dependees_lookupOrigBy : forall Y_x R D Vq n v,
          (forall m,
             NSet.In m (ownNegDepNames (DependencyRelFibred.tailFibre D (n, v))) ->
             Vq m = Source.versions R m) ->
          Reduced.dependees (reduceDeps Y_x R D)
            (Name.Orig (inl n), Version.Orig (inl v)) =
          Reduced.dependees (reduceDepsBy Y_x Vq (DependencyRelFibred.tailFibre D (n, v)))
            (Name.Orig (inl n), Version.Orig (inl v)).
      Proof.
        intros Y_x R D Vq n v HVq; unfold reduceDeps, reduceDepsBy.
        rewrite (PF.Reduction.Lookup.dependees_lookupOrigBy _ _
                   (liftOracle Y_x Vq)).
        - rewrite liftDeps_tailFibre; reflexivity.
        - rewrite liftDeps_tailFibre; intros [m' | x] Hn;
            rewrite versions_liftReal; [| reflexivity].
          cbn [liftOracle]; f_equal; apply HVq.
          exact (ownNegDepNames_liftDeps Y_x _ m' Hn).
      Qed.

      Theorem dependees_lookupOrig : forall Y_x R D n v,
          Reduced.dependees (reduceDeps Y_x R D)
            (Name.Orig (inl n), Version.Orig (inl v)) =
          Reduced.dependees
            (reduceDeps Y_x
               (Source.namePreimage R
                  (ownNegDepNames (DependencyRelFibred.tailFibre D (n, v))))
               (DependencyRelFibred.tailFibre D (n, v)))
            (Name.Orig (inl n), Version.Orig (inl v)).
      Proof.
        intros Y_x R D n v.
        rewrite (dependees_lookupOrigBy Y_x R D
                   (Source.versions (Source.namePreimage R
                      (ownNegDepNames (DependencyRelFibred.tailFibre D (n, v)))))),
          reduceDeps_by by
          (intros m Hn; apply Source.versions_namePreimage; exact Hn).
        reflexivity.
      Qed.

      Theorem dependees_lookupAbsent : forall Y_x R D n,
          Reduced.dependees (reduceDeps Y_x R D) (Name.Orig (inl n), Version.Bot) =
          Reduced.DependeeSet.empty.
      Proof.
        intros Y_x R D n; apply PF.Reduction.Lookup.dependees_lookupAbsent.
      Qed.

      Theorem dependees_lookupVar : forall Y_x R D x (y : Version.t),
          Reduced.dependees (reduceDeps Y_x R D) (Name.Orig (inr x), y) =
          Reduced.DependeeSet.empty.
      Proof.
        intros Y_x R D x y; apply Reduced.dependees_empty_iff; intros h H.
        apply PF.Reduction.mem_reduceDeps in H.
        destruct H as [p [g [Hg He]]].
        assert (E := proj1
                       (PF.Reduction.Lookup.encode_depender_orig_aux _ g)
                       _ _ _ _ He).
        apply mem_liftDeps in Hg; destruct Hg as [[m v] [psi [_ Ep]]].
        injection Ep as -> _.
        unfold PF.Reduction.embedPkg, liftPkg in E; cbn [fst snd] in E.
        discriminate E.
      Qed.

      Theorem versions_lookupDisjunct : forall Y_x R D chis,
          (exists p h, Reduced.DependencyRel.In (p, (Name.Disjunct chis, h))
                         (reduceDeps Y_x R D)) ->
          Reduced.versions (reduceReal Y_x R D) (Name.Disjunct chis) =
          PF.Reduction.idxSet (List.length chis).
      Proof.
        intros Y_x R D chis H;
          exact (PF.Reduction.Lookup.versions_lookupDisjunct _ _ chis H).
      Qed.

      Theorem dependees_lookupDisjunct : forall Y_x R D chis (i : Version.t),
          Reduced.PackageSet.In (Name.Disjunct chis, i) (reduceReal Y_x R D) ->
          Reduced.dependees (reduceDeps Y_x R D) (Name.Disjunct chis, i) =
          match PF.Reduction.Lookup.disjAlt chis i with
          | Some chi =>
              Reduced.dependees
                (PF.Reduction.encode (liftOracle Y_x (Source.versions R))
                   (Name.Disjunct chis, i) chi)
                (Name.Disjunct chis, i)
          | None => Reduced.DependeeSet.empty
          end.
      Proof.
        intros Y_x R D chis i H; unfold reduceDeps.
        rewrite (PF.Reduction.Lookup.dependees_lookupDisjunct _ _ chis i H).
        destruct (PF.Reduction.Lookup.disjAlt chis i) as [chi |];
          [| reflexivity].
        f_equal.
        refine (proj1 (PF.Reduction.Lookup.encode_agree_aux _ _ chi _) _).
        intros n _; apply versions_liftReal.
      Qed.

      Theorem dependees_lookupDisjunctBy : forall Y_x R D R' D' Vq chis i,
          DependencyRel.Subset D' D ->
          Reduced.PackageSet.In (Name.Disjunct chis, i) (reduceReal Y_x R' D') ->
          (forall p psi m, DependencyRel.In (p, psi) D' ->
             PF.Reduction.NSet.In m
               (PF.Reduction.Lookup.negNames (liftFormula Y_x psi)) ->
             liftOracle Y_x Vq m = liftOracle Y_x (Source.versions R) m) ->
          Reduced.dependees (reduceDeps Y_x R D) (Name.Disjunct chis, i) =
          Reduced.dependees (reduceDepsBy Y_x Vq D') (Name.Disjunct chis, i).
      Proof.
        intros Y_x R D R' D' Vq chis i Hsub Hin HVq.
        unfold reduceDeps, reduceDepsBy.
        apply (PF.Reduction.Lookup.dependees_lookupDisjunctBy _ _
                 (liftReal Y_x R') (liftDeps Y_x D')).
        - intros e He; apply mem_liftDeps in He; apply mem_liftDeps.
          destruct He as [p [psi [Hd ->]]]; exists p, psi.
          split; [exact (Hsub _ Hd) | reflexivity].
        - exact Hin.
        - intros p psi' n Hg Hn; apply mem_liftDeps in Hg.
          destruct Hg as [p' [psi [Hf E]]]; injection E as _ ->.
          rewrite versions_liftReal; exact (HVq p' psi n Hf Hn).
      Qed.
    End Lookup.
  End Reduction.
End VariableFormula.
