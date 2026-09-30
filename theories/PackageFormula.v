From Stdlib Require Import MSets List Lia.
From PackageCalculus Require Import Prelude Core.

Create HintDb cmp_pkgf.
Create Rewrite HintDb cmp_pkgf.

(* Each spine-fused fixpoint family is four functions, so its lemmas are
   four-way conjunctions; repeat split would run past the conjunction and
   into the products and conjunctions of the conjuncts themselves. *)
Ltac split4 := split; [| split; [| split]].

Module Type AbsentNames (N : UsualOrderedType).
  Parameter hasAbsent : N.t -> bool.
End AbsentNames.

Module FormulaCalculus (N V : UsualOrderedType) (Ab : AbsentNames N).
  Module C := Core N V.
  Module Pkg := C.Pkg.
  Module PkgSet := C.PkgSet.
  Module VSet := C.VSet.

  Inductive Formula : Type :=
  | FDep (n : N.t) (vs : VSet.t)
  | FConj (psiL psiR : Formula)
  | FDisj (psiL psiR : Formula)
  | FNeg (psi : Formula).

  Fixpoint Satisfies (S : PkgSet.t) (psi : Formula) : Prop :=
    match psi with
    | FDep n vs => exists v, VSet.In v vs /\ PkgSet.In (n, v) S
    | FConj psiL psiR => Satisfies S psiL /\ Satisfies S psiR
    | FDisj psiL psiR => Satisfies S psiL \/ Satisfies S psiR
    | FNeg psi' => ~ Satisfies S psi'
    end.

  Fixpoint satisfiesb (S : PkgSet.t) (psi : Formula) : bool :=
    match psi with
    | FDep m vs => VSet.exists_ (fun v => PkgSet.mem (m, v) S) vs
    | FConj psiL psiR => andb (satisfiesb S psiL) (satisfiesb S psiR)
    | FDisj psiL psiR => orb (satisfiesb S psiL) (satisfiesb S psiR)
    | FNeg psi' => negb (satisfiesb S psi')
    end.

  Lemma satisfiesb_iff : forall S psi,
      satisfiesb S psi = true <-> Satisfies S psi.
  Proof.
    intros S psi;
      induction psi
        as [m vs | psiL IHa psiR IHb | psiL IHa psiR IHb | psi' IHa];
      simpl.
    - rewrite VSet.exists_spec'.
      split; intros [v [Hv Hm]]; exists v; split; try assumption;
        apply PkgSet.mem_spec; assumption.
    - rewrite Bool.andb_true_iff, IHa, IHb; reflexivity.
    - rewrite Bool.orb_true_iff, IHa, IHb; reflexivity.
    - rewrite Bool.negb_true_iff; split.
      + intros E Hs; apply IHa in Hs; congruence.
      + intro Hn; destruct (satisfiesb S psi') eqn:E; [| reflexivity].
        exfalso; apply Hn, IHa; reflexivity.
  Qed.

  Lemma satisfiesb_false_iff : forall S psi,
      satisfiesb S psi = false <-> ~ Satisfies S psi.
  Proof.
    intros S psi; split.
    - intros E Hs; apply satisfiesb_iff in Hs; congruence.
    - intro Hn; destruct (satisfiesb S psi) eqn:E; [| reflexivity].
      exfalso; apply Hn, satisfiesb_iff; exact E.
  Qed.

  Lemma satisfies_double_neg : forall S psi,
      ~ ~ Satisfies S psi -> Satisfies S psi.
  Proof.
    intros S psi Hnn; destruct (satisfiesb S psi) eqn:E.
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
    Definition rank (psi : Formula) : nat :=
      match psi with
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
      intros x;
        induction x
          as [n1 vs1 | psiL IHa psiR IHb | psiL IHa psiR IHb | psi' IHa];
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
      intros x;
        induction x
          as [n1 vs1 | psiL IHa psiR IHb | psiL IHa psiR IHb | psi' IHa];
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
        forall psi : Formula, DepRel.In (p, psi) D -> Satisfies S psi
    ; res_version_unique : C.VersionUnique S }.

  Module Reduction.
    Module DepF := UOTCompareFacts C.Dependees.
    Module FList := ListComp FComp.
    Module FListOT := UOTFromCompare FList.
    Module FListF := UOTCompareFacts FListOT.
    #[local] Hint Rewrite DepF.compare_eq_iff FListF.compare_eq_iff : cmp_pkgf.
    #[local] Hint Extern 1 => cmp_by DepF.compare_antisym : cmp_pkgf.
    #[local] Hint Extern 1 => cmp_by FListF.compare_antisym : cmp_pkgf.
    #[local] Hint Extern 1 => cmp_by DepF.compare_lt_trans : cmp_pkgf.
    #[local] Hint Extern 1 => cmp_by FListF.compare_lt_trans : cmp_pkgf.

    Module Name.
      Inductive name : Type :=
      | Orig (m : N.t)
      | Disjunct (chis : list Formula).
      Definition t := name.

      Definition compare (x y : t) : comparison :=
        match x, y with
        | Orig n1, Orig n2 => N.compare n1 n2
        | Orig _, Disjunct _ => Lt
        | Disjunct _, Orig _ => Gt
        | Disjunct chis1, Disjunct chis2 => FListOT.compare chis1 chis2
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
    Module NatF := UOTCompareFacts Nat_as_OT.
    #[local] Hint Rewrite VF.compare_eq_iff NatF.compare_eq_iff : cmp_pkgf.
    #[local] Hint Extern 1 => cmp_by VF.compare_antisym : cmp_pkgf.
    #[local] Hint Extern 1 => cmp_by NatF.compare_antisym : cmp_pkgf.
    #[local] Hint Extern 1 => cmp_by VF.compare_lt_trans : cmp_pkgf.
    #[local] Hint Extern 1 => cmp_by NatF.compare_lt_trans : cmp_pkgf.

    Module Version.
      Inductive version : Type :=
      | Orig (v : V.t)
      | Idx (i : nat)
      | Bot.
      Definition t := version.

      Definition compare (x y : t) : comparison :=
        match x, y with
        | Orig v1, Orig v2 => V.compare v1 v2
        | Orig _, _ => Lt
        | Idx _, Orig _ => Gt
        | Idx i, Idx j => Nat.compare i j
        | Idx _, Bot => Lt
        | Bot, Bot => Eq
        | Bot, _ => Gt
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
    Module NSet := C.NSet.

    Definition embedPkg (p : Pkg.t) : T.Pkg.t :=
      let '(m, v) := p in (Name.Orig m, Version.Orig v).

    Module SOvv := SetOps V VersionOT VSet T.VSet.
    Definition embedVS (vs : VSet.t) : T.VSet.t :=
      SOvv.map Version.Orig vs.

    Fixpoint disjSpine (psi : Formula) : list Formula :=
      match psi with
      | FDisj psiL psiR => psiL :: disjSpine psiR
      | _ => psi :: nil
      end.

    Fixpoint negConjSpine (psi : Formula) : list Formula :=
      match psi with
      | FConj psiL psiR => FNeg psiL :: negConjSpine psiR
      | _ => FNeg psi :: nil
      end.

    Definition idxSet (k : nat) : T.VSet.t :=
      T.VSet.ofList (List.map Version.Idx (List.seq 0 k)).

    Definition idxPkgs (n : Name.t) (k : nat) : T.PkgSet.t :=
      T.PkgSet.ofList (List.map (fun i => (n, Version.Idx i)) (List.seq 0 k)).

    Definition absentVS (m : N.t) (ws : T.VSet.t) : T.VSet.t :=
      if Ab.hasAbsent m then T.VSet.add Version.Bot ws else ws.

    Definition complementVS (Vq : N.t -> VSet.t) (m : N.t) (vs : VSet.t)
      : T.VSet.t :=
      absentVS m (embedVS (VSet.diff (Vq m) vs)).

    (* A De Morgan case would recurse on a rewritten term, demanding
       well-founded recursion on a measure under which negation strictly
       decreases; fusing one unfolding step keeps this pair structural.
       The spine walkers carry the position of the alternative they are
       encoding, and repeat their sibling's non-spine cases for the same
       reason: calling the sibling on the matched term itself would leave
       the guard condition. *)
    Fixpoint encodeNNF (Vq : N.t -> VSet.t) (p : T.Pkg.t) (psi : Formula)
      : T.DepRel.t :=
      match psi with
      | FDep m vs =>
          T.DepRel.singleton (p, (Name.Orig m, embedVS vs))
      | FConj psiL psiR =>
          T.DepRel.union (encodeNNF Vq p psiL) (encodeNNF Vq p psiR)
      | FDisj psiL psiR =>
          let n := Name.Disjunct (psiL :: disjSpine psiR) in
          T.DepRel.add (p, (n, idxSet (List.length (psiL :: disjSpine psiR))))
            (T.DepRel.union (encodeNNF Vq (n, Version.Idx 0) psiL)
               (encodeDisj Vq n 1 psiR))
      | FNeg psi' => encodeNNFneg Vq p psi'
      end
    with encodeDisj (Vq : N.t -> VSet.t) (n : Name.t) (i : nat) (psi : Formula)
      : T.DepRel.t :=
      match psi with
      | FDep m vs =>
          T.DepRel.singleton ((n, Version.Idx i), (Name.Orig m, embedVS vs))
      | FConj psiL psiR =>
          T.DepRel.union (encodeNNF Vq (n, Version.Idx i) psiL)
            (encodeNNF Vq (n, Version.Idx i) psiR)
      | FDisj psiL psiR =>
          T.DepRel.union (encodeNNF Vq (n, Version.Idx i) psiL)
            (encodeDisj Vq n (S i) psiR)
      | FNeg psi' => encodeNNFneg Vq (n, Version.Idx i) psi'
      end
    with encodeNNFneg (Vq : N.t -> VSet.t) (p : T.Pkg.t) (psi : Formula)
      : T.DepRel.t :=
      match psi with
      | FDep m vs =>
          T.DepRel.singleton (p, (Name.Orig m, complementVS Vq m vs))
      | FConj psiL psiR =>
          let n := Name.Disjunct (FNeg psiL :: negConjSpine psiR) in
          T.DepRel.add
            (p, (n, idxSet (List.length (FNeg psiL :: negConjSpine psiR))))
            (T.DepRel.union (encodeNNFneg Vq (n, Version.Idx 0) psiL)
               (encodeConjNeg Vq n 1 psiR))
      | FDisj psiL psiR =>
          T.DepRel.union (encodeNNFneg Vq p psiL) (encodeNNFneg Vq p psiR)
      | FNeg psi' => encodeNNF Vq p psi'
      end
    with encodeConjNeg (Vq : N.t -> VSet.t) (n : Name.t) (i : nat)
        (psi : Formula) : T.DepRel.t :=
      match psi with
      | FDep m vs =>
          T.DepRel.singleton ((n, Version.Idx i), (Name.Orig m, complementVS Vq m vs))
      | FConj psiL psiR =>
          T.DepRel.union (encodeNNFneg Vq (n, Version.Idx i) psiL)
            (encodeConjNeg Vq n (S i) psiR)
      | FDisj psiL psiR =>
          T.DepRel.union (encodeNNFneg Vq (n, Version.Idx i) psiL)
            (encodeNNFneg Vq (n, Version.Idx i) psiR)
      | FNeg psi' => encodeNNF Vq (n, Version.Idx i) psi'
      end.

    Fixpoint arisingPkgs (p : T.Pkg.t) (psi : Formula) : T.PkgSet.t :=
      match psi with
      | FDep _ _ => T.PkgSet.empty
      | FConj psiL psiR =>
          T.PkgSet.union (arisingPkgs p psiL) (arisingPkgs p psiR)
      | FDisj psiL psiR =>
          let n := Name.Disjunct (psiL :: disjSpine psiR) in
          T.PkgSet.union (idxPkgs n (List.length (psiL :: disjSpine psiR)))
            (T.PkgSet.union (arisingPkgs (n, Version.Idx 0) psiL)
               (arisingDisj n 1 psiR))
      | FNeg psi' => arisingNeg p psi'
      end
    with arisingDisj (n : Name.t) (i : nat) (psi : Formula) : T.PkgSet.t :=
      match psi with
      | FDep _ _ => T.PkgSet.empty
      | FConj psiL psiR =>
          T.PkgSet.union (arisingPkgs (n, Version.Idx i) psiL)
            (arisingPkgs (n, Version.Idx i) psiR)
      | FDisj psiL psiR =>
          T.PkgSet.union (arisingPkgs (n, Version.Idx i) psiL)
            (arisingDisj n (S i) psiR)
      | FNeg psi' => arisingNeg (n, Version.Idx i) psi'
      end
    with arisingNeg (p : T.Pkg.t) (psi : Formula) : T.PkgSet.t :=
      match psi with
      | FDep _ _ => T.PkgSet.empty
      | FConj psiL psiR =>
          let n := Name.Disjunct (FNeg psiL :: negConjSpine psiR) in
          T.PkgSet.union
            (idxPkgs n (List.length (FNeg psiL :: negConjSpine psiR)))
            (T.PkgSet.union (arisingNeg (n, Version.Idx 0) psiL)
               (arisingConjNeg n 1 psiR))
      | FDisj psiL psiR =>
          T.PkgSet.union (arisingNeg p psiL) (arisingNeg p psiR)
      | FNeg psi' => arisingPkgs p psi'
      end
    with arisingConjNeg (n : Name.t) (i : nat) (psi : Formula) : T.PkgSet.t :=
      match psi with
      | FDep _ _ => T.PkgSet.empty
      | FConj psiL psiR =>
          T.PkgSet.union (arisingNeg (n, Version.Idx i) psiL)
            (arisingConjNeg n (S i) psiR)
      | FDisj psiL psiR =>
          T.PkgSet.union (arisingNeg (n, Version.Idx i) psiL)
            (arisingNeg (n, Version.Idx i) psiR)
      | FNeg psi' => arisingPkgs (n, Version.Idx i) psi'
      end.

    Fixpoint fnames (psi : Formula) : NSet.t :=
      match psi with
      | FDep m _ => NSet.singleton m
      | FConj psiL psiR => NSet.union (fnames psiL) (fnames psiR)
      | FDisj psiL psiR => NSet.union (fnames psiL) (fnames psiR)
      | FNeg psi' => fnames psi'
      end.

    Module SOen := SetOps DepElt N DepRel NSet.
    Definition depNames (D : DepRel.t) : NSet.t :=
      SOen.unionMap (fun '(_, psi) => fnames psi) D.

    Module SOpn := SetOps Pkg N PkgSet NSet.
    Definition instNames (R : PkgSet.t) (D : DepRel.t) : NSet.t :=
      NSet.union (SOpn.map fst R) (depNames D).

    Module SOnt := SetOps N T.Pkg NSet T.PkgSet.
    Definition absentPkgs (ns : NSet.t) : T.PkgSet.t :=
      SOnt.filterMap (fun n =>
          if Ab.hasAbsent n then Some (Name.Orig n, Version.Bot) else None) ns.

    Module SOpt := SetOps Pkg T.Pkg PkgSet T.PkgSet.
    Module SOet := SetOps DepElt T.Pkg DepRel T.PkgSet.
    Definition reduceReal (R : PkgSet.t) (D : DepRel.t) : T.PkgSet.t :=
      T.PkgSet.union (SOpt.map embedPkg R)
        (T.PkgSet.union
           (SOet.unionMap (fun '(p, psi) => arisingPkgs (embedPkg p) psi) D)
           (absentPkgs (instNames R D))).

    Module SOed := SetOps DepElt T.DepElt DepRel T.DepRel.
    Definition reduceDepsBy (Vq : N.t -> VSet.t) (D : DepRel.t) : T.DepRel.t :=
      SOed.unionMap (fun '(p, psi) => encodeNNF Vq (embedPkg p) psi) D.

    Definition reduceDeps (R : PkgSet.t) (D : DepRel.t) : T.DepRel.t :=
      reduceDepsBy (C.versions R) D.

    Lemma mem_idxSet : forall k v,
        T.VSet.In v (idxSet k) <-> exists i, i < k /\ v = Version.Idx i.
    Proof.
      intros k v; unfold idxSet;
        rewrite T.VSet.mem_ofList, in_map_iff.
      split.
      - intros [i [<- Hi]]; apply in_seq in Hi.
        exists i; split; [lia | reflexivity].
      - intros [i [Hi ->]]; exists i; split; [reflexivity |].
        apply in_seq; lia.
    Qed.

    Lemma mem_idxPkgs : forall n k p,
        T.PkgSet.In p (idxPkgs n k) <->
        exists i, i < k /\ p = (n, Version.Idx i).
    Proof.
      intros n k p; unfold idxPkgs;
        rewrite T.PkgSet.mem_ofList, in_map_iff.
      split.
      - intros [i [<- Hi]]; apply in_seq in Hi.
        exists i; split; [lia | reflexivity].
      - intros [i [Hi ->]]; exists i; split; [reflexivity |].
        apply in_seq; lia.
    Qed.

    Lemma mem_complementVS : forall Vq m vs (v : Version.t),
        T.VSet.In v (complementVS Vq m vs) <->
        (v = Version.Bot /\ Ab.hasAbsent m = true) \/
        exists u, VSet.In u (Vq m) /\ ~ VSet.In u vs /\ v = Version.Orig u.
    Proof.
      intros Vq m vs v.
      assert (Hd : T.VSet.In v (embedVS (VSet.diff (Vq m) vs)) <->
                   exists u, VSet.In u (Vq m) /\ ~ VSet.In u vs /\
                             v = Version.Orig u).
      { unfold embedVS; rewrite SOvv.mem_map; split.
        - intros [u [Hu ->]]; apply VSet.diff_spec in Hu.
          destruct Hu as [Hu Hnv]; exists u; auto.
        - intros [u [Hu [Hnv ->]]]; exists u; split; [| reflexivity].
          apply VSet.diff_spec; split; assumption. }
      unfold complementVS, absentVS; destruct (Ab.hasAbsent m).
      - rewrite SOvv.add_in, Hd; split; intros [H | H];
          [left; split; [exact H | reflexivity] | right; exact H
          | left; exact (proj1 H) | right; exact H].
      - rewrite Hd; split; [intro H; right; exact H |].
        intros [[_ E] | H]; [discriminate E | exact H].
    Qed.

    Lemma mem_depNames : forall D (n : N.t),
        NSet.In n (depNames D) <->
        exists p psi, DepRel.In (p, psi) D /\ NSet.In n (fnames psi).
    Proof.
      intros D n; unfold depNames; rewrite SOen.mem_unionMap.
      split.
      - intros [[q chi] [He Hn]]; exists q, chi; split; [exact He | exact Hn].
      - intros [q [chi [Hq Hn]]]; exists (q, chi); split; [exact Hq | exact Hn].
    Qed.

    Lemma mem_instNames : forall R D (n : N.t),
        NSet.In n (instNames R D) <->
        (exists u, PkgSet.In (n, u) R) \/ NSet.In n (depNames D).
    Proof.
      intros R D n; unfold instNames.
      rewrite NSet.union_spec, SOpn.mem_map.
      split.
      - intros [[[m v] [HR Hm]] | H]; [simpl in Hm; subst | right; exact H].
        left; exists v; exact HR.
      - intros [[v HR] | H]; [| right; exact H].
        left; exists (n, v); split; [exact HR | reflexivity].
    Qed.

    Lemma mem_absentPkgs : forall ns (p : T.Pkg.t),
        T.PkgSet.In p (absentPkgs ns) <->
        exists n, NSet.In n ns /\ Ab.hasAbsent n = true /\
                  p = (Name.Orig n, Version.Bot).
    Proof.
      intros ns p; unfold absentPkgs; rewrite SOnt.mem_filterMap; split.
      - intros [n [Hn Hf]]; destruct (Ab.hasAbsent n) eqn:Ha;
          [| discriminate Hf].
        injection Hf as <-; exists n; auto.
      - intros [n [Hn [Ha ->]]]; exists n; split; [exact Hn |].
        rewrite Ha; reflexivity.
    Qed.

    Lemma mem_reduceReal : forall R D (p' : T.Pkg.t),
        T.PkgSet.In p' (reduceReal R D) <->
        (exists p, PkgSet.In p R /\ p' = embedPkg p) \/
        (exists p psi, DepRel.In (p, psi) D /\
                     T.PkgSet.In p' (arisingPkgs (embedPkg p) psi)) \/
        (exists n, NSet.In n (instNames R D) /\ Ab.hasAbsent n = true /\
                   p' = (Name.Orig n, Version.Bot)).
    Proof.
      intros R D p'; unfold reduceReal.
      rewrite !T.PkgSet.union_spec, SOpt.mem_map, SOet.mem_unionMap,
        mem_absentPkgs.
      split.
      - intros [H | [[[q chi] [He Hy]] | H]];
          [left; exact H | | right; right; exact H].
        right; left; exists q, chi; split; [exact He | exact Hy].
      - intros [H | [[q [chi [Hd Hy]]] | H]];
          [left; exact H | | right; right; exact H].
        right; left; exists (q, chi); split; [exact Hd | exact Hy].
    Qed.

    Lemma mem_reduceDepsBy : forall Vq D (d : T.DepElt.t),
        T.DepRel.In d (reduceDepsBy Vq D) <->
        exists p psi, DepRel.In (p, psi) D /\
                    T.DepRel.In d (encodeNNF Vq (embedPkg p) psi).
    Proof.
      intros Vq D d; unfold reduceDepsBy; rewrite SOed.mem_unionMap.
      split.
      - intros [[q chi] [He Hd]]; exists q, chi; split; [exact He | exact Hd].
      - intros [q [chi [Hq Hd]]]; exists (q, chi); split; [exact Hq | exact Hd].
    Qed.

    Lemma mem_reduceDeps : forall R D (d : T.DepElt.t),
        T.DepRel.In d (reduceDeps R D) <->
        exists p psi, DepRel.In (p, psi) D /\
                    T.DepRel.In d (encodeNNF (C.versions R) (embedPkg p) psi).
    Proof. intros R D d; apply mem_reduceDepsBy. Qed.

    Definition tryInvPkg (p' : T.Pkg.t) : option Pkg.t :=
      match p' with
      | (Name.Orig m, Version.Orig v) => Some (m, v)
      | _ => None
      end.

    Lemma tryInvPkg_embed : forall p, tryInvPkg (embedPkg p) = Some p.
    Proof. intros [m v]; reflexivity. Qed.

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

    Definition SyntheticName (n : Name.t) : Prop :=
      exists chis, n = Name.Disjunct chis.

    Lemma arisingPkgs_name_classify_aux : forall psi : Formula,
        (forall (p : T.Pkg.t) (n : Name.t) (v : Version.t),
            T.PkgSet.In (n, v) (arisingPkgs p psi) -> SyntheticName n) /\
        (forall (p : T.Pkg.t) (n : Name.t) (v : Version.t),
            T.PkgSet.In (n, v) (arisingNeg p psi) -> SyntheticName n) /\
        (forall (n' : Name.t) (i : nat) (n : Name.t) (v : Version.t),
            T.PkgSet.In (n, v) (arisingDisj n' i psi) -> SyntheticName n) /\
        (forall (n' : Name.t) (i : nat) (n : Name.t) (v : Version.t),
            T.PkgSet.In (n, v) (arisingConjNeg n' i psi) -> SyntheticName n).
    Proof.
      unfold SyntheticName;
        induction psi
          as [m ws | psiL IHa psiR IHb | psiL IHa psiR IHb | psi' IHa].
      - split4; intros; exfalso; eapply SOpt.empty_in; eassumption.
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
          destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4.
        + intros p n v H; simpl in H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exact (IHa1 _ _ _ H) | exact (IHb1 _ _ _ H)].
        + intros p n v H; simpl in H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [apply mem_idxPkgs in H; destruct H as [j [_ E]];
             injection E as -> _; eauto |].
          apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exact (IHa2 _ _ _ H) | exact (IHb4 _ _ _ _ H)].
        + intros n' i n v H; simpl in H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exact (IHa1 _ _ _ H) | exact (IHb1 _ _ _ H)].
        + intros n' i n v H; simpl in H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exact (IHa2 _ _ _ H) | exact (IHb4 _ _ _ _ H)].
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
          destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4.
        + intros p n v H; simpl in H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [apply mem_idxPkgs in H; destruct H as [j [_ E]];
             injection E as -> _; eauto |].
          apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exact (IHa1 _ _ _ H) | exact (IHb3 _ _ _ _ H)].
        + intros p n v H; simpl in H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exact (IHa2 _ _ _ H) | exact (IHb2 _ _ _ H)].
        + intros n' i n v H; simpl in H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exact (IHa1 _ _ _ H) | exact (IHb3 _ _ _ _ H)].
        + intros n' i n v H; simpl in H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exact (IHa2 _ _ _ H) | exact (IHb2 _ _ _ H)].
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4); split4.
        + intros p n v H; exact (IHa2 _ _ _ H).
        + intros p n v H; exact (IHa1 _ _ _ H).
        + intros n' i n v H; exact (IHa2 _ _ _ H).
        + intros n' i n v H; exact (IHa1 _ _ _ H).
    Qed.

    Lemma arisingPkgs_not_orig : forall (p : T.Pkg.t) (psi : Formula) m v,
        ~ T.PkgSet.In (Name.Orig m, v) (arisingPkgs p psi).
    Proof.
      intros p psi m v H.
      destruct (proj1 (arisingPkgs_name_classify_aux psi) _ _ _ H) as [chis E];
        discriminate.
    Qed.

    Lemma embedPkg_mem_reduceReal : forall (p : Pkg.t) R D,
        T.PkgSet.In (embedPkg p) (reduceReal R D) -> PkgSet.In p R.
    Proof.
      intros [pn pv] R D H; apply mem_reduceReal in H.
      destruct H as [[q [HqR Hq]] | [[q [chi [_ Hy]]] | [n [_ [_ Hy]]]]].
      - apply embedPkg_injective in Hq as ->; exact HqR.
      - exfalso; exact (arisingPkgs_not_orig _ _ _ _ Hy).
      - discriminate Hy.
    Qed.

    Definition AgreesOn (S : T.PkgSet.t) (ps : PkgSet.t) : Prop :=
      forall m v,
        (Ab.hasAbsent m = true \/
         exists u, T.PkgSet.In (Name.Orig m, Version.Orig u) S) ->
        (PkgSet.In (m, v) ps <->
         T.PkgSet.In (Name.Orig m, Version.Orig v) S).

    Lemma agreesOn_resolution : forall S,
        AgreesOn S (packageFormulaResolution S).
    Proof.
      intros S m v _; rewrite mem_packageFormulaResolution; reflexivity.
    Qed.

    Lemma encodeNNF_satisfies : forall (R : T.PkgSet.t) (D : T.DepRel.t)
                                    (r : T.Pkg.t) (S : T.PkgSet.t) ps,
        T.IsResolution R D r S -> AgreesOn S ps ->
        forall (Vq : N.t -> VSet.t) (q : T.Pkg.t) (psi : Formula),
          (forall d, T.DepRel.In d (encodeNNF Vq q psi) -> T.DepRel.In d D) ->
          T.PkgSet.In q S ->
          Satisfies ps psi.
    Proof.
      intros R D r S ps Hres HM Vq; destruct Hres as [Hsub Hroot Hdep Huniq].
      cut (forall psi : Formula,
        (forall q : T.Pkg.t,
            (forall d, T.DepRel.In d (encodeNNF Vq q psi) -> T.DepRel.In d D) ->
            T.PkgSet.In q S -> Satisfies ps psi) /\
        (forall q : T.Pkg.t,
            (forall d, T.DepRel.In d (encodeNNFneg Vq q psi) ->
               T.DepRel.In d D) ->
            T.PkgSet.In q S -> ~ Satisfies ps psi) /\
        (forall (n : Name.t) (i0 i : nat),
            (forall d, T.DepRel.In d (encodeDisj Vq n i0 psi) ->
               T.DepRel.In d D) ->
            T.PkgSet.In (n, Version.Idx i) S ->
            i0 <= i -> i < i0 + List.length (disjSpine psi) ->
            Satisfies ps psi) /\
        (forall (n : Name.t) (i0 i : nat),
            (forall d,
                T.DepRel.In d (encodeConjNeg Vq n i0 psi) -> T.DepRel.In d D) ->
            T.PkgSet.In (n, Version.Idx i) S ->
            i0 <= i -> i < i0 + List.length (negConjSpine psi) ->
            ~ Satisfies ps psi)).
      { intros H q psi; exact (proj1 (H psi) q). }
      assert (Hpos : forall (q : T.Pkg.t) m vs,
                 T.DepRel.In (q, (Name.Orig m, embedVS vs)) D ->
                 T.PkgSet.In q S ->
                 Satisfies ps (FDep m vs)).
      { intros q m vs Hd HqS.
        destruct (Hdep q HqS _ _ Hd) as [w [Hw HwS]].
        unfold embedVS in Hw; apply SOvv.mem_map in Hw;
          destruct Hw as [v [Hv ->]].
        exists v; split; [exact Hv |].
        apply (HM m v); [right; exists v; exact HwS | exact HwS]. }
      assert (Hneg : forall (q : T.Pkg.t) m vs,
                 T.DepRel.In (q, (Name.Orig m, complementVS Vq m vs)) D ->
                 T.PkgSet.In q S ->
                 ~ Satisfies ps (FDep m vs)).
      { intros q m vs Hd HqS.
        destruct (Hdep q HqS _ _ Hd) as [w [Hw HwS]].
        intros [v [Hv HvM]].
        apply mem_complementVS in Hw.
        destruct Hw as [[-> Ha] | [u [_ [Hnv ->]]]].
        - apply (HM m v (or_introl Ha)) in HvM.
          assert (E := Huniq _ _ _ HwS HvM); discriminate E.
        - apply (HM m v (or_intror (ex_intro _ u HwS))) in HvM.
          assert (E := Huniq _ _ _ HwS HvM); injection E as ->.
          exact (Hnv Hv). }
      induction psi
        as [m vs | psiL IHa psiR IHb | psiL IHa psiR IHb | psi' IHa].
      - split4.
        + intros q Henc HqS; apply (Hpos q); [| exact HqS].
          apply Henc; simpl; apply SOed.singleton_in; reflexivity.
        + intros q Henc HqS; apply (Hneg q m vs); [| exact HqS].
          apply Henc; simpl; apply SOed.singleton_in; reflexivity.
        + intros n i0 i Henc HiS Hle Hlt; simpl in Hlt.
          assert (i = i0) as -> by lia.
          apply (Hpos (n, Version.Idx i0)); [| exact HiS].
          apply Henc; simpl; apply SOed.singleton_in; reflexivity.
        + intros n i0 i Henc HiS Hle Hlt; simpl in Hlt.
          assert (i = i0) as -> by lia.
          apply (Hneg (n, Version.Idx i0) m vs); [| exact HiS].
          apply Henc; simpl; apply SOed.singleton_in; reflexivity.
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
          destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4.
        + intros q Henc HqS; simpl; split.
          * apply (IHa1 q); [| exact HqS].
            intros d Hd; apply Henc; simpl;
              apply T.DepRel.union_spec; left; exact Hd.
          * apply (IHb1 q); [| exact HqS].
            intros d Hd; apply Henc; simpl;
              apply T.DepRel.union_spec; right; exact Hd.
        + intros q Henc HqS; simpl.
          set (n := Name.Disjunct (FNeg psiL :: negConjSpine psiR)).
          assert (Hd : T.DepRel.In
                    (q, (n, idxSet
                           (List.length (FNeg psiL :: negConjSpine psiR)))) D).
          { apply Henc; simpl; apply SOed.add_in; left; reflexivity. }
          destruct (Hdep q HqS _ _ Hd) as [w [Hw HwS]].
          apply mem_idxSet in Hw; destruct Hw as [i [Hi ->]].
          simpl in Hi; intros [HsatA HsatB].
          destruct i as [| i'].
          * refine (IHa2 (n, Version.Idx 0) _ HwS HsatA).
            intros d Hd'; apply Henc; simpl; apply SOed.add_in; right;
              apply T.DepRel.union_spec; left; exact Hd'.
          * refine (IHb4 n 1 (Datatypes.S i') _ HwS _ _ HsatB); [| lia | simpl; lia].
            intros d Hd'; apply Henc; simpl; apply SOed.add_in; right;
              apply T.DepRel.union_spec; right; exact Hd'.
        + intros n i0 i Henc HiS Hle Hlt; simpl in Hlt.
          assert (i = i0) as -> by lia; simpl; split.
          * apply (IHa1 (n, Version.Idx i0)); [| exact HiS].
            intros d Hd; apply Henc; simpl;
              apply T.DepRel.union_spec; left; exact Hd.
          * apply (IHb1 (n, Version.Idx i0)); [| exact HiS].
            intros d Hd; apply Henc; simpl;
              apply T.DepRel.union_spec; right; exact Hd.
        + intros n i0 i Henc HiS Hle Hlt; simpl in Hlt; simpl.
          intros [HsatA HsatB].
          destruct (Nat_as_OT.eq_dec i i0) as [-> | Hne].
          * refine (IHa2 (n, Version.Idx i0) _ HiS HsatA).
            intros d Hd; apply Henc; simpl;
              apply T.DepRel.union_spec; left; exact Hd.
          * refine (IHb4 n (Datatypes.S i0) i _ HiS _ _ HsatB); [| lia | lia].
            intros d Hd; apply Henc; simpl;
              apply T.DepRel.union_spec; right; exact Hd.
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
          destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4.
        + intros q Henc HqS; simpl.
          set (n := Name.Disjunct (psiL :: disjSpine psiR)).
          assert (Hd : T.DepRel.In
                    (q, (n, idxSet (List.length (psiL :: disjSpine psiR)))) D).
          { apply Henc; simpl; apply SOed.add_in; left; reflexivity. }
          destruct (Hdep q HqS _ _ Hd) as [w [Hw HwS]].
          apply mem_idxSet in Hw; destruct Hw as [i [Hi ->]].
          simpl in Hi; destruct i as [| i'].
          * left; apply (IHa1 (n, Version.Idx 0)); [| exact HwS].
            intros d Hd'; apply Henc; simpl; apply SOed.add_in; right;
              apply T.DepRel.union_spec; left; exact Hd'.
          * right; refine (IHb3 n 1 (Datatypes.S i') _ HwS _ _); [| lia | simpl; lia].
            intros d Hd'; apply Henc; simpl; apply SOed.add_in; right;
              apply T.DepRel.union_spec; right; exact Hd'.
        + intros q Henc HqS; simpl; intros [HsatA | HsatB].
          * refine (IHa2 q _ HqS HsatA).
            intros d Hd; apply Henc; simpl;
              apply T.DepRel.union_spec; left; exact Hd.
          * refine (IHb2 q _ HqS HsatB).
            intros d Hd; apply Henc; simpl;
              apply T.DepRel.union_spec; right; exact Hd.
        + intros n i0 i Henc HiS Hle Hlt; simpl in Hlt; simpl.
          destruct (Nat_as_OT.eq_dec i i0) as [-> | Hne].
          * left; apply (IHa1 (n, Version.Idx i0)); [| exact HiS].
            intros d Hd; apply Henc; simpl;
              apply T.DepRel.union_spec; left; exact Hd.
          * right; refine (IHb3 n (Datatypes.S i0) i _ HiS _ _); [| lia | lia].
            intros d Hd; apply Henc; simpl;
              apply T.DepRel.union_spec; right; exact Hd.
        + intros n i0 i Henc HiS Hle Hlt; simpl in Hlt.
          assert (i = i0) as -> by lia; simpl; intros [HsatA | HsatB].
          * refine (IHa2 (n, Version.Idx i0) _ HiS HsatA).
            intros d Hd; apply Henc; simpl;
              apply T.DepRel.union_spec; left; exact Hd.
          * refine (IHb2 (n, Version.Idx i0) _ HiS HsatB).
            intros d Hd; apply Henc; simpl;
              apply T.DepRel.union_spec; right; exact Hd.
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4); split4.
        + intros q Henc HqS; exact (IHa2 q Henc HqS).
        + intros q Henc HqS; simpl; intro Hn; exact (Hn (IHa1 q Henc HqS)).
        + intros n i0 i Henc HiS Hle Hlt; simpl in Hlt.
          assert (i = i0) as -> by lia.
          exact (IHa2 (n, Version.Idx i0) Henc HiS).
        + intros n i0 i Henc HiS Hle Hlt; simpl in Hlt.
          assert (i = i0) as -> by lia; simpl; intro Hn.
          exact (Hn (IHa1 (n, Version.Idx i0) Henc HiS)).
    Qed.

    Theorem package_formula_soundness :
      forall (R : PkgSet.t) (D : DepRel.t) (r : Pkg.t) (S : T.PkgSet.t),
        T.IsResolution (reduceReal R D) (reduceDeps R D) (embedPkg r) S ->
        IsResolution R D r (packageFormulaResolution S).
    Proof.
      intros R D r S Hres.
      assert (H := Hres); destruct H as [Hsub Hroot Hdep Huniq].
      constructor.
      - intros p Hp; apply mem_packageFormulaResolution in Hp.
        exact (embedPkg_mem_reduceReal p R D (Hsub _ Hp)).
      - apply mem_packageFormulaResolution; exact Hroot.
      - intros p Hp psi Hdf.
        apply mem_packageFormulaResolution in Hp.
        apply (encodeNNF_satisfies _ _ _ _ _ Hres (agreesOn_resolution S)
                 (C.versions R) (embedPkg p) psi); [| exact Hp].
        intros d Hd; apply mem_reduceDeps;
          exists p, psi; split; [exact Hdf | exact Hd].
      - intros m v v' Hv Hv'.
        apply mem_packageFormulaResolution in Hv, Hv'.
        unfold embedPkg in Hv, Hv'; simpl in Hv, Hv'.
        assert (E := Huniq _ _ _ Hv Hv').
        injection E as E; exact E.
    Qed.

    Lemma package_formula_soundness_agree :
      forall (R : PkgSet.t) (D : DepRel.t) (r : Pkg.t) (S : T.PkgSet.t) ps,
        T.IsResolution (reduceReal R D) (reduceDeps R D) (embedPkg r) S ->
        AgreesOn S ps ->
        forall p psi, PkgSet.In p (packageFormulaResolution S) ->
          DepRel.In (p, psi) D -> Satisfies ps psi.
    Proof.
      intros R D r S ps Hres HM p psi Hp Hdf.
      apply mem_packageFormulaResolution in Hp.
      apply (encodeNNF_satisfies _ _ _ _ _ Hres HM (C.versions R)
               (embedPkg p) psi); [| exact Hp].
      intros d Hd; apply mem_reduceDeps; exists p, psi.
      split; [exact Hdf | exact Hd].
    Qed.

    Fixpoint firstSatIdx (S : PkgSet.t) (chis : list Formula) : nat :=
      match chis with
      | nil => 0
      | _ :: nil => 0
      | chi :: chis' =>
          if satisfiesb S chi then 0 else Datatypes.S (firstSatIdx S chis')
      end.

    Fixpoint witnessSet (S : PkgSet.t) (psi : Formula) : T.PkgSet.t :=
      match psi with
      | FDep _ _ => T.PkgSet.empty
      | FConj psiL psiR =>
          T.PkgSet.union (witnessSet S psiL) (witnessSet S psiR)
      | FDisj psiL psiR =>
          T.PkgSet.add
            (Name.Disjunct (psiL :: disjSpine psiR),
             Version.Idx (firstSatIdx S (psiL :: disjSpine psiR)))
            (if satisfiesb S psiL then witnessSet S psiL else takenDisj S psiR)
      | FNeg psi' => witnessSetNeg S psi'
      end
    with takenDisj (S : PkgSet.t) (psi : Formula) : T.PkgSet.t :=
      match psi with
      | FDep _ _ => T.PkgSet.empty
      | FConj psiL psiR =>
          T.PkgSet.union (witnessSet S psiL) (witnessSet S psiR)
      | FDisj psiL psiR =>
          if satisfiesb S psiL then witnessSet S psiL else takenDisj S psiR
      | FNeg psi' => witnessSetNeg S psi'
      end
    with witnessSetNeg (S : PkgSet.t) (psi : Formula) : T.PkgSet.t :=
      match psi with
      | FDep _ _ => T.PkgSet.empty
      | FConj psiL psiR =>
          T.PkgSet.add
            (Name.Disjunct (FNeg psiL :: negConjSpine psiR),
             Version.Idx (firstSatIdx S (FNeg psiL :: negConjSpine psiR)))
            (if satisfiesb S psiL then takenConjNeg S psiR
             else witnessSetNeg S psiL)
      | FDisj psiL psiR =>
          T.PkgSet.union (witnessSetNeg S psiL) (witnessSetNeg S psiR)
      | FNeg psi' => witnessSet S psi'
      end
    with takenConjNeg (S : PkgSet.t) (psi : Formula) : T.PkgSet.t :=
      match psi with
      | FDep _ _ => T.PkgSet.empty
      | FConj psiL psiR =>
          if satisfiesb S psiL then takenConjNeg S psiR
          else witnessSetNeg S psiL
      | FDisj psiL psiR =>
          T.PkgSet.union (witnessSetNeg S psiL) (witnessSetNeg S psiR)
      | FNeg psi' => witnessSet S psi'
      end.

    Lemma witnessSet_disj_eq : forall S psiL psiR,
        witnessSet S (FDisj psiL psiR) =
        T.PkgSet.add
          (Name.Disjunct (psiL :: disjSpine psiR),
           Version.Idx (firstSatIdx S (psiL :: disjSpine psiR)))
          (takenDisj S (FDisj psiL psiR)).
    Proof. reflexivity. Qed.

    Lemma witnessSetNeg_conj_eq : forall S psiL psiR,
        witnessSetNeg S (FConj psiL psiR) =
        T.PkgSet.add
          (Name.Disjunct (FNeg psiL :: negConjSpine psiR),
           Version.Idx (firstSatIdx S (FNeg psiL :: negConjSpine psiR)))
          (takenConjNeg S (FConj psiL psiR)).
    Proof. reflexivity. Qed.

    Lemma takenDisj_disj_eq : forall S psiL psiR,
        takenDisj S (FDisj psiL psiR) =
        (if satisfiesb S psiL then witnessSet S psiL else takenDisj S psiR).
    Proof. reflexivity. Qed.

    Lemma takenConjNeg_conj_eq : forall S psiL psiR,
        takenConjNeg S (FConj psiL psiR) =
        (if satisfiesb S psiL then takenConjNeg S psiR
         else witnessSetNeg S psiL).
    Proof. reflexivity. Qed.

    Lemma firstSatIdx_lt : forall S chis,
        chis <> nil -> firstSatIdx S chis < List.length chis.
    Proof.
      intros S chis; induction chis as [| chi chis IH]; intro Hne.
      - contradiction Hne; reflexivity.
      - destruct chis as [| h t]; [simpl; lia |].
        change (firstSatIdx S (chi :: h :: t))
          with (if satisfiesb S chi then 0
                else Datatypes.S (firstSatIdx S (h :: t))).
        assert (Hlt : firstSatIdx S (h :: t) < List.length (h :: t))
          by (apply IH; discriminate).
        destruct (satisfiesb S chi); simpl List.length in *; lia.
    Qed.

    Lemma disjSpine_nonnil : forall psi, disjSpine psi <> nil.
    Proof. intro psi; destruct psi; simpl; discriminate. Qed.

    Lemma negConjSpine_nonnil : forall psi, negConjSpine psi <> nil.
    Proof. intro psi; destruct psi; simpl; discriminate. Qed.

    Lemma firstSatIdx_cons : forall S chi chis,
        chis <> nil ->
        firstSatIdx S (chi :: chis) =
        (if satisfiesb S chi then 0 else Datatypes.S (firstSatIdx S chis)).
    Proof.
      intros S chi [| h t] Hne;
        [contradiction Hne; reflexivity | reflexivity].
    Qed.

    Lemma takenDisj_firstSat : forall S psi,
        Satisfies S psi ->
        exists chi,
          List.nth_error (disjSpine psi) (firstSatIdx S (disjSpine psi)) =
            Some chi /\
          Satisfies S chi /\
          T.PkgSet.Subset (witnessSet S chi) (takenDisj S psi).
    Proof.
      intros S psi;
        induction psi
          as [m vs | psiL IHa psiR IHb | psiL IHa psiR IHb | psi' IHa];
        intro Hsat;
        try (eexists; split; [reflexivity |]; split;
             [exact Hsat | intros p Hy; exact Hy]).
      cbn [disjSpine];
        rewrite (firstSatIdx_cons S psiL (disjSpine psiR)
            (disjSpine_nonnil psiR)).
      destruct (satisfiesb S psiL) eqn:Ea.
      - exists psiL; split; [reflexivity |]; split;
          [apply satisfiesb_iff; exact Ea |].
        intros p Hy; simpl; rewrite Ea; exact Hy.
      - assert (Hb : Satisfies S psiR).
        { destruct Hsat as [Ha | Hb]; [| exact Hb].
          exfalso; exact (proj1 (satisfiesb_false_iff S psiL) Ea Ha). }
        destruct (IHb Hb) as [chi [Hg [Hsg Hsub]]].
        exists chi; split; [exact Hg |]; split; [exact Hsg |].
        intros p Hy; simpl; rewrite Ea; exact (Hsub p Hy).
    Qed.

    Lemma takenConjNeg_firstSat : forall S psi,
        ~ Satisfies S psi ->
        exists chi,
          List.nth_error (negConjSpine psi) (firstSatIdx S (negConjSpine psi)) =
            Some chi /\
          Satisfies S chi /\
          T.PkgSet.Subset (witnessSet S chi) (takenConjNeg S psi).
    Proof.
      intros S psi;
        induction psi
          as [m vs | psiL IHa psiR IHb | psiL IHa psiR IHb | psi' IHa];
        intro Hsat;
        try (eexists; split; [reflexivity |]; split;
             [exact Hsat | intros p Hy; exact Hy]).
      cbn [negConjSpine];
        rewrite (firstSatIdx_cons S (FNeg psiL) (negConjSpine psiR)
                   (negConjSpine_nonnil psiR)).
      destruct (satisfiesb S psiL) eqn:Ea.
      - assert (Hb : ~ Satisfies S psiR).
        { intro Hb; apply Hsat; split;
            [apply satisfiesb_iff; exact Ea | exact Hb]. }
        destruct (IHb Hb) as [chi [Hg [Hsg Hsub]]].
        exists chi; split;
          [change (satisfiesb S (FNeg psiL)) with (negb (satisfiesb S psiL));
           rewrite Ea; exact Hg |]; split; [exact Hsg |].
        intros p Hy; simpl; rewrite Ea; exact (Hsub p Hy).
      - exists (FNeg psiL); split;
          [change (satisfiesb S (FNeg psiL)) with (negb (satisfiesb S psiL));
           rewrite Ea; reflexivity |]; split;
          [apply satisfiesb_false_iff; exact Ea |].
        intros p Hy; simpl; rewrite Ea; exact Hy.
    Qed.

    Definition coreResolution (R : PkgSet.t) (D : DepRel.t) (S : PkgSet.t)
      : T.PkgSet.t :=
      T.PkgSet.union (SOpt.map embedPkg S)
        (T.PkgSet.union
           (SOet.unionMap (fun '(p, psi) =>
                if PkgSet.mem p S then witnessSet S psi else T.PkgSet.empty)
              D)
           (absentPkgs (C.absentIn S (instNames R D)))).

    Lemma witnessSet_subset_arisingPkgs_aux : forall S psi,
        (forall p : T.Pkg.t,
            T.PkgSet.Subset (witnessSet S psi) (arisingPkgs p psi)) /\
        (forall p : T.Pkg.t,
            T.PkgSet.Subset (witnessSetNeg S psi) (arisingNeg p psi)) /\
        (forall (n : Name.t) (i : nat),
            T.PkgSet.Subset (takenDisj S psi) (arisingDisj n i psi)) /\
        (forall (n : Name.t) (i : nat),
            T.PkgSet.Subset (takenConjNeg S psi) (arisingConjNeg n i psi)).
    Proof.
      intros S psi;
        induction psi
          as [m ws | psiL IHa psiR IHb | psiL IHa psiR IHb | psi' IHa].
      - split4; intros; intros q H; exfalso; exact (SOpt.empty_in _ H).
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
          destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4.
        + intros p y; simpl; intro H;
            apply T.PkgSet.union_spec in H; apply T.PkgSet.union_spec;
            destruct H as [H | H];
            [left; exact (IHa1 p _ H) | right; exact (IHb1 p _ H)].
        + intros p y; rewrite witnessSetNeg_conj_eq; intro H;
            apply SOpt.add_in in H; simpl arisingNeg;
            apply T.PkgSet.union_spec.
          destruct H as [-> | H].
          * left; apply mem_idxPkgs;
              exists (firstSatIdx S (FNeg psiL :: negConjSpine psiR));
              split; [apply firstSatIdx_lt; discriminate | reflexivity].
          * right; revert H; rewrite takenConjNeg_conj_eq;
              destruct (satisfiesb S psiL); intro H;
              apply T.PkgSet.union_spec;
              [right; exact (IHb4 _ _ _ H) | left; exact (IHa2 _ _ H)].
        + intros n i y; simpl; intro H;
            apply T.PkgSet.union_spec in H; apply T.PkgSet.union_spec;
            destruct H as [H | H];
            [left; exact (IHa1 _ _ H) | right; exact (IHb1 _ _ H)].
        + intros n i y; rewrite takenConjNeg_conj_eq; simpl arisingConjNeg;
            destruct (satisfiesb S psiL); intro H;
            apply T.PkgSet.union_spec;
            [right; exact (IHb4 _ _ _ H) | left; exact (IHa2 _ _ H)].
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
          destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4.
        + intros p y; rewrite witnessSet_disj_eq; intro H;
            apply SOpt.add_in in H; simpl arisingPkgs;
            apply T.PkgSet.union_spec.
          destruct H as [-> | H].
          * left; apply mem_idxPkgs;
              exists (firstSatIdx S (psiL :: disjSpine psiR));
              split; [apply firstSatIdx_lt; discriminate | reflexivity].
          * right; revert H; rewrite takenDisj_disj_eq;
              destruct (satisfiesb S psiL); intro H;
              apply T.PkgSet.union_spec;
              [left; exact (IHa1 _ _ H) | right; exact (IHb3 _ _ _ H)].
        + intros p y; simpl; intro H;
            apply T.PkgSet.union_spec in H; apply T.PkgSet.union_spec;
            destruct H as [H | H];
            [left; exact (IHa2 p _ H) | right; exact (IHb2 p _ H)].
        + intros n i y; rewrite takenDisj_disj_eq; simpl arisingDisj;
            destruct (satisfiesb S psiL); intro H;
            apply T.PkgSet.union_spec;
            [left; exact (IHa1 _ _ H) | right; exact (IHb3 _ _ _ H)].
        + intros n i y; simpl; intro H;
            apply T.PkgSet.union_spec in H; apply T.PkgSet.union_spec;
            destruct H as [H | H];
            [left; exact (IHa2 _ _ H) | right; exact (IHb2 _ _ H)].
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4); split4.
        + intros p y; exact (IHa2 p y).
        + intros p y; exact (IHa1 p y).
        + intros n i y; exact (IHa2 _ y).
        + intros n i y; exact (IHa1 _ y).
    Qed.

    Lemma witnessSet_subset_arisingPkgs : forall S (p : T.Pkg.t) psi,
        T.PkgSet.Subset (witnessSet S psi) (arisingPkgs p psi).
    Proof.
      intros S p psi;
        exact (proj1 (witnessSet_subset_arisingPkgs_aux S psi) p).
    Qed.

    Lemma witnessSet_disjunct_det_aux : forall S psi,
        (forall chis v,
            T.PkgSet.In (Name.Disjunct chis, v) (witnessSet S psi) ->
            v = Version.Idx (firstSatIdx S chis)) /\
        (forall chis v,
            T.PkgSet.In (Name.Disjunct chis, v) (witnessSetNeg S psi) ->
            v = Version.Idx (firstSatIdx S chis)) /\
        (forall chis v,
            T.PkgSet.In (Name.Disjunct chis, v) (takenDisj S psi) ->
            v = Version.Idx (firstSatIdx S chis)) /\
        (forall chis v,
            T.PkgSet.In (Name.Disjunct chis, v) (takenConjNeg S psi) ->
            v = Version.Idx (firstSatIdx S chis)).
    Proof.
      intros S psi;
        induction psi
          as [m ws | psiL IHa psiR IHb | psiL IHa psiR IHb | psi' IHa].
      - split4; intros chis v; simpl; intro H;
          exfalso; exact (SOpt.empty_in _ H).
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
          destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4.
        + intros chis v; simpl; intro H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exact (IHa1 _ _ H) | exact (IHb1 _ _ H)].
        + intros chis v; rewrite witnessSetNeg_conj_eq; intro H;
            apply SOpt.add_in in H; destruct H as [H | H];
            [injection H as -> ->; reflexivity |].
          revert H; rewrite takenConjNeg_conj_eq; destruct (satisfiesb S psiL);
            intro H; [exact (IHb4 _ _ H) | exact (IHa2 _ _ H)].
        + intros chis v; simpl; intro H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exact (IHa1 _ _ H) | exact (IHb1 _ _ H)].
        + intros chis v; rewrite takenConjNeg_conj_eq;
            destruct (satisfiesb S psiL);
            intro H; [exact (IHb4 _ _ H) | exact (IHa2 _ _ H)].
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
          destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4.
        + intros chis v; rewrite witnessSet_disj_eq; intro H;
            apply SOpt.add_in in H; destruct H as [H | H];
            [injection H as -> ->; reflexivity |].
          revert H; rewrite takenDisj_disj_eq; destruct (satisfiesb S psiL);
            intro H; [exact (IHa1 _ _ H) | exact (IHb3 _ _ H)].
        + intros chis v; simpl; intro H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exact (IHa2 _ _ H) | exact (IHb2 _ _ H)].
        + intros chis v; rewrite takenDisj_disj_eq;
            destruct (satisfiesb S psiL);
            intro H; [exact (IHa1 _ _ H) | exact (IHb3 _ _ H)].
        + intros chis v; simpl; intro H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exact (IHa2 _ _ H) | exact (IHb2 _ _ H)].
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4); split4;
          intros chis v; [exact (IHa2 chis v) | exact (IHa1 chis v)
                       | exact (IHa2 chis v) | exact (IHa1 chis v)].
    Qed.

    Lemma witnessSet_disjunct_det : forall S psi chis v,
        T.PkgSet.In (Name.Disjunct chis, v) (witnessSet S psi) ->
        v = Version.Idx (firstSatIdx S chis).
    Proof.
      intros S psi; exact (proj1 (witnessSet_disjunct_det_aux S psi)).
    Qed.

    Lemma witnessSet_name_classify_aux : forall S psi,
        (forall (n : Name.t) (v : Version.t),
            T.PkgSet.In (n, v) (witnessSet S psi) -> SyntheticName n) /\
        (forall (n : Name.t) (v : Version.t),
            T.PkgSet.In (n, v) (witnessSetNeg S psi) -> SyntheticName n) /\
        (forall (n : Name.t) (v : Version.t),
            T.PkgSet.In (n, v) (takenDisj S psi) -> SyntheticName n) /\
        (forall (n : Name.t) (v : Version.t),
            T.PkgSet.In (n, v) (takenConjNeg S psi) -> SyntheticName n).
    Proof.
      unfold SyntheticName; intros S psi;
        induction psi
          as [m ws | psiL IHa psiR IHb | psiL IHa psiR IHb | psi' IHa].
      - split4; intros n v; simpl; intro H;
          exfalso; exact (SOpt.empty_in _ H).
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
          destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4.
        + intros n v; simpl; intro H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exact (IHa1 _ _ H) | exact (IHb1 _ _ H)].
        + intros n v; rewrite witnessSetNeg_conj_eq; intro H;
            apply SOpt.add_in in H; destruct H as [H | H];
            [injection H as -> _; eauto |].
          revert H; rewrite takenConjNeg_conj_eq; destruct (satisfiesb S psiL);
            intro H; [exact (IHb4 _ _ H) | exact (IHa2 _ _ H)].
        + intros n v; simpl; intro H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exact (IHa1 _ _ H) | exact (IHb1 _ _ H)].
        + intros n v; rewrite takenConjNeg_conj_eq;
            destruct (satisfiesb S psiL);
            intro H; [exact (IHb4 _ _ H) | exact (IHa2 _ _ H)].
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
          destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4.
        + intros n v; rewrite witnessSet_disj_eq; intro H;
            apply SOpt.add_in in H; destruct H as [H | H];
            [injection H as -> _; eauto |].
          revert H; rewrite takenDisj_disj_eq; destruct (satisfiesb S psiL);
            intro H; [exact (IHa1 _ _ H) | exact (IHb3 _ _ H)].
        + intros n v; simpl; intro H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exact (IHa2 _ _ H) | exact (IHb2 _ _ H)].
        + intros n v; rewrite takenDisj_disj_eq; destruct (satisfiesb S psiL);
            intro H; [exact (IHa1 _ _ H) | exact (IHb3 _ _ H)].
        + intros n v; simpl; intro H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exact (IHa2 _ _ H) | exact (IHb2 _ _ H)].
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4); split4; intros n v;
          [exact (IHa2 n v) | exact (IHa1 n v)
          | exact (IHa2 n v) | exact (IHa1 n v)].
    Qed.

    Lemma witnessSet_not_orig : forall S psi m v,
        ~ T.PkgSet.In (Name.Orig m, v) (witnessSet S psi).
    Proof.
      intros S psi m v H.
      destruct (proj1 (witnessSet_name_classify_aux S psi) _ _ H) as [chis E];
        discriminate.
    Qed.

    Lemma mem_coreResolution : forall S R D (p' : T.Pkg.t),
        T.PkgSet.In p' (coreResolution R D S) <->
        (exists p, PkgSet.In p S /\ p' = embedPkg p) \/
        (exists p psi, DepRel.In (p, psi) D /\ PkgSet.In p S /\
                     T.PkgSet.In p' (witnessSet S psi)) \/
        (exists n, NSet.In n (instNames R D) /\ Ab.hasAbsent n = true /\
                   (forall u, ~ PkgSet.In (n, u) S) /\
                   p' = (Name.Orig n, Version.Bot)).
    Proof.
      intros S R D p'; unfold coreResolution.
      rewrite !T.PkgSet.union_spec, SOpt.mem_map, SOet.mem_unionMap,
        mem_absentPkgs.
      split.
      - intros [H | [[[q chi] [He Hy]] | [n [Hn [Ha ->]]]]];
          [left; exact H | |].
        + right; left; cbn beta iota in Hy.
          destruct (PkgSet.mem q S) eqn:E;
            [| exfalso; exact (SOpt.empty_in _ Hy)].
          exists q, chi; split; [exact He |];
            split; [apply PkgSet.mem_spec; exact E | exact Hy].
        + right; right; apply C.mem_absentIn in Hn; destruct Hn as [Hn Hnone].
          exists n; auto.
      - intros [H | [[q [chi [Hd [HqS Hy]]]] | [n [Hn [Ha [Hnone ->]]]]]];
          [left; exact H | |].
        + right; left; exists (q, chi); split; [exact Hd |].
          apply PkgSet.mem_spec in HqS; cbn beta iota; rewrite HqS; exact Hy.
        + right; right; exists n; split; [| split; [exact Ha | reflexivity]].
          apply C.mem_absentIn; auto.
    Qed.

    Theorem package_formula_retraction : forall S R D,
        packageFormulaResolution (coreResolution R D S) = S.
    Proof.
      intros S R D; apply PkgSet.ext; intro p.
      rewrite mem_packageFormulaResolution, mem_coreResolution.
      split.
      - intros [[q [Hq E]] | [[q [psi [_ [_ Hw]]]] | [n [_ [_ E]]]]].
        + apply embedPkg_injective in E; subst q; exact Hq.
        + destruct p as [m v]; exfalso.
          exact (witnessSet_not_orig _ _ _ _ Hw).
        + destruct p as [m v]; discriminate (proj2 E).
      - intro Hp; left; exists p; split; [exact Hp | reflexivity].
    Qed.

    Lemma witnessSet_subset_coreResolution : forall S R D p psi,
        DepRel.In (p, psi) D -> PkgSet.In p S ->
        T.PkgSet.Subset (witnessSet S psi) (coreResolution R D S).
    Proof.
      intros S R D p psi Hd HpS y Hy; apply mem_coreResolution; right; left.
      exists p, psi; auto.
    Qed.

    Ltac pick_alt H nav :=
      let g0 := fresh "g0" in let Hg0 := fresh "Hg0" in
      let Hs0 := fresh "Hs0" in let Hu0 := fresh "Hu0" in
      destruct H as [g0 [Hg0 [Hs0 Hu0]]];
      exists g0; split; [exact Hg0 |]; split; [exact Hs0 |];
      let y0 := fresh "y0" in let Hy0 := fresh "Hy0" in
      intros y0 Hy0; nav; exact (Hu0 y0 Hy0).

    Lemma witnessSet_disj_mono_aux : forall S psi,
        (Satisfies S psi ->
         forall chis i,
           T.PkgSet.In (Name.Disjunct chis, Version.Idx i)
             (witnessSet S psi) ->
           exists chi, List.nth_error chis i = Some chi /\ Satisfies S chi /\
             T.PkgSet.Subset (witnessSet S chi) (witnessSet S psi)) /\
        (~ Satisfies S psi ->
         forall chis i,
           T.PkgSet.In (Name.Disjunct chis, Version.Idx i)
             (witnessSetNeg S psi) ->
           exists chi, List.nth_error chis i = Some chi /\ Satisfies S chi /\
             T.PkgSet.Subset (witnessSet S chi) (witnessSetNeg S psi)) /\
        (Satisfies S psi ->
         forall chis i,
           T.PkgSet.In (Name.Disjunct chis, Version.Idx i) (takenDisj S psi) ->
           exists chi, List.nth_error chis i = Some chi /\ Satisfies S chi /\
             T.PkgSet.Subset (witnessSet S chi) (takenDisj S psi)) /\
        (~ Satisfies S psi ->
         forall chis i,
           T.PkgSet.In (Name.Disjunct chis, Version.Idx i)
             (takenConjNeg S psi) ->
           exists chi, List.nth_error chis i = Some chi /\ Satisfies S chi /\
             T.PkgSet.Subset (witnessSet S chi) (takenConjNeg S psi)).
    Proof.
      intros S psi;
        induction psi
          as [m ws | psiL IHa psiR IHb | psiL IHa psiR IHb | psi' IHa].
      - split4; intros Hyp chis i; simpl; intro H;
          exfalso; exact (SOpt.empty_in _ H).
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
          destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4.
        + intros Hyp chis i; simpl; intro H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [pick_alt (IHa1 (proj1 Hyp) _ _ H)
               ltac:(apply T.PkgSet.union_spec; left)
            | pick_alt (IHb1 (proj2 Hyp) _ _ H)
                ltac:(apply T.PkgSet.union_spec; right)].
        + intros Hyp chis i; rewrite witnessSetNeg_conj_eq; intro H;
            apply SOpt.add_in in H; destruct H as [H | H].
          * injection H as -> ->;
              pick_alt (takenConjNeg_firstSat S (FConj psiL psiR) Hyp)
                ltac:(apply SOpt.add_in; right).
          * revert H; rewrite takenConjNeg_conj_eq;
              destruct (satisfiesb S psiL) eqn:Ea; intro H.
            -- assert (Hb : ~ Satisfies S psiR).
               { intro Hb; apply Hyp; split;
                   [apply satisfiesb_iff; exact Ea | exact Hb]. }
               pick_alt (IHb4 Hb _ _ H) ltac:(apply SOpt.add_in; right).
            -- pick_alt (IHa2 (proj1 (satisfiesb_false_iff S psiL) Ea) _ _ H)
                 ltac:(apply SOpt.add_in; right).
        + intros Hyp chis i; simpl; intro H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [pick_alt (IHa1 (proj1 Hyp) _ _ H)
               ltac:(apply T.PkgSet.union_spec; left)
            | pick_alt (IHb1 (proj2 Hyp) _ _ H)
                ltac:(apply T.PkgSet.union_spec; right)].
        + intros Hyp chis i; rewrite takenConjNeg_conj_eq;
            destruct (satisfiesb S psiL) eqn:Ea; intro H.
          * assert (Hb : ~ Satisfies S psiR).
            { intro Hb; apply Hyp; split;
                [apply satisfiesb_iff; exact Ea | exact Hb]. }
            pick_alt (IHb4 Hb _ _ H) ltac:(idtac).
          * pick_alt (IHa2 (proj1 (satisfiesb_false_iff S psiL) Ea) _ _ H)
              ltac:(idtac).
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
          destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4.
        + intros Hyp chis i; rewrite witnessSet_disj_eq; intro H;
            apply SOpt.add_in in H; destruct H as [H | H].
          * injection H as -> ->;
              pick_alt (takenDisj_firstSat S (FDisj psiL psiR) Hyp)
                ltac:(apply SOpt.add_in; right).
          * revert H; rewrite takenDisj_disj_eq;
              destruct (satisfiesb S psiL) eqn:Ea; intro H.
            -- pick_alt (IHa1 (proj1 (satisfiesb_iff S psiL) Ea) _ _ H)
                 ltac:(apply SOpt.add_in; right).
            -- assert (Hb : Satisfies S psiR).
               { destruct Hyp as [Ha | Hb]; [| exact Hb].
                 exfalso; exact (proj1 (satisfiesb_false_iff S psiL) Ea Ha). }
               pick_alt (IHb3 Hb _ _ H) ltac:(apply SOpt.add_in; right).
        + intros Hyp chis i; simpl; intro H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H].
          * pick_alt (IHa2 (fun Ha => Hyp (or_introl Ha)) _ _ H)
              ltac:(apply T.PkgSet.union_spec; left).
          * pick_alt (IHb2 (fun Hb => Hyp (or_intror Hb)) _ _ H)
              ltac:(apply T.PkgSet.union_spec; right).
        + intros Hyp chis i; rewrite takenDisj_disj_eq;
            destruct (satisfiesb S psiL) eqn:Ea; intro H.
          * pick_alt (IHa1 (proj1 (satisfiesb_iff S psiL) Ea) _ _ H)
              ltac:(idtac).
          * assert (Hb : Satisfies S psiR).
            { destruct Hyp as [Ha | Hb]; [| exact Hb].
              exfalso; exact (proj1 (satisfiesb_false_iff S psiL) Ea Ha). }
            pick_alt (IHb3 Hb _ _ H) ltac:(idtac).
        + intros Hyp chis i; simpl; intro H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H].
          * pick_alt (IHa2 (fun Ha => Hyp (or_introl Ha)) _ _ H)
              ltac:(apply T.PkgSet.union_spec; left).
          * pick_alt (IHb2 (fun Hb => Hyp (or_intror Hb)) _ _ H)
              ltac:(apply T.PkgSet.union_spec; right).
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4); split4; intros Hyp chis i.
        + exact (IHa2 Hyp chis i).
        + exact (IHa1 (satisfies_double_neg S psi' Hyp) chis i).
        + exact (IHa2 Hyp chis i).
        + exact (IHa1 (satisfies_double_neg S psi' Hyp) chis i).
    Qed.

    Lemma coreResolution_disj : forall S R D chis i,
        (forall p, PkgSet.In p S ->
         forall psi, DepRel.In (p, psi) D -> Satisfies S psi) ->
        T.PkgSet.In (Name.Disjunct chis, Version.Idx i)
          (coreResolution R D S) ->
        exists chi, List.nth_error chis i = Some chi /\ Satisfies S chi /\
          T.PkgSet.Subset (witnessSet S chi) (coreResolution R D S).
    Proof.
      intros S R D chis i Hclo H; apply mem_coreResolution in H.
      destruct H
        as [[p [_ Hp]] | [[p [chi [Hd [HpS Hw]]]] | [n [_ [_ [_ Hn]]]]]].
      - destruct p as [pn pv]; unfold embedPkg in Hp; discriminate.
      - assert (Hsat : Satisfies S chi) by exact (Hclo p HpS chi Hd).
        destruct (proj1 (witnessSet_disj_mono_aux S chi) Hsat chis i Hw)
          as [h [Hh [Hsh Hsubh]]].
        exists h; split; [exact Hh |]; split; [exact Hsh |].
        intros q Hy;
          apply (witnessSet_subset_coreResolution S R D p chi Hd HpS), Hsubh;
          exact Hy.
      - discriminate Hn.
    Qed.

    Lemma encodeNNF_dep_closure_aux :
      forall (S_Psi : PkgSet.t) (Vq : N.t -> VSet.t) (ns : NSet.t)
        (S : T.PkgSet.t),
        (forall p, PkgSet.In p S_Psi -> T.PkgSet.In (embedPkg p) S) ->
        (forall m u, PkgSet.In (m, u) S_Psi -> VSet.In u (Vq m)) ->
        (forall m, NSet.In m ns -> Ab.hasAbsent m = true ->
           (forall u, ~ PkgSet.In (m, u) S_Psi) ->
           T.PkgSet.In (Name.Orig m, Version.Bot) S) ->
        (forall m, NSet.In m ns -> Ab.hasAbsent m = false ->
           exists u, PkgSet.In (m, u) S_Psi) ->
        (forall chis i, T.PkgSet.In (Name.Disjunct chis, Version.Idx i) S ->
           exists chi, List.nth_error chis i = Some chi /\
             Satisfies S_Psi chi /\
             T.PkgSet.Subset (witnessSet S_Psi chi) S) ->
        forall psi : Formula,
          NSet.Subset (fnames psi) ns ->
          (forall q0 : T.Pkg.t,
              ~ T.PkgSet.In q0 S \/
              (Satisfies S_Psi psi /\
                 T.PkgSet.Subset (witnessSet S_Psi psi) S) ->
              forall (q : T.Pkg.t) (n : NameOT.t) (ws : T.VSet.t),
                T.DepRel.In (q, (n, ws)) (encodeNNF Vq q0 psi) ->
                T.PkgSet.In q S ->
                exists v, T.VSet.In v ws /\ T.PkgSet.In (n, v) S) /\
          (forall q0 : T.Pkg.t,
              ~ T.PkgSet.In q0 S \/
              (~ Satisfies S_Psi psi /\
               T.PkgSet.Subset (witnessSetNeg S_Psi psi) S) ->
              forall (q : T.Pkg.t) (n : NameOT.t) (ws : T.VSet.t),
                T.DepRel.In (q, (n, ws)) (encodeNNFneg Vq q0 psi) ->
                T.PkgSet.In q S ->
                exists v, T.VSet.In v ws /\ T.PkgSet.In (n, v) S) /\
          (forall (n' : Name.t) (i0 : nat),
              (forall k chi, List.nth_error (disjSpine psi) k = Some chi ->
                 ~ T.PkgSet.In (n', Version.Idx (i0 + k)) S \/
                 (Satisfies S_Psi chi /\
                  T.PkgSet.Subset (witnessSet S_Psi chi) S)) ->
              forall (q : T.Pkg.t) (n : NameOT.t) (ws : T.VSet.t),
                T.DepRel.In (q, (n, ws)) (encodeDisj Vq n' i0 psi) ->
                T.PkgSet.In q S ->
                exists v, T.VSet.In v ws /\ T.PkgSet.In (n, v) S) /\
          (forall (n' : Name.t) (i0 : nat),
              (forall k chi, List.nth_error (negConjSpine psi) k = Some chi ->
                 ~ T.PkgSet.In (n', Version.Idx (i0 + k)) S \/
                 (Satisfies S_Psi chi /\
                  T.PkgSet.Subset (witnessSet S_Psi chi) S)) ->
              forall (q : T.Pkg.t) (n : NameOT.t) (ws : T.VSet.t),
                T.DepRel.In (q, (n, ws)) (encodeConjNeg Vq n' i0 psi) ->
                T.PkgSet.In q S ->
                exists v, T.VSet.In v ws /\ T.PkgSet.In (n, v) S).
    Proof.
      intros S_Psi Vq ns S Hemb HVq Hbot Htot Hdisj psi.
      assert (Hneg : forall m vs,
                 NSet.In m ns ->
                 ~ Satisfies S_Psi (FDep m vs) ->
                 exists v, T.VSet.In v (complementVS Vq m vs) /\
                           T.PkgSet.In (Name.Orig m, v) S).
      { intros m vs Hm Hns.
        destruct (C.hasNameb S_Psi m) eqn:E.
        - apply C.hasNameb_true in E; destruct E as [u Hu].
          exists (Version.Orig u); split; [| exact (Hemb (m, u) Hu)].
          apply mem_complementVS; right; exists u.
          split; [exact (HVq m u Hu) | split; [| reflexivity]].
          intro Huv; apply Hns; exists u; auto.
        - assert (Hnone := proj1 (C.hasNameb_false S_Psi m) E).
          destruct (Ab.hasAbsent m) eqn:Ha.
          + exists Version.Bot; split;
              [apply mem_complementVS; left; split; [reflexivity | exact Ha] |].
            exact (Hbot m Hm Ha Hnone).
          + destruct (Htot m Hm Ha) as [u Hu]; destruct (Hnone u Hu). }
      induction psi
        as [m vs | psiL IHa psiR IHb | psiL IHa psiR IHb | psi' IHa];
        intro Hsub.
      - assert (Hm : NSet.In m ns)
          by (apply Hsub; simpl; apply NSet.singleton_spec; reflexivity).
        split4.
        + intros q0 Hwit q n ws Henc Hqw.
          apply SOed.singleton_in in Henc; injection Henc as -> -> ->.
          destruct Hwit as [Hq0 | [Hsat _]]; [exfalso; exact (Hq0 Hqw) |].
          destruct Hsat as [u [Hu HuS]].
          exists (Version.Orig u); split;
            [unfold embedVS; apply SOvv.mem_map;
             exists u; split; [exact Hu | reflexivity]
            | exact (Hemb (m, u) HuS)].
        + intros q0 Hwit q n ws Henc Hqw.
          apply SOed.singleton_in in Henc; injection Henc as -> -> ->.
          destruct Hwit as [Hq0 | [Hns _]]; [exfalso; exact (Hq0 Hqw) |].
          exact (Hneg m vs Hm Hns).
        + intros n' i0 Hspine q n ws Henc Hqw.
          assert (Hwit := Hspine 0 (FDep m vs) eq_refl);
            replace (i0 + 0) with i0 in Hwit by lia.
          apply SOed.singleton_in in Henc; injection Henc as -> -> ->.
          destruct Hwit as [Hq0 | [Hsat _]]; [exfalso; exact (Hq0 Hqw) |].
          destruct Hsat as [u [Hu HuS]].
          exists (Version.Orig u); split;
            [unfold embedVS; apply SOvv.mem_map;
             exists u; split; [exact Hu | reflexivity]
            | exact (Hemb (m, u) HuS)].
        + intros n' i0 Hspine q n ws Henc Hqw.
          assert (Hwit := Hspine 0 (FNeg (FDep m vs)) eq_refl);
            replace (i0 + 0) with i0 in Hwit by lia.
          apply SOed.singleton_in in Henc; injection Henc as -> -> ->.
          destruct Hwit as [Hq0 | [Hns _]]; [exfalso; exact (Hq0 Hqw) |].
          exact (Hneg m vs Hm Hns).
      - assert (Hsa : NSet.Subset (fnames psiL) ns)
          by (intros x Hx; apply Hsub; simpl; apply NSet.union_spec; left; exact Hx).
        assert (Hsb : NSet.Subset (fnames psiR) ns)
          by (intros x Hx; apply Hsub; simpl; apply NSet.union_spec; right; exact Hx).
        destruct (IHa Hsa) as (IHa1 & IHa2 & IHa3 & IHa4);
          destruct (IHb Hsb) as (IHb1 & IHb2 & IHb3 & IHb4); split4.
        + intros q0 Hwit q n ws Henc Hqw.
          apply T.DepRel.union_spec in Henc; destruct Henc as [He | He].
          * refine (IHa1 q0 _ q n ws He Hqw).
            destruct Hwit as [Hq0 | [Hsat Hsub']];
              [left; exact Hq0 | right; split; [exact (proj1 Hsat) |]];
              intros p' Hy; apply Hsub', T.PkgSet.union_spec; left; exact Hy.
          * refine (IHb1 q0 _ q n ws He Hqw).
            destruct Hwit as [Hq0 | [Hsat Hsub']];
              [left; exact Hq0 | right; split; [exact (proj2 Hsat) |]];
              intros p' Hy; apply Hsub', T.PkgSet.union_spec; right; exact Hy.
        + intros q0 Hwit q n ws Henc Hqw.
          apply SOed.add_in in Henc; destruct Henc as [He | He].
          * injection He as -> -> ->.
            destruct Hwit as [Hq0 | [_ Hsub']]; [exfalso; exact (Hq0 Hqw) |].
            exists (Version.Idx
                      (firstSatIdx S_Psi (FNeg psiL :: negConjSpine psiR)));
                        split.
            -- apply mem_idxSet;
                 exists (firstSatIdx S_Psi (FNeg psiL :: negConjSpine psiR));
                   split;
                 [apply firstSatIdx_lt; discriminate | reflexivity].
            -- apply Hsub'; rewrite witnessSetNeg_conj_eq;
                 apply SOpt.add_in; left; reflexivity.
          * apply T.DepRel.union_spec in He; destruct He as [He | He].
            -- refine (IHa2 (Name.Disjunct (FNeg psiL :: negConjSpine psiR),
                             Version.Idx 0) _ q n ws He Hqw).
               destruct (T.PkgSet.mem
                           (Name.Disjunct (FNeg psiL :: negConjSpine psiR),
                            Version.Idx 0) S) eqn:EM.
               ++ apply T.PkgSet.mem_spec in EM.
                  destruct (Hdisj _ _ EM) as [chi [Hg [Hsg Hsub']]].
                  cbn [List.nth_error] in Hg; injection Hg as <-.
                  right; split; [exact Hsg | exact Hsub'].
               ++ left; intro Hin; apply T.PkgSet.mem_spec in Hin;
                    discriminate (eq_trans (eq_sym Hin) EM).
            -- refine (IHb4 (Name.Disjunct (FNeg psiL :: negConjSpine psiR)) 1
                         _ q n ws He Hqw).
               intros k chi Hg.
               assert (Hg' : List.nth_error (FNeg psiL :: negConjSpine psiR)
                               (1 + k) = Some chi) by exact Hg.
               destruct (T.PkgSet.mem
                           (Name.Disjunct (FNeg psiL :: negConjSpine psiR),
                            Version.Idx (1 + k)) S) eqn:EM.
               ++ apply T.PkgSet.mem_spec in EM.
                  destruct (Hdisj _ _ EM) as [chi' [Hg2 [Hsg Hsub']]].
                  rewrite Hg' in Hg2; injection Hg2 as <-.
                  right; split; [exact Hsg | exact Hsub'].
               ++ left; intro Hin; apply T.PkgSet.mem_spec in Hin;
                    discriminate (eq_trans (eq_sym Hin) EM).
        + intros n' i0 Hspine q n ws Henc Hqw.
          assert (Hwit := Hspine 0 (FConj psiL psiR) eq_refl);
            replace (i0 + 0) with i0 in Hwit by lia.
          apply T.DepRel.union_spec in Henc; destruct Henc as [He | He].
          * refine (IHa1 (n', Version.Idx i0) _ q n ws He Hqw).
            destruct Hwit as [Hq0 | [Hsat Hsub']];
              [left; exact Hq0 | right; split; [exact (proj1 Hsat) |]];
              intros p' Hy; apply Hsub', T.PkgSet.union_spec; left; exact Hy.
          * refine (IHb1 (n', Version.Idx i0) _ q n ws He Hqw).
            destruct Hwit as [Hq0 | [Hsat Hsub']];
              [left; exact Hq0 | right; split; [exact (proj2 Hsat) |]];
              intros p' Hy; apply Hsub', T.PkgSet.union_spec; right; exact Hy.
        + intros n' i0 Hspine q n ws Henc Hqw.
          apply T.DepRel.union_spec in Henc; destruct Henc as [He | He].
          * refine (IHa2 (n', Version.Idx i0) _ q n ws He Hqw).
            assert (Hwit := Hspine 0 (FNeg psiL) eq_refl);
              replace (i0 + 0) with i0 in Hwit by lia.
            exact Hwit.
          * refine (IHb4 n' (Datatypes.S i0) _ q n ws He Hqw).
            intros k chi Hg.
            assert (H := Hspine (Datatypes.S k) chi Hg).
            replace (Datatypes.S i0 + k) with (i0 + Datatypes.S k) by lia.
            exact H.
      - assert (Hsa : NSet.Subset (fnames psiL) ns)
          by (intros x Hx; apply Hsub; simpl; apply NSet.union_spec; left; exact Hx).
        assert (Hsb : NSet.Subset (fnames psiR) ns)
          by (intros x Hx; apply Hsub; simpl; apply NSet.union_spec; right; exact Hx).
        destruct (IHa Hsa) as (IHa1 & IHa2 & IHa3 & IHa4);
          destruct (IHb Hsb) as (IHb1 & IHb2 & IHb3 & IHb4); split4.
        + intros q0 Hwit q n ws Henc Hqw.
          apply SOed.add_in in Henc; destruct Henc as [He | He].
          * injection He as -> -> ->.
            destruct Hwit as [Hq0 | [_ Hsub']]; [exfalso; exact (Hq0 Hqw) |].
            exists (Version.Idx (firstSatIdx S_Psi (psiL :: disjSpine psiR)));
              split.
            -- apply mem_idxSet;
                 exists (firstSatIdx S_Psi (psiL :: disjSpine psiR)); split;
                 [apply firstSatIdx_lt; discriminate | reflexivity].
            -- apply Hsub'; rewrite witnessSet_disj_eq;
                 apply SOpt.add_in; left; reflexivity.
          * apply T.DepRel.union_spec in He; destruct He as [He | He].
            -- refine (IHa1 (Name.Disjunct (psiL :: disjSpine psiR),
                             Version.Idx 0) _ q n ws He Hqw).
               destruct (T.PkgSet.mem (Name.Disjunct (psiL :: disjSpine psiR),
                                       Version.Idx 0) S) eqn:EM.
               ++ apply T.PkgSet.mem_spec in EM.
                  destruct (Hdisj _ _ EM) as [chi [Hg [Hsg Hsub']]].
                  cbn [List.nth_error] in Hg; injection Hg as <-.
                  right; split; [exact Hsg | exact Hsub'].
               ++ left; intro Hin; apply T.PkgSet.mem_spec in Hin;
                    discriminate (eq_trans (eq_sym Hin) EM).
            -- refine (IHb3 (Name.Disjunct (psiL :: disjSpine psiR)) 1
                         _ q n ws He Hqw).
               intros k chi Hg.
               assert (Hg' : List.nth_error (psiL :: disjSpine psiR) (1 + k)
                             = Some chi) by exact Hg.
               destruct (T.PkgSet.mem (Name.Disjunct (psiL :: disjSpine psiR),
                                       Version.Idx (1 + k)) S) eqn:EM.
               ++ apply T.PkgSet.mem_spec in EM.
                  destruct (Hdisj _ _ EM) as [chi' [Hg2 [Hsg Hsub']]].
                  rewrite Hg' in Hg2; injection Hg2 as <-.
                  right; split; [exact Hsg | exact Hsub'].
               ++ left; intro Hin; apply T.PkgSet.mem_spec in Hin;
                    discriminate (eq_trans (eq_sym Hin) EM).
        + intros q0 Hwit q n ws Henc Hqw.
          apply T.DepRel.union_spec in Henc; destruct Henc as [He | He].
          * refine (IHa2 q0 _ q n ws He Hqw).
            destruct Hwit as [Hq0 | [Hns Hsub']];
              [left; exact Hq0
              | right; split; [intro Ha; exact (Hns (or_introl Ha)) |]];
              intros p' Hy; apply Hsub', T.PkgSet.union_spec; left; exact Hy.
          * refine (IHb2 q0 _ q n ws He Hqw).
            destruct Hwit as [Hq0 | [Hns Hsub']];
              [left; exact Hq0
              | right; split; [intro Hb; exact (Hns (or_intror Hb)) |]];
              intros p' Hy; apply Hsub', T.PkgSet.union_spec; right; exact Hy.
        + intros n' i0 Hspine q n ws Henc Hqw.
          apply T.DepRel.union_spec in Henc; destruct Henc as [He | He].
          * refine (IHa1 (n', Version.Idx i0) _ q n ws He Hqw).
            assert (Hwit := Hspine 0 psiL eq_refl);
              replace (i0 + 0) with i0 in Hwit by lia.
            exact Hwit.
          * refine (IHb3 n' (Datatypes.S i0) _ q n ws He Hqw).
            intros k chi Hg.
            assert (H := Hspine (Datatypes.S k) chi Hg).
            replace (Datatypes.S i0 + k) with (i0 + Datatypes.S k) by lia.
            exact H.
        + intros n' i0 Hspine q n ws Henc Hqw.
          assert (Hwit := Hspine 0 (FNeg (FDisj psiL psiR)) eq_refl);
            replace (i0 + 0) with i0 in Hwit by lia.
          apply T.DepRel.union_spec in Henc; destruct Henc as [He | He].
          * refine (IHa2 (n', Version.Idx i0) _ q n ws He Hqw).
            destruct Hwit as [Hq0 | [Hns Hsub']];
              [left; exact Hq0
              | right; split; [intro Ha; exact (Hns (or_introl Ha)) |]];
              intros p' Hy; apply Hsub', T.PkgSet.union_spec; left; exact Hy.
          * refine (IHb2 (n', Version.Idx i0) _ q n ws He Hqw).
            destruct Hwit as [Hq0 | [Hns Hsub']];
              [left; exact Hq0
              | right; split; [intro Hb; exact (Hns (or_intror Hb)) |]];
              intros p' Hy; apply Hsub', T.PkgSet.union_spec; right; exact Hy.
      - destruct (IHa Hsub) as (IHa1 & IHa2 & IHa3 & IHa4); split4.
        + intros q0 Hwit q n ws Henc Hqw.
          exact (IHa2 q0 Hwit q n ws Henc Hqw).
        + intros q0 Hwit q n ws Henc Hqw.
          destruct Hwit as [Hq0 | [Hnn Hsub']];
            [exact (IHa1 q0 (or_introl Hq0) q n ws Henc Hqw)
            | exact (IHa1 q0
                       (or_intror
                          (conj (satisfies_double_neg S_Psi psi' Hnn) Hsub'))
                       q n ws Henc Hqw)].
        + intros n' i0 Hspine q n ws Henc Hqw.
          assert (Hwit := Hspine 0 (FNeg psi') eq_refl);
            replace (i0 + 0) with i0 in Hwit by lia.
          exact (IHa2 (n', Version.Idx i0) Hwit q n ws Henc Hqw).
        + intros n' i0 Hspine q n ws Henc Hqw.
          assert (Hwit := Hspine 0 (FNeg (FNeg psi')) eq_refl);
            replace (i0 + 0) with i0 in Hwit by lia.
          destruct Hwit as [Hq0 | [Hnn Hsub']];
            [exact (IHa1 (n', Version.Idx i0) (or_introl Hq0) q n ws Henc Hqw)
            | exact (IHa1 (n', Version.Idx i0)
                       (or_intror
                          (conj (satisfies_double_neg S_Psi psi' Hnn) Hsub'))
                       q n ws Henc Hqw)].
    Qed.

    Theorem formula_calculus_completeness :
      forall (R : PkgSet.t) (D : DepRel.t) (r : Pkg.t) (S : PkgSet.t),
        IsResolution R D r S ->
        (forall m, NSet.In m (depNames D) -> Ab.hasAbsent m = false ->
           exists u, PkgSet.In (m, u) S) ->
        T.IsResolution (reduceReal R D) (reduceDeps R D) (embedPkg r)
          (coreResolution R D S).
    Proof.
      intros R D r S Hres Htot; destruct Hres as [Hsub Hroot Hclo Huniq].
      assert (Hemb : forall p, PkgSet.In p S ->
          T.PkgSet.In (embedPkg p) (coreResolution R D S)).
      { intros p Hp; apply mem_coreResolution; left.
        exists p; split; [exact Hp | reflexivity]. }
      assert (HVq : forall m u, PkgSet.In (m, u) S ->
          VSet.In u (C.versions R m)).
      { intros m u Hu; apply C.mem_versions; apply Hsub; exact Hu. }
      assert (Hbot : forall m, NSet.In m (depNames D) ->
          Ab.hasAbsent m = true -> (forall u, ~ PkgSet.In (m, u) S) ->
          T.PkgSet.In (Name.Orig m, Version.Bot) (coreResolution R D S)).
      { intros m Hm Ha Hnone; apply mem_coreResolution; right; right.
        exists m; split; [apply mem_instNames; right; exact Hm |]; auto. }
      assert (Horig : forall m v,
          T.PkgSet.In (Name.Orig m, Version.Orig v) (coreResolution R D S) ->
          PkgSet.In (m, v) S).
      { intros m v Hv; apply mem_coreResolution in Hv.
        destruct Hv as [[[pn pv] [Hp Hpe]] | [[p [chi [_ [_ Hw]]]]
                       | [n [_ [_ [_ Hn]]]]]].
        - unfold embedPkg in Hpe; injection Hpe as -> ->; exact Hp.
        - exfalso; exact (witnessSet_not_orig _ _ _ _ Hw).
        - discriminate Hn. }
      assert (Hdisj := fun chis i => coreResolution_disj S R D chis i Hclo).
      constructor.
      - intros p' Hy; apply mem_coreResolution in Hy.
        apply mem_reduceReal.
        destruct Hy as [[p [Hp ->]] | [[p [chi [Hd [_ Hw]]]]
                       | [n [Hn [Ha [_ ->]]]]]].
        + left; exists p; split; [apply Hsub; exact Hp | reflexivity].
        + right; left; exists p, chi; split; [exact Hd |].
          exact (witnessSet_subset_arisingPkgs S (embedPkg p) chi _ Hw).
        + right; right; exists n; auto.
      - exact (Hemb r Hroot).
      - intros q Hq m vs Hd.
        apply mem_reduceDeps in Hd; destruct Hd as [p [chi [Hpg Henc]]].
        assert (Hfn : NSet.Subset (fnames chi) (depNames D)).
        { intros x Hx; apply mem_depNames; exists p, chi; auto. }
        refine (proj1 (encodeNNF_dep_closure_aux S (C.versions R) (depNames D)
                         _ Hemb HVq Hbot Htot Hdisj chi Hfn)
                  (embedPkg p) _ q m vs Henc Hq).
        destruct (PkgSet.mem p S) eqn:Ep.
        + apply PkgSet.mem_spec in Ep.
          right; split; [exact (Hclo p Ep chi Hpg) |].
          exact (witnessSet_subset_coreResolution S R D p chi Hpg Ep).
        + left; intro Hin; destruct p as [pn pv].
          apply Horig, PkgSet.mem_spec in Hin; congruence.
      - intros n v v' Hv Hv'.
        apply mem_coreResolution in Hv, Hv'.
        destruct Hv as [[[n1 w1] [Hp1 He1]] | [[p1 [g1 [Hd1 [Hp1 Hw1]]]]
                       | [m1 [_ [_ [Hn1 He1]]]]]];
          destruct Hv' as [[[n2 w2] [Hp2 He2]] | [[p2 [g2 [Hd2 [Hp2 Hw2]]]]
                          | [m2 [_ [_ [Hn2 He2]]]]]];
          unfold embedPkg in *.
        + injection He1 as -> ->; injection He2 as -> ->.
          f_equal; exact (Huniq _ _ _ Hp1 Hp2).
        + injection He1 as -> ->.
          exfalso; exact (witnessSet_not_orig _ _ _ _ Hw2).
        + injection He1 as -> ->; injection He2 as -> ->.
          exfalso; exact (Hn2 _ Hp1).
        + injection He2 as -> ->.
          exfalso; exact (witnessSet_not_orig _ _ _ _ Hw1).
        + destruct n as [n0 | chis].
          * exfalso; exact (witnessSet_not_orig _ _ _ _ Hw1).
          * rewrite (witnessSet_disjunct_det _ _ _ _ Hw1),
              (witnessSet_disjunct_det _ _ _ _ Hw2); reflexivity.
        + injection He2 as -> ->.
          exfalso; exact (witnessSet_not_orig _ _ _ _ Hw1).
        + injection He1 as -> ->; injection He2 as -> ->.
          exfalso; exact (Hn1 _ Hp2).
        + injection He1 as -> ->.
          exfalso; exact (witnessSet_not_orig _ _ _ _ Hw2).
        + injection He1 as -> ->; injection He2 as _ ->; reflexivity.
    Qed.

    Module Lookup.
      Definition disjAlt (chis : list Formula) (i : Version.t) :
          option Formula :=
        match i with
        | Version.Idx k => List.nth_error chis k
        | _ => None
        end.

      Lemma encodeNNF_depender_orig_aux : forall Vq psi,
          (forall (q : T.Pkg.t) m (v : Version.t) (d : T.Dependees.t),
              T.DepRel.In ((Name.Orig m, v), d) (encodeNNF Vq q psi) ->
              q = (Name.Orig m, v)) /\
          (forall (q : T.Pkg.t) m (v : Version.t) (d : T.Dependees.t),
              T.DepRel.In ((Name.Orig m, v), d) (encodeNNFneg Vq q psi) ->
              q = (Name.Orig m, v)) /\
          (forall (n : Name.t) (i0 : nat) m (v : Version.t) (d : T.Dependees.t),
              T.DepRel.In ((Name.Orig m, v), d) (encodeDisj Vq n i0 psi) ->
              n = Name.Orig m) /\
          (forall (n : Name.t) (i0 : nat) m (v : Version.t) (d : T.Dependees.t),
              T.DepRel.In ((Name.Orig m, v), d) (encodeConjNeg Vq n i0 psi) ->
              n = Name.Orig m).
      Proof.
        intros Vq psi;
          induction psi
            as [o ws | psiL IHa psiR IHb | psiL IHa psiR IHb | psi' IHa].
        - split4.
          + intros q m w d H; apply SOed.singleton_in in H; congruence.
          + intros q m w d H; apply SOed.singleton_in in H; congruence.
          + intros n i0 m w d H; apply SOed.singleton_in in H; congruence.
          + intros n i0 m w d H; apply SOed.singleton_in in H; congruence.
        - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
            destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4.
          + intros q m w d H; simpl in H.
            apply T.DepRel.union_spec in H; destruct H as [H | H];
              [exact (IHa1 _ _ _ _ H) | exact (IHb1 _ _ _ _ H)].
          + intros q m w d H; simpl in H.
            apply SOed.add_in in H; destruct H as [H | H]; [congruence |].
            apply T.DepRel.union_spec in H; destruct H as [H | H];
              [assert (E := IHa2 _ _ _ _ H) | assert (E := IHb4 _ _ _ _ _ H)];
              discriminate E.
          + intros n i0 m w d H; simpl in H.
            apply T.DepRel.union_spec in H; destruct H as [H | H];
              [assert (E := IHa1 _ _ _ _ H) | assert (E := IHb1 _ _ _ _ H)];
              injection E as E _; exact E.
          + intros n i0 m w d H; simpl in H.
            apply T.DepRel.union_spec in H; destruct H as [H | H];
              [assert (E := IHa2 _ _ _ _ H); injection E as E _; exact E
              | exact (IHb4 _ _ _ _ _ H)].
        - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
            destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4.
          + intros q m w d H; simpl in H.
            apply SOed.add_in in H; destruct H as [H | H]; [congruence |].
            apply T.DepRel.union_spec in H; destruct H as [H | H];
              [assert (E := IHa1 _ _ _ _ H) | assert (E := IHb3 _ _ _ _ _ H)];
              discriminate E.
          + intros q m w d H; simpl in H.
            apply T.DepRel.union_spec in H; destruct H as [H | H];
              [exact (IHa2 _ _ _ _ H) | exact (IHb2 _ _ _ _ H)].
          + intros n i0 m w d H; simpl in H.
            apply T.DepRel.union_spec in H; destruct H as [H | H];
              [assert (E := IHa1 _ _ _ _ H); injection E as E _; exact E
              | exact (IHb3 _ _ _ _ _ H)].
          + intros n i0 m w d H; simpl in H.
            apply T.DepRel.union_spec in H; destruct H as [H | H];
              [assert (E := IHa2 _ _ _ _ H) | assert (E := IHb2 _ _ _ _ H)];
              injection E as E _; exact E.
        - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4); split4.
          + intros q m w d H; exact (IHa2 _ _ _ _ H).
          + intros q m w d H; exact (IHa1 _ _ _ _ H).
          + intros n i0 m w d H; assert (E := IHa2 _ _ _ _ H);
              injection E as E _; exact E.
          + intros n i0 m w d H; assert (E := IHa1 _ _ _ _ H);
              injection E as E _; exact E.
      Qed.

      Lemma encodeNNF_dependee_orig_aux : forall Vq psi,
          (forall (q q' : T.Pkg.t) m (ws : T.VSet.t),
              T.DepRel.In (q', (Name.Orig m, ws)) (encodeNNF Vq q psi) ->
              NSet.In m (fnames psi)) /\
          (forall (q q' : T.Pkg.t) m (ws : T.VSet.t),
              T.DepRel.In (q', (Name.Orig m, ws)) (encodeNNFneg Vq q psi) ->
              NSet.In m (fnames psi)) /\
          (forall (n : Name.t) (i0 : nat) (q' : T.Pkg.t) m (ws : T.VSet.t),
              T.DepRel.In (q', (Name.Orig m, ws)) (encodeDisj Vq n i0 psi) ->
              NSet.In m (fnames psi)) /\
          (forall (n : Name.t) (i0 : nat) (q' : T.Pkg.t) m (ws : T.VSet.t),
              T.DepRel.In (q', (Name.Orig m, ws)) (encodeConjNeg Vq n i0 psi) ->
              NSet.In m (fnames psi)).
      Proof.
        intros Vq psi;
          induction psi
            as [o vs | psiL IHa psiR IHb | psiL IHa psiR IHb | psi' IHa].
        - split4; intros; apply SOed.singleton_in in H; injection H as _ <- _;
            simpl; apply NSet.singleton_spec; reflexivity.
        - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
            destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4.
          + intros q q' m ws H; simpl in H; simpl.
            apply T.DepRel.union_spec in H; apply NSet.union_spec;
              destruct H as [H | H];
              [left; exact (IHa1 _ _ _ _ H) | right; exact (IHb1 _ _ _ _ H)].
          + intros q q' m ws H; simpl in H; simpl.
            apply SOed.add_in in H; destruct H as [H | H]; [discriminate |].
            apply T.DepRel.union_spec in H; apply NSet.union_spec;
              destruct H as [H | H];
              [left; exact (IHa2 _ _ _ _ H) | right; exact (IHb4 _ _ _ _ _ H)].
          + intros n i0 q' m ws H; simpl in H; simpl.
            apply T.DepRel.union_spec in H; apply NSet.union_spec;
              destruct H as [H | H];
              [left; exact (IHa1 _ _ _ _ H) | right; exact (IHb1 _ _ _ _ H)].
          + intros n i0 q' m ws H; simpl in H; simpl.
            apply T.DepRel.union_spec in H; apply NSet.union_spec;
              destruct H as [H | H];
              [left; exact (IHa2 _ _ _ _ H) | right; exact (IHb4 _ _ _ _ _ H)].
        - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
            destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4.
          + intros q q' m ws H; simpl in H; simpl.
            apply SOed.add_in in H; destruct H as [H | H]; [discriminate |].
            apply T.DepRel.union_spec in H; apply NSet.union_spec;
              destruct H as [H | H];
              [left; exact (IHa1 _ _ _ _ H) | right; exact (IHb3 _ _ _ _ _ H)].
          + intros q q' m ws H; simpl in H; simpl.
            apply T.DepRel.union_spec in H; apply NSet.union_spec;
              destruct H as [H | H];
              [left; exact (IHa2 _ _ _ _ H) | right; exact (IHb2 _ _ _ _ H)].
          + intros n i0 q' m ws H; simpl in H; simpl.
            apply T.DepRel.union_spec in H; apply NSet.union_spec;
              destruct H as [H | H];
              [left; exact (IHa1 _ _ _ _ H) | right; exact (IHb3 _ _ _ _ _ H)].
          + intros n i0 q' m ws H; simpl in H; simpl.
            apply T.DepRel.union_spec in H; apply NSet.union_spec;
              destruct H as [H | H];
              [left; exact (IHa2 _ _ _ _ H) | right; exact (IHb2 _ _ _ _ H)].
        - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4); split4.
          + intros q q' m ws H; exact (IHa2 _ _ _ _ H).
          + intros q q' m ws H; exact (IHa1 _ _ _ _ H).
          + intros n i0 q' m ws H; exact (IHa2 _ _ _ _ H).
          + intros n i0 q' m ws H; exact (IHa1 _ _ _ _ H).
      Qed.

      Lemma encodeNNF_agree_aux : forall Vq Vq' psi,
          (forall m, NSet.In m (fnames psi) -> Vq m = Vq' m) ->
          (forall p, encodeNNF Vq p psi = encodeNNF Vq' p psi) /\
          (forall p, encodeNNFneg Vq p psi = encodeNNFneg Vq' p psi) /\
          (forall n i, encodeDisj Vq n i psi = encodeDisj Vq' n i psi) /\
          (forall n i, encodeConjNeg Vq n i psi = encodeConjNeg Vq' n i psi).
      Proof.
        intros Vq Vq' psi;
          induction psi
            as [m vs | psiL IHa psiR IHb | psiL IHa psiR IHb | psi' IHa];
            intro Hag.
        - assert (E : Vq m = Vq' m)
            by (apply Hag; simpl; apply NSet.singleton_spec; reflexivity).
          split4; intros; simpl; unfold complementVS; try rewrite E; reflexivity.
        - assert (Ha : forall m, NSet.In m (fnames psiL) -> Vq m = Vq' m)
            by (intros m Hm; apply Hag; simpl; apply NSet.union_spec; left;
                exact Hm).
          assert (Hb : forall m, NSet.In m (fnames psiR) -> Vq m = Vq' m)
            by (intros m Hm; apply Hag; simpl; apply NSet.union_spec; right;
                exact Hm).
          destruct (IHa Ha) as (IHa1 & IHa2 & IHa3 & IHa4);
            destruct (IHb Hb) as (IHb1 & IHb2 & IHb3 & IHb4); split4;
            intros; simpl.
          + rewrite IHa1, IHb1; reflexivity.
          + rewrite IHa2, IHb4; reflexivity.
          + rewrite IHa1, IHb1; reflexivity.
          + rewrite IHa2, IHb4; reflexivity.
        - assert (Ha : forall m, NSet.In m (fnames psiL) -> Vq m = Vq' m)
            by (intros m Hm; apply Hag; simpl; apply NSet.union_spec; left;
                exact Hm).
          assert (Hb : forall m, NSet.In m (fnames psiR) -> Vq m = Vq' m)
            by (intros m Hm; apply Hag; simpl; apply NSet.union_spec; right;
                exact Hm).
          destruct (IHa Ha) as (IHa1 & IHa2 & IHa3 & IHa4);
            destruct (IHb Hb) as (IHb1 & IHb2 & IHb3 & IHb4); split4;
            intros; simpl.
          + rewrite IHa1, IHb3; reflexivity.
          + rewrite IHa2, IHb2; reflexivity.
          + rewrite IHa1, IHb3; reflexivity.
          + rewrite IHa2, IHb2; reflexivity.
        - destruct (IHa Hag) as (IHa1 & IHa2 & IHa3 & IHa4); split4;
            intros; simpl; [apply IHa2 | apply IHa1 | apply IHa2 | apply IHa1].
      Qed.

      Lemma reduceDepsBy_agree : forall Vq Vq' D,
          (forall m, NSet.In m (depNames D) -> Vq m = Vq' m) ->
          reduceDepsBy Vq D = reduceDepsBy Vq' D.
      Proof.
        intros Vq Vq' D Hag; apply T.DepRel.ext; intro d.
        rewrite !mem_reduceDepsBy.
        split; intros [p [psi [Hd He]]]; exists p, psi; split; try exact Hd;
          assert (Hf : forall m, NSet.In m (fnames psi) -> Vq m = Vq' m)
            by (intros m Hm; apply Hag, mem_depNames; exists p, psi; auto);
          [rewrite <- (proj1 (encodeNNF_agree_aux Vq Vq' psi Hf))
          | rewrite (proj1 (encodeNNF_agree_aux Vq Vq' psi Hf))]; exact He.
      Qed.

      Fixpoint negNames (psi : Formula) : NSet.t :=
        match psi with
        | FDep _ _ => NSet.empty
        | FConj psiL psiR => NSet.union (negNames psiL) (negNames psiR)
        | FDisj psiL psiR => NSet.union (negNames psiL) (negNames psiR)
        | FNeg psi' => fnames psi'
        end.

      Lemma encodeNNF_agreeNeg_aux : forall Vq Vq' psi,
          (forall m, NSet.In m (negNames psi) -> Vq m = Vq' m) ->
          (forall p, encodeNNF Vq p psi = encodeNNF Vq' p psi) /\
          (forall n i, encodeDisj Vq n i psi = encodeDisj Vq' n i psi).
      Proof.
        intros Vq Vq' psi;
          induction psi
            as [m vs | psiL IHa psiR IHb | psiL IHa psiR IHb | psi' IHa];
            intro Hag.
        - split; intros; reflexivity.
        - assert (Ha : forall m, NSet.In m (negNames psiL) -> Vq m = Vq' m)
            by (intros m Hm; apply Hag; simpl; apply NSet.union_spec; left;
                exact Hm).
          assert (Hb : forall m, NSet.In m (negNames psiR) -> Vq m = Vq' m)
            by (intros m Hm; apply Hag; simpl; apply NSet.union_spec; right;
                exact Hm).
          destruct (IHa Ha) as [IHa1 _]; destruct (IHb Hb) as [IHb1 _];
            split; intros; simpl; rewrite IHa1, IHb1; reflexivity.
        - assert (Ha : forall m, NSet.In m (negNames psiL) -> Vq m = Vq' m)
            by (intros m Hm; apply Hag; simpl; apply NSet.union_spec; left;
                exact Hm).
          assert (Hb : forall m, NSet.In m (negNames psiR) -> Vq m = Vq' m)
            by (intros m Hm; apply Hag; simpl; apply NSet.union_spec; right;
                exact Hm).
          destruct (IHa Ha) as [IHa1 _]; destruct (IHb Hb) as [_ IHb2];
            split; intros; simpl; rewrite IHa1, IHb2; reflexivity.
        - destruct (encodeNNF_agree_aux Vq Vq' psi' Hag) as (_ & Hn & _ & _);
            split; intros; simpl; apply Hn.
      Qed.

      Lemma reduceDepsBy_agreeNeg : forall Vq Vq' D,
          (forall p psi m, DepRel.In (p, psi) D -> NSet.In m (negNames psi) ->
                         Vq m = Vq' m) ->
          reduceDepsBy Vq D = reduceDepsBy Vq' D.
      Proof.
        intros Vq Vq' D Hag; apply T.DepRel.ext; intro d.
        rewrite !mem_reduceDepsBy.
        split; intros [p [psi [Hd He]]]; exists p, psi; split; try exact Hd;
          destruct (encodeNNF_agreeNeg_aux Vq Vq' psi (fun m => Hag p psi m Hd))
            as [E _]; [rewrite <- E | rewrite E]; exact He.
      Qed.

      Module PkgFibred := FibredRel N V Pkg PkgSet.
      Module DepRelFibred := FibredRel Pkg Dependees DepElt DepRel.

      Definition syntheticPkgs (n : Name.t) : T.PkgSet.t :=
        match n with
        | Name.Orig _ => T.PkgSet.empty
        | Name.Disjunct chis => idxPkgs (Name.Disjunct chis) (List.length chis)
        end.

      Lemma arisingPkgs_synthetic_aux : forall psi : Formula,
          (forall (p q : T.Pkg.t),
              T.PkgSet.In q (arisingPkgs p psi) ->
              T.PkgSet.In q (syntheticPkgs (fst q))) /\
          (forall (p q : T.Pkg.t),
              T.PkgSet.In q (arisingNeg p psi) ->
              T.PkgSet.In q (syntheticPkgs (fst q))) /\
          (forall (n : Name.t) (i : nat) (q : T.Pkg.t),
              T.PkgSet.In q (arisingDisj n i psi) ->
              T.PkgSet.In q (syntheticPkgs (fst q))) /\
          (forall (n : Name.t) (i : nat) (q : T.Pkg.t),
              T.PkgSet.In q (arisingConjNeg n i psi) ->
              T.PkgSet.In q (syntheticPkgs (fst q))).
      Proof.
        induction psi
          as [m ws | psiL IHa psiR IHb | psiL IHa psiR IHb | psi' IHa].
        - split4; intros; exfalso; eapply SOpt.empty_in; eassumption.
        - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
            destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4.
          + intros p q H; simpl in H; apply T.PkgSet.union_spec in H;
              destruct H as [H | H]; [exact (IHa1 _ _ H) | exact (IHb1 _ _ H)].
          + intros p q H; simpl in H; apply T.PkgSet.union_spec in H;
              destruct H as [H | H].
            * apply mem_idxPkgs in H; destruct H as [i [Hi ->]];
                cbn [fst syntheticPkgs]; apply mem_idxPkgs; exists i;
                split; [exact Hi | reflexivity].
            * apply T.PkgSet.union_spec in H; destruct H as [H | H];
                [exact (IHa2 _ _ H) | exact (IHb4 _ _ _ H)].
          + intros n i q H; simpl in H; apply T.PkgSet.union_spec in H;
              destruct H as [H | H]; [exact (IHa1 _ _ H) | exact (IHb1 _ _ H)].
          + intros n i q H; simpl in H; apply T.PkgSet.union_spec in H;
              destruct H as [H | H];
              [exact (IHa2 _ _ H) | exact (IHb4 _ _ _ H)].
        - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
            destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4.
          + intros p q H; simpl in H; apply T.PkgSet.union_spec in H;
              destruct H as [H | H].
            * apply mem_idxPkgs in H; destruct H as [i [Hi ->]];
                cbn [fst syntheticPkgs]; apply mem_idxPkgs; exists i;
                split; [exact Hi | reflexivity].
            * apply T.PkgSet.union_spec in H; destruct H as [H | H];
                [exact (IHa1 _ _ H) | exact (IHb3 _ _ _ H)].
          + intros p q H; simpl in H; apply T.PkgSet.union_spec in H;
              destruct H as [H | H]; [exact (IHa2 _ _ H) | exact (IHb2 _ _ H)].
          + intros n i q H; simpl in H; apply T.PkgSet.union_spec in H;
              destruct H as [H | H];
              [exact (IHa1 _ _ H) | exact (IHb3 _ _ _ H)].
          + intros n i q H; simpl in H; apply T.PkgSet.union_spec in H;
              destruct H as [H | H]; [exact (IHa2 _ _ H) | exact (IHb2 _ _ H)].
        - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4); split4.
          + intros p q H; simpl in H; exact (IHa2 _ _ H).
          + intros p q H; simpl in H; exact (IHa1 _ _ H).
          + intros n i q H; simpl in H; exact (IHa2 _ _ H).
          + intros n i q H; simpl in H; exact (IHa1 _ _ H).
      Qed.

      Lemma encodeNNF_dependee_synthetic_aux : forall Vq (psi : Formula),
          (forall (p : T.Pkg.t) (d : T.DepElt.t),
              T.DepRel.In d (encodeNNF Vq p psi) ->
              T.PkgSet.Subset (syntheticPkgs (fst (snd d)))
                (arisingPkgs p psi)) /\
          (forall (p : T.Pkg.t) (d : T.DepElt.t),
              T.DepRel.In d (encodeNNFneg Vq p psi) ->
              T.PkgSet.Subset (syntheticPkgs (fst (snd d)))
                (arisingNeg p psi)) /\
          (forall (n : Name.t) (i : nat) (d : T.DepElt.t),
              T.DepRel.In d (encodeDisj Vq n i psi) ->
              T.PkgSet.Subset (syntheticPkgs (fst (snd d)))
                (arisingDisj n i psi)) /\
          (forall (n : Name.t) (i : nat) (d : T.DepElt.t),
              T.DepRel.In d (encodeConjNeg Vq n i psi) ->
              T.PkgSet.Subset (syntheticPkgs (fst (snd d)))
                (arisingConjNeg n i psi)).
      Proof.
        intros Vq psi;
          induction psi
            as [m ws | psiL IHa psiR IHb | psiL IHa psiR IHb | psi' IHa].
        - split4; intros; apply SOed.singleton_in in H; subst d;
            cbn [fst snd syntheticPkgs]; apply T.PkgSet.empty_subset.
        - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
            destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4.
          + intros p d H; simpl in H; apply T.DepRel.union_spec in H;
              intros z Hz; apply T.PkgSet.union_spec; destruct H as [H | H];
              [left; exact (IHa1 _ d H z Hz) | right; exact (IHb1 _ d H z Hz)].
          + intros p d H; simpl in H; rewrite SOed.add_in in H;
              destruct H as [-> | H].
            * intros z Hz; cbn [fst snd syntheticPkgs] in Hz;
                apply T.PkgSet.union_spec; left; exact Hz.
            * apply T.DepRel.union_spec in H; intros z Hz;
                apply T.PkgSet.union_spec; right;
                apply T.PkgSet.union_spec; destruct H as [H | H];
                [left; exact (IHa2 _ d H z Hz)
                | right; exact (IHb4 _ _ d H z Hz)].
          + intros n i d H; simpl in H; apply T.DepRel.union_spec in H;
              intros z Hz; apply T.PkgSet.union_spec; destruct H as [H | H];
              [left; exact (IHa1 _ d H z Hz) | right; exact (IHb1 _ d H z Hz)].
          + intros n i d H; simpl in H; apply T.DepRel.union_spec in H;
              intros z Hz; apply T.PkgSet.union_spec; destruct H as [H | H];
              [left; exact (IHa2 _ d H z Hz)
              | right; exact (IHb4 _ _ d H z Hz)].
        - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
            destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4.
          + intros p d H; simpl in H; rewrite SOed.add_in in H;
              destruct H as [-> | H].
            * intros z Hz; cbn [fst snd syntheticPkgs] in Hz;
                apply T.PkgSet.union_spec; left; exact Hz.
            * apply T.DepRel.union_spec in H; intros z Hz;
                apply T.PkgSet.union_spec; right;
                apply T.PkgSet.union_spec; destruct H as [H | H];
                [left; exact (IHa1 _ d H z Hz)
                | right; exact (IHb3 _ _ d H z Hz)].
          + intros p d H; simpl in H; apply T.DepRel.union_spec in H;
              intros z Hz; apply T.PkgSet.union_spec; destruct H as [H | H];
              [left; exact (IHa2 _ d H z Hz) | right; exact (IHb2 _ d H z Hz)].
          + intros n i d H; simpl in H; apply T.DepRel.union_spec in H;
              intros z Hz; apply T.PkgSet.union_spec; destruct H as [H | H];
              [left; exact (IHa1 _ d H z Hz)
              | right; exact (IHb3 _ _ d H z Hz)].
          + intros n i d H; simpl in H; apply T.DepRel.union_spec in H;
              intros z Hz; apply T.PkgSet.union_spec; destruct H as [H | H];
              [left; exact (IHa2 _ d H z Hz) | right; exact (IHb2 _ d H z Hz)].
        - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4); split4.
          + intros p d H; simpl in H; exact (IHa2 _ d H).
          + intros p d H; simpl in H; exact (IHa1 _ d H).
          + intros n i d H; simpl in H; exact (IHa2 _ d H).
          + intros n i d H; simpl in H; exact (IHa1 _ d H).
      Qed.

      Lemma reachable_instNames : forall R D (m : N.t),
          (exists p h, T.DepRel.In (p, (Name.Orig m, h)) (reduceDeps R D)) ->
          NSet.In m (instNames R D).
      Proof.
        intros R D m [p [h Hd]]; apply mem_reduceDeps in Hd.
        destruct Hd as [q [psi [Hq He]]].
        apply mem_instNames; right; apply mem_depNames; exists q, psi.
        split; [exact Hq |].
        exact (proj1
            (encodeNNF_dependee_orig_aux (C.versions R) psi) _ _ _ _ He).
      Qed.

      Lemma versions_reduceReal_bot : forall R D (n : N.t),
          T.VSet.add Version.Bot (T.versions (reduceReal R D) (Name.Orig n)) =
          T.VSet.add Version.Bot (embedVS (C.versions R n)).
      Proof.
        intros R D n; apply T.VSet.ext; intro w.
        rewrite !SOvv.add_in, T.mem_versions, mem_reduceReal.
        unfold embedVS; rewrite SOvv.mem_map.
        split.
        - intros [-> | [[[qn qv] [HR Hq]] | [[p [psi [_ Hw]]] | [m [_ [_ Hy]]]]]];
            [left; reflexivity | | |].
          + unfold embedPkg in Hq; injection Hq as -> ->.
            right; exists qv; split; [apply C.mem_versions; exact HR |].
            reflexivity.
          + exfalso; exact (arisingPkgs_not_orig _ _ _ _ Hw).
          + injection Hy as -> ->; left; reflexivity.
        - intros [-> | [v [Hv ->]]]; [left; reflexivity |].
          right; left; exists (n, v); split; [| reflexivity].
          apply C.mem_versions; exact Hv.
      Qed.

      Theorem versions_lookupOrig :
        forall R D (r : Pkg.t) (n : N.t),
          PkgSet.In r R ->
          (exists p h, T.DepRel.In (p, (Name.Orig n, h)) (reduceDeps R D)) \/
          n = fst r ->
          Ab.hasAbsent n = true ->
          T.versions (reduceReal R D) (Name.Orig n) =
          T.VSet.add Version.Bot
            (T.versions (reduceReal (PkgFibred.tailFibre R n) DepRel.empty)
               (Name.Orig n)).
      Proof.
        intros R D [rn rv] n Hr Hreach Ha; cbn [fst] in Hreach.
        rewrite versions_reduceReal_bot.
        assert (Hm : NSet.In n (instNames R D)).
        { destruct Hreach as [Hreach | ->];
            [exact (reachable_instNames R D n Hreach) |].
          apply mem_instNames; left; exists rv; exact Hr. }
        apply T.VSet.ext; intro w.
        rewrite T.mem_versions, mem_reduceReal, SOvv.add_in.
        unfold embedVS; rewrite SOvv.mem_map.
        split.
        - intros [[[qn qv] [HR Hq]] | [[p [psi [_ Hw]]] | [m [_ [_ Hy]]]]].
          + unfold embedPkg in Hq; injection Hq as -> ->.
            right; exists qv; split; [| reflexivity].
            apply C.mem_versions, PkgFibred.mem_tailFibre; auto.
          + exfalso; exact (arisingPkgs_not_orig _ _ _ _ Hw).
          + injection Hy as -> ->; left; reflexivity.
        - intros [-> | [v [Hv ->]]].
          + right; right; exists n; auto.
          + apply C.mem_versions, PkgFibred.mem_tailFibre in Hv.
            destruct Hv as [Hv _].
            left; exists (n, v); split; [exact Hv | reflexivity].
      Qed.

      Theorem versions_lookupOrigPresent : forall R D (n : N.t),
          Ab.hasAbsent n = false ->
          T.versions (reduceReal R D) (Name.Orig n) =
          embedVS (C.versions (PkgFibred.tailFibre R n) n).
      Proof.
        intros R D n Ha; apply T.VSet.ext; intro w.
        rewrite T.mem_versions, mem_reduceReal.
        unfold embedVS; rewrite SOvv.mem_map.
        split.
        - intros [[[qn qv] [HR Hq]] | [[p [psi [_ Hw]]] | [m [_ [Hn Hy]]]]].
          + unfold embedPkg in Hq; injection Hq as -> ->.
            exists qv; split; [| reflexivity].
            apply C.mem_versions, PkgFibred.mem_tailFibre; auto.
          + exfalso; exact (arisingPkgs_not_orig _ _ _ _ Hw).
          + injection Hy as -> _; rewrite Ha in Hn; discriminate Hn.
        - intros [v [Hv ->]].
          apply C.mem_versions, PkgFibred.mem_tailFibre in Hv.
          destruct Hv as [Hv _].
          left; exists (n, v); split; [exact Hv | reflexivity].
      Qed.

      (* An original package's own edges are its formula's top level.  A
         disjunction, and by De Morgan a negated conjunction, hangs off its
         disjunct, so only a negated atom reads its name's versions, for
         its complement. *)
      Fixpoint ownNegNames (psi : Formula) : NSet.t :=
        match psi with
        | FDep _ _ => NSet.empty
        | FConj psiL psiR => NSet.union (ownNegNames psiL) (ownNegNames psiR)
        | FDisj _ _ => NSet.empty
        | FNeg psi' => ownNegNamesNeg psi'
        end
      with ownNegNamesNeg (psi : Formula) : NSet.t :=
        match psi with
        | FDep m _ => NSet.singleton m
        | FConj _ _ => NSet.empty
        | FDisj psiL psiR =>
            NSet.union (ownNegNamesNeg psiL) (ownNegNamesNeg psiR)
        | FNeg psi' => ownNegNames psi'
        end.

      Definition ownNegDepNames (D : DepRel.t) : NSet.t :=
        SOen.unionMap (fun '(_, psi) => ownNegNames psi) D.

      Lemma mem_ownNegDepNames : forall D (n : N.t),
          NSet.In n (ownNegDepNames D) <->
          exists p psi, DepRel.In (p, psi) D /\ NSet.In n (ownNegNames psi).
      Proof.
        intros D n; unfold ownNegDepNames; rewrite SOen.mem_unionMap.
        split.
        - intros [[q chi] [He Hn]]; exists q, chi; split; [exact He | exact Hn].
        - intros [q [chi [Hq Hn]]]; exists (q, chi); split;
            [exact Hq | exact Hn].
      Qed.

      Lemma encodeNNF_agreeOwn_aux : forall Vq Vq' psi,
          ((forall m, NSet.In m (ownNegNames psi) -> Vq m = Vq' m) ->
           forall (q : T.Pkg.t) n (v : Version.t) (d : T.Dependees.t),
             T.DepRel.In ((Name.Orig n, v), d) (encodeNNF Vq q psi) ->
             T.DepRel.In ((Name.Orig n, v), d) (encodeNNF Vq' q psi)) /\
          ((forall m, NSet.In m (ownNegNamesNeg psi) -> Vq m = Vq' m) ->
           forall (q : T.Pkg.t) n (v : Version.t) (d : T.Dependees.t),
             T.DepRel.In ((Name.Orig n, v), d) (encodeNNFneg Vq q psi) ->
             T.DepRel.In ((Name.Orig n, v), d) (encodeNNFneg Vq' q psi)).
      Proof.
        intros Vq Vq' psi;
          induction psi
            as [o vs | psiL IHa psiR IHb | psiL IHa psiR IHb | psi' IHa].
        - split; intros Hag q n w d H; simpl in H |- *; [exact H |].
          assert (E : Vq o = Vq' o)
            by (apply Hag; simpl; apply NSet.singleton_spec; reflexivity).
          unfold complementVS in H |- *; rewrite <- E; exact H.
        - destruct IHa as [IHa1 IHa2]; destruct IHb as [IHb1 IHb2]; split;
            intros Hag q n w d H; simpl in H |- *.
          + apply T.DepRel.union_spec in H; apply T.DepRel.union_spec.
            destruct H as [H | H]; [left | right];
              [refine (IHa1 _ _ _ _ _ H) | refine (IHb1 _ _ _ _ _ H)];
              intros m Hx; apply Hag; simpl; apply NSet.union_spec; tauto.
          + apply SOed.add_in in H; apply SOed.add_in.
            destruct H as [H | H]; [left; exact H | exfalso].
            apply T.DepRel.union_spec in H; destruct H as [H | H];
              [assert (E := proj1 (proj2 (encodeNNF_depender_orig_aux Vq psiL))
                              _ _ _ _ H)
              | assert (E := proj2 (proj2 (proj2
                               (encodeNNF_depender_orig_aux Vq psiR)))
                              _ _ _ _ _ H)];
              discriminate E.
        - destruct IHa as [IHa1 IHa2]; destruct IHb as [IHb1 IHb2]; split;
            intros Hag q n w d H; simpl in H |- *.
          + apply SOed.add_in in H; apply SOed.add_in.
            destruct H as [H | H]; [left; exact H | exfalso].
            apply T.DepRel.union_spec in H; destruct H as [H | H];
              [assert (E := proj1 (encodeNNF_depender_orig_aux Vq psiL)
                              _ _ _ _ H)
              | assert (E := proj1 (proj2 (proj2
                               (encodeNNF_depender_orig_aux Vq psiR)))
                              _ _ _ _ _ H)];
              discriminate E.
          + apply T.DepRel.union_spec in H; apply T.DepRel.union_spec.
            destruct H as [H | H]; [left | right];
              [refine (IHa2 _ _ _ _ _ H) | refine (IHb2 _ _ _ _ _ H)];
              intros m Hx; apply Hag; simpl; apply NSet.union_spec; tauto.
        - destruct IHa as [IHa1 IHa2]; split; intros Hag q n w d H;
            simpl in H |- *;
            [exact (IHa2 Hag _ _ _ _ H) | exact (IHa1 Hag _ _ _ _ H)].
      Qed.

      Lemma dependees_origAgree : forall Vq Vq' D n (v : Version.t),
          (forall p psi m, DepRel.In (p, psi) D ->
                           NSet.In m (ownNegNames psi) -> Vq m = Vq' m) ->
          T.dependees (reduceDepsBy Vq D) (Name.Orig n, v) =
          T.dependees (reduceDepsBy Vq' D) (Name.Orig n, v).
      Proof.
        intros Vq Vq' D n v Hag; apply T.dependees_ext; intro h.
        rewrite !mem_reduceDepsBy.
        split; intros [p [psi [Hd He]]]; exists p, psi; split; try exact Hd.
        - exact (proj1 (encodeNNF_agreeOwn_aux Vq Vq' psi)
                   (fun m Hx => Hag p psi m Hd Hx) _ _ _ _ He).
        - exact (proj1 (encodeNNF_agreeOwn_aux Vq' Vq psi)
                   (fun m Hx => eq_sym (Hag p psi m Hd Hx)) _ _ _ _ He).
      Qed.

      Lemma dependees_tailFibreBy : forall Vq D m v,
          T.dependees (reduceDepsBy Vq D) (Name.Orig m, Version.Orig v) =
          T.dependees (reduceDepsBy Vq (DepRelFibred.tailFibre D (m, v)))
            (Name.Orig m, Version.Orig v).
      Proof.
        intros Vq D m v; apply T.dependees_ext; intro h.
        rewrite !mem_reduceDepsBy.
        split.
        - intros [p [psi [Hd He]]].
          assert (E := proj1 (encodeNNF_depender_orig_aux Vq psi) _ _ _ _ He).
          destruct p as [pn pv]; unfold embedPkg in E; injection E as -> ->.
          exists (m, v), psi; split; [| exact He].
          apply DepRelFibred.mem_tailFibre; auto.
        - intros [p [psi [Hd He]]].
          apply DepRelFibred.mem_tailFibre in Hd; destruct Hd as [HD ->].
          exists (m, v), psi; split; [exact HD | exact He].
      Qed.

      Theorem dependees_lookupOrigBy : forall R D Vq n v,
          (forall m,
             NSet.In m (ownNegDepNames (DepRelFibred.tailFibre D (n, v))) ->
             Vq m = C.versions R m) ->
          T.dependees (reduceDeps R D) (Name.Orig n, Version.Orig v) =
          T.dependees (reduceDepsBy Vq (DepRelFibred.tailFibre D (n, v)))
            (Name.Orig n, Version.Orig v).
      Proof.
        intros R D Vq n v HVq; unfold reduceDeps.
        rewrite dependees_tailFibreBy; apply dependees_origAgree.
        intros p psi x Hpf Hx; symmetry; apply HVq.
        apply mem_ownNegDepNames; exists p, psi; auto.
      Qed.

      Theorem dependees_lookupOrig : forall R D n v,
          T.dependees (reduceDeps R D) (Name.Orig n, Version.Orig v) =
          T.dependees
            (reduceDeps
               (C.namePreimage R
                  (ownNegDepNames (DepRelFibred.tailFibre D (n, v))))
               (DepRelFibred.tailFibre D (n, v)))
            (Name.Orig n, Version.Orig v).
      Proof.
        intros R D n v; rewrite (dependees_lookupOrigBy R D
          (C.versions (C.namePreimage R
             (ownNegDepNames (DepRelFibred.tailFibre D (n, v)))))).
        - reflexivity.
        - intros m Hn; apply C.versions_namePreimage; exact Hn.
      Qed.

      Theorem dependees_lookupAbsent : forall R D n,
          T.dependees (reduceDeps R D) (Name.Orig n, Version.Bot) =
          T.DependeesSet.empty.
      Proof.
        intros R D n; apply T.dependees_empty_iff; intros h H.
        apply mem_reduceDeps in H.
        destruct H as [[pn pv] [psi [_ He]]].
        assert (E := proj1 (encodeNNF_depender_orig_aux (C.versions R) psi)
                       _ _ _ _ He).
        unfold embedPkg in E; discriminate.
      Qed.

      Theorem versions_lookupDisjunct : forall R D (chis : list Formula),
          (exists p h,
              T.DepRel.In (p, (Name.Disjunct chis, h)) (reduceDeps R D)) ->
          T.versions (reduceReal R D) (Name.Disjunct chis) =
          idxSet (List.length chis).
      Proof.
        intros R D chis [p [h Hd]].
        apply mem_reduceDeps in Hd; destruct Hd as [r [chi [HD He]]].
        pose proof (proj1 (encodeNNF_dependee_synthetic_aux (C.versions R) chi)
                      (embedPkg r) (p, (Name.Disjunct chis, h)) He) as Hsub.
        cbn [fst snd] in Hsub.
        apply T.VSet.ext; intro w.
        rewrite T.mem_versions, mem_idxSet, mem_reduceReal.
        split.
        - intros [[[qn qv] [_ Hq]] | [[r1 [g1 [_ Hw]]] | [n [_ [_ Hy]]]]].
          + unfold embedPkg in Hq; discriminate Hq.
          + pose proof (proj1 (arisingPkgs_synthetic_aux g1) _ _ Hw) as Hg.
            cbn [fst syntheticPkgs] in Hg; apply mem_idxPkgs in Hg.
            destruct Hg as [i [Hi Hq]]; exists i;
              split; [exact Hi | congruence].
          + discriminate Hy.
        - intros [i [Hi ->]]; right; left; exists r, chi; split; [exact HD |].
          apply Hsub; cbn [syntheticPkgs]; apply mem_idxPkgs;
            exists i; split; [exact Hi | reflexivity].
      Qed.

      Lemma encodeDisj_alt : forall Vq (psi : Formula) (n : Name.t) (i0 j : nat)
                                    (chi : Formula) (d : T.Dependees.t),
          List.nth_error (disjSpine psi) j = Some chi ->
          T.DepRel.In ((n, Version.Idx (i0 + j)), d)
            (encodeNNF Vq (n, Version.Idx (i0 + j)) chi) ->
          T.DepRel.In ((n, Version.Idx (i0 + j)), d) (encodeDisj Vq n i0 psi).
      Proof.
        intros Vq psi;
          induction psi
            as [m ws | psiL IHa psiR IHb | psiL IHa psiR IHb | psi' IHa];
          intros n i0 j chi d Hg Hd; simpl in Hg.
        - destruct j as [| j]; [| destruct j; discriminate].
          injection Hg as <-; replace (i0 + 0) with i0 in * by lia; exact Hd.
        - destruct j as [| j]; [| destruct j; discriminate].
          injection Hg as <-; replace (i0 + 0) with i0 in * by lia; exact Hd.
        - destruct j as [| j].
          + injection Hg as <-; replace (i0 + 0) with i0 in * by lia;
              apply T.DepRel.union_spec; left; exact Hd.
          + apply T.DepRel.union_spec; right;
              replace (i0 + S j) with (S i0 + j) in * by lia;
              exact (IHb n (S i0) j chi d Hg Hd).
        - destruct j as [| j]; [| destruct j; discriminate].
          injection Hg as <-; replace (i0 + 0) with i0 in * by lia; exact Hd.
      Qed.

      Lemma encodeConjNeg_alt : forall Vq (psi : Formula) (n : Name.t)
                                       (i0 j : nat) (chi : Formula)
                                       (d : T.Dependees.t),
          List.nth_error (negConjSpine psi) j = Some chi ->
          T.DepRel.In ((n, Version.Idx (i0 + j)), d)
            (encodeNNF Vq (n, Version.Idx (i0 + j)) chi) ->
          T.DepRel.In ((n, Version.Idx (i0 + j)), d)
            (encodeConjNeg Vq n i0 psi).
      Proof.
        intros Vq psi;
          induction psi
            as [m ws | psiL IHa psiR IHb | psiL IHa psiR IHb | psi' IHa];
          intros n i0 j chi d Hg Hd; simpl in Hg.
        - destruct j as [| j]; [| destruct j; discriminate].
          injection Hg as <-; replace (i0 + 0) with i0 in * by lia; exact Hd.
        - destruct j as [| j].
          + injection Hg as <-; replace (i0 + 0) with i0 in * by lia;
              apply T.DepRel.union_spec; left; exact Hd.
          + apply T.DepRel.union_spec; right;
              replace (i0 + S j) with (S i0 + j) in * by lia;
              exact (IHb n (S i0) j chi d Hg Hd).
        - destruct j as [| j]; [| destruct j; discriminate].
          injection Hg as <-; replace (i0 + 0) with i0 in * by lia; exact Hd.
        - destruct j as [| j]; [| destruct j; discriminate].
          injection Hg as <-; replace (i0 + 0) with i0 in * by lia; exact Hd.
      Qed.

      Lemma arisingPkgs_alt_aux : forall Vq (psi : Formula),
          (forall (p : T.Pkg.t) (chis : list Formula) (i : nat) (chi : Formula)
                  (d : T.Dependees.t),
              T.PkgSet.In (Name.Disjunct chis, Version.Idx i)
                (arisingPkgs p psi) ->
              List.nth_error chis i = Some chi ->
              T.DepRel.In ((Name.Disjunct chis, Version.Idx i), d)
                (encodeNNF Vq (Name.Disjunct chis, Version.Idx i) chi) ->
              T.DepRel.In ((Name.Disjunct chis, Version.Idx i), d)
                (encodeNNF Vq p psi)) /\
          (forall (p : T.Pkg.t) (chis : list Formula) (i : nat) (chi : Formula)
                  (d : T.Dependees.t),
              T.PkgSet.In (Name.Disjunct chis, Version.Idx i)
                (arisingNeg p psi) ->
              List.nth_error chis i = Some chi ->
              T.DepRel.In ((Name.Disjunct chis, Version.Idx i), d)
                (encodeNNF Vq (Name.Disjunct chis, Version.Idx i) chi) ->
              T.DepRel.In ((Name.Disjunct chis, Version.Idx i), d)
                (encodeNNFneg Vq p psi)) /\
          (forall (n : Name.t) (i0 : nat) (chis : list Formula) (i : nat)
                  (chi : Formula) (d : T.Dependees.t),
              T.PkgSet.In (Name.Disjunct chis, Version.Idx i)
                (arisingDisj n i0 psi) ->
              List.nth_error chis i = Some chi ->
              T.DepRel.In ((Name.Disjunct chis, Version.Idx i), d)
                (encodeNNF Vq (Name.Disjunct chis, Version.Idx i) chi) ->
              T.DepRel.In ((Name.Disjunct chis, Version.Idx i), d)
                (encodeDisj Vq n i0 psi)) /\
          (forall (n : Name.t) (i0 : nat) (chis : list Formula) (i : nat)
                  (chi : Formula) (d : T.Dependees.t),
              T.PkgSet.In (Name.Disjunct chis, Version.Idx i)
                (arisingConjNeg n i0 psi) ->
              List.nth_error chis i = Some chi ->
              T.DepRel.In ((Name.Disjunct chis, Version.Idx i), d)
                (encodeNNF Vq (Name.Disjunct chis, Version.Idx i) chi) ->
              T.DepRel.In ((Name.Disjunct chis, Version.Idx i), d)
                (encodeConjNeg Vq n i0 psi)).
      Proof.
        intros Vq psi;
          induction psi
            as [m ws | psiL IHa psiR IHb | psiL IHa psiR IHb | psi' IHa].
        - split4; intros; exfalso; eapply SOpt.empty_in; eassumption.
        - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
            destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4.
          + intros p chis i chi d H Hg Hd; simpl in H; simpl;
              apply T.PkgSet.union_spec in H; apply T.DepRel.union_spec;
              destruct H as [H | H];
              [left; exact (IHa1 _ _ _ _ _ H Hg Hd)
              | right; exact (IHb1 _ _ _ _ _ H Hg Hd)].
          + intros p chis i chi d H Hg Hd; simpl in H; simpl.
            apply T.PkgSet.union_spec in H; apply SOed.add_in;
              destruct H as [H | H]; [| right; apply T.DepRel.union_spec].
            * apply mem_idxPkgs in H; destruct H as [j [_ H]];
                injection H as H1 H2; subst chis; subst i; right;
                apply T.DepRel.union_spec; destruct j as [| j];
                simpl in Hg; [left | right].
              -- injection Hg as <-; exact Hd.
              -- exact (encodeConjNeg_alt Vq psiR
                          (Name.Disjunct (FNeg psiL :: negConjSpine psiR))
                          1 j chi d Hg Hd).
            * apply T.PkgSet.union_spec in H; destruct H as [H | H];
                [left; exact (IHa2 _ _ _ _ _ H Hg Hd)
                | right; exact (IHb4 _ _ _ _ _ _ H Hg Hd)].
          + intros n i0 chis i chi d H Hg Hd; simpl in H; simpl;
              apply T.PkgSet.union_spec in H; apply T.DepRel.union_spec;
              destruct H as [H | H];
              [left; exact (IHa1 _ _ _ _ _ H Hg Hd)
              | right; exact (IHb1 _ _ _ _ _ H Hg Hd)].
          + intros n i0 chis i chi d H Hg Hd; simpl in H; simpl;
              apply T.PkgSet.union_spec in H; apply T.DepRel.union_spec;
              destruct H as [H | H];
              [left; exact (IHa2 _ _ _ _ _ H Hg Hd)
              | right; exact (IHb4 _ _ _ _ _ _ H Hg Hd)].
        - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
            destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4.
          + intros p chis i chi d H Hg Hd; simpl in H; simpl.
            apply T.PkgSet.union_spec in H; apply SOed.add_in;
              destruct H as [H | H]; [| right; apply T.DepRel.union_spec].
            * apply mem_idxPkgs in H; destruct H as [j [_ H]];
                injection H as H1 H2; subst chis; subst i; right;
                apply T.DepRel.union_spec; destruct j as [| j];
                simpl in Hg; [left | right].
              -- injection Hg as <-; exact Hd.
              -- exact (encodeDisj_alt Vq psiR
                          (Name.Disjunct (psiL :: disjSpine psiR))
                          1 j chi d Hg Hd).
            * apply T.PkgSet.union_spec in H; destruct H as [H | H];
                [left; exact (IHa1 _ _ _ _ _ H Hg Hd)
                | right; exact (IHb3 _ _ _ _ _ _ H Hg Hd)].
          + intros p chis i chi d H Hg Hd; simpl in H; simpl;
              apply T.PkgSet.union_spec in H; apply T.DepRel.union_spec;
              destruct H as [H | H];
              [left; exact (IHa2 _ _ _ _ _ H Hg Hd)
              | right; exact (IHb2 _ _ _ _ _ H Hg Hd)].
          + intros n i0 chis i chi d H Hg Hd; simpl in H; simpl;
              apply T.PkgSet.union_spec in H; apply T.DepRel.union_spec;
              destruct H as [H | H];
              [left; exact (IHa1 _ _ _ _ _ H Hg Hd)
              | right; exact (IHb3 _ _ _ _ _ _ H Hg Hd)].
          + intros n i0 chis i chi d H Hg Hd; simpl in H; simpl;
              apply T.PkgSet.union_spec in H; apply T.DepRel.union_spec;
              destruct H as [H | H];
              [left; exact (IHa2 _ _ _ _ _ H Hg Hd)
              | right; exact (IHb2 _ _ _ _ _ H Hg Hd)].
        - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4); split4.
          + intros p chis i chi d H Hg Hd; exact (IHa2 _ _ _ _ _ H Hg Hd).
          + intros p chis i chi d H Hg Hd; exact (IHa1 _ _ _ _ _ H Hg Hd).
          + intros n i0 chis i chi d H Hg Hd; exact (IHa2 _ _ _ _ _ H Hg Hd).
          + intros n i0 chis i chi d H Hg Hd; exact (IHa1 _ _ _ _ _ H Hg Hd).
      Qed.

      Lemma encodeNNF_alt_aux : forall Vq (psi : Formula),
          (forall (q : T.Pkg.t) (chis : list Formula) (i : nat)
                  (d : T.Dependees.t),
              T.DepRel.In ((Name.Disjunct chis, Version.Idx i), d)
                (encodeNNF Vq q psi) ->
              q = (Name.Disjunct chis, Version.Idx i) \/
              (exists chi, List.nth_error chis i = Some chi /\
                         T.DepRel.In ((Name.Disjunct chis, Version.Idx i), d)
                           (encodeNNF Vq
                              (Name.Disjunct chis, Version.Idx i) chi))) /\
          (forall (q : T.Pkg.t) (chis : list Formula) (i : nat)
                  (d : T.Dependees.t),
              T.DepRel.In ((Name.Disjunct chis, Version.Idx i), d)
                (encodeNNFneg Vq q psi) ->
              q = (Name.Disjunct chis, Version.Idx i) \/
              (exists chi, List.nth_error chis i = Some chi /\
                         T.DepRel.In ((Name.Disjunct chis, Version.Idx i), d)
                           (encodeNNF Vq
                              (Name.Disjunct chis, Version.Idx i) chi))) /\
          (forall (n : Name.t) (i0 : nat) (chis : list Formula) (i : nat)
                  (d : T.Dependees.t),
              T.DepRel.In ((Name.Disjunct chis, Version.Idx i), d)
                (encodeDisj Vq n i0 psi) ->
              (n = Name.Disjunct chis /\
               exists j chi, i = i0 + j /\
                           List.nth_error (disjSpine psi) j = Some chi /\
                           T.DepRel.In ((Name.Disjunct chis, Version.Idx i), d)
                             (encodeNNF Vq
                                (Name.Disjunct chis, Version.Idx i) chi))
              \/
              (exists chi, List.nth_error chis i = Some chi /\
                         T.DepRel.In ((Name.Disjunct chis, Version.Idx i), d)
                           (encodeNNF Vq
                              (Name.Disjunct chis, Version.Idx i) chi))) /\
          (forall (n : Name.t) (i0 : nat) (chis : list Formula) (i : nat)
                  (d : T.Dependees.t),
              T.DepRel.In ((Name.Disjunct chis, Version.Idx i), d)
                (encodeConjNeg Vq n i0 psi) ->
              (n = Name.Disjunct chis /\
               exists j chi, i = i0 + j /\
                           List.nth_error (negConjSpine psi) j = Some chi /\
                           T.DepRel.In ((Name.Disjunct chis, Version.Idx i), d)
                             (encodeNNF Vq
                                (Name.Disjunct chis, Version.Idx i) chi))
              \/
              (exists chi, List.nth_error chis i = Some chi /\
                         T.DepRel.In ((Name.Disjunct chis, Version.Idx i), d)
                           (encodeNNF Vq
                              (Name.Disjunct chis, Version.Idx i) chi))).
      Proof.
        intros Vq psi;
          induction psi
            as [m ws | psiL IHa psiR IHb | psiL IHa psiR IHb | psi' IHa].
        - split4.
          + intros q chis i d H; apply SOed.singleton_in in H;
              left; congruence.
          + intros q chis i d H; apply SOed.singleton_in in H;
              left; congruence.
          + intros n i0 chis i d H; apply SOed.singleton_in in H;
              injection H as H1 H2 H3; left; split; [congruence |].
            exists 0, (FDep m ws); subst i;
              split; [lia | split; [reflexivity |]].
            apply SOed.singleton_in; subst d; reflexivity.
          + intros n i0 chis i d H; apply SOed.singleton_in in H;
              injection H as H1 H2 H3; left; split; [congruence |].
            exists 0, (FNeg (FDep m ws)); subst i;
              split; [lia | split; [reflexivity |]].
            simpl; apply SOed.singleton_in; subst d; reflexivity.
        - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
            destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4.
          + intros q chis i d H; simpl in H; apply T.DepRel.union_spec in H;
              destruct H as [H | H];
              [exact (IHa1 _ _ _ _ H) | exact (IHb1 _ _ _ _ H)].
          + intros q chis i d H; simpl in H; apply SOed.add_in in H;
              destruct H as [H | H]; [left; congruence |].
            apply T.DepRel.union_spec in H; destruct H as [H | H].
            * destruct (IHa2 _ _ _ _ H) as [Eq | Hex]; [| right; exact Hex].
              injection Eq as Eq1 Eq2; right; exists (FNeg psiL);
                subst chis; subst i; split; [reflexivity | exact H].
            * destruct (IHb4 _ _ _ _ _ H)
                as [[Eq [j [chi [Hk [Hg Hin]]]]] | Hex];
                [| right; exact Hex].
              injection Eq as Eq; right; exists chi; subst chis; subst i;
                split; [| exact Hin].
              simpl; exact Hg.
          + intros n i0 chis i d H; simpl in H;
              apply T.DepRel.union_spec in H; destruct H as [H | H].
            * destruct (IHa1 _ _ _ _ H) as [Eq | Hex]; [| right; exact Hex].
              injection Eq as Eq1 Eq2; subst n; left;
                split; [reflexivity |].
              exists 0, (FConj psiL psiR); subst i;
                split; [lia | split; [reflexivity |]].
              simpl; apply T.DepRel.union_spec; left;
                exact H.
            * destruct (IHb1 _ _ _ _ H) as [Eq | Hex]; [| right; exact Hex].
              injection Eq as Eq1 Eq2; subst n; left;
                split; [reflexivity |].
              exists 0, (FConj psiL psiR); subst i;
                split; [lia | split; [reflexivity |]].
              simpl; apply T.DepRel.union_spec; right;
                exact H.
          + intros n i0 chis i d H; simpl in H;
              apply T.DepRel.union_spec in H; destruct H as [H | H].
            * destruct (IHa2 _ _ _ _ H) as [Eq | Hex]; [| right; exact Hex].
              injection Eq as Eq1 Eq2; subst n; left;
                split; [reflexivity |].
              exists 0, (FNeg psiL); subst i;
                split; [lia | split; [reflexivity |]].
              exact H.
            * destruct (IHb4 _ _ _ _ _ H)
                as [[Eq [j [chi [Hk [Hg Hin]]]]] | Hex];
                [| right; exact Hex].
              left; split; [exact Eq |]; exists (S j), chi;
                split; [lia | split; [exact Hg | exact Hin]].
        - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
            destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4.
          + intros q chis i d H; simpl in H; apply SOed.add_in in H;
              destruct H as [H | H]; [left; congruence |].
            apply T.DepRel.union_spec in H; destruct H as [H | H].
            * destruct (IHa1 _ _ _ _ H) as [Eq | Hex]; [| right; exact Hex].
              injection Eq as Eq1 Eq2; right; exists psiL;
                subst chis; subst i; split; [reflexivity | exact H].
            * destruct (IHb3 _ _ _ _ _ H)
                as [[Eq [j [chi [Hk [Hg Hin]]]]] | Hex];
                [| right; exact Hex].
              injection Eq as Eq; right; exists chi; subst chis; subst i;
                split; [| exact Hin].
              simpl; exact Hg.
          + intros q chis i d H; simpl in H; apply T.DepRel.union_spec in H;
              destruct H as [H | H];
              [exact (IHa2 _ _ _ _ H) | exact (IHb2 _ _ _ _ H)].
          + intros n i0 chis i d H; simpl in H;
              apply T.DepRel.union_spec in H; destruct H as [H | H].
            * destruct (IHa1 _ _ _ _ H) as [Eq | Hex]; [| right; exact Hex].
              injection Eq as Eq1 Eq2; subst n; left;
                split; [reflexivity |].
              exists 0, psiL; subst i; split; [lia | split; [reflexivity |]].
              exact H.
            * destruct (IHb3 _ _ _ _ _ H)
                as [[Eq [j [chi [Hk [Hg Hin]]]]] | Hex];
                [| right; exact Hex].
              left; split; [exact Eq |]; exists (S j), chi;
                split; [lia | split; [exact Hg | exact Hin]].
          + intros n i0 chis i d H; simpl in H;
              apply T.DepRel.union_spec in H; destruct H as [H | H].
            * destruct (IHa2 _ _ _ _ H) as [Eq | Hex]; [| right; exact Hex].
              injection Eq as Eq1 Eq2; subst n; left;
                split; [reflexivity |].
              exists 0, (FNeg (FDisj psiL psiR)); subst i;
                split; [lia | split; [reflexivity |]].
              simpl; apply T.DepRel.union_spec; left;
                exact H.
            * destruct (IHb2 _ _ _ _ H) as [Eq | Hex]; [| right; exact Hex].
              injection Eq as Eq1 Eq2; subst n; left;
                split; [reflexivity |].
              exists 0, (FNeg (FDisj psiL psiR)); subst i;
                split; [lia | split; [reflexivity |]].
              simpl; apply T.DepRel.union_spec; right;
                exact H.
        - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4); split4.
          + intros q chis i d H; exact (IHa2 _ _ _ _ H).
          + intros q chis i d H; exact (IHa1 _ _ _ _ H).
          + intros n i0 chis i d H; simpl in H.
            destruct (IHa2 _ _ _ _ H) as [Eq | Hex]; [| right; exact Hex].
            injection Eq as Eq1 Eq2; subst n; left;
              split; [reflexivity |].
            exists 0, (FNeg psi'); subst i;
              split; [lia | split; [reflexivity |]].
            exact H.
          + intros n i0 chis i d H; simpl in H.
            destruct (IHa1 _ _ _ _ H) as [Eq | Hex]; [| right; exact Hex].
            injection Eq as Eq1 Eq2; subst n; left;
              split; [reflexivity |].
            exists 0, (FNeg (FNeg psi')); subst i;
              split; [lia | split; [reflexivity |]].
            exact H.
      Qed.

      Theorem dependees_lookupDisjunct : forall R D chis (i : Version.t),
          T.PkgSet.In (Name.Disjunct chis, i) (reduceReal R D) ->
          T.dependees (reduceDeps R D) (Name.Disjunct chis, i) =
          match disjAlt chis i with
          | Some chi =>
              T.dependees (encodeNNF (C.versions R) (Name.Disjunct chis, i) chi)
                (Name.Disjunct chis, i)
          | None => T.DependeesSet.empty
          end.
      Proof.
        intros R D chis i H; apply mem_reduceReal in H.
        destruct H as [[[pn pv] [_ Hq]] | [[p [psi [HD Hw]]] | [n [_ [_ Hy]]]]];
          [unfold embedPkg in Hq; discriminate Hq | | discriminate Hy].
        pose proof (proj1 (arisingPkgs_synthetic_aux psi) _ _ Hw) as Hgd.
        cbn [fst syntheticPkgs] in Hgd; apply mem_idxPkgs in Hgd.
        destruct Hgd as [k [Hk Hi]].
        assert (Hv : i = Version.Idx k) by congruence; subst i.
        cbn [disjAlt].
        destruct (List.nth_error chis k) as [chi |] eqn:E;
          [| apply List.nth_error_None in E; lia].
        apply T.dependees_ext; intro h; rewrite mem_reduceDeps.
        split.
        - intros [q [psi' [_ He]]].
          destruct (proj1 (encodeNNF_alt_aux (C.versions R) psi') _ _ _ _ He)
            as [Eq | [chi' [Hg' Hin]]].
          + destruct q as [qn qv]; unfold embedPkg in Eq; simpl in Eq;
              discriminate.
          + rewrite E in Hg'; injection Hg' as <-; exact Hin.
        - intro Hin; exists p, psi; split; [exact HD |].
          exact (proj1
              (arisingPkgs_alt_aux (C.versions R) psi) _ _ _ _ _ Hw E Hin).
      Qed.

      Lemma negNames_fnames : forall psi m,
          NSet.In m (negNames psi) -> NSet.In m (fnames psi).
      Proof.
        induction psi
          as [o vs | psiL IHa psiR IHb | psiL IHa psiR IHb | psi' IHa];
          intros m Hx; cbn [negNames fnames] in *.
        - destruct (NSet.empty_spec Hx).
        - apply NSet.union_spec in Hx; apply NSet.union_spec.
          destruct Hx as [Hx | Hx];
            [left; exact (IHa _ Hx) | right; exact (IHb _ Hx)].
        - apply NSet.union_spec in Hx; apply NSet.union_spec.
          destruct Hx as [Hx | Hx];
            [left; exact (IHa _ Hx) | right; exact (IHb _ Hx)].
        - exact Hx.
      Qed.

      Lemma disjSpine_negNames : forall psiR chi m,
          List.In chi (disjSpine psiR) -> NSet.In m (negNames chi) ->
          NSet.In m (negNames psiR).
      Proof.
        induction psiR
          as [o vs | psiL IHa psiR IHb | psiL IHa psiR IHb | psi' IHa];
          intros chi m Hg Hx; cbn [disjSpine] in Hg;
          try (destruct Hg as [<- | []]; exact Hx).
        destruct Hg as [<- | Hg]; cbn [negNames]; apply NSet.union_spec;
          [left; exact Hx | right; exact (IHb _ _ Hg Hx)].
      Qed.

      Lemma negConjSpine_negNames : forall psiR chi m,
          List.In chi (negConjSpine psiR) -> NSet.In m (negNames chi) ->
          NSet.In m (fnames psiR).
      Proof.
        induction psiR
          as [o vs | psiL IHa psiR IHb | psiL IHa psiR IHb | psi' IHa];
          intros chi m Hg Hx; cbn [negConjSpine] in Hg;
          try (destruct Hg as [<- | []]; exact Hx).
        destruct Hg as [<- | Hg]; cbn [fnames]; apply NSet.union_spec;
          [left; exact Hx | right; exact (IHb _ _ Hg Hx)].
      Qed.

      Lemma arisingPkgs_negNames_aux : forall psi : Formula,
          (forall (p : T.Pkg.t) chis v chi m,
              T.PkgSet.In (Name.Disjunct chis, v) (arisingPkgs p psi) ->
              List.In chi chis -> NSet.In m (negNames chi) ->
              NSet.In m (negNames psi)) /\
          (forall (p : T.Pkg.t) chis v chi m,
              T.PkgSet.In (Name.Disjunct chis, v) (arisingNeg p psi) ->
              List.In chi chis -> NSet.In m (negNames chi) ->
              NSet.In m (fnames psi)) /\
          (forall (n : Name.t) (i : nat) chis v chi m,
              T.PkgSet.In (Name.Disjunct chis, v) (arisingDisj n i psi) ->
              List.In chi chis -> NSet.In m (negNames chi) ->
              NSet.In m (negNames psi)) /\
          (forall (n : Name.t) (i : nat) chis v chi m,
              T.PkgSet.In (Name.Disjunct chis, v) (arisingConjNeg n i psi) ->
              List.In chi chis -> NSet.In m (negNames chi) ->
              NSet.In m (fnames psi)).
      Proof.
        induction psi
          as [o vs | psiL IHa psiR IHb | psiL IHa psiR IHb | psi' IHa].
        - split4; intros; exfalso; eapply SOpt.empty_in; eassumption.
        - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
            destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4.
          + intros p chis v chi m H Hg Hx; simpl in H; cbn [negNames].
            apply NSet.union_spec; apply T.PkgSet.union_spec in H;
              destruct H as [H | H];
              [left; exact (IHa1 _ _ _ _ _ H Hg Hx)
              | right; exact (IHb1 _ _ _ _ _ H Hg Hx)].
          + intros p chis v chi m H Hg Hx; simpl in H; cbn [fnames].
            apply NSet.union_spec.
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
              [| apply T.PkgSet.union_spec in H; destruct H as [H | H]].
            * apply mem_idxPkgs in H; destruct H as [k [_ E]].
              injection E as -> _; destruct Hg as [<- | Hg];
                [left; exact Hx
                | right; exact (negConjSpine_negNames _ _ _ Hg Hx)].
            * left; exact (IHa2 _ _ _ _ _ H Hg Hx).
            * right; exact (IHb4 _ _ _ _ _ _ H Hg Hx).
          + intros n i chis v chi m H Hg Hx; simpl in H; cbn [negNames].
            apply NSet.union_spec; apply T.PkgSet.union_spec in H;
              destruct H as [H | H];
              [left; exact (IHa1 _ _ _ _ _ H Hg Hx)
              | right; exact (IHb1 _ _ _ _ _ H Hg Hx)].
          + intros n i chis v chi m H Hg Hx; simpl in H; cbn [fnames].
            apply NSet.union_spec; apply T.PkgSet.union_spec in H;
              destruct H as [H | H];
              [left; exact (IHa2 _ _ _ _ _ H Hg Hx)
              | right; exact (IHb4 _ _ _ _ _ _ H Hg Hx)].
        - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
            destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4.
          + intros p chis v chi m H Hg Hx; simpl in H; cbn [negNames].
            apply NSet.union_spec.
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
              [| apply T.PkgSet.union_spec in H; destruct H as [H | H]].
            * apply mem_idxPkgs in H; destruct H as [k [_ E]].
              injection E as -> _; destruct Hg as [<- | Hg];
                [left; exact Hx
                | right; exact (disjSpine_negNames _ _ _ Hg Hx)].
            * left; exact (IHa1 _ _ _ _ _ H Hg Hx).
            * right; exact (IHb3 _ _ _ _ _ _ H Hg Hx).
          + intros p chis v chi m H Hg Hx; simpl in H; cbn [fnames].
            apply NSet.union_spec; apply T.PkgSet.union_spec in H;
              destruct H as [H | H];
              [left; exact (IHa2 _ _ _ _ _ H Hg Hx)
              | right; exact (IHb2 _ _ _ _ _ H Hg Hx)].
          + intros n i chis v chi m H Hg Hx; simpl in H; cbn [negNames].
            apply NSet.union_spec; apply T.PkgSet.union_spec in H;
              destruct H as [H | H];
              [left; exact (IHa1 _ _ _ _ _ H Hg Hx)
              | right; exact (IHb3 _ _ _ _ _ _ H Hg Hx)].
          + intros n i chis v chi m H Hg Hx; simpl in H; cbn [fnames].
            apply NSet.union_spec; apply T.PkgSet.union_spec in H;
              destruct H as [H | H];
              [left; exact (IHa2 _ _ _ _ _ H Hg Hx)
              | right; exact (IHb2 _ _ _ _ _ H Hg Hx)].
        - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4); split4.
          + intros p chis v chi m H Hg Hx; simpl in H.
            exact (IHa2 _ _ _ _ _ H Hg Hx).
          + intros p chis v chi m H Hg Hx; simpl in H.
            exact (negNames_fnames _ _ (IHa1 _ _ _ _ _ H Hg Hx)).
          + intros n i chis v chi m H Hg Hx; simpl in H.
            exact (IHa2 _ _ _ _ _ H Hg Hx).
          + intros n i chis v chi m H Hg Hx; simpl in H.
            exact (negNames_fnames _ _ (IHa1 _ _ _ _ _ H Hg Hx)).
      Qed.

      Lemma dependees_disjunctBy : forall Vq D chis i,
          (exists p psi, DepRel.In (p, psi) D /\
             T.PkgSet.In (Name.Disjunct chis, i)
               (arisingPkgs (embedPkg p) psi)) ->
          T.dependees (reduceDepsBy Vq D) (Name.Disjunct chis, i) =
          match disjAlt chis i with
          | Some chi =>
              T.dependees (encodeNNF Vq (Name.Disjunct chis, i) chi)
                (Name.Disjunct chis, i)
          | None => T.DependeesSet.empty
          end.
      Proof.
        intros Vq D chis i [p [psi [HD Hw]]].
        pose proof (proj1 (arisingPkgs_synthetic_aux psi) _ _ Hw) as Hgd.
        cbn [fst syntheticPkgs] in Hgd; apply mem_idxPkgs in Hgd.
        destruct Hgd as [k [Hk Hi]].
        assert (Hv : i = Version.Idx k) by congruence; subst i.
        cbn [disjAlt].
        destruct (List.nth_error chis k) as [chi |] eqn:E;
          [| apply List.nth_error_None in E; lia].
        apply T.dependees_ext; intro h; rewrite mem_reduceDepsBy.
        split.
        - intros [q [psi' [_ He]]].
          destruct (proj1 (encodeNNF_alt_aux Vq psi') _ _ _ _ He)
            as [Eq | [chi' [Hg' Hin]]].
          + destruct q as [qn qv]; unfold embedPkg in Eq; simpl in Eq;
              discriminate.
          + rewrite E in Hg'; injection Hg' as <-; exact Hin.
        - intro Hin; exists p, psi; split; [exact HD |].
          exact (proj1 (arisingPkgs_alt_aux Vq psi) _ _ _ _ _ Hw E Hin).
      Qed.

      Theorem dependees_lookupDisjunctBy : forall R D R' D' Vq chis i,
          DepRel.Subset D' D ->
          T.PkgSet.In (Name.Disjunct chis, i) (reduceReal R' D') ->
          (forall p psi m, DepRel.In (p, psi) D' -> NSet.In m (negNames psi) ->
                         Vq m = C.versions R m) ->
          T.dependees (reduceDeps R D) (Name.Disjunct chis, i) =
          T.dependees (reduceDepsBy Vq D') (Name.Disjunct chis, i).
      Proof.
        intros R D R' D' Vq chis i Hsub Hin HVq.
        apply mem_reduceReal in Hin.
        destruct Hin as [[[pn pv] [_ Hq]] | [[p [psi [HD Hw]]]
                        | [n [_ [_ Hy]]]]];
          [unfold embedPkg in Hq; discriminate Hq | | discriminate Hy].
        unfold reduceDeps.
        rewrite (dependees_disjunctBy (C.versions R) D chis i)
          by (exists p, psi; split; [exact (Hsub _ HD) | exact Hw]).
        rewrite (dependees_disjunctBy Vq D' chis i)
          by (exists p, psi; split; [exact HD | exact Hw]).
        destruct (disjAlt chis i) as [chi |] eqn:Eg; [| reflexivity].
        assert (Hg : List.In chi chis).
        { destruct i as [v | k |]; cbn [disjAlt] in Eg; try discriminate.
          exact (nth_error_In _ _ Eg). }
        rewrite (proj1 (encodeNNF_agreeNeg_aux (C.versions R) Vq chi
                          (fun x Hx =>
                             eq_sym (HVq p psi x HD
                                       (proj1 (arisingPkgs_negNames_aux psi)
                                          _ _ _ _ _ Hw Hg Hx))))).
        reflexivity.
      Qed.

    End Lookup.
  End Reduction.
End FormulaCalculus.

Module AllAbsent (N : UsualOrderedType) <: AbsentNames N.
  Definition hasAbsent (_ : N.t) : bool := true.
End AllAbsent.

Module PackageFormula (N V : UsualOrderedType).
  Module Ab := AllAbsent N.
  Include FormulaCalculus N V Ab.

  Theorem package_formula_completeness :
    forall (R : PkgSet.t) (D : DepRel.t) (r : Pkg.t) (S : PkgSet.t),
      IsResolution R D r S ->
      Reduction.T.IsResolution (Reduction.reduceReal R D)
        (Reduction.reduceDeps R D) (Reduction.embedPkg r)
        (Reduction.coreResolution R D S).
  Proof.
    intros R D r S Hres.
    apply (Reduction.formula_calculus_completeness R D r S Hres).
    intros m _ Ha; discriminate Ha.
  Qed.
End PackageFormula.
