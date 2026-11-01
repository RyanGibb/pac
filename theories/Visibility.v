From Stdlib Require Import MSets MSetProperties Lia.
From PackageCalculus Require Import Prelude Core Concurrent.

Create HintDb cmp_vis.
Create Rewrite HintDb cmp_vis.

Module Visibility (N V : UsualOrderedType).
  Module Concurrent := Concurrent N V V.
  Module Source := Concurrent.Source.
  Module Package := Source.Package.
  Module PackageSet := Source.PackageSet.
  Module VSet := Source.VSet.
  Module ParentElt := Concurrent.ParentElt.
  Module ParentRel := Concurrent.ParentRel.

  Module PublicDependencyElt := PairUOT Package N.
  Module PublicDependencyRel := FSetUOT PublicDependencyElt.

  Definition Priv (D : Source.DependencyRel.t) (pub : PublicDependencyRel.t) (p : Package.t) : Prop :=
    exists (n : N.t) (vs : VSet.t),
      Source.DependencyRel.In (p, (n, vs)) D /\ ~ PublicDependencyRel.In (p, n) pub.

  Lemma not_priv_pub : forall D pub p (n : N.t) (vs : VSet.t),
      ~ Priv D pub p -> Source.DependencyRel.In (p, (n, vs)) D -> PublicDependencyRel.In (p, n) pub.
  Proof.
    intros D pub p n vs Hnp HD.
    destruct (PublicDependencyRel.mem (p, n) pub) eqn:Hm;
      [apply PublicDependencyRel.mem_spec; exact Hm | exfalso].
    apply Hnp; exists n, vs; split; [exact HD |].
    intro Hin; apply PublicDependencyRel.mem_spec in Hin; congruence.
  Qed.

  Definition IsOrigin (D : Source.DependencyRel.t) (pub : PublicDependencyRel.t) (r : Package.t)
      (S : PackageSet.t) (q : Package.t) : Prop :=
    q = r \/ (PackageSet.In q S /\ Priv D pub q).

  Lemma isOrigin_mem : forall D pub r S q,
      IsOrigin D pub r S q -> PackageSet.In r S -> PackageSet.In q S.
  Proof. intros D pub r S q [-> | [Hq _]] Hr; [exact Hr | exact Hq]. Qed.

  Inductive InSub (pub : PublicDependencyRel.t) (pi : ParentRel.t) (p : Package.t)
    : Package.t -> Prop :=
  | InSubSelf : InSub pub pi p p
  | InSubChild : forall (n : N.t) (v : V.t),
      ParentRel.In ((n, v), p) pi -> InSub pub pi p (n, v)
  | PublicPropagation : forall (q : Package.t) (n : N.t) (v : V.t),
      InSub pub pi p q -> ParentRel.In ((n, v), q) pi ->
      PublicDependencyRel.In (q, n) pub -> InSub pub pi p (n, v).

  Record IsResolution
      (R : PackageSet.t) (D : Source.DependencyRel.t) (pub : PublicDependencyRel.t) (r : Package.t)
      (S : PackageSet.t) (pi : ParentRel.t) : Prop :=
    { res_concurrent : Concurrent.IsResolution R D (fun v => v) r S pi
    ; res_version_visibility :
        forall p, PackageSet.In p S ->
        forall (n : N.t) (v v' : V.t),
          InSub pub pi p (n, v) -> InSub pub pi p (n, v') -> v = v' }.

  Definition OriginVisibility (D : Source.DependencyRel.t) (pub : PublicDependencyRel.t) (r : Package.t)
      (S : PackageSet.t) (pi : ParentRel.t) : Prop :=
    forall p, PackageSet.In p S ->
      exists q, IsOrigin D pub r S q /\ InSub pub pi q p.

  Module SOpp := SetOps ParentElt Package ParentRel PackageSet.
  Module SOppp := SetOps Package Package PackageSet PackageSet.

  Definition children (pi : ParentRel.t) (p : Package.t) : PackageSet.t :=
    SOpp.filterMap (fun '(c, d) => if Package.eq_dec d p then Some c else None) pi.

  Lemma mem_children : forall pi p q,
      PackageSet.In q (children pi p) <-> ParentRel.In (q, p) pi.
  Proof.
    intros pi p q; unfold children; rewrite SOpp.mem_filterMap.
    split.
    - intros [[q' d] [He Hc]]; cbn beta iota in Hc.
      destruct (Package.eq_dec d p); [mem_destruct; exact He | discriminate].
    - intro H; exists (q, p); split; [exact H | cbn beta iota].
      apply dec_refl.
  Qed.

  Definition pubChildren (pub : PublicDependencyRel.t) (pi : ParentRel.t) (p : Package.t)
      : PackageSet.t :=
    SOpp.filterMap (fun '(c, d) =>
        if Package.eq_dec d p
        then if PublicDependencyRel.mem (p, fst c) pub then Some c else None
        else None)
      pi.

  Lemma mem_pubChildren : forall pub pi p n v,
      PackageSet.In (n, v) (pubChildren pub pi p) <->
      ParentRel.In ((n, v), p) pi /\ PublicDependencyRel.In (p, n) pub.
  Proof.
    intros pub pi p n v; unfold pubChildren; rewrite SOpp.mem_filterMap.
    split.
    - intros [[q' d] [He Hc]]; cbn beta iota in Hc.
      destruct (Package.eq_dec d p) as [-> |]; [| discriminate].
      destruct (PublicDependencyRel.mem (p, fst q') pub) eqn:Hm; [| discriminate].
      mem_destruct; split; [exact He | apply PublicDependencyRel.mem_spec; exact Hm].
    - intros [He Hm]; exists ((n, v), p); split;
        [exact He | cbn beta iota; cbn [fst]].
      apply PublicDependencyRel.mem_spec in Hm; rewrite dec_refl, Hm; reflexivity.
  Qed.

  Definition subBase (pi : ParentRel.t) (q : Package.t) : PackageSet.t :=
    PackageSet.add q (children pi q).

  Lemma mem_subBase : forall pi q p,
      PackageSet.In p (subBase pi q) <-> p = q \/ ParentRel.In (p, q) pi.
  Proof.
    intros pi q p; unfold subBase.
    rewrite SOppp.add_in, mem_children; reflexivity.
  Qed.

  Definition subStep (pub : PublicDependencyRel.t) (pi : ParentRel.t) (acc : PackageSet.t)
      : PackageSet.t :=
    PackageSet.union acc (SOppp.unionMap (pubChildren pub pi) acc).

  Lemma mem_subStep : forall pub pi acc n v,
      PackageSet.In (n, v) (subStep pub pi acc) <->
      PackageSet.In (n, v) acc \/
      (exists q, PackageSet.In q acc /\ ParentRel.In ((n, v), q) pi /\
         PublicDependencyRel.In (q, n) pub).
  Proof.
    intros pub pi acc n v; unfold subStep.
    rewrite PackageSet.union_spec, SOppp.mem_unionMap.
    apply or_iff_compat_l; split.
    - intros [q [Hq Hc]]; apply mem_pubChildren in Hc.
      exists q; split; [exact Hq | exact Hc].
    - intros [q [Hq [He Hm]]]; exists q; split; [exact Hq |].
      apply mem_pubChildren; split; [exact He | exact Hm].
  Qed.

  Lemma subStep_incl : forall pub pi acc,
      PackageSet.Subset acc (subStep pub pi acc).
  Proof.
    intros pub pi acc [n v] Hc; apply mem_subStep; left; exact Hc.
  Qed.

  (* Saturation by a fixed number of rounds rather than well-founded
     recursion: the completeness witness has to test membership of the least
     set InSub describes, and every witness in this development computes. *)
  Fixpoint subIter (pub : PublicDependencyRel.t) (pi : ParentRel.t) (fuel : nat)
      (acc : PackageSet.t) : PackageSet.t :=
    match fuel with
    | O => acc
    | S k => subIter pub pi k (subStep pub pi acc)
    end.

  Lemma subIter_incl : forall pub pi fuel acc,
      PackageSet.Subset acc (subIter pub pi fuel acc).
  Proof.
    intros pub pi fuel; induction fuel as [| k IH]; intros acc c Hc.
    - exact Hc.
    - apply IH, subStep_incl; exact Hc.
  Qed.

  Lemma subIter_fix : forall pub pi fuel acc,
      subStep pub pi acc = acc -> subIter pub pi fuel acc = acc.
  Proof.
    intros pub pi fuel; induction fuel as [| k IH]; intros acc H;
      [reflexivity | simpl; rewrite H; apply IH; exact H].
  Qed.

  Lemma subIter_sound : forall pub pi (P : Package.t -> Prop),
      (forall (q : Package.t) (n : N.t) (v : V.t),
         P q -> ParentRel.In ((n, v), q) pi -> PublicDependencyRel.In (q, n) pub ->
         P (n, v)) ->
      forall fuel acc,
        (forall q, PackageSet.In q acc -> P q) ->
        forall q, PackageSet.In q (subIter pub pi fuel acc) -> P q.
  Proof.
    intros pub pi P Hstep fuel; induction fuel as [| k IH];
      intros acc Hacc q Hc.
    - exact (Hacc q Hc).
    - apply (IH (subStep pub pi acc)); [| exact Hc].
      intros [m u] Hc'; apply mem_subStep in Hc'.
      destruct Hc' as [Hc' | [p [Hp [He Hm]]]]; [exact (Hacc _ Hc') |].
      exact (Hstep p m u (Hacc p Hp) He Hm).
  Qed.

  (* The saturation never leaves q and the tails of pi, so that set's
     cardinal bounds how many rounds can each add an element. *)
  Definition subUniverse (pi : ParentRel.t) (q : Package.t) : PackageSet.t :=
    PackageSet.add q (SOpp.map fst pi).

  Lemma mem_subUniverse_tail : forall pi q p' p,
      ParentRel.In (p', p) pi -> PackageSet.In p' (subUniverse pi q).
  Proof.
    intros pi q p' p H; unfold subUniverse; apply SOppp.add_in; right.
    apply SOpp.mem_map; exists (p', p); split; [exact H | reflexivity].
  Qed.

  Lemma subBase_universe : forall pi q,
      PackageSet.Subset (subBase pi q) (subUniverse pi q).
  Proof.
    intros pi q c Hc; apply mem_subBase in Hc.
    destruct Hc as [-> | He];
      [apply SOppp.add_in; left; reflexivity
      | exact (mem_subUniverse_tail pi q c q He)].
  Qed.

  Lemma subStep_universe : forall pub pi q acc,
      PackageSet.Subset acc (subUniverse pi q) ->
      PackageSet.Subset (subStep pub pi acc) (subUniverse pi q).
  Proof.
    intros pub pi q acc Hacc [n v] Hc; apply mem_subStep in Hc.
    destruct Hc as [Hc | [p [_ [He _]]]];
      [exact (Hacc _ Hc) | exact (mem_subUniverse_tail pi q (n, v) p He)].
  Qed.

  Lemma subIter_universe : forall pub pi q fuel acc,
      PackageSet.Subset acc (subUniverse pi q) ->
      PackageSet.Subset (subIter pub pi fuel acc) (subUniverse pi q).
  Proof.
    intros pub pi q fuel; induction fuel as [| k IH]; intros acc Hacc.
    - exact Hacc.
    - apply IH, subStep_universe; exact Hacc.
  Qed.

  Module PackageSetProperties := MSetProperties.WPropertiesOn Package PackageSet.

  Lemma subIter_grow : forall pub pi fuel acc,
      subStep pub pi (subIter pub pi fuel acc) = subIter pub pi fuel acc \/
      PackageSet.cardinal acc + fuel <=
        PackageSet.cardinal (subIter pub pi fuel acc).
  Proof.
    intros pub pi fuel; induction fuel as [| k IH]; intro acc.
    - right; simpl; lia.
    - destruct (PackageSet.is_empty (PackageSet.diff (subStep pub pi acc) acc)) eqn:He.
      + assert (Hfix : subStep pub pi acc = acc).
        { apply PackageSet.ext; intro x; split; [| apply subStep_incl].
          intro Hx; destruct (PackageSet.mem x acc) eqn:Hm;
            [apply PackageSet.mem_spec; exact Hm | exfalso].
          rewrite PackageSet.is_empty_spec in He.
          apply (He x), PackageSet.diff_spec; split; [exact Hx |].
          intro Hc; rewrite <- PackageSet.mem_spec in Hc; congruence. }
        left; simpl; rewrite Hfix, (subIter_fix pub pi k acc Hfix); exact Hfix.
      + destruct (PackageSet.choose_nonempty _ He) as [x Hx].
        apply PackageSet.diff_spec in Hx; destruct Hx as [Hx1 Hx2].
        pose proof (PackageSetProperties.subset_cardinal_lt
                      (subStep_incl pub pi acc) Hx1 Hx2) as Hlt.
        simpl; destruct (IH (subStep pub pi acc)) as [E | Hc];
          [left; exact E | right; lia].
  Qed.

  Definition sub (pub : PublicDependencyRel.t) (pi : ParentRel.t) (q : Package.t) : PackageSet.t :=
    subIter pub pi (PackageSet.cardinal (subUniverse pi q)) (subBase pi q).

  Lemma sub_fix : forall pub pi q, subStep pub pi (sub pub pi q) = sub pub pi q.
  Proof.
    intros pub pi q; unfold sub.
    destruct (subIter_grow pub pi (PackageSet.cardinal (subUniverse pi q))
                (subBase pi q)) as [E | Hc]; [exact E | exfalso].
    assert (Hle : PackageSet.cardinal
                    (subIter pub pi (PackageSet.cardinal (subUniverse pi q))
                       (subBase pi q)) <=
                  PackageSet.cardinal (subUniverse pi q))
      by (apply PackageSetProperties.subset_cardinal, subIter_universe,
            subBase_universe).
    assert (Hpos : 1 <= PackageSet.cardinal (subBase pi q)).
    { destruct (PackageSet.cardinal (subBase pi q)) eqn:Hcb; [| lia].
      exfalso.
      assert (PackageSet.Empty (subBase pi q)) as Hemp
        by (apply PackageSetProperties.cardinal_inv_1; exact Hcb).
      apply (Hemp q), mem_subBase; left; reflexivity. }
    lia.
  Qed.

  Lemma mem_sub : forall pub pi q p,
      PackageSet.In p (sub pub pi q) <-> InSub pub pi q p.
  Proof.
    intros pub pi q p; split.
    - unfold sub; apply subIter_sound.
      + intros p' m u Hp He Hm.
        exact (PublicPropagation pub pi q p' m u Hp He Hm).
      + intros [n v] Hc'; apply mem_subBase in Hc'.
        destruct Hc' as [-> | He];
          [apply InSubSelf | exact (InSubChild pub pi q n v He)].
    - intro H; induction H as [| n v He | p' m u H IH He Hm].
      + unfold sub; apply subIter_incl, mem_subBase; left; reflexivity.
      + unfold sub; apply subIter_incl, mem_subBase; right; exact He.
      + assert (Hin : PackageSet.In (m, u) (subStep pub pi (sub pub pi q))).
        { apply mem_subStep; right.
          exists p'; split; [exact IH | split; [exact He | exact Hm]]. }
        rewrite sub_fix in Hin; exact Hin.
  Qed.

  Module Reduction.
    Module PackageEqb := UOTEqb Package.

    Definition privb (D : Source.DependencyRel.t) (pub : PublicDependencyRel.t) (p : Package.t) : bool :=
      Source.DependencyRel.exists_ (fun '(q, (n, _)) =>
          andb (PackageEqb.eqb q p) (negb (PublicDependencyRel.mem (p, n) pub)))
        D.

    Lemma privb_iff : forall D pub p, privb D pub p = true <-> Priv D pub p.
    Proof.
      intros D pub p; unfold privb, Priv.
      rewrite Source.DependencyRel.exists_spec'.
      split.
      - intros [[q [n vs]] [He Hb]]; cbn beta iota in Hb.
        apply Bool.andb_true_iff in Hb; destruct Hb as [H1 H2].
        apply PackageEqb.eqb_true_iff in H1 as ->.
        exists n, vs; split; [exact He |].
        apply Bool.negb_true_iff in H2.
        intro Hin; apply PublicDependencyRel.mem_spec in Hin; congruence.
      - intros [n [vs [He Hn]]]; exists (p, (n, vs)); split; [exact He |].
        cbn beta iota; apply Bool.andb_true_iff; split;
          [apply PackageEqb.eqb_refl |].
        apply Bool.negb_true_iff, Bool.not_true_iff_false.
        intro Hm; apply Hn, PublicDependencyRel.mem_spec; exact Hm.
    Qed.

    Definition Carried (pub : PublicDependencyRel.t) (q : Package.t) (p : Package.t) (m : N.t)
        : Prop :=
      PublicDependencyRel.In (p, m) pub \/ p = q.

    Definition carriedb (pub : PublicDependencyRel.t) (q : Package.t) (p : Package.t) (m : N.t)
        : bool :=
      orb (PublicDependencyRel.mem (p, m) pub) (PackageEqb.eqb p q).

    Lemma carriedb_iff : forall pub q p m,
        carriedb pub q p m = true <-> Carried pub q p m.
    Proof.
      intros pub q p m; unfold carriedb, Carried.
      rewrite Bool.orb_true_iff, PublicDependencyRel.mem_spec, PackageEqb.eqb_true_iff;
        reflexivity.
    Qed.

    Definition isOriginb (D : Source.DependencyRel.t) (pub : PublicDependencyRel.t) (r : Package.t)
        (S : PackageSet.t) (q : Package.t) : bool :=
      orb (PackageEqb.eqb q r) (andb (PackageSet.mem q S) (privb D pub q)).

    Lemma isOriginb_iff : forall D pub r S q,
        isOriginb D pub r S q = true <-> IsOrigin D pub r S q.
    Proof.
      intros D pub r S q; unfold isOriginb, IsOrigin.
      rewrite Bool.orb_true_iff, Bool.andb_true_iff, PackageEqb.eqb_true_iff,
        PackageSet.mem_spec, privb_iff; reflexivity.
    Qed.

    Definition origins (R : PackageSet.t) (D : Source.DependencyRel.t)
        (pub : PublicDependencyRel.t) (r : Package.t) : PackageSet.t :=
      PackageSet.add r (PackageSet.filter (privb D pub) R).

    Lemma mem_origins : forall R D pub r q,
        PackageSet.In q (origins R D pub r) <->
        q = r \/ (PackageSet.In q R /\ Priv D pub q).
    Proof.
      intros R D pub r q; unfold origins.
      rewrite SOppp.add_in, PackageSet.filter_spec', privb_iff; reflexivity.
    Qed.

    Module OccurrenceName := PairUOT N Package.
    Module IntermediateNameTail := TripleUOT V N Package.
    Module IntermediateName := PairUOT N IntermediateNameTail.
    Module AgreementName := TripleUOT N V N.
    Module OccurrenceNameFacts := UOTCompareFacts OccurrenceName.
    Module IntermediateNameFacts := UOTCompareFacts IntermediateName.
    Module AgreementNameFacts := UOTCompareFacts AgreementName.
    #[local] Hint Rewrite OccurrenceNameFacts.compare_eq_iff IntermediateNameFacts.compare_eq_iff
      AgreementNameFacts.compare_eq_iff : cmp_vis.
    #[local] Hint Extern 1 => cmp_by OccurrenceNameFacts.compare_antisym : cmp_vis.
    #[local] Hint Extern 1 => cmp_by IntermediateNameFacts.compare_antisym : cmp_vis.
    #[local] Hint Extern 1 => cmp_by AgreementNameFacts.compare_antisym : cmp_vis.
    #[local] Hint Extern 1 => cmp_by OccurrenceNameFacts.compare_lt_trans : cmp_vis.
    #[local] Hint Extern 1 => cmp_by IntermediateNameFacts.compare_lt_trans : cmp_vis.
    #[local] Hint Extern 1 => cmp_by AgreementNameFacts.compare_lt_trans : cmp_vis.

    Module Name.
      Inductive name : Type :=
      | Occurrence (n : N.t) (q : Package.t)
      | Intermediate (n : N.t) (v : V.t) (m : N.t) (q : Package.t)
      | Agreement (n : N.t) (v : V.t) (m : N.t).
      Definition t := name.

      Definition rank (x : t) : nat :=
        match x with
        | Occurrence _ _ => 0
        | Intermediate _ _ _ _ => 1
        | Agreement _ _ _ => 2
        end.

      Definition compare (x y : t) : comparison :=
        match Nat.compare (rank x) (rank y) with
        | Eq =>
            match x, y with
            | Occurrence n1 q1, Occurrence n2 q2 =>
                OccurrenceName.compare (n1, q1) (n2, q2)
            | Intermediate n1 v1 m1 q1, Intermediate n2 v2 m2 q2 =>
                IntermediateName.compare (n1, (v1, (m1, q1))) (n2, (v2, (m2, q2)))
            | Agreement n1 v1 m1, Agreement n2 v2 m2 =>
                AgreementName.compare (n1, (v1, m1)) (n2, (v2, m2))
            | _, _ => Eq
            end
        | c => c
        end.

      Lemma compare_eq_iff : forall x y, compare x y = Eq <-> x = y.
      Proof. cmp_eq_iff cmp_vis. Qed.

      Lemma compare_antisym : forall x y, compare y x = CompOpp (compare x y).
      Proof. cmp_antisym cmp_vis. Qed.

      Lemma compare_lt_trans : forall x y z,
          compare x y = Lt -> compare y z = Lt -> compare x z = Lt.
      Proof. cmp_lt_trans cmp_vis. Qed.
    End Name.

    Module NameOT := UOTFromCompare Name.
    Module Reduced := Core NameOT V.

    Module SOvv := SetOps V V VSet Reduced.VSet.
    (* Module application is generative, so the core's version sets are a
       fresh type even though the versions in them are the same. *)
    Definition embedVS (vs : VSet.t) : Reduced.VSet.t := SOvv.map (fun v => v) vs.

    Lemma mem_embedVS : forall vs v, Reduced.VSet.In v (embedVS vs) <-> VSet.In v vs.
    Proof.
      intros vs v; unfold embedVS; rewrite SOvv.mem_map.
      split; [intros [u [Hu ->]]; exact Hu |].
      intro H; exists v; split; [exact H | reflexivity].
    Qed.

    Definition embedRoot (r : Package.t) : Reduced.Package.t :=
      (Name.Occurrence (fst r) r, snd r).

    Module SOptp := SetOps Package Reduced.Package PackageSet Reduced.PackageSet.
    Definition reduceRealOccurrence (R : PackageSet.t) (origins : PackageSet.t)
        : Reduced.PackageSet.t :=
      SOptp.unionMap (fun '(n, v) =>
          SOptp.map (fun q => (Name.Occurrence n q, v)) origins)
        R.

    Module SOdtp := SetOps Source.DependencyElt Reduced.Package Source.DependencyRel Reduced.PackageSet.
    Module SOvtp := SetOps V Reduced.Package VSet Reduced.PackageSet.
    Definition reduceRealIntermediate (D : Source.DependencyRel.t) (origins : PackageSet.t)
        : Reduced.PackageSet.t :=
      SOdtp.unionMap (fun '((n, v), (m, vs)) =>
          SOptp.unionMap (fun q =>
              SOvtp.map (fun u => (Name.Intermediate n v m q, u)) vs)
            origins)
        D.

    Definition reduceRealAgreement (D : Source.DependencyRel.t) : Reduced.PackageSet.t :=
      SOdtp.unionMap (fun '((n, v), (m, vs)) =>
          SOvtp.map (fun u => (Name.Agreement n v m, u)) vs)
        D.

    Definition reduceReal (R : PackageSet.t) (D : Source.DependencyRel.t) (pub : PublicDependencyRel.t)
        (r : Package.t) : Reduced.PackageSet.t :=
      Reduced.PackageSet.union (reduceRealOccurrence R (origins R D pub r))
        (Reduced.PackageSet.union
           (reduceRealIntermediate D (origins R D pub r))
           (reduceRealAgreement D)).

    Module SOptd := SetOps Package Reduced.DependencyElt PackageSet Reduced.DependencyRel.
    Definition reduceDepsSelf (R : PackageSet.t) (D : Source.DependencyRel.t) (pub : PublicDependencyRel.t)
        (origins : PackageSet.t) : Reduced.DependencyRel.t :=
      SOptd.unionMap (fun '(n, v) =>
          SOptd.filterMap (fun q =>
              if andb (privb D pub (n, v)) (negb (PackageEqb.eqb q (n, v)))
              then Some ((Name.Occurrence n q, v),
                         (Name.Occurrence n (n, v), Reduced.VSet.singleton v))
              else None)
            origins)
        R.

    Module SOdtd := SetOps Source.DependencyElt Reduced.DependencyElt Source.DependencyRel Reduced.DependencyRel.
    Definition reduceDepsOccToInt (D : Source.DependencyRel.t) (pub : PublicDependencyRel.t)
        (origins : PackageSet.t) : Reduced.DependencyRel.t :=
      SOdtd.unionMap (fun '((n, v), (m, vs)) =>
          SOptd.filterMap (fun q =>
              if carriedb pub q (n, v) m
              then Some ((Name.Occurrence n q, v),
                         (Name.Intermediate n v m q, embedVS vs))
              else None)
            origins)
        D.

    Module SOvtd := SetOps V Reduced.DependencyElt VSet Reduced.DependencyRel.
    Definition reduceDepsIntToOcc (D : Source.DependencyRel.t) (pub : PublicDependencyRel.t)
        (origins : PackageSet.t) : Reduced.DependencyRel.t :=
      SOdtd.unionMap (fun '((n, v), (m, vs)) =>
          SOptd.unionMap (fun q =>
              if carriedb pub q (n, v) m
              then SOvtd.map (fun u =>
                       ((Name.Intermediate n v m q, u),
                        (Name.Occurrence m q, Reduced.VSet.singleton u)))
                     vs
              else Reduced.DependencyRel.empty)
            origins)
        D.

    Definition reduceDepsIntToAgr (D : Source.DependencyRel.t) (pub : PublicDependencyRel.t)
        (origins : PackageSet.t) : Reduced.DependencyRel.t :=
      SOdtd.unionMap (fun '((n, v), (m, vs)) =>
          SOptd.unionMap (fun q =>
              if carriedb pub q (n, v) m
              then SOvtd.map (fun u =>
                       ((Name.Intermediate n v m q, u),
                        (Name.Agreement n v m, Reduced.VSet.singleton u)))
                     vs
              else Reduced.DependencyRel.empty)
            origins)
        D.

    Definition reduceDeps (R : PackageSet.t) (D : Source.DependencyRel.t) (pub : PublicDependencyRel.t)
        (r : Package.t) : Reduced.DependencyRel.t :=
      Reduced.DependencyRel.union (reduceDepsSelf R D pub (origins R D pub r))
        (Reduced.DependencyRel.union
           (reduceDepsOccToInt D pub (origins R D pub r))
           (Reduced.DependencyRel.union
              (reduceDepsIntToOcc D pub (origins R D pub r))
              (reduceDepsIntToAgr D pub (origins R D pub r)))).

    Lemma mem_reduceRealOccurrence : forall R origins p,
        Reduced.PackageSet.In p (reduceRealOccurrence R origins) <->
        exists n v q, PackageSet.In (n, v) R /\ PackageSet.In q origins /\
          p = (Name.Occurrence n q, v).
    Proof.
      intros R origins p; unfold reduceRealOccurrence.
      rewrite SOptp.mem_unionMap.
      split.
      - intros [[n v] [HR Hh]]; cbn beta iota in Hh.
        apply SOptp.mem_map in Hh; destruct Hh as [q [Hq ->]].
        exists n, v, q; auto.
      - intros (n & v & q & HR & Hq & ->).
        exists (n, v); split; [exact HR | cbn beta iota].
        apply SOptp.mem_map; exists q; auto.
    Qed.

    Lemma mem_reduceRealIntermediate : forall D origins p,
        Reduced.PackageSet.In p (reduceRealIntermediate D origins) <->
        exists n v m vs q u,
          Source.DependencyRel.In ((n, v), (m, vs)) D /\ PackageSet.In q origins /\
          VSet.In u vs /\ p = (Name.Intermediate n v m q, u).
    Proof.
      intros D origins p; unfold reduceRealIntermediate.
      rewrite SOdtp.mem_unionMap.
      split.
      - intros [[[n v] [m vs]] [HD Hh]]; cbn beta iota in Hh.
        apply SOptp.mem_unionMap in Hh; destruct Hh as [q [Hq Hh]].
        apply SOvtp.mem_map in Hh; destruct Hh as [u [Hu ->]].
        exists n, v, m, vs, q, u; auto.
      - intros (n & v & m & vs & q & u & HD & Hq & Hu & ->).
        exists ((n, v), (m, vs)); split; [exact HD | cbn beta iota].
        apply SOptp.mem_unionMap; exists q; split; [exact Hq |].
        apply SOvtp.mem_map; exists u; auto.
    Qed.

    Lemma mem_reduceRealAgreement : forall D p,
        Reduced.PackageSet.In p (reduceRealAgreement D) <->
        exists n v m vs u,
          Source.DependencyRel.In ((n, v), (m, vs)) D /\ VSet.In u vs /\
          p = (Name.Agreement n v m, u).
    Proof.
      intros D p; unfold reduceRealAgreement; rewrite SOdtp.mem_unionMap.
      split.
      - intros [[[n v] [m vs]] [HD Hh]]; cbn beta iota in Hh.
        apply SOvtp.mem_map in Hh; destruct Hh as [u [Hu ->]].
        exists n, v, m, vs, u; auto.
      - intros (n & v & m & vs & u & HD & Hu & ->).
        exists ((n, v), (m, vs)); split; [exact HD | cbn beta iota].
        apply SOvtp.mem_map; exists u; auto.
    Qed.

    (* The name of an element fixes which of the three parts it is from, so
       inversion discards the other two. *)
    Inductive RealSpec (R : PackageSet.t) (D : Source.DependencyRel.t) (pub : PublicDependencyRel.t)
        (r : Package.t) : Reduced.Package.t -> Prop :=
    | RealOccurrence : forall n v q,
        PackageSet.In (n, v) R -> PackageSet.In q (origins R D pub r) ->
        RealSpec R D pub r (Name.Occurrence n q, v)
    | RealIntermediate : forall n v m vs q u,
        Source.DependencyRel.In ((n, v), (m, vs)) D ->
        PackageSet.In q (origins R D pub r) -> VSet.In u vs ->
        RealSpec R D pub r (Name.Intermediate n v m q, u)
    | RealAgreement : forall n v m vs u,
        Source.DependencyRel.In ((n, v), (m, vs)) D -> VSet.In u vs ->
        RealSpec R D pub r (Name.Agreement n v m, u).

    Lemma mem_reduceReal : forall R D pub r p,
        Reduced.PackageSet.In p (reduceReal R D pub r) <-> RealSpec R D pub r p.
    Proof.
      intros R D pub r p; unfold reduceReal.
      rewrite !Reduced.PackageSet.union_spec, mem_reduceRealOccurrence,
        mem_reduceRealIntermediate, mem_reduceRealAgreement.
      split.
      - intros [H | [H | H]]; mem_destruct; econstructor; eassumption.
      - destruct 1 as [n v q | n v m vs q u | n v m vs u].
        + left; exists n, v, q; auto.
        + right; left; exists n, v, m, vs, q, u; auto.
        + right; right; exists n, v, m, vs, u; auto.
    Qed.

    Lemma mem_reduceDepsSelf : forall R D pub origins y,
        Reduced.DependencyRel.In y (reduceDepsSelf R D pub origins) <->
        exists n v q, PackageSet.In (n, v) R /\ PackageSet.In q origins /\
          Priv D pub (n, v) /\ q <> (n, v) /\
          y = ((Name.Occurrence n q, v),
               (Name.Occurrence n (n, v), Reduced.VSet.singleton v)).
    Proof.
      intros R D pub origins y; unfold reduceDepsSelf.
      rewrite SOptd.mem_unionMap.
      split.
      - intros [[n v] [HR Hh]]; cbn beta iota in Hh.
        apply SOptd.mem_filterMap_if in Hh; destruct Hh as [q [Hq [Hb ->]]].
        cbn beta in Hb; rewrite Bool.andb_true_iff, Bool.negb_true_iff,
          PackageEqb.eqb_false_iff, privb_iff in Hb.
        destruct Hb; exists n, v, q; auto.
      - intros (n & v & q & HR & Hq & Hpriv & Hne & ->).
        exists (n, v); split; [exact HR | cbn beta iota].
        apply SOptd.mem_filterMap_if; exists q; cbn beta.
        rewrite Bool.andb_true_iff, Bool.negb_true_iff, PackageEqb.eqb_false_iff,
          privb_iff; auto.
    Qed.

    Lemma mem_reduceDepsOccToInt : forall D pub origins y,
        Reduced.DependencyRel.In y (reduceDepsOccToInt D pub origins) <->
        exists n v m vs q,
          Source.DependencyRel.In ((n, v), (m, vs)) D /\ PackageSet.In q origins /\
          Carried pub q (n, v) m /\
          y = ((Name.Occurrence n q, v),
               (Name.Intermediate n v m q, embedVS vs)).
    Proof.
      intros D pub origins y; unfold reduceDepsOccToInt.
      rewrite SOdtd.mem_unionMap.
      split.
      - intros [[[n v] [m vs]] [HD Hh]]; cbn beta iota in Hh.
        apply SOptd.mem_filterMap_if in Hh; destruct Hh as [q [Hq [Hb ->]]].
        apply carriedb_iff in Hb; exists n, v, m, vs, q; auto.
      - intros (n & v & m & vs & q & HD & Hq & Hc & ->).
        exists ((n, v), (m, vs)); split; [exact HD | cbn beta iota].
        apply SOptd.mem_filterMap_if; exists q; cbn beta.
        rewrite carriedb_iff; auto.
    Qed.

    Lemma mem_reduceDepsIntToOcc : forall D pub origins y,
        Reduced.DependencyRel.In y (reduceDepsIntToOcc D pub origins) <->
        exists n v m vs q u,
          Source.DependencyRel.In ((n, v), (m, vs)) D /\ PackageSet.In q origins /\
          Carried pub q (n, v) m /\ VSet.In u vs /\
          y = ((Name.Intermediate n v m q, u),
               (Name.Occurrence m q, Reduced.VSet.singleton u)).
    Proof.
      intros D pub origins y; unfold reduceDepsIntToOcc.
      rewrite SOdtd.mem_unionMap.
      split.
      - intros [[[n v] [m vs]] [HD Hh]]; cbn beta iota in Hh.
        apply SOptd.mem_unionMap_if in Hh; destruct Hh as [q [Hq [Hb Hh]]].
        apply SOvtd.mem_map in Hh; destruct Hh as [u [Hu ->]].
        apply carriedb_iff in Hb; exists n, v, m, vs, q, u; auto.
      - intros (n & v & m & vs & q & u & HD & Hq & Hc & Hu & ->).
        exists ((n, v), (m, vs)); split; [exact HD | cbn beta iota].
        apply SOptd.mem_unionMap_if; exists q; cbn beta.
        rewrite carriedb_iff, SOvtd.mem_map; eauto.
    Qed.

    Lemma mem_reduceDepsIntToAgr : forall D pub origins y,
        Reduced.DependencyRel.In y (reduceDepsIntToAgr D pub origins) <->
        exists n v m vs q u,
          Source.DependencyRel.In ((n, v), (m, vs)) D /\ PackageSet.In q origins /\
          Carried pub q (n, v) m /\ VSet.In u vs /\
          y = ((Name.Intermediate n v m q, u),
               (Name.Agreement n v m, Reduced.VSet.singleton u)).
    Proof.
      intros D pub origins y; unfold reduceDepsIntToAgr.
      rewrite SOdtd.mem_unionMap.
      split.
      - intros [[[n v] [m vs]] [HD Hh]]; cbn beta iota in Hh.
        apply SOptd.mem_unionMap_if in Hh; destruct Hh as [q [Hq [Hb Hh]]].
        apply SOvtd.mem_map in Hh; destruct Hh as [u [Hu ->]].
        apply carriedb_iff in Hb; exists n, v, m, vs, q, u; auto.
      - intros (n & v & m & vs & q & u & HD & Hq & Hc & Hu & ->).
        exists ((n, v), (m, vs)); split; [exact HD | cbn beta iota].
        apply SOptd.mem_unionMap_if; exists q; cbn beta.
        rewrite carriedb_iff, SOvtd.mem_map; eauto.
    Qed.

    (* An edge's depender's name and dependee name together fix which of
       the four parts it is from, so inversion discards the others. *)
    Inductive DepsSpec (R : PackageSet.t) (D : Source.DependencyRel.t) (pub : PublicDependencyRel.t)
        (r : Package.t) : Reduced.DependencyElt.t -> Prop :=
    | DepsSelf : forall n v q,
        PackageSet.In (n, v) R -> PackageSet.In q (origins R D pub r) ->
        Priv D pub (n, v) -> q <> (n, v) ->
        DepsSpec R D pub r
          ((Name.Occurrence n q, v),
           (Name.Occurrence n (n, v), Reduced.VSet.singleton v))
    | DepsOccToInt : forall n v m vs q,
        Source.DependencyRel.In ((n, v), (m, vs)) D ->
        PackageSet.In q (origins R D pub r) -> Carried pub q (n, v) m ->
        DepsSpec R D pub r
          ((Name.Occurrence n q, v), (Name.Intermediate n v m q, embedVS vs))
    | DepsIntToOcc : forall n v m vs q u,
        Source.DependencyRel.In ((n, v), (m, vs)) D ->
        PackageSet.In q (origins R D pub r) -> Carried pub q (n, v) m ->
        VSet.In u vs ->
        DepsSpec R D pub r
          ((Name.Intermediate n v m q, u),
           (Name.Occurrence m q, Reduced.VSet.singleton u))
    | DepsIntToAgr : forall n v m vs q u,
        Source.DependencyRel.In ((n, v), (m, vs)) D ->
        PackageSet.In q (origins R D pub r) -> Carried pub q (n, v) m ->
        VSet.In u vs ->
        DepsSpec R D pub r
          ((Name.Intermediate n v m q, u),
           (Name.Agreement n v m, Reduced.VSet.singleton u)).

    Lemma mem_reduceDeps : forall R D pub r y,
        Reduced.DependencyRel.In y (reduceDeps R D pub r) <-> DepsSpec R D pub r y.
    Proof.
      intros R D pub r y; unfold reduceDeps.
      rewrite !Reduced.DependencyRel.union_spec, mem_reduceDepsSelf, mem_reduceDepsOccToInt,
        mem_reduceDepsIntToOcc, mem_reduceDepsIntToAgr.
      split.
      - intros [H | [H | [H | H]]]; mem_destruct; econstructor; eassumption.
      - destruct 1 as [n v q | n v m vs q | n v m vs q u | n v m vs q u].
        + left; exists n, v, q; auto.
        + right; left; exists n, v, m, vs, q; auto.
        + right; right; left; exists n, v, m, vs, q, u; auto.
        + right; right; right; exists n, v, m, vs, q, u; auto.
    Qed.

    Lemma occurrence_mem_reduceReal : forall R D pub r n v q,
        Reduced.PackageSet.In (Name.Occurrence n q, v) (reduceReal R D pub r) ->
        PackageSet.In (n, v) R /\ PackageSet.In q (origins R D pub r).
    Proof.
      intros R D pub r n v q H; apply mem_reduceReal in H.
      inversion H; subst; auto.
    Qed.

    Lemma mem_reduceDeps_self : forall R D pub r n v q,
        PackageSet.In (n, v) R -> PackageSet.In q (origins R D pub r) ->
        Priv D pub (n, v) -> q <> (n, v) ->
        Reduced.DependencyRel.In ((Name.Occurrence n q, v),
                     (Name.Occurrence n (n, v), Reduced.VSet.singleton v))
          (reduceDeps R D pub r).
    Proof. intros; apply mem_reduceDeps; constructor; assumption. Qed.

    Lemma mem_reduceDeps_occ2int : forall R D pub r n v m vs q,
        Source.DependencyRel.In ((n, v), (m, vs)) D ->
        PackageSet.In q (origins R D pub r) -> Carried pub q (n, v) m ->
        Reduced.DependencyRel.In ((Name.Occurrence n q, v),
                     (Name.Intermediate n v m q, embedVS vs))
          (reduceDeps R D pub r).
    Proof. intros; apply mem_reduceDeps; constructor; assumption. Qed.

    Lemma mem_reduceDeps_int2occ : forall R D pub r n v m vs q u,
        Source.DependencyRel.In ((n, v), (m, vs)) D ->
        PackageSet.In q (origins R D pub r) -> Carried pub q (n, v) m ->
        VSet.In u vs ->
        Reduced.DependencyRel.In ((Name.Intermediate n v m q, u),
                     (Name.Occurrence m q, Reduced.VSet.singleton u))
          (reduceDeps R D pub r).
    Proof. intros; apply mem_reduceDeps; econstructor; eassumption. Qed.

    Lemma mem_reduceDeps_int2agr : forall R D pub r n v m vs q u,
        Source.DependencyRel.In ((n, v), (m, vs)) D ->
        PackageSet.In q (origins R D pub r) -> Carried pub q (n, v) m ->
        VSet.In u vs ->
        Reduced.DependencyRel.In ((Name.Intermediate n v m q, u),
                     (Name.Agreement n v m, Reduced.VSet.singleton u))
          (reduceDeps R D pub r).
    Proof. intros; apply mem_reduceDeps; econstructor; eassumption. Qed.

    Definition visibilityResolution (R : PackageSet.t) (D : Source.DependencyRel.t)
        (pub : PublicDependencyRel.t) (r : Package.t) (S : Reduced.PackageSet.t) : PackageSet.t :=
      SOppp.filterExists
        (fun '(n, v) q => Reduced.PackageSet.mem (Name.Occurrence n q, v) S)
        (origins R D pub r) R.

    Lemma mem_visibilityResolution : forall R D pub r S n v,
        PackageSet.In (n, v) (visibilityResolution R D pub r S) <->
        PackageSet.In (n, v) R /\
        (exists q, PackageSet.In q (origins R D pub r) /\
           Reduced.PackageSet.In (Name.Occurrence n q, v) S).
    Proof.
      intros R D pub r S n v; unfold visibilityResolution.
      rewrite SOppp.mem_filterExists.
      apply and_iff_compat_l; split;
        (intros [q [Hq Hm]]; exists q; split;
         [exact Hq | apply Reduced.PackageSet.mem_spec; exact Hm]).
    Qed.

    Lemma occurrence_mem_visibilityResolution : forall R D pub r S n v q,
        Reduced.PackageSet.Subset S (reduceReal R D pub r) ->
        Reduced.PackageSet.In (Name.Occurrence n q, v) S ->
        PackageSet.In (n, v) (visibilityResolution R D pub r S).
    Proof.
      intros R D pub r S n v q Hsub Hocc.
      destruct (occurrence_mem_reduceReal R D pub r n v q (Hsub _ Hocc))
        as [HR Hq].
      apply mem_visibilityResolution; split; [exact HR |].
      exists q; split; [exact Hq | exact Hocc].
    Qed.

    Definition parentGuardb (R : PackageSet.t) (D : Source.DependencyRel.t) (pub : PublicDependencyRel.t)
        (r : Package.t) (S : Reduced.PackageSet.t) (n : N.t) (v : V.t) (m : N.t) (u : V.t)
        : bool :=
      andb (Reduced.PackageSet.mem (Name.Agreement n v m, u) S)
        (PackageSet.mem (n, v) (visibilityResolution R D pub r S)).

    Lemma parentGuardb_iff : forall R D pub r S n v m u,
        parentGuardb R D pub r S n v m u = true <->
        Reduced.PackageSet.In (Name.Agreement n v m, u) S /\
        PackageSet.In (n, v) (visibilityResolution R D pub r S).
    Proof.
      intros R D pub r S n v m u; unfold parentGuardb.
      rewrite Bool.andb_true_iff, Reduced.PackageSet.mem_spec, PackageSet.mem_spec;
        reflexivity.
    Qed.

    Module SOdpp := Concurrent.Reduction.SOdpp.
    Module SOvpp := Concurrent.Reduction.SOvpp.
    Definition parents (R : PackageSet.t) (D : Source.DependencyRel.t) (pub : PublicDependencyRel.t)
        (r : Package.t) (S : Reduced.PackageSet.t) : ParentRel.t :=
      SOdpp.unionMap (fun '((n, v), (m, vs)) =>
          SOvpp.filterMap (fun u =>
              if parentGuardb R D pub r S n v m u
              then Some ((m, u), (n, v))
              else None)
            vs)
        D.

    Lemma mem_parents : forall R D pub r S m u n v,
        ParentRel.In ((m, u), (n, v)) (parents R D pub r S) <->
        exists vs, Source.DependencyRel.In ((n, v), (m, vs)) D /\ VSet.In u vs /\
          PackageSet.In (n, v) (visibilityResolution R D pub r S) /\
          Reduced.PackageSet.In (Name.Agreement n v m, u) S.
    Proof.
      intros R D pub r S m u n v; unfold parents; rewrite SOdpp.mem_unionMap.
      split.
      - intros [[[n' v'] [m' vs]] [HD Hh]]; cbn beta iota in Hh.
        apply SOvpp.mem_filterMap_if in Hh; destruct Hh as [u' [Hu [Hb E]]].
        injection E as <- <- <- <-.
        apply parentGuardb_iff in Hb; destruct Hb.
        exists vs; auto.
      - intros (vs & HD & Hu & Hnv & Hagr).
        exists ((n, v), (m, vs)); split; [exact HD | cbn beta iota].
        apply SOvpp.mem_filterMap_if; exists u; cbn beta.
        rewrite parentGuardb_iff; auto.
    Qed.

    Lemma occurrence_step : forall R D pub r S (n : N.t) (v : V.t) (m : N.t)
        (vs : VSet.t) (q : Package.t),
        Reduced.IsResolution (reduceReal R D pub r) (reduceDeps R D pub r)
          (embedRoot r) S ->
        Source.DependencyRel.In ((n, v), (m, vs)) D ->
        PackageSet.In q (origins R D pub r) ->
        Carried pub q (n, v) m ->
        Reduced.PackageSet.In (Name.Occurrence n q, v) S ->
        exists u, VSet.In u vs /\
          Reduced.PackageSet.In (Name.Intermediate n v m q, u) S /\
          Reduced.PackageSet.In (Name.Agreement n v m, u) S /\
          Reduced.PackageSet.In (Name.Occurrence m q, u) S.
    Proof.
      intros R D pub r S n v m vs q Hres HD Hq Hc Hocc.
      destruct Hres as [Hsub Hroot Hdc Huniq].
      destruct (Hdc _ Hocc _ _
                  (mem_reduceDeps_occ2int R D pub r n v m vs q HD Hq Hc))
        as [u [Hu HintS]].
      apply mem_embedVS in Hu.
      destruct (Hdc _ HintS _ _
                  (mem_reduceDeps_int2agr R D pub r n v m vs q u HD Hq Hc Hu))
        as [w1 [Hw1 HagrS]].
      apply SOvv.singleton_in in Hw1; subst w1.
      destruct (Hdc _ HintS _ _
                  (mem_reduceDeps_int2occ R D pub r n v m vs q u HD Hq Hc Hu))
        as [w2 [Hw2 HoccS]].
      apply SOvv.singleton_in in Hw2; subst w2.
      exists u; repeat split; assumption.
    Qed.

    Lemma occurrence_step_at : forall R D pub r S (n : N.t) (v : V.t)
        (m : N.t) (vs : VSet.t) (q : Package.t) (u : V.t),
        Reduced.IsResolution (reduceReal R D pub r) (reduceDeps R D pub r)
          (embedRoot r) S ->
        Source.DependencyRel.In ((n, v), (m, vs)) D ->
        PackageSet.In q (origins R D pub r) ->
        Carried pub q (n, v) m ->
        Reduced.PackageSet.In (Name.Occurrence n q, v) S ->
        Reduced.PackageSet.In (Name.Agreement n v m, u) S ->
        VSet.In u vs /\ Reduced.PackageSet.In (Name.Occurrence m q, u) S.
    Proof.
      intros R D pub r S n v m vs q u Hres HD Hq Hc Hocc Hagr.
      destruct (occurrence_step R D pub r S n v m vs q Hres HD Hq Hc Hocc)
        as [u' [Hu' [_ [Hagr' Hocc']]]].
      destruct Hres as [_ _ _ Huniq].
      assert (u' = u) as -> by exact (Huniq _ _ _ Hagr' Hagr).
      split; [exact Hu' | exact Hocc'].
    Qed.

    Lemma self_occurrence : forall R D pub r S (n : N.t) (v : V.t) (q : Package.t),
        Reduced.IsResolution (reduceReal R D pub r) (reduceDeps R D pub r)
          (embedRoot r) S ->
        PackageSet.In (n, v) R -> PackageSet.In q (origins R D pub r) ->
        Priv D pub (n, v) ->
        Reduced.PackageSet.In (Name.Occurrence n q, v) S ->
        Reduced.PackageSet.In (Name.Occurrence n (n, v), v) S.
    Proof.
      intros R D pub r S n v q Hres HR Hq Hpriv Hocc.
      destruct (Package.eq_dec q (n, v)) as [-> | NE]; [exact Hocc |].
      destruct Hres as [Hsub Hroot Hdc Huniq].
      destruct (Hdc _ Hocc _ _
                  (mem_reduceDeps_self R D pub r n v q HR Hq Hpriv NE))
        as [w [Hw HwS]].
      apply SOvv.singleton_in in Hw; subst w; exact HwS.
    Qed.

    Lemma base_occurrence : forall R D pub r S (n : N.t) (v : V.t),
        Reduced.IsResolution (reduceReal R D pub r) (reduceDeps R D pub r)
          (embedRoot r) S ->
        PackageSet.In (n, v) (visibilityResolution R D pub r S) ->
        exists q, PackageSet.In q (origins R D pub r) /\
          Reduced.PackageSet.In (Name.Occurrence n q, v) S /\
          (forall (m : N.t) (vs : VSet.t),
             Source.DependencyRel.In ((n, v), (m, vs)) D -> Carried pub q (n, v) m).
    Proof.
      intros R D pub r S n v Hres Hp.
      apply mem_visibilityResolution in Hp.
      destruct Hp as [HR [q0 [Hq Hocc]]].
      destruct (privb D pub (n, v)) eqn:Hpb.
      - apply privb_iff in Hpb.
        exists (n, v); split;
          [apply mem_origins; right; split; assumption |].
        split;
          [exact (self_occurrence R D pub r S n v q0 Hres HR Hq Hpb Hocc) |].
        intros m vs _; right; reflexivity.
      - exists q0; split; [exact Hq | split; [exact Hocc |]].
        intros m vs HD; left.
        apply (not_priv_pub D pub (n, v) m vs); [| exact HD].
        intro Hpr; apply privb_iff in Hpr; congruence.
    Qed.

    Lemma inSub_occurrence : forall R D pub r S (n : N.t) (v : V.t)
        (q : Package.t) (m : N.t) (u : V.t),
        Reduced.IsResolution (reduceReal R D pub r) (reduceDeps R D pub r)
          (embedRoot r) S ->
        PackageSet.In q (origins R D pub r) ->
        Reduced.PackageSet.In (Name.Occurrence n q, v) S ->
        (forall (o : N.t) (vs : VSet.t),
           Source.DependencyRel.In ((n, v), (o, vs)) D -> Carried pub q (n, v) o) ->
        InSub pub (parents R D pub r S) (n, v) (m, u) ->
        Reduced.PackageSet.In (Name.Occurrence m q, u) S.
    Proof.
      intros R D pub r S n v q m0 u0 Hres Hc0 Hocc Htr Hins.
      enough (H : forall p, InSub pub (parents R D pub r S) (n, v) p ->
                  Reduced.PackageSet.In (Name.Occurrence (fst p) q, snd p) S)
        by exact (H (m0, u0) Hins).
      clear m0 u0 Hins; intros p Hins.
      induction Hins as [| cn cv He | p' m u Hp IH He Hm].
      - exact Hocc.
      - apply mem_parents in He.
        destruct He as (vs2 & HD & _ & _ & Hagr).
        exact (proj2 (occurrence_step_at R D pub r S n v cn vs2 q cv Hres HD
                        Hc0 (Htr cn vs2 HD) Hocc Hagr)).
      - destruct p' as [pn pv].
        apply mem_parents in He.
        destruct He as (vs2 & HD & _ & _ & Hagr).
        exact (proj2 (occurrence_step_at R D pub r S pn pv m vs2 q u Hres HD
                        Hc0 (or_introl Hm) IH Hagr)).
    Qed.

    Theorem visibility_soundness :
      forall (R : PackageSet.t) (D : Source.DependencyRel.t) (pub : PublicDependencyRel.t) (r : Package.t)
             (S : Reduced.PackageSet.t),
        Reduced.IsResolution (reduceReal R D pub r) (reduceDeps R D pub r)
          (embedRoot r) S ->
        IsResolution R D pub r (visibilityResolution R D pub r S)
          (parents R D pub r S).
    Proof.
      intros R D pub r S Hres.
      pose proof Hres as Hres0.
      destruct Hres0 as [Hsub Hroot Hdc Huniq].
      constructor.
      - constructor.
        + intros [pn pv] Hp; apply mem_visibilityResolution in Hp.
          exact (proj1 Hp).
        + destruct r as [rn rv].
          exact (occurrence_mem_visibilityResolution R D pub (rn, rv) S rn rv
                   (rn, rv) Hsub Hroot).
        + intros [pn pv] Hp m vs HD.
          destruct (base_occurrence R D pub r S pn pv Hres Hp)
            as [c0 [Hc0 [Hocc Htr]]].
          destruct (occurrence_step R D pub r S pn pv m vs c0 Hres HD Hc0
                      (Htr m vs HD) Hocc) as [u [Hu [_ [Hagr Hcp]]]].
          exists u; split; [exact Hu | split].
          * exact (occurrence_mem_visibilityResolution R D pub r S m u c0
                     Hsub Hcp).
          * apply mem_parents.
            exists vs; repeat split; assumption.
        + intros m u u' [pn pv] H1 H2.
          apply mem_parents in H1, H2.
          destruct H1 as (vs & _ & _ & _ & Hagr).
          destruct H2 as (vs' & _ & _ & _ & Hagr').
          exact (Huniq _ _ _ Hagr Hagr').
        + intros n v v' _ _ Hne; exact Hne.
        + intros [m u] [n v] Hcp; apply mem_parents in Hcp.
          destruct Hcp as (vs & HD & Hu & Hnv & Hagr).
          split; [| exact Hnv].
          destruct (base_occurrence R D pub r S n v Hres Hnv)
            as [c0 [Hc0 [Hocc Htr]]].
          destruct (occurrence_step_at R D pub r S n v m vs c0 u Hres HD Hc0
                      (Htr m vs HD) Hocc Hagr) as [_ Hcp2].
          exact (occurrence_mem_visibilityResolution R D pub r S m u c0
                   Hsub Hcp2).
      - intros [pn pv] Hp n v v' Hv Hv'.
        destruct (base_occurrence R D pub r S pn pv Hres Hp)
          as [c0 [Hc0 [Hocc Htr]]].
        assert (H1 : Reduced.PackageSet.In (Name.Occurrence n c0, v) S)
          by exact (inSub_occurrence R D pub r S pn pv c0 n v Hres Hc0 Hocc
                      Htr Hv).
        assert (H2 : Reduced.PackageSet.In (Name.Occurrence n c0, v') S)
          by exact (inSub_occurrence R D pub r S pn pv c0 n v' Hres Hc0 Hocc
                      Htr Hv').
        exact (Huniq _ _ _ H1 H2).
    Qed.

    Definition edgeb (pi : ParentRel.t) (n : N.t) (v : V.t) (m : N.t)
        (u : V.t) : bool :=
      ParentRel.mem ((m, u), (n, v)) pi.

    Lemma edgeb_iff : forall pi n v m u,
        edgeb pi n v m u = true <-> ParentRel.In ((m, u), (n, v)) pi.
    Proof.
      intros pi n v m u; unfold edgeb.
      rewrite ParentRel.mem_spec; reflexivity.
    Qed.

    Definition coreResolutionOccurrence (D : Source.DependencyRel.t) (pub : PublicDependencyRel.t)
        (r : Package.t) (S : PackageSet.t) (pi : ParentRel.t) (origins : PackageSet.t)
        : Reduced.PackageSet.t :=
      SOptp.unionMap (fun '(n, v) =>
          SOptp.filterMap (fun q =>
              if andb (isOriginb D pub r S q)
                   (PackageSet.mem (n, v) (sub pub pi q))
              then Some (Name.Occurrence n q, v)
              else None)
            origins)
        S.

    Definition coreResolutionIntermediate (D : Source.DependencyRel.t) (pub : PublicDependencyRel.t)
        (r : Package.t) (S : PackageSet.t) (pi : ParentRel.t) (origins : PackageSet.t)
        : Reduced.PackageSet.t :=
      SOdtp.unionMap (fun '((n, v), (m, vs)) =>
          SOptp.unionMap (fun q =>
              if andb (isOriginb D pub r S q)
                   (andb (PackageSet.mem (n, v) (sub pub pi q))
                      (carriedb pub q (n, v) m))
              then SOvtp.filterMap (fun u =>
                       if edgeb pi n v m u
                       then Some (Name.Intermediate n v m q, u)
                       else None)
                     vs
              else Reduced.PackageSet.empty)
            origins)
        D.

    Definition coreResolutionAgreement (D : Source.DependencyRel.t) (S : PackageSet.t)
        (pi : ParentRel.t) : Reduced.PackageSet.t :=
      SOdtp.unionMap (fun '((n, v), (m, vs)) =>
          if PackageSet.mem (n, v) S
          then SOvtp.filterMap (fun u =>
                   if edgeb pi n v m u
                   then Some (Name.Agreement n v m, u)
                   else None)
                 vs
          else Reduced.PackageSet.empty)
        D.

    Definition coreResolution (R : PackageSet.t) (D : Source.DependencyRel.t) (pub : PublicDependencyRel.t)
        (r : Package.t) (S : PackageSet.t) (pi : ParentRel.t) : Reduced.PackageSet.t :=
      Reduced.PackageSet.union
        (coreResolutionOccurrence D pub r S pi (origins R D pub r))
        (Reduced.PackageSet.union
           (coreResolutionIntermediate D pub r S pi
              (origins R D pub r))
           (coreResolutionAgreement D S pi)).

    Lemma mem_coreResolutionOccurrence : forall D pub r S pi origins p,
        Reduced.PackageSet.In p (coreResolutionOccurrence D pub r S pi origins) <->
        exists n v q, PackageSet.In (n, v) S /\ PackageSet.In q origins /\
          IsOrigin D pub r S q /\ InSub pub pi q (n, v) /\
          p = (Name.Occurrence n q, v).
    Proof.
      intros D pub r S pi origins p; unfold coreResolutionOccurrence.
      rewrite SOptp.mem_unionMap.
      split.
      - intros [[n v] [HS Hh]]; cbn beta iota in Hh.
        apply SOptp.mem_filterMap_if in Hh; destruct Hh as [q [Hq [Hb ->]]].
        cbn beta in Hb; rewrite Bool.andb_true_iff, isOriginb_iff,
          PackageSet.mem_spec, mem_sub in Hb.
        destruct Hb; exists n, v, q; auto.
      - intros (n & v & q & HS & Hq & Ho & Hins & ->).
        exists (n, v); split; [exact HS | cbn beta iota].
        apply SOptp.mem_filterMap_if; exists q; cbn beta.
        rewrite Bool.andb_true_iff, isOriginb_iff, PackageSet.mem_spec, mem_sub;
          auto.
    Qed.

    Lemma mem_coreResolutionIntermediate : forall D pub r S pi origins p,
        Reduced.PackageSet.In p (coreResolutionIntermediate D pub r S pi origins) <->
        exists n v m vs q u,
          Source.DependencyRel.In ((n, v), (m, vs)) D /\ PackageSet.In q origins /\
          VSet.In u vs /\ IsOrigin D pub r S q /\ InSub pub pi q (n, v) /\
          Carried pub q (n, v) m /\ ParentRel.In ((m, u), (n, v)) pi /\
          p = (Name.Intermediate n v m q, u).
    Proof.
      intros D pub r S pi origins p; unfold coreResolutionIntermediate.
      rewrite SOdtp.mem_unionMap.
      split.
      - intros [[[n v] [m vs]] [HD Hh]]; cbn beta iota in Hh.
        apply SOptp.mem_unionMap_if in Hh; destruct Hh as [q [Hq [Hb Hh]]].
        apply SOvtp.mem_filterMap_if in Hh; destruct Hh as [u [Hu [Hp ->]]].
        cbn beta in Hb, Hp; rewrite edgeb_iff in Hp.
        rewrite !Bool.andb_true_iff, isOriginb_iff, PackageSet.mem_spec, mem_sub,
          carriedb_iff in Hb.
        destruct Hb as (Ho & Hins & Hc); exists n, v, m, vs, q, u; auto 10.
      - intros (n & v & m & vs & q & u & HD & Hq & Hu & Ho & Hins & Hc & Hpi
                & ->).
        exists ((n, v), (m, vs)); split; [exact HD | cbn beta iota].
        apply SOptp.mem_unionMap_if; exists q; cbn beta.
        rewrite !Bool.andb_true_iff, isOriginb_iff, PackageSet.mem_spec, mem_sub,
          carriedb_iff.
        split; [exact Hq | split; [auto |]].
        apply SOvtp.mem_filterMap_if; exists u; cbn beta.
        rewrite edgeb_iff; auto.
    Qed.

    Lemma mem_coreResolutionAgreement : forall D S pi p,
        Reduced.PackageSet.In p (coreResolutionAgreement D S pi) <->
        exists n v m vs u,
          Source.DependencyRel.In ((n, v), (m, vs)) D /\ VSet.In u vs /\
          PackageSet.In (n, v) S /\ ParentRel.In ((m, u), (n, v)) pi /\
          p = (Name.Agreement n v m, u).
    Proof.
      intros D S pi p; unfold coreResolutionAgreement.
      rewrite SOdtp.mem_unionMap.
      split.
      - intros [[[n v] [m vs]] [HD Hh]]; cbn beta iota in Hh.
        apply SOptp.in_if_empty in Hh; destruct Hh as [Hs Hh].
        apply SOvtp.mem_filterMap_if in Hh; destruct Hh as [u [Hu [Hp ->]]].
        apply PackageSet.mem_spec in Hs; apply edgeb_iff in Hp.
        exists n, v, m, vs, u; auto.
      - intros (n & v & m & vs & u & HD & Hu & HS & Hpi & ->).
        exists ((n, v), (m, vs)); split; [exact HD | cbn beta iota].
        apply SOptp.in_if_empty; rewrite PackageSet.mem_spec; split; [exact HS |].
        apply SOvtp.mem_filterMap_if; exists u; cbn beta.
        rewrite edgeb_iff; auto.
    Qed.

    Inductive CoreSpec (R : PackageSet.t) (D : Source.DependencyRel.t) (pub : PublicDependencyRel.t)
        (r : Package.t) (S : PackageSet.t) (pi : ParentRel.t) : Reduced.Package.t -> Prop :=
    | CoreOccurrence : forall n v q,
        PackageSet.In (n, v) S -> PackageSet.In q (origins R D pub r) ->
        IsOrigin D pub r S q -> InSub pub pi q (n, v) ->
        CoreSpec R D pub r S pi (Name.Occurrence n q, v)
    | CoreIntermediate : forall n v m vs q u,
        Source.DependencyRel.In ((n, v), (m, vs)) D ->
        PackageSet.In q (origins R D pub r) -> VSet.In u vs ->
        IsOrigin D pub r S q -> InSub pub pi q (n, v) ->
        Carried pub q (n, v) m -> ParentRel.In ((m, u), (n, v)) pi ->
        CoreSpec R D pub r S pi (Name.Intermediate n v m q, u)
    | CoreAgreement : forall n v m vs u,
        Source.DependencyRel.In ((n, v), (m, vs)) D -> VSet.In u vs ->
        PackageSet.In (n, v) S -> ParentRel.In ((m, u), (n, v)) pi ->
        CoreSpec R D pub r S pi (Name.Agreement n v m, u).

    Lemma mem_coreResolution : forall R D pub r S pi p,
        Reduced.PackageSet.In p (coreResolution R D pub r S pi) <->
        CoreSpec R D pub r S pi p.
    Proof.
      intros R D pub r S pi p; unfold coreResolution.
      rewrite !Reduced.PackageSet.union_spec, mem_coreResolutionOccurrence,
        mem_coreResolutionIntermediate, mem_coreResolutionAgreement.
      split.
      - intros [H | [H | H]]; mem_destruct; econstructor; eassumption.
      - destruct 1 as [n v q | n v m vs q u | n v m vs u].
        + left; exists n, v, q; auto.
        + right; left; exists n, v, m, vs, q, u; auto 10.
        + right; right; exists n, v, m, vs, u; auto.
    Qed.

    Theorem visibility_completeness :
      forall (R : PackageSet.t) (D : Source.DependencyRel.t) (pub : PublicDependencyRel.t) (r : Package.t)
             (S : PackageSet.t) (pi : ParentRel.t),
        IsResolution R D pub r S pi ->
        Reduced.IsResolution (reduceReal R D pub r) (reduceDeps R D pub r)
          (embedRoot r) (coreResolution R D pub r S pi).
    Proof.
      intros R D pub r S pi Hres.
      destruct Hres as [Hconc Hvv].
      destruct Hconc as [Hsub Hroot Hpc Hpif Hvg Hps].
      constructor.
      - intros p Hp; apply mem_coreResolution in Hp; apply mem_reduceReal.
        destruct Hp; econstructor; try apply Hsub; eassumption.
      - destruct r as [rn rv].
        apply mem_coreResolution; constructor;
          [exact Hroot | apply mem_origins; left; reflexivity
          | left; reflexivity | apply InSubSelf].
      - intros p Hp; apply mem_coreResolution in Hp.
        destruct Hp as [n v q HS Hq Ho Hins
                       | n v m vs q u HD Hq Hu Ho Hins Hc Hpi
                       | n v m vs u HD Hu HS Hpi];
          intros o us Hd; apply mem_reduceDeps in Hd.
        + inversion Hd as [n1 v1 q1 HR1 Hq1 Hpriv1 Hne1
                          | n1 v1 m1 vs1 q1 HD1 Hq1 Hc1 | |]; subst.
          * eexists; split; [apply SOvv.singleton_in; reflexivity |].
            apply mem_coreResolution; constructor;
              [exact HS | apply mem_origins; right; split; assumption
              | right; split; assumption | apply InSubSelf].
          * destruct (Hpc _ HS _ _ HD1) as [u [Hu [HmS Hpi]]].
            exists u; split; [apply mem_embedVS; exact Hu |].
            apply mem_coreResolution; econstructor; eassumption.
        + inversion Hd as [| | n1 v1 m1 vs1 q1 u1 HD1 Hq1 Hc1 Hu1
                          | n1 v1 m1 vs1 q1 u1 HD1 Hq1 Hc1 Hu1]; subst;
            (eexists; split; [apply SOvv.singleton_in; reflexivity |]);
            apply mem_coreResolution.
          * constructor; [exact (proj1 (Hps _ _ Hpi)) | exact Hq | exact Ho |].
            destruct Hc as [Hpub | <-];
              [ eapply PublicPropagation; eassumption
              | apply InSubChild; exact Hpi ].
          * econstructor;
              [exact HD1 | exact Hu1 | exact (proj2 (Hps _ _ Hpi)) | exact Hpi].
        + inversion Hd.
      - intros n w1 w2 H1 H2.
        apply mem_coreResolution in H1; apply mem_coreResolution in H2.
        inversion H1 as [n1 v1 q1 HS1 _ Ho1 Hins1
                        | n1 v1 m1 vs1 q1 u1 HD1 _ Hu1 _ _ _ Hpi1
                        | n1 v1 m1 vs1 u1 HD1 Hu1 _ Hpi1]; subst;
          inversion H2 as [n2 v2 q2 HS2 _ Ho2 Hins2
                          | n2 v2 m2 vs2 q2 u2 HD2 _ Hu2 _ _ _ Hpi2
                          | n2 v2 m2 vs2 u2 HD2 Hu2 _ Hpi2]; subst;
          [exact (Hvv _ (isOrigin_mem D pub r S _ Ho1 Hroot) _ _ _
                    Hins1 Hins2) | |].
        all: exact (Hpif _ _ _ _ Hpi1 Hpi2).
    Qed.

    Lemma visibilityResolution_coreResolution_iff : forall R D pub r S pi,
        IsResolution R D pub r S pi ->
        forall p,
          PackageSet.In p
            (visibilityResolution R D pub r (coreResolution R D pub r S pi))
          <-> PackageSet.In p S /\
              exists q, IsOrigin D pub r S q /\ InSub pub pi q p.
    Proof.
      intros R D pub r S pi [[Hsub _ _ _ _ _] _] [n v].
      rewrite mem_visibilityResolution; split.
      - intros [_ [q [_ Hocc]]]; apply mem_coreResolution in Hocc.
        inversion Hocc; subst.
        split; [assumption | eexists; split; eassumption].
      - intros [HS [q [Ho Hins]]]; split; [exact (Hsub _ HS) |].
        assert (Hq : PackageSet.In q (origins R D pub r)).
        { apply mem_origins.
          destruct Ho as [-> | [HqS Hpriv]]; [left; reflexivity | right].
          split; [exact (Hsub _ HqS) | exact Hpriv]. }
        exists q; split; [exact Hq |].
        apply mem_coreResolution; constructor; assumption.
    Qed.

    Lemma parents_coreResolution_iff : forall R D pub r S pi,
        IsResolution R D pub r S pi ->
        forall m u n v,
          ParentRel.In ((m, u), (n, v))
            (parents R D pub r (coreResolution R D pub r S pi))
          <-> ParentRel.In ((m, u), (n, v)) pi /\
              (exists vs, Source.DependencyRel.In ((n, v), (m, vs)) D /\ VSet.In u vs) /\
              exists q, IsOrigin D pub r S q /\ InSub pub pi q (n, v).
    Proof.
      intros R D pub r S pi Hres m u n v.
      assert (Hdec := visibilityResolution_coreResolution_iff R D pub r S pi
                        Hres (n, v)).
      destruct Hres as [[_ _ _ _ _ Hps] _].
      rewrite mem_parents; split.
      - intros (vs & HD & Hu & Hnv & Hagr).
        apply Hdec in Hnv; destruct Hnv as [_ Hvis].
        apply mem_coreResolution in Hagr.
        split; [inversion Hagr; assumption |].
        split; [exists vs; split; assumption | exact Hvis].
      - intros [Hpi [(vs & HD & Hu) Hvis]].
        destruct (Hps _ _ Hpi) as [_ HnS].
        exists vs.
        split; [exact HD |]; split; [exact Hu |].
        split; [apply Hdec; split; assumption |].
        apply mem_coreResolution; exact (CoreAgreement R D pub r S pi
                                           n v m vs u HD Hu HnS Hpi).
    Qed.

    Theorem visibility_retraction : forall R D pub r S pi,
        IsResolution R D pub r S pi -> OriginVisibility D pub r S pi ->
        Concurrent.ParentDependency D pi ->
        visibilityResolution R D pub r (coreResolution R D pub r S pi) = S /\
        parents R D pub r (coreResolution R D pub r S pi) = pi.
    Proof.
      intros R D pub r S pi Hres Hvis Hdep; split.
      - apply PackageSet.ext; intro p.
        rewrite (visibilityResolution_coreResolution_iff R D pub r S pi Hres).
        split; [intros [H _]; exact H | intro H; exact (conj H (Hvis p H))].
      - apply ParentRel.ext; intros [[m u] [n v]].
        rewrite (parents_coreResolution_iff R D pub r S pi Hres).
        split; [intros [H _]; exact H | intro H].
        split; [exact H | split; [exact (Hdep _ _ _ _ H) | apply Hvis]].
        exact (proj2 (Concurrent.res_parent_subset _ _ _ _ _ _
                        (res_concurrent _ _ _ _ _ _ Hres) _ _ H)).
    Qed.

    Module Lookup.
      Module PackageSetFibred := FibredRel N V Package PackageSet.
      Module DependencyRelFibred :=
        FibredLabelledRel Package N VSet.AsUOT Source.DependencyElt Source.DependencyRel.
      Module PublicDependencyRelFibred := FibredRel Package N PublicDependencyElt PublicDependencyRel.

      Lemma Priv_block : forall D D' pub pub' (p : Package.t),
          Source.DependencyRel.Subset (DependencyRelFibred.tailFibre D p) D' ->
          Source.DependencyRel.Subset D' D ->
          PublicDependencyRel.Subset (PublicDependencyRelFibred.tailFibre pub p) pub' ->
          PublicDependencyRel.Subset pub' pub ->
          (Priv D' pub' p <-> Priv D pub p).
      Proof.
        intros D D' pub pub' p HDl HDr Hpl Hpr; split.
        - intros [n [vs [He Hn]]]; exists n, vs; split; [exact (HDr _ He) |].
          intro Hin; apply Hn, Hpl, PublicDependencyRelFibred.mem_tailFibre.
          split; [exact Hin | reflexivity].
        - intros [n [vs [He Hn]]]; exists n, vs; split.
          + apply HDl, DependencyRelFibred.mem_tailFibre; split; [exact He | reflexivity].
          + intro Hin; exact (Hn (Hpr _ Hin)).
      Qed.

      Lemma priv_tailFibre : forall D pub (p : Package.t),
          Priv (DependencyRelFibred.tailFibre D p) (PublicDependencyRelFibred.tailFibre pub p) p <->
          Priv D pub p.
      Proof.
        intros D pub p; apply Priv_block.
        - intros y Hy; exact Hy.
        - apply DependencyRelFibred.tailFibre_subset.
        - intros y Hy; exact Hy.
        - apply PublicDependencyRelFibred.tailFibre_subset.
      Qed.

      Lemma carried_tailFibre : forall pub (q p : Package.t) (m : N.t),
          Carried (PublicDependencyRelFibred.tailFibre pub p) q p m <-> Carried pub q p m.
      Proof.
        intros pub q p m; unfold Carried.
        rewrite PublicDependencyRelFibred.mem_tailFibre.
        split; [intros [[Hin _] | ->] | intros [Hin | ->]];
          [left; exact Hin | right; reflexivity
           | left; split; [exact Hin | reflexivity] | right; reflexivity].
      Qed.

      Definition depRange (D : Source.DependencyRel.t) (p : Package.t) (m : N.t) : VSet.t :=
        Source.Merge.SOdv.unionMap (fun '(_, (_, vs)) => vs)
          (DependencyRelFibred.endsFibre D p m).

      Lemma mem_depRange : forall D (p : Package.t) (m : N.t) (u : V.t),
          VSet.In u (depRange D p m) <->
          exists vs, Source.DependencyRel.In (p, (m, vs)) D /\ VSet.In u vs.
      Proof.
        intros D p m u; unfold depRange; rewrite Source.Merge.SOdv.mem_unionMap.
        split.
        - intros [[x [m1 vs]] [He Hu]]; cbn beta iota in Hu.
          apply DependencyRelFibred.mem_endsFibre in He; destruct He as [HD [-> ->]].
          exists vs; split; [exact HD | exact Hu].
        - intros [vs [HD Hu]]; exists (p, (m, vs)); split; [| exact Hu].
          apply DependencyRelFibred.mem_endsFibre;
            split; [exact HD | split; reflexivity].
      Qed.

      Lemma reduceDeps_dependee_potentialOrigin :
        forall R D pub r (p : Reduced.Package.t) (o : Name.t) (h : Reduced.VSet.t)
               (q : Package.t),
          Reduced.DependencyRel.In (p, (o, h)) (reduceDeps R D pub r) ->
          (exists n : N.t, o = Name.Occurrence n q) \/
          (exists (n : N.t) (v : V.t) (m : N.t),
              o = Name.Intermediate n v m q) ->
          PackageSet.In q (origins R D pub r).
      Proof.
        intros R D pub r p o h q Hin Hname; apply mem_reduceDeps in Hin.
        inversion Hin; subst;
          destruct Hname as [[n2 Hn] | [n2 [v2 [m2 Hn]]]];
          try discriminate Hn; injection Hn; intros; subst;
          first [assumption
                | apply mem_origins; right; split; assumption].
      Qed.

      Theorem versions_lookupOccurrence :
        forall R D pub (m : N.t) (u : V.t) (n : N.t) (q : Package.t),
          (exists p h, Reduced.DependencyRel.In (p, (Name.Occurrence n q, h))
                         (reduceDeps R D pub (m, u))) \/
          Name.Occurrence n q = Name.Occurrence m (m, u) ->
          Reduced.versions (reduceReal R D pub (m, u)) (Name.Occurrence n q) =
          Reduced.versions
            (reduceReal (PackageSetFibred.tailFibre R n) Source.DependencyRel.empty PublicDependencyRel.empty q)
            (Name.Occurrence n q).
      Proof.
        intros R D pub rn rv n q Hreach; set (r := (rn, rv)) in *.
        assert (Hq : PackageSet.In q (origins R D pub r)).
        { destruct Hreach as [[p [h Hin]] | Heq].
          - apply (reduceDeps_dependee_potentialOrigin R D pub r p
                     (Name.Occurrence n q) h q Hin).
            left; exists n; reflexivity.
          - injection Heq as _ ->.
            apply mem_origins; left; reflexivity. }
        apply Reduced.VSet.ext; intro v.
        rewrite !Reduced.mem_versions.
        split.
        - intro Hin.
          destruct (occurrence_mem_reduceReal R D pub r n v q Hin) as [HR _].
          apply mem_reduceReal; constructor.
          + apply PackageSetFibred.mem_tailFibre; split; [exact HR | reflexivity].
          + apply mem_origins; left; reflexivity.
        - intro Hin; apply mem_reduceReal; constructor; [| exact Hq].
          apply mem_reduceReal in Hin; inversion Hin as [n1 v1 q1 HR | |];
            subst.
          exact (PackageSetFibred.tailFibre_subset R _ _ HR).
      Qed.

      (* Membership gives R (n, v) and q's origin status for the fibre. *)
      Theorem dependees_lookupOccurrence :
        forall R D pub r (n : N.t) (v : V.t) (q : Package.t),
          Reduced.PackageSet.In (Name.Occurrence n q, v) (reduceReal R D pub r) ->
          Reduced.dependees (reduceDeps R D pub r) (Name.Occurrence n q, v) =
          Reduced.dependees
            (reduceDeps (PackageSet.singleton (n, v))
               (DependencyRelFibred.tailFibre D (n, v))
               (PublicDependencyRelFibred.tailFibre pub (n, v)) q)
            (Name.Occurrence n q, v).
      Proof.
        intros R D pub r n v q Hmem.
        destruct (occurrence_mem_reduceReal R D pub r n v q Hmem) as [HR Hq].
        apply Reduced.dependees_ext; intros [o us].
        rewrite !mem_reduceDeps.
        split; intro H;
          inversion H as [n1 v1 q1 HR1 Hq1 Hpriv Hne
                         | n1 v1 m vs q1 HD1 Hq1 Hc | |]; subst.
        - constructor.
          + apply SOppp.singleton_in; reflexivity.
          + apply mem_origins; left; reflexivity.
          + apply priv_tailFibre; exact Hpriv.
          + exact Hne.
        - constructor.
          + apply DependencyRelFibred.mem_tailFibre; split; [exact HD1 | reflexivity].
          + apply mem_origins; left; reflexivity.
          + apply carried_tailFibre; exact Hc.
        - constructor;
            [exact HR | exact Hq | apply priv_tailFibre; exact Hpriv
            | exact Hne].
        - constructor;
            [exact (DependencyRelFibred.tailFibre_subset D _ _ HD1) | exact Hq
            | apply carried_tailFibre; exact Hc].
      Qed.

      Theorem versions_lookupIntermediate :
        forall R D pub r (n : N.t) (v : V.t) (m : N.t) (q : Package.t),
          (exists p h, Reduced.DependencyRel.In (p, (Name.Intermediate n v m q, h))
                         (reduceDeps R D pub r)) ->
          Reduced.versions (reduceReal R D pub r) (Name.Intermediate n v m q) =
          Reduced.versions
            (reduceReal PackageSet.empty (DependencyRelFibred.endsFibre D (n, v) m)
               PublicDependencyRel.empty q)
            (Name.Intermediate n v m q).
      Proof.
        intros R D pub r n v m q Hreach.
        assert (Hq : PackageSet.In q (origins R D pub r)).
        { destruct Hreach as [p [h Hin]].
          apply (reduceDeps_dependee_potentialOrigin R D pub r p
                   (Name.Intermediate n v m q) h q Hin).
          right; exists n, v, m; reflexivity. }
        apply Reduced.VSet.ext; intro u.
        rewrite !Reduced.mem_versions, !mem_reduceReal.
        split.
        - intro H; inversion H as [| n1 v1 m1 vs q1 u1 HD _ Hu |]; subst.
          econstructor; [| | exact Hu].
          + apply DependencyRelFibred.mem_endsFibre; split; [exact HD | auto].
          + apply mem_origins; left; reflexivity.
        - intro H; inversion H as [| n1 v1 m1 vs q1 u1 HD _ Hu |]; subst.
          econstructor; [| exact Hq | exact Hu].
          exact (DependencyRelFibred.endsFibre_subset D _ _ _ HD).
      Qed.

      (* Membership is what makes q a potential origin for the fibre. *)
      Theorem dependees_lookupIntermediate :
        forall R D pub r (n : N.t) (v : V.t) (m : N.t) (q : Package.t) (u : V.t),
          Reduced.PackageSet.In (Name.Intermediate n v m q, u) (reduceReal R D pub r) ->
          Reduced.dependees (reduceDeps R D pub r) (Name.Intermediate n v m q, u) =
          Reduced.dependees
            (reduceDeps PackageSet.empty
               (DependencyRelFibred.tailFibre D (n, v))
               (PublicDependencyRelFibred.tailFibre pub (n, v)) q)
            (Name.Intermediate n v m q, u).
      Proof.
        intros R D pub r n v m q u Hmem.
        assert (Hq : PackageSet.In q (origins R D pub r))
          by (apply mem_reduceReal in Hmem; inversion Hmem; assumption).
        apply Reduced.dependees_ext; intros [o us].
        rewrite !mem_reduceDeps.
        split; intro H;
          inversion H as [| | n1 v1 m1 vs q1 u1 HD1 Hq1 Hc Hu1
                         | n1 v1 m1 vs q1 u1 HD1 Hq1 Hc Hu1]; subst.
        1-2: econstructor;
          [apply DependencyRelFibred.mem_tailFibre; split; [exact HD1 | reflexivity]
          | apply mem_origins; left; reflexivity
          | apply carried_tailFibre; exact Hc | exact Hu1].
        all: econstructor;
          [exact (DependencyRelFibred.tailFibre_subset D _ _ HD1) | exact Hq
          | apply carried_tailFibre; exact Hc | exact Hu1].
      Qed.

      Theorem versions_lookupAgreement :
        forall R D pub r (n : N.t) (v : V.t) (m : N.t),
          Reduced.versions (reduceReal R D pub r) (Name.Agreement n v m) =
          Reduced.versions
            (reduceReal PackageSet.empty (DependencyRelFibred.endsFibre D (n, v) m)
               PublicDependencyRel.empty r)
            (Name.Agreement n v m).
      Proof.
        intros R D pub r n v m; apply Reduced.versions_ext; intro u.
        rewrite !mem_reduceReal.
        split; intro H; inversion H as [| | n1 v1 m1 vs u1 HD Hu]; subst.
        - econstructor; [| exact Hu].
          apply DependencyRelFibred.mem_endsFibre; split; [exact HD | split; reflexivity].
        - apply DependencyRelFibred.mem_endsFibre in HD; destruct HD as [HD _].
          econstructor; eassumption.
      Qed.

      Theorem dependees_lookupAgreement :
        forall R D pub r (n : N.t) (v : V.t) (m : N.t) (u : V.t),
          Reduced.dependees (reduceDeps R D pub r) (Name.Agreement n v m, u) =
          Reduced.DependeeSet.empty.
      Proof.
        intros R D pub r n v m u; apply Reduced.dependees_empty_iff.
        intros [o us] H; apply mem_reduceDeps in H; inversion H.
      Qed.

    End Lookup.
  End Reduction.
End Visibility.
