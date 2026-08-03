From Stdlib Require Import MSets MSetProperties Lia.
From PackageCalculus Require Import Prelude Core Concurrent.

Create HintDb cmp_vis.
Create Rewrite HintDb cmp_vis.

Module Visibility (N V : UsualOrderedType).
  (* Visibility resolutions are concurrent resolutions at the identity
     granularity, under which version granularity is vacuous. *)
  Module Conc := Concurrent N V V.
  Module C := Conc.C.
  Module Pkg := C.Pkg.
  Module PkgSet := C.PkgSet.
  Module VSet := C.VSet.
  Module ParentElt := Conc.ParentElt.
  Module ParentRel := Conc.ParentRel.

  Module PubElt := PairUOT Pkg N.
  Module PubRel := FSetUOT PubElt.

  Definition Priv (D : C.DepRel.t) (pub : PubRel.t) (p : Pkg.t) : Prop :=
    exists (n : N.t) (vs : VSet.t),
      C.DepRel.In (p, (n, vs)) D /\ ~ PubRel.In (p, n) pub.

  Lemma not_priv_pub : forall D pub p (n : N.t) (vs : VSet.t),
      ~ Priv D pub p -> C.DepRel.In (p, (n, vs)) D -> PubRel.In (p, n) pub.
  Proof.
    intros D pub p n vs Hnp HD.
    destruct (PubRel.mem (p, n) pub) eqn:Hm;
      [apply PubRel.mem_spec; exact Hm | exfalso].
    apply Hnp; exists n, vs; split; [exact HD |].
    intro Hin; apply PubRel.mem_spec in Hin; congruence.
  Qed.

  Definition IsOrigin (D : C.DepRel.t) (pub : PubRel.t) (r : Pkg.t)
      (S : PkgSet.t) (q : Pkg.t) : Prop :=
    q = r \/ (PkgSet.In q S /\ Priv D pub q).

  Lemma isOrigin_mem : forall D pub r S q,
      IsOrigin D pub r S q -> PkgSet.In r S -> PkgSet.In q S.
  Proof. intros D pub r S q [-> | [Hq _]] Hr; [exact Hr | exact Hq]. Qed.

  Inductive InSub (pub : PubRel.t) (pi : ParentRel.t) (q : Pkg.t)
    : Pkg.t -> Prop :=
  | InSubSelf : InSub pub pi q q
  | InSubChild : forall c, ParentRel.In (c, q) pi -> InSub pub pi q c
  | InSubPubStep : forall (p : Pkg.t) (m : N.t) (u : V.t),
      InSub pub pi q p -> ParentRel.In ((m, u), p) pi ->
      PubRel.In (p, m) pub -> InSub pub pi q (m, u).

  Record IsResolution
      (R : PkgSet.t) (D : C.DepRel.t) (pub : PubRel.t) (r : Pkg.t)
      (S : PkgSet.t) (pi : ParentRel.t) : Prop :=
    { res_concurrent : Conc.IsResolution R D (fun v => v) r S pi
    ; res_version_visibility :
        forall p, PkgSet.In p S ->
        forall (n : N.t) (v v' : V.t),
          InSub pub pi p (n, v) -> InSub pub pi p (n, v') -> v = v' }.

  Module SOpp := SetOps ParentElt Pkg ParentRel PkgSet.
  Module SOppp := SetOps Pkg Pkg PkgSet PkgSet.

  Definition children (pi : ParentRel.t) (p : Pkg.t) : PkgSet.t :=
    SOpp.filterMap (fun '(c, d) => if Pkg.eq_dec d p then Some c else None) pi.

  Lemma mem_children : forall pi p c,
      PkgSet.In c (children pi p) <-> ParentRel.In (c, p) pi.
  Proof.
    intros pi p c; unfold children; rewrite SOpp.mem_filterMap.
    split.
    - intros [[c' d] [He Hc]]; cbn beta iota in Hc.
      destruct (Pkg.eq_dec d p) as [-> | NE]; [| discriminate].
      injection Hc as <-; exact He.
    - intro H; exists (c, p); split; [exact H | cbn beta iota].
      destruct (Pkg.eq_dec p p) as [_ | NE];
        [reflexivity | contradiction NE; reflexivity].
  Qed.

  Definition pubChildren (pub : PubRel.t) (pi : ParentRel.t) (p : Pkg.t)
      : PkgSet.t :=
    SOpp.filterMap (fun '(c, d) =>
        if Pkg.eq_dec d p
        then if PubRel.mem (p, fst c) pub then Some c else None
        else None)
      pi.

  Lemma mem_pubChildren : forall pub pi p c,
      PkgSet.In c (pubChildren pub pi p) <->
      ParentRel.In (c, p) pi /\ PubRel.In (p, fst c) pub.
  Proof.
    intros pub pi p c; unfold pubChildren; rewrite SOpp.mem_filterMap.
    split.
    - intros [[c' d] [He Hc]]; cbn beta iota in Hc.
      destruct (Pkg.eq_dec d p) as [-> | NE]; [| discriminate].
      destruct (PubRel.mem (p, fst c') pub) eqn:Hm; [| discriminate].
      injection Hc as <-.
      split; [exact He | apply PubRel.mem_spec; exact Hm].
    - intros [He Hm]; exists (c, p); split; [exact He | cbn beta iota].
      destruct (Pkg.eq_dec p p) as [_ | NE]; [| contradiction NE; reflexivity].
      assert (PubRel.mem (p, fst c) pub = true) as ->
        by (apply PubRel.mem_spec; exact Hm).
      reflexivity.
  Qed.

  Definition subBase (pi : ParentRel.t) (q : Pkg.t) : PkgSet.t :=
    PkgSet.add q (children pi q).

  Lemma mem_subBase : forall pi q c,
      PkgSet.In c (subBase pi q) <-> c = q \/ ParentRel.In (c, q) pi.
  Proof.
    intros pi q c; unfold subBase.
    rewrite SOppp.add_in, mem_children; reflexivity.
  Qed.

  Definition subStep (pub : PubRel.t) (pi : ParentRel.t) (acc : PkgSet.t)
      : PkgSet.t :=
    PkgSet.union acc (SOppp.unionMap (pubChildren pub pi) acc).

  Lemma mem_subStep : forall pub pi acc c,
      PkgSet.In c (subStep pub pi acc) <->
      PkgSet.In c acc \/
      (exists p, PkgSet.In p acc /\ ParentRel.In (c, p) pi /\
         PubRel.In (p, fst c) pub).
  Proof.
    intros pub pi acc c; unfold subStep.
    rewrite PkgSet.union_spec, SOppp.mem_unionMap.
    apply or_iff_compat_l; split.
    - intros [p [Hp Hc]]; apply mem_pubChildren in Hc.
      exists p; split; [exact Hp | exact Hc].
    - intros [p [Hp [He Hm]]]; exists p; split; [exact Hp |].
      apply mem_pubChildren; split; [exact He | exact Hm].
  Qed.

  Lemma subStep_incl : forall pub pi acc,
      PkgSet.Subset acc (subStep pub pi acc).
  Proof. intros pub pi acc c Hc; apply mem_subStep; left; exact Hc. Qed.

  (* Saturation by a fixed number of rounds rather than well-founded
     recursion: the completeness witness has to test membership of the least
     set InSub describes, and every witness in this development computes. *)
  Fixpoint subIter (pub : PubRel.t) (pi : ParentRel.t) (fuel : nat)
      (acc : PkgSet.t) : PkgSet.t :=
    match fuel with
    | O => acc
    | S k => subIter pub pi k (subStep pub pi acc)
    end.

  Lemma subIter_incl : forall pub pi fuel acc,
      PkgSet.Subset acc (subIter pub pi fuel acc).
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

  Lemma subIter_sound : forall pub pi (P : Pkg.t -> Prop),
      (forall (p : Pkg.t) (m : N.t) (u : V.t),
         P p -> ParentRel.In ((m, u), p) pi -> PubRel.In (p, m) pub ->
         P (m, u)) ->
      forall fuel acc,
        (forall c, PkgSet.In c acc -> P c) ->
        forall c, PkgSet.In c (subIter pub pi fuel acc) -> P c.
  Proof.
    intros pub pi P Hstep fuel; induction fuel as [| k IH];
      intros acc Hacc c Hc.
    - exact (Hacc c Hc).
    - apply (IH (subStep pub pi acc)); [| exact Hc].
      intros c' Hc'; apply mem_subStep in Hc'.
      destruct Hc' as [Hc' | [p [Hp [He Hm]]]]; [exact (Hacc c' Hc') |].
      destruct c' as [m u]; exact (Hstep p m u (Hacc p Hp) He Hm).
  Qed.

  (* The saturation never leaves the tails of pi, so that set's cardinal
     bounds how many rounds can each add an element. *)
  Definition subUniverse (pi : ParentRel.t) (q : Pkg.t) : PkgSet.t :=
    PkgSet.add q (SOpp.map fst pi).

  Lemma mem_subUniverse_tail : forall pi q c p,
      ParentRel.In (c, p) pi -> PkgSet.In c (subUniverse pi q).
  Proof.
    intros pi q c p H; unfold subUniverse; apply SOppp.add_in; right.
    apply SOpp.mem_map; exists (c, p); split; [exact H | reflexivity].
  Qed.

  Lemma subBase_universe : forall pi q,
      PkgSet.Subset (subBase pi q) (subUniverse pi q).
  Proof.
    intros pi q c Hc; apply mem_subBase in Hc.
    destruct Hc as [-> | He];
      [apply SOppp.add_in; left; reflexivity
      | exact (mem_subUniverse_tail pi q c q He)].
  Qed.

  Lemma subStep_universe : forall pub pi q acc,
      PkgSet.Subset acc (subUniverse pi q) ->
      PkgSet.Subset (subStep pub pi acc) (subUniverse pi q).
  Proof.
    intros pub pi q acc Hacc c Hc; apply mem_subStep in Hc.
    destruct Hc as [Hc | [p [_ [He _]]]];
      [exact (Hacc c Hc) | exact (mem_subUniverse_tail pi q c p He)].
  Qed.

  Lemma subIter_universe : forall pub pi q fuel acc,
      PkgSet.Subset acc (subUniverse pi q) ->
      PkgSet.Subset (subIter pub pi fuel acc) (subUniverse pi q).
  Proof.
    intros pub pi q fuel; induction fuel as [| k IH]; intros acc Hacc.
    - exact Hacc.
    - apply IH, subStep_universe; exact Hacc.
  Qed.

  Module PkgSetProps := MSetProperties.WPropertiesOn Pkg PkgSet.

  Lemma subIter_grow : forall pub pi fuel acc,
      subStep pub pi (subIter pub pi fuel acc) = subIter pub pi fuel acc \/
      PkgSet.cardinal acc + fuel <=
        PkgSet.cardinal (subIter pub pi fuel acc).
  Proof.
    intros pub pi fuel; induction fuel as [| k IH]; intro acc.
    - right; simpl; lia.
    - destruct (PkgSet.is_empty (PkgSet.diff (subStep pub pi acc) acc)) eqn:He.
      + assert (Hfix : subStep pub pi acc = acc).
        { apply PkgSet.ext; intro x; split; [| apply subStep_incl].
          intro Hx; destruct (PkgSet.mem x acc) eqn:Hm;
            [apply PkgSet.mem_spec; exact Hm | exfalso].
          rewrite PkgSet.is_empty_spec in He.
          apply (He x), PkgSet.diff_spec; split; [exact Hx |].
          intro Hc; rewrite <- PkgSet.mem_spec in Hc; congruence. }
        left; simpl; rewrite Hfix, (subIter_fix pub pi k acc Hfix); exact Hfix.
      + destruct (PkgSet.choose_nonempty _ He) as [x Hx].
        apply PkgSet.diff_spec in Hx; destruct Hx as [Hx1 Hx2].
        pose proof (PkgSetProps.subset_cardinal_lt
                      (subStep_incl pub pi acc) Hx1 Hx2) as Hlt.
        simpl; destruct (IH (subStep pub pi acc)) as [E | Hc];
          [left; exact E | right; lia].
  Qed.

  Definition sub (pub : PubRel.t) (pi : ParentRel.t) (q : Pkg.t) : PkgSet.t :=
    subIter pub pi (PkgSet.cardinal (subUniverse pi q)) (subBase pi q).

  Lemma sub_fix : forall pub pi q, subStep pub pi (sub pub pi q) = sub pub pi q.
  Proof.
    intros pub pi q; unfold sub.
    destruct (subIter_grow pub pi (PkgSet.cardinal (subUniverse pi q))
                (subBase pi q)) as [E | Hc]; [exact E | exfalso].
    assert (Hle : PkgSet.cardinal
                    (subIter pub pi (PkgSet.cardinal (subUniverse pi q))
                       (subBase pi q)) <=
                  PkgSet.cardinal (subUniverse pi q))
      by (apply PkgSetProps.subset_cardinal, subIter_universe,
            subBase_universe).
    assert (Hpos : 1 <= PkgSet.cardinal (subBase pi q)).
    { destruct (PkgSet.cardinal (subBase pi q)) eqn:Hcb; [| lia].
      exfalso.
      assert (PkgSet.Empty (subBase pi q)) as Hemp
        by (apply PkgSetProps.cardinal_inv_1; exact Hcb).
      apply (Hemp q), mem_subBase; left; reflexivity. }
    lia.
  Qed.

  Lemma mem_sub : forall pub pi q c,
      PkgSet.In c (sub pub pi q) <-> InSub pub pi q c.
  Proof.
    intros pub pi q c; split.
    - unfold sub; apply subIter_sound.
      + intros p m u Hp He Hm; exact (InSubPubStep pub pi q p m u Hp He Hm).
      + intros c' Hc'; apply mem_subBase in Hc'.
        destruct Hc' as [-> | He];
          [apply InSubSelf | exact (InSubChild pub pi q c' He)].
    - intro H; induction H as [| c He | p m u H IH He Hm].
      + unfold sub; apply subIter_incl, mem_subBase; left; reflexivity.
      + unfold sub; apply subIter_incl, mem_subBase; right; exact He.
      + assert (Hin : PkgSet.In (m, u) (subStep pub pi (sub pub pi q))).
        { apply mem_subStep; right.
          exists p; split; [exact IH | split; [exact He | exact Hm]]. }
        rewrite sub_fix in Hin; exact Hin.
  Qed.

  Module Reduction.
    Module PkgEqb := UOTEqb Pkg.

    Definition privb (D : C.DepRel.t) (pub : PubRel.t) (p : Pkg.t) : bool :=
      C.DepRel.exists_ (fun '(q, (n, _)) =>
          andb (PkgEqb.eqb q p) (negb (PubRel.mem (p, n) pub)))
        D.

    Lemma privb_iff : forall D pub p, privb D pub p = true <-> Priv D pub p.
    Proof.
      intros D pub p; unfold privb, Priv.
      rewrite C.DepRel.exists_spec'.
      split.
      - intros [[q [n vs]] [He Hb]]; cbn beta iota in Hb.
        apply Bool.andb_true_iff in Hb; destruct Hb as [H1 H2].
        apply PkgEqb.eqb_true_iff in H1 as ->.
        exists n, vs; split; [exact He |].
        apply Bool.negb_true_iff in H2.
        intro Hin; apply PubRel.mem_spec in Hin; congruence.
      - intros [n [vs [He Hn]]]; exists (p, (n, vs)); split; [exact He |].
        cbn beta iota; apply Bool.andb_true_iff; split;
          [apply PkgEqb.eqb_refl |].
        apply Bool.negb_true_iff, Bool.not_true_iff_false.
        intro Hm; apply Hn, PubRel.mem_spec; exact Hm.
    Qed.

    Definition Carried (pub : PubRel.t) (p : Pkg.t) (m : N.t) (q : Pkg.t)
        : Prop :=
      PubRel.In (p, m) pub \/ p = q.

    Definition carriedb (pub : PubRel.t) (p : Pkg.t) (m : N.t) (q : Pkg.t)
        : bool :=
      orb (PubRel.mem (p, m) pub) (PkgEqb.eqb p q).

    Lemma carriedb_iff : forall pub p m q,
        carriedb pub p m q = true <-> Carried pub p m q.
    Proof.
      intros pub p m q; unfold carriedb, Carried.
      rewrite Bool.orb_true_iff, PubRel.mem_spec, PkgEqb.eqb_true_iff;
        reflexivity.
    Qed.

    Definition isOriginb (D : C.DepRel.t) (pub : PubRel.t) (r : Pkg.t)
        (S : PkgSet.t) (q : Pkg.t) : bool :=
      orb (PkgEqb.eqb q r) (andb (PkgSet.mem q S) (privb D pub q)).

    Lemma isOriginb_iff : forall D pub r S q,
        isOriginb D pub r S q = true <-> IsOrigin D pub r S q.
    Proof.
      intros D pub r S q; unfold isOriginb, IsOrigin.
      rewrite Bool.orb_true_iff, Bool.andb_true_iff, PkgEqb.eqb_true_iff,
        PkgSet.mem_spec, privb_iff; reflexivity.
    Qed.

    Definition potentialOrigins (R : PkgSet.t) (D : C.DepRel.t)
        (pub : PubRel.t) (r : Pkg.t) : PkgSet.t :=
      PkgSet.add r (PkgSet.filter (privb D pub) R).

    Lemma mem_potentialOrigins : forall R D pub r q,
        PkgSet.In q (potentialOrigins R D pub r) <->
        q = r \/ (PkgSet.In q R /\ Priv D pub q).
    Proof.
      intros R D pub r q; unfold potentialOrigins.
      rewrite SOppp.add_in, PkgSet.filter_spec', privb_iff; reflexivity.
    Qed.

    Module NP := PairUOT N Pkg.
    Module VNP := TripleUOT V N Pkg.
    Module NVNP := PairUOT N VNP.
    Module NVN := TripleUOT N V N.
    Module NPF := UOTCompareFacts NP.
    Module NVNPF := UOTCompareFacts NVNP.
    Module NVNF := UOTCompareFacts NVN.
    #[local] Hint Rewrite NPF.compare_eq_iff NVNPF.compare_eq_iff
      NVNF.compare_eq_iff : cmp_vis.
    #[local] Hint Extern 1 => cmp_by NPF.compare_antisym : cmp_vis.
    #[local] Hint Extern 1 => cmp_by NVNPF.compare_antisym : cmp_vis.
    #[local] Hint Extern 1 => cmp_by NVNF.compare_antisym : cmp_vis.
    #[local] Hint Extern 1 => cmp_by NPF.compare_lt_trans : cmp_vis.
    #[local] Hint Extern 1 => cmp_by NVNPF.compare_lt_trans : cmp_vis.
    #[local] Hint Extern 1 => cmp_by NVNF.compare_lt_trans : cmp_vis.

    Module Name.
      Inductive name : Type :=
      | Occurrence (n : N.t) (q : Pkg.t)
      | Intermediate (n : N.t) (v : V.t) (m : N.t) (q : Pkg.t)
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
                NP.compare (n1, q1) (n2, q2)
            | Intermediate n1 v1 m1 q1, Intermediate n2 v2 m2 q2 =>
                NVNP.compare (n1, (v1, (m1, q1))) (n2, (v2, (m2, q2)))
            | Agreement n1 v1 m1, Agreement n2 v2 m2 =>
                NVN.compare (n1, (v1, m1)) (n2, (v2, m2))
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
    Module T := Core NameOT V.

    Module SOvv := SetOps V V VSet T.VSet.
    (* Module application is generative, so the target's version sets are a
       fresh type even though the versions in them are the same. *)
    Definition embedVS (vs : VSet.t) : T.VSet.t := SOvv.map (fun u => u) vs.

    Lemma mem_embedVS : forall vs u, T.VSet.In u (embedVS vs) <-> VSet.In u vs.
    Proof.
      intros vs u; unfold embedVS; rewrite SOvv.mem_map.
      split; [intros [x [Hx ->]]; exact Hx |].
      intro H; exists u; split; [exact H | reflexivity].
    Qed.

    Definition embedRoot (r : Pkg.t) : T.Pkg.t :=
      (Name.Occurrence (fst r) r, snd r).

    Module SOptp := SetOps Pkg T.Pkg PkgSet T.PkgSet.
    Definition reduceRealOccurrence (R : PkgSet.t) (origins : PkgSet.t)
        : T.PkgSet.t :=
      SOptp.unionMap (fun '(n, v) =>
          SOptp.map (fun q => (Name.Occurrence n q, v)) origins)
        R.

    Module SOdtp := SetOps C.DepElt T.Pkg C.DepRel T.PkgSet.
    Module SOvtp := SetOps V T.Pkg VSet T.PkgSet.
    Definition reduceRealIntermediate (D : C.DepRel.t) (origins : PkgSet.t)
        : T.PkgSet.t :=
      SOdtp.unionMap (fun '((n, v), (m, vs)) =>
          SOptp.unionMap (fun q =>
              SOvtp.map (fun u => (Name.Intermediate n v m q, u)) vs)
            origins)
        D.

    Definition reduceRealAgreement (D : C.DepRel.t) : T.PkgSet.t :=
      SOdtp.unionMap (fun '((n, v), (m, vs)) =>
          SOvtp.map (fun u => (Name.Agreement n v m, u)) vs)
        D.

    Definition reduceReal (R : PkgSet.t) (D : C.DepRel.t) (pub : PubRel.t)
        (r : Pkg.t) : T.PkgSet.t :=
      T.PkgSet.union (reduceRealOccurrence R (potentialOrigins R D pub r))
        (T.PkgSet.union
           (reduceRealIntermediate D (potentialOrigins R D pub r))
           (reduceRealAgreement D)).

    Module SOptd := SetOps Pkg T.DepElt PkgSet T.DepRel.
    Definition reduceDepsSelf (R : PkgSet.t) (D : C.DepRel.t) (pub : PubRel.t)
        (origins : PkgSet.t) : T.DepRel.t :=
      SOptd.unionMap (fun '(n, v) =>
          SOptd.filterMap (fun q =>
              if andb (privb D pub (n, v)) (negb (PkgEqb.eqb q (n, v)))
              then Some ((Name.Occurrence n q, v),
                         (Name.Occurrence n (n, v), T.VSet.singleton v))
              else None)
            origins)
        R.

    Module SOdtd := SetOps C.DepElt T.DepElt C.DepRel T.DepRel.
    Definition reduceDepsOccToInt (D : C.DepRel.t) (pub : PubRel.t)
        (origins : PkgSet.t) : T.DepRel.t :=
      SOdtd.unionMap (fun '((n, v), (m, vs)) =>
          SOptd.filterMap (fun q =>
              if carriedb pub (n, v) m q
              then Some ((Name.Occurrence n q, v),
                         (Name.Intermediate n v m q, embedVS vs))
              else None)
            origins)
        D.

    Module SOvtd := SetOps V T.DepElt VSet T.DepRel.
    Definition reduceDepsIntToOcc (D : C.DepRel.t) (pub : PubRel.t)
        (origins : PkgSet.t) : T.DepRel.t :=
      SOdtd.unionMap (fun '((n, v), (m, vs)) =>
          SOptd.unionMap (fun q =>
              if carriedb pub (n, v) m q
              then SOvtd.map (fun u =>
                       ((Name.Intermediate n v m q, u),
                        (Name.Occurrence m q, T.VSet.singleton u)))
                     vs
              else T.DepRel.empty)
            origins)
        D.

    Definition reduceDepsIntToAgr (D : C.DepRel.t) (pub : PubRel.t)
        (origins : PkgSet.t) : T.DepRel.t :=
      SOdtd.unionMap (fun '((n, v), (m, vs)) =>
          SOptd.unionMap (fun q =>
              if carriedb pub (n, v) m q
              then SOvtd.map (fun u =>
                       ((Name.Intermediate n v m q, u),
                        (Name.Agreement n v m, T.VSet.singleton u)))
                     vs
              else T.DepRel.empty)
            origins)
        D.

    Definition reduceDeps (R : PkgSet.t) (D : C.DepRel.t) (pub : PubRel.t)
        (r : Pkg.t) : T.DepRel.t :=
      T.DepRel.union (reduceDepsSelf R D pub (potentialOrigins R D pub r))
        (T.DepRel.union
           (reduceDepsOccToInt D pub (potentialOrigins R D pub r))
           (T.DepRel.union
              (reduceDepsIntToOcc D pub (potentialOrigins R D pub r))
              (reduceDepsIntToAgr D pub (potentialOrigins R D pub r)))).

    Lemma mem_reduceRealOccurrence : forall R origins y,
        T.PkgSet.In y (reduceRealOccurrence R origins) <->
        exists n v q, PkgSet.In (n, v) R /\ PkgSet.In q origins /\
          y = (Name.Occurrence n q, v).
    Proof.
      intros R origins y; unfold reduceRealOccurrence.
      rewrite SOptp.mem_unionMap.
      split.
      - intros [[n v] [HR Hh]]; cbn beta iota in Hh.
        apply SOptp.mem_map in Hh; destruct Hh as [q [Hq ->]].
        exists n, v, q; split; [exact HR | split; [exact Hq | reflexivity]].
      - intros [n [v [q [HR [Hq ->]]]]].
        exists (n, v); split; [exact HR | cbn beta iota].
        apply SOptp.mem_map; exists q; split; [exact Hq | reflexivity].
    Qed.

    Lemma mem_reduceRealIntermediate : forall D origins y,
        T.PkgSet.In y (reduceRealIntermediate D origins) <->
        exists n v m vs q u,
          C.DepRel.In ((n, v), (m, vs)) D /\ PkgSet.In q origins /\
          VSet.In u vs /\ y = (Name.Intermediate n v m q, u).
    Proof.
      intros D origins y; unfold reduceRealIntermediate.
      rewrite SOdtp.mem_unionMap.
      split.
      - intros [[[n v] [m vs]] [HD Hh]]; cbn beta iota in Hh.
        apply SOptp.mem_unionMap in Hh; destruct Hh as [q [Hq Hh]].
        apply SOvtp.mem_map in Hh; destruct Hh as [u [Hu ->]].
        exists n, v, m, vs, q, u; repeat split; assumption.
      - intros [n [v [m [vs [q [u [HD [Hq [Hu ->]]]]]]]]].
        exists ((n, v), (m, vs)); split; [exact HD | cbn beta iota].
        apply SOptp.mem_unionMap; exists q; split; [exact Hq |].
        apply SOvtp.mem_map; exists u; split; [exact Hu | reflexivity].
    Qed.

    Lemma mem_reduceRealAgreement : forall D y,
        T.PkgSet.In y (reduceRealAgreement D) <->
        exists n v m vs u,
          C.DepRel.In ((n, v), (m, vs)) D /\ VSet.In u vs /\
          y = (Name.Agreement n v m, u).
    Proof.
      intros D y; unfold reduceRealAgreement; rewrite SOdtp.mem_unionMap.
      split.
      - intros [[[n v] [m vs]] [HD Hh]]; cbn beta iota in Hh.
        apply SOvtp.mem_map in Hh; destruct Hh as [u [Hu ->]].
        exists n, v, m, vs, u; repeat split; assumption.
      - intros [n [v [m [vs [u [HD [Hu ->]]]]]]].
        exists ((n, v), (m, vs)); split; [exact HD | cbn beta iota].
        apply SOvtp.mem_map; exists u; split; [exact Hu | reflexivity].
    Qed.

    Lemma mem_reduceReal : forall R D pub r y,
        T.PkgSet.In y (reduceReal R D pub r) <->
        (exists n v q, PkgSet.In (n, v) R /\
           PkgSet.In q (potentialOrigins R D pub r) /\
           y = (Name.Occurrence n q, v)) \/
        ((exists n v m vs q u,
             C.DepRel.In ((n, v), (m, vs)) D /\
             PkgSet.In q (potentialOrigins R D pub r) /\ VSet.In u vs /\
             y = (Name.Intermediate n v m q, u)) \/
         (exists n v m vs u,
             C.DepRel.In ((n, v), (m, vs)) D /\ VSet.In u vs /\
             y = (Name.Agreement n v m, u))).
    Proof.
      intros R D pub r y; unfold reduceReal.
      rewrite !T.PkgSet.union_spec, mem_reduceRealOccurrence,
        mem_reduceRealIntermediate, mem_reduceRealAgreement; reflexivity.
    Qed.

    Lemma mem_reduceDepsSelf : forall R D pub origins y,
        T.DepRel.In y (reduceDepsSelf R D pub origins) <->
        exists n v q, PkgSet.In (n, v) R /\ PkgSet.In q origins /\
          Priv D pub (n, v) /\ q <> (n, v) /\
          y = ((Name.Occurrence n q, v),
               (Name.Occurrence n (n, v), T.VSet.singleton v)).
    Proof.
      intros R D pub origins y; unfold reduceDepsSelf.
      rewrite SOptd.mem_unionMap.
      split.
      - intros [[n v] [HR Hh]]; cbn beta iota in Hh.
        apply SOptd.mem_filterMap in Hh; destruct Hh as [q [Hq Hc]];
          cbn beta iota in Hc.
        destruct (andb (privb D pub (n, v)) (negb (PkgEqb.eqb q (n, v))))
          eqn:Hb; [| discriminate].
        injection Hc as <-.
        apply Bool.andb_true_iff in Hb; destruct Hb as [H1 H2].
        apply Bool.negb_true_iff, PkgEqb.eqb_false_iff in H2.
        exists n, v, q; repeat split;
          [exact HR | exact Hq | apply privb_iff; exact H1 | exact H2].
      - intros [n [v [q [HR [Hq [Hpriv [Hne ->]]]]]]].
        exists (n, v); split; [exact HR | cbn beta iota].
        apply SOptd.mem_filterMap; exists q; split; [exact Hq |].
        cbn beta iota.
        assert (andb (privb D pub (n, v)) (negb (PkgEqb.eqb q (n, v))) = true)
          as -> by (apply Bool.andb_true_iff; split;
                    [apply privb_iff; exact Hpriv
                    | apply Bool.negb_true_iff, PkgEqb.eqb_false_iff;
                      exact Hne]).
        reflexivity.
    Qed.

    Lemma mem_reduceDepsOccToInt : forall D pub origins y,
        T.DepRel.In y (reduceDepsOccToInt D pub origins) <->
        exists n v m vs q,
          C.DepRel.In ((n, v), (m, vs)) D /\ PkgSet.In q origins /\
          Carried pub (n, v) m q /\
          y = ((Name.Occurrence n q, v),
               (Name.Intermediate n v m q, embedVS vs)).
    Proof.
      intros D pub origins y; unfold reduceDepsOccToInt.
      rewrite SOdtd.mem_unionMap.
      split.
      - intros [[[n v] [m vs]] [HD Hh]]; cbn beta iota in Hh.
        apply SOptd.mem_filterMap in Hh; destruct Hh as [q [Hq Hc]];
          cbn beta iota in Hc.
        destruct (carriedb pub (n, v) m q) eqn:Hb; [| discriminate].
        injection Hc as <-.
        exists n, v, m, vs, q; repeat split;
          [exact HD | exact Hq | apply carriedb_iff; exact Hb].
      - intros [n [v [m [vs [q [HD [Hq [Hc ->]]]]]]]].
        exists ((n, v), (m, vs)); split; [exact HD | cbn beta iota].
        apply SOptd.mem_filterMap; exists q; split; [exact Hq |].
        cbn beta iota.
        assert (carriedb pub (n, v) m q = true) as ->
          by (apply carriedb_iff; exact Hc).
        reflexivity.
    Qed.

    Lemma mem_reduceDepsIntToOcc : forall D pub origins y,
        T.DepRel.In y (reduceDepsIntToOcc D pub origins) <->
        exists n v m vs q u,
          C.DepRel.In ((n, v), (m, vs)) D /\ PkgSet.In q origins /\
          Carried pub (n, v) m q /\ VSet.In u vs /\
          y = ((Name.Intermediate n v m q, u),
               (Name.Occurrence m q, T.VSet.singleton u)).
    Proof.
      intros D pub origins y; unfold reduceDepsIntToOcc.
      rewrite SOdtd.mem_unionMap.
      split.
      - intros [[[n v] [m vs]] [HD Hh]]; cbn beta iota in Hh.
        apply SOptd.mem_unionMap in Hh; destruct Hh as [q [Hq Hh]].
        destruct (carriedb pub (n, v) m q) eqn:Hb;
          [| destruct (SOptd.empty_in _ Hh)].
        apply SOvtd.mem_map in Hh; destruct Hh as [u [Hu ->]].
        exists n, v, m, vs, q, u; repeat split;
          [exact HD | exact Hq | apply carriedb_iff; exact Hb | exact Hu].
      - intros [n [v [m [vs [q [u [HD [Hq [Hc [Hu ->]]]]]]]]]].
        exists ((n, v), (m, vs)); split; [exact HD | cbn beta iota].
        apply SOptd.mem_unionMap; exists q; split; [exact Hq |].
        assert (carriedb pub (n, v) m q = true) as ->
          by (apply carriedb_iff; exact Hc).
        apply SOvtd.mem_map; exists u; split; [exact Hu | reflexivity].
    Qed.

    Lemma mem_reduceDepsIntToAgr : forall D pub origins y,
        T.DepRel.In y (reduceDepsIntToAgr D pub origins) <->
        exists n v m vs q u,
          C.DepRel.In ((n, v), (m, vs)) D /\ PkgSet.In q origins /\
          Carried pub (n, v) m q /\ VSet.In u vs /\
          y = ((Name.Intermediate n v m q, u),
               (Name.Agreement n v m, T.VSet.singleton u)).
    Proof.
      intros D pub origins y; unfold reduceDepsIntToAgr.
      rewrite SOdtd.mem_unionMap.
      split.
      - intros [[[n v] [m vs]] [HD Hh]]; cbn beta iota in Hh.
        apply SOptd.mem_unionMap in Hh; destruct Hh as [q [Hq Hh]].
        destruct (carriedb pub (n, v) m q) eqn:Hb;
          [| destruct (SOptd.empty_in _ Hh)].
        apply SOvtd.mem_map in Hh; destruct Hh as [u [Hu ->]].
        exists n, v, m, vs, q, u; repeat split;
          [exact HD | exact Hq | apply carriedb_iff; exact Hb | exact Hu].
      - intros [n [v [m [vs [q [u [HD [Hq [Hc [Hu ->]]]]]]]]]].
        exists ((n, v), (m, vs)); split; [exact HD | cbn beta iota].
        apply SOptd.mem_unionMap; exists q; split; [exact Hq |].
        assert (carriedb pub (n, v) m q = true) as ->
          by (apply carriedb_iff; exact Hc).
        apply SOvtd.mem_map; exists u; split; [exact Hu | reflexivity].
    Qed.

    Lemma mem_reduceDeps : forall R D pub r y,
        T.DepRel.In y (reduceDeps R D pub r) <->
        (exists n v q, PkgSet.In (n, v) R /\
           PkgSet.In q (potentialOrigins R D pub r) /\
           Priv D pub (n, v) /\ q <> (n, v) /\
           y = ((Name.Occurrence n q, v),
                (Name.Occurrence n (n, v), T.VSet.singleton v))) \/
        ((exists n v m vs q,
             C.DepRel.In ((n, v), (m, vs)) D /\
             PkgSet.In q (potentialOrigins R D pub r) /\
             Carried pub (n, v) m q /\
             y = ((Name.Occurrence n q, v),
                  (Name.Intermediate n v m q, embedVS vs))) \/
         ((exists n v m vs q u,
              C.DepRel.In ((n, v), (m, vs)) D /\
              PkgSet.In q (potentialOrigins R D pub r) /\
              Carried pub (n, v) m q /\ VSet.In u vs /\
              y = ((Name.Intermediate n v m q, u),
                   (Name.Occurrence m q, T.VSet.singleton u))) \/
          (exists n v m vs q u,
              C.DepRel.In ((n, v), (m, vs)) D /\
              PkgSet.In q (potentialOrigins R D pub r) /\
              Carried pub (n, v) m q /\ VSet.In u vs /\
              y = ((Name.Intermediate n v m q, u),
                   (Name.Agreement n v m, T.VSet.singleton u))))).
    Proof.
      intros R D pub r y; unfold reduceDeps.
      rewrite !T.DepRel.union_spec, mem_reduceDepsSelf, mem_reduceDepsOccToInt,
        mem_reduceDepsIntToOcc, mem_reduceDepsIntToAgr; reflexivity.
    Qed.

    Lemma mem_reduceReal_occurrence : forall R D pub r n v q,
        PkgSet.In (n, v) R -> PkgSet.In q (potentialOrigins R D pub r) ->
        T.PkgSet.In (Name.Occurrence n q, v) (reduceReal R D pub r).
    Proof.
      intros; apply mem_reduceReal.
      left; exists n, v, q; repeat split; assumption.
    Qed.

    Lemma mem_reduceReal_intermediate : forall R D pub r n v m vs q u,
        C.DepRel.In ((n, v), (m, vs)) D ->
        PkgSet.In q (potentialOrigins R D pub r) -> VSet.In u vs ->
        T.PkgSet.In (Name.Intermediate n v m q, u) (reduceReal R D pub r).
    Proof.
      intros; apply mem_reduceReal.
      right; left; exists n, v, m, vs, q, u; repeat split; assumption.
    Qed.

    Lemma mem_reduceReal_agreement : forall R D pub r n v m vs u,
        C.DepRel.In ((n, v), (m, vs)) D -> VSet.In u vs ->
        T.PkgSet.In (Name.Agreement n v m, u) (reduceReal R D pub r).
    Proof.
      intros; apply mem_reduceReal.
      right; right; exists n, v, m, vs, u; repeat split; assumption.
    Qed.

    Lemma occurrence_mem_reduceReal : forall R D pub r n v q,
        T.PkgSet.In (Name.Occurrence n q, v) (reduceReal R D pub r) ->
        PkgSet.In (n, v) R /\ PkgSet.In q (potentialOrigins R D pub r).
    Proof.
      intros R D pub r n v q H; apply mem_reduceReal in H.
      destruct H as [[n' [v' [q' [HR [Hq Heq]]]]] | [H | H]].
      - injection Heq as <- <- <-; split; [exact HR | exact Hq].
      - destruct H as [n' [v' [m' [vs' [q' [u' [_ [_ [_ Heq]]]]]]]]];
          discriminate Heq.
      - destruct H as [n' [v' [m' [vs' [u' [_ [_ Heq]]]]]]]; discriminate Heq.
    Qed.

    Lemma mem_reduceDeps_self : forall R D pub r n v q,
        PkgSet.In (n, v) R -> PkgSet.In q (potentialOrigins R D pub r) ->
        Priv D pub (n, v) -> q <> (n, v) ->
        T.DepRel.In ((Name.Occurrence n q, v),
                     (Name.Occurrence n (n, v), T.VSet.singleton v))
          (reduceDeps R D pub r).
    Proof.
      intros; apply mem_reduceDeps.
      left; exists n, v, q; repeat split; assumption.
    Qed.

    Lemma mem_reduceDeps_occ2int : forall R D pub r n v m vs q,
        C.DepRel.In ((n, v), (m, vs)) D ->
        PkgSet.In q (potentialOrigins R D pub r) -> Carried pub (n, v) m q ->
        T.DepRel.In ((Name.Occurrence n q, v),
                     (Name.Intermediate n v m q, embedVS vs))
          (reduceDeps R D pub r).
    Proof.
      intros; apply mem_reduceDeps.
      right; left; exists n, v, m, vs, q; repeat split; assumption.
    Qed.

    Lemma mem_reduceDeps_int2occ : forall R D pub r n v m vs q u,
        C.DepRel.In ((n, v), (m, vs)) D ->
        PkgSet.In q (potentialOrigins R D pub r) -> Carried pub (n, v) m q ->
        VSet.In u vs ->
        T.DepRel.In ((Name.Intermediate n v m q, u),
                     (Name.Occurrence m q, T.VSet.singleton u))
          (reduceDeps R D pub r).
    Proof.
      intros; apply mem_reduceDeps.
      right; right; left; exists n, v, m, vs, q, u; repeat split; assumption.
    Qed.

    Lemma mem_reduceDeps_int2agr : forall R D pub r n v m vs q u,
        C.DepRel.In ((n, v), (m, vs)) D ->
        PkgSet.In q (potentialOrigins R D pub r) -> Carried pub (n, v) m q ->
        VSet.In u vs ->
        T.DepRel.In ((Name.Intermediate n v m q, u),
                     (Name.Agreement n v m, T.VSet.singleton u))
          (reduceDeps R D pub r).
    Proof.
      intros; apply mem_reduceDeps.
      right; right; right; exists n, v, m, vs, q, u; repeat split; assumption.
    Qed.

    Definition visibilityResolution (R : PkgSet.t) (D : C.DepRel.t)
        (pub : PubRel.t) (r : Pkg.t) (S : T.PkgSet.t) : PkgSet.t :=
      SOppp.filterExists
        (fun '(n, v) q => T.PkgSet.mem (Name.Occurrence n q, v) S)
        (potentialOrigins R D pub r) R.

    Lemma mem_visibilityResolution : forall R D pub r S n v,
        PkgSet.In (n, v) (visibilityResolution R D pub r S) <->
        PkgSet.In (n, v) R /\
        (exists q, PkgSet.In q (potentialOrigins R D pub r) /\
           T.PkgSet.In (Name.Occurrence n q, v) S).
    Proof.
      intros R D pub r S n v; unfold visibilityResolution.
      rewrite SOppp.mem_filterExists.
      apply and_iff_compat_l; split;
        (intros [q [Hq Hm]]; exists q; split;
         [exact Hq | apply T.PkgSet.mem_spec; exact Hm]).
    Qed.

    Lemma occurrence_mem_visibilityResolution : forall R D pub r S n v q,
        T.PkgSet.Subset S (reduceReal R D pub r) ->
        T.PkgSet.In (Name.Occurrence n q, v) S ->
        PkgSet.In (n, v) (visibilityResolution R D pub r S).
    Proof.
      intros R D pub r S n v q Hsub Hocc.
      destruct (occurrence_mem_reduceReal R D pub r n v q (Hsub _ Hocc))
        as [HR Hq].
      apply mem_visibilityResolution; split; [exact HR |].
      exists q; split; [exact Hq | exact Hocc].
    Qed.

    Definition parentGuardb (R : PkgSet.t) (D : C.DepRel.t) (pub : PubRel.t)
        (r : Pkg.t) (S : T.PkgSet.t) (n : N.t) (v : V.t) (m : N.t) (u : V.t)
        : bool :=
      andb (T.PkgSet.mem (Name.Agreement n v m, u) S)
        (PkgSet.mem (n, v) (visibilityResolution R D pub r S)).

    Lemma parentGuardb_iff : forall R D pub r S n v m u,
        parentGuardb R D pub r S n v m u = true <->
        T.PkgSet.In (Name.Agreement n v m, u) S /\
        PkgSet.In (n, v) (visibilityResolution R D pub r S).
    Proof.
      intros R D pub r S n v m u; unfold parentGuardb.
      rewrite Bool.andb_true_iff, T.PkgSet.mem_spec, PkgSet.mem_spec;
        reflexivity.
    Qed.

    Module SOdpp := Conc.Reduction.SOdpp.
    Module SOvpp := Conc.Reduction.SOvpp.
    Definition parents (R : PkgSet.t) (D : C.DepRel.t) (pub : PubRel.t)
        (r : Pkg.t) (S : T.PkgSet.t) : ParentRel.t :=
      SOdpp.unionMap (fun '((n, v), (m, vs)) =>
          SOvpp.filterMap (fun u =>
              if parentGuardb R D pub r S n v m u
              then Some ((m, u), (n, v))
              else None)
            vs)
        D.

    Lemma mem_parents : forall R D pub r S (pair : ParentElt.t),
        ParentRel.In pair (parents R D pub r S) <->
        exists n v m vs u,
          C.DepRel.In ((n, v), (m, vs)) D /\ VSet.In u vs /\
          T.PkgSet.In (Name.Agreement n v m, u) S /\
          PkgSet.In (n, v) (visibilityResolution R D pub r S) /\
          pair = ((m, u), (n, v)).
    Proof.
      intros R D pub r S pair; unfold parents; rewrite SOdpp.mem_unionMap.
      split.
      - intros [[[n v] [m vs]] [HD Hh]]; cbn beta iota in Hh.
        apply SOvpp.mem_filterMap in Hh; destruct Hh as [u [Hu Hc]];
          cbn beta iota in Hc.
        destruct (parentGuardb R D pub r S n v m u) eqn:Hb; [| discriminate].
        injection Hc as <-.
        apply parentGuardb_iff in Hb; destruct Hb as [H1 H2].
        exists n, v, m, vs, u; repeat split; assumption.
      - intros [n [v [m [vs [u [HD [Hu [Hagr [Hnv ->]]]]]]]]].
        exists ((n, v), (m, vs)); split; [exact HD | cbn beta iota].
        apply SOvpp.mem_filterMap; exists u; split; [exact Hu | cbn beta iota].
        assert (parentGuardb R D pub r S n v m u = true) as ->
          by (apply parentGuardb_iff; split; assumption).
        reflexivity.
    Qed.

    Lemma occurrence_step : forall R D pub r S (n : N.t) (v : V.t) (m : N.t)
        (vs : VSet.t) (q : Pkg.t),
        T.IsResolution (reduceReal R D pub r) (reduceDeps R D pub r)
          (embedRoot r) S ->
        C.DepRel.In ((n, v), (m, vs)) D ->
        PkgSet.In q (potentialOrigins R D pub r) ->
        Carried pub (n, v) m q ->
        T.PkgSet.In (Name.Occurrence n q, v) S ->
        exists u, VSet.In u vs /\
          T.PkgSet.In (Name.Intermediate n v m q, u) S /\
          T.PkgSet.In (Name.Agreement n v m, u) S /\
          T.PkgSet.In (Name.Occurrence m q, u) S.
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
        (m : N.t) (vs : VSet.t) (q : Pkg.t) (u : V.t),
        T.IsResolution (reduceReal R D pub r) (reduceDeps R D pub r)
          (embedRoot r) S ->
        C.DepRel.In ((n, v), (m, vs)) D ->
        PkgSet.In q (potentialOrigins R D pub r) ->
        Carried pub (n, v) m q ->
        T.PkgSet.In (Name.Occurrence n q, v) S ->
        T.PkgSet.In (Name.Agreement n v m, u) S ->
        VSet.In u vs /\ T.PkgSet.In (Name.Occurrence m q, u) S.
    Proof.
      intros R D pub r S n v m vs q u Hres HD Hq Hc Hocc Hagr.
      destruct (occurrence_step R D pub r S n v m vs q Hres HD Hq Hc Hocc)
        as [u' [Hu' [_ [Hagr' Hocc']]]].
      destruct Hres as [_ _ _ Huniq].
      assert (u' = u) as -> by exact (Huniq _ _ _ Hagr' Hagr).
      split; [exact Hu' | exact Hocc'].
    Qed.

    Lemma self_occurrence : forall R D pub r S (n : N.t) (v : V.t) (q : Pkg.t),
        T.IsResolution (reduceReal R D pub r) (reduceDeps R D pub r)
          (embedRoot r) S ->
        PkgSet.In (n, v) R -> PkgSet.In q (potentialOrigins R D pub r) ->
        Priv D pub (n, v) ->
        T.PkgSet.In (Name.Occurrence n q, v) S ->
        T.PkgSet.In (Name.Occurrence n (n, v), v) S.
    Proof.
      intros R D pub r S n v q Hres HR Hq Hpriv Hocc.
      destruct (Pkg.eq_dec q (n, v)) as [-> | NE]; [exact Hocc |].
      destruct Hres as [Hsub Hroot Hdc Huniq].
      destruct (Hdc _ Hocc _ _
                  (mem_reduceDeps_self R D pub r n v q HR Hq Hpriv NE))
        as [w [Hw HwS]].
      apply SOvv.singleton_in in Hw; subst w; exact HwS.
    Qed.

    Lemma base_occurrence : forall R D pub r S (n : N.t) (v : V.t),
        T.IsResolution (reduceReal R D pub r) (reduceDeps R D pub r)
          (embedRoot r) S ->
        PkgSet.In (n, v) (visibilityResolution R D pub r S) ->
        exists c0, PkgSet.In c0 (potentialOrigins R D pub r) /\
          T.PkgSet.In (Name.Occurrence n c0, v) S /\
          (forall (m : N.t) (vs : VSet.t),
             C.DepRel.In ((n, v), (m, vs)) D -> Carried pub (n, v) m c0).
    Proof.
      intros R D pub r S n v Hres Hp.
      apply mem_visibilityResolution in Hp.
      destruct Hp as [HR [q [Hq Hocc]]].
      destruct (privb D pub (n, v)) eqn:Hpb.
      - apply privb_iff in Hpb.
        exists (n, v); split;
          [apply mem_potentialOrigins; right; split; assumption |].
        split;
          [exact (self_occurrence R D pub r S n v q Hres HR Hq Hpb Hocc) |].
        intros m vs _; right; reflexivity.
      - exists q; split; [exact Hq | split; [exact Hocc |]].
        intros m vs HD; left.
        apply (not_priv_pub D pub (n, v) m vs); [| exact HD].
        intro Hpr; apply privb_iff in Hpr; congruence.
    Qed.

    Lemma inSub_occurrence : forall R D pub r S (n : N.t) (v : V.t)
        (c0 c : Pkg.t),
        T.IsResolution (reduceReal R D pub r) (reduceDeps R D pub r)
          (embedRoot r) S ->
        PkgSet.In c0 (potentialOrigins R D pub r) ->
        T.PkgSet.In (Name.Occurrence n c0, v) S ->
        (forall (m : N.t) (vs : VSet.t),
           C.DepRel.In ((n, v), (m, vs)) D -> Carried pub (n, v) m c0) ->
        InSub pub (parents R D pub r S) (n, v) c ->
        T.PkgSet.In (Name.Occurrence (fst c) c0, snd c) S.
    Proof.
      intros R D pub r S n v c0 c Hres Hc0 Hocc Htr Hins.
      induction Hins as [| c He | p m u Hp IH He Hm].
      - exact Hocc.
      - destruct c as [cn cv].
        apply mem_parents in He.
        destruct He as [n2 [v2 [m2 [vs2 [u2 [HD [Hu2 [Hagr [_ Heq]]]]]]]]].
        injection Heq as <- <- <- <-.
        exact (proj2 (occurrence_step_at R D pub r S n v cn vs2 c0 cv Hres HD
                        Hc0 (Htr cn vs2 HD) Hocc Hagr)).
      - destruct p as [pn pv].
        apply mem_parents in He.
        destruct He as [n2 [v2 [m2 [vs2 [u2 [HD [Hu2 [Hagr [_ Heq]]]]]]]]].
        injection Heq as <- <- <- <-.
        exact (proj2 (occurrence_step_at R D pub r S pn pv m vs2 c0 u Hres HD
                        Hc0 (or_introl Hm) IH Hagr)).
    Qed.

    Theorem visibility_soundness :
      forall (R : PkgSet.t) (D : C.DepRel.t) (pub : PubRel.t) (r : Pkg.t)
             (S : T.PkgSet.t),
        T.IsResolution (reduceReal R D pub r) (reduceDeps R D pub r)
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
          exists u; split.
          * split; [exact Hu | split].
            -- exact (occurrence_mem_visibilityResolution R D pub r S m u c0
                        Hsub Hcp).
            -- apply mem_parents.
               exists pn, pv, m, vs, u; repeat split; assumption.
          * intros u' [_ [_ Hpi']].
            apply mem_parents in Hpi'.
            destruct Hpi'
              as [n2 [v2 [m2 [vs2 [u2 [_ [_ [Hagr2 [_ Heq]]]]]]]]].
            injection Heq as <- <- <- <-.
            exact (Huniq _ _ _ Hagr Hagr2).
        + intros n v v' _ _ Hne; exact Hne.
        + intros c p Hcp; apply mem_parents in Hcp.
          destruct Hcp as [n [v [m [vs [u [HD [Hu [Hagr [Hnv Heq]]]]]]]]].
          injection Heq as -> ->.
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
        assert (H1 : T.PkgSet.In (Name.Occurrence n c0, v) S)
          by exact (inSub_occurrence R D pub r S pn pv c0 (n, v) Hres Hc0 Hocc
                      Htr Hv).
        assert (H2 : T.PkgSet.In (Name.Occurrence n c0, v') S)
          by exact (inSub_occurrence R D pub r S pn pv c0 (n, v') Hres Hc0 Hocc
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

    Definition coreResolutionOccurrence (D : C.DepRel.t) (pub : PubRel.t)
        (r : Pkg.t) (S : PkgSet.t) (pi : ParentRel.t) (origins : PkgSet.t)
        : T.PkgSet.t :=
      SOptp.unionMap (fun '(n, v) =>
          SOptp.filterMap (fun q =>
              if andb (isOriginb D pub r S q)
                   (PkgSet.mem (n, v) (sub pub pi q))
              then Some (Name.Occurrence n q, v)
              else None)
            origins)
        S.

    Definition coreResolutionIntermediate (D : C.DepRel.t) (pub : PubRel.t)
        (r : Pkg.t) (S : PkgSet.t) (pi : ParentRel.t) (origins : PkgSet.t)
        : T.PkgSet.t :=
      SOdtp.unionMap (fun '((n, v), (m, vs)) =>
          SOptp.unionMap (fun q =>
              if andb (isOriginb D pub r S q)
                   (andb (PkgSet.mem (n, v) (sub pub pi q))
                      (carriedb pub (n, v) m q))
              then SOvtp.filterMap (fun u =>
                       if edgeb pi n v m u
                       then Some (Name.Intermediate n v m q, u)
                       else None)
                     vs
              else T.PkgSet.empty)
            origins)
        D.

    Definition coreResolutionAgreement (D : C.DepRel.t) (S : PkgSet.t)
        (pi : ParentRel.t) : T.PkgSet.t :=
      SOdtp.unionMap (fun '((n, v), (m, vs)) =>
          if PkgSet.mem (n, v) S
          then SOvtp.filterMap (fun u =>
                   if edgeb pi n v m u
                   then Some (Name.Agreement n v m, u)
                   else None)
                 vs
          else T.PkgSet.empty)
        D.

    Definition coreResolution (R : PkgSet.t) (D : C.DepRel.t) (pub : PubRel.t)
        (r : Pkg.t) (S : PkgSet.t) (pi : ParentRel.t) : T.PkgSet.t :=
      T.PkgSet.union
        (coreResolutionOccurrence D pub r S pi (potentialOrigins R D pub r))
        (T.PkgSet.union
           (coreResolutionIntermediate D pub r S pi
              (potentialOrigins R D pub r))
           (coreResolutionAgreement D S pi)).

    Lemma mem_coreResolutionOccurrence : forall D pub r S pi origins y,
        T.PkgSet.In y (coreResolutionOccurrence D pub r S pi origins) <->
        exists n v q, PkgSet.In (n, v) S /\ PkgSet.In q origins /\
          IsOrigin D pub r S q /\ InSub pub pi q (n, v) /\
          y = (Name.Occurrence n q, v).
    Proof.
      intros D pub r S pi origins y; unfold coreResolutionOccurrence.
      rewrite SOptp.mem_unionMap.
      split.
      - intros [[n v] [HS Hh]]; cbn beta iota in Hh.
        apply SOptp.mem_filterMap in Hh; destruct Hh as [q [Hq Hc]];
          cbn beta iota in Hc.
        destruct (andb (isOriginb D pub r S q)
                    (PkgSet.mem (n, v) (sub pub pi q))) eqn:Hb;
          [| discriminate].
        injection Hc as <-.
        apply Bool.andb_true_iff in Hb; destruct Hb as [H1 H2].
        apply isOriginb_iff in H1.
        apply PkgSet.mem_spec in H2; apply mem_sub in H2.
        exists n, v, q; repeat split; assumption.
      - intros [n [v [q [HS [Hq [Ho [Hins ->]]]]]]].
        exists (n, v); split; [exact HS | cbn beta iota].
        apply SOptp.mem_filterMap; exists q; split; [exact Hq | cbn beta iota].
        assert (andb (isOriginb D pub r S q)
                  (PkgSet.mem (n, v) (sub pub pi q)) = true) as ->
          by (apply Bool.andb_true_iff; split;
              [apply isOriginb_iff; exact Ho
              | apply PkgSet.mem_spec, mem_sub; exact Hins]).
        reflexivity.
    Qed.

    Lemma mem_coreResolutionIntermediate : forall D pub r S pi origins y,
        T.PkgSet.In y (coreResolutionIntermediate D pub r S pi origins) <->
        exists n v m vs q u,
          C.DepRel.In ((n, v), (m, vs)) D /\ PkgSet.In q origins /\
          VSet.In u vs /\ IsOrigin D pub r S q /\ InSub pub pi q (n, v) /\
          Carried pub (n, v) m q /\ ParentRel.In ((m, u), (n, v)) pi /\
          y = (Name.Intermediate n v m q, u).
    Proof.
      intros D pub r S pi origins y; unfold coreResolutionIntermediate.
      rewrite SOdtp.mem_unionMap.
      split.
      - intros [[[n v] [m vs]] [HD Hh]]; cbn beta iota in Hh.
        apply SOptp.mem_unionMap in Hh; destruct Hh as [q [Hq Hh]].
        destruct (andb (isOriginb D pub r S q)
                    (andb (PkgSet.mem (n, v) (sub pub pi q))
                       (carriedb pub (n, v) m q))) eqn:Hb;
          [| destruct (SOptp.empty_in _ Hh)].
        apply SOvtp.mem_filterMap in Hh; destruct Hh as [u [Hu Hc]];
          cbn beta iota in Hc.
        destruct (edgeb pi n v m u) eqn:Hp; [| discriminate].
        injection Hc as <-.
        apply Bool.andb_true_iff in Hb; destruct Hb as [H1 Hb].
        apply Bool.andb_true_iff in Hb; destruct Hb as [H2 H3].
        apply isOriginb_iff in H1.
        apply PkgSet.mem_spec in H2; apply mem_sub in H2.
        apply carriedb_iff in H3; apply edgeb_iff in Hp.
        exists n, v, m, vs, q, u; repeat split; assumption.
      - intros [n [v [m [vs [q [u
            [HD [Hq [Hu [Ho [Hins [Hc [Hpi ->]]]]]]]]]]]]].
        exists ((n, v), (m, vs)); split; [exact HD | cbn beta iota].
        apply SOptp.mem_unionMap; exists q; split; [exact Hq |].
        assert (andb (isOriginb D pub r S q)
                  (andb (PkgSet.mem (n, v) (sub pub pi q))
                     (carriedb pub (n, v) m q)) = true) as ->.
        { apply Bool.andb_true_iff; split; [apply isOriginb_iff; exact Ho |].
          apply Bool.andb_true_iff; split;
            [apply PkgSet.mem_spec, mem_sub; exact Hins
            | apply carriedb_iff; exact Hc]. }
        apply SOvtp.mem_filterMap; exists u; split; [exact Hu | cbn beta iota].
        assert (edgeb pi n v m u = true) as ->
          by (apply edgeb_iff; exact Hpi).
        reflexivity.
    Qed.

    Lemma mem_coreResolutionAgreement : forall D S pi y,
        T.PkgSet.In y (coreResolutionAgreement D S pi) <->
        exists n v m vs u,
          C.DepRel.In ((n, v), (m, vs)) D /\ VSet.In u vs /\
          PkgSet.In (n, v) S /\ ParentRel.In ((m, u), (n, v)) pi /\
          y = (Name.Agreement n v m, u).
    Proof.
      intros D S pi y; unfold coreResolutionAgreement.
      rewrite SOdtp.mem_unionMap.
      split.
      - intros [[[n v] [m vs]] [HD Hh]]; cbn beta iota in Hh.
        destruct (PkgSet.mem (n, v) S) eqn:Hs;
          [| destruct (SOptp.empty_in _ Hh)].
        apply SOvtp.mem_filterMap in Hh; destruct Hh as [u [Hu Hc]];
          cbn beta iota in Hc.
        destruct (edgeb pi n v m u) eqn:Hp; [| discriminate].
        injection Hc as <-.
        apply PkgSet.mem_spec in Hs; apply edgeb_iff in Hp.
        exists n, v, m, vs, u; repeat split; assumption.
      - intros [n [v [m [vs [u [HD [Hu [HS [Hpi ->]]]]]]]]].
        exists ((n, v), (m, vs)); split; [exact HD | cbn beta iota].
        assert (PkgSet.mem (n, v) S = true) as ->
          by (apply PkgSet.mem_spec; exact HS).
        apply SOvtp.mem_filterMap; exists u; split; [exact Hu | cbn beta iota].
        assert (edgeb pi n v m u = true) as ->
          by (apply edgeb_iff; exact Hpi).
        reflexivity.
    Qed.

    Lemma mem_coreResolution : forall R D pub r S pi y,
        T.PkgSet.In y (coreResolution R D pub r S pi) <->
        (exists n v q, PkgSet.In (n, v) S /\
           PkgSet.In q (potentialOrigins R D pub r) /\
           IsOrigin D pub r S q /\ InSub pub pi q (n, v) /\
           y = (Name.Occurrence n q, v)) \/
        ((exists n v m vs q u,
             C.DepRel.In ((n, v), (m, vs)) D /\
             PkgSet.In q (potentialOrigins R D pub r) /\ VSet.In u vs /\
             IsOrigin D pub r S q /\ InSub pub pi q (n, v) /\
             Carried pub (n, v) m q /\ ParentRel.In ((m, u), (n, v)) pi /\
             y = (Name.Intermediate n v m q, u)) \/
         (exists n v m vs u,
             C.DepRel.In ((n, v), (m, vs)) D /\ VSet.In u vs /\
             PkgSet.In (n, v) S /\ ParentRel.In ((m, u), (n, v)) pi /\
             y = (Name.Agreement n v m, u))).
    Proof.
      intros R D pub r S pi y; unfold coreResolution.
      rewrite !T.PkgSet.union_spec, mem_coreResolutionOccurrence,
        mem_coreResolutionIntermediate, mem_coreResolutionAgreement;
        reflexivity.
    Qed.

    Lemma mem_coreResolution_occurrence : forall R D pub r S pi n v q,
        PkgSet.In (n, v) S -> PkgSet.In q (potentialOrigins R D pub r) ->
        IsOrigin D pub r S q -> InSub pub pi q (n, v) ->
        T.PkgSet.In (Name.Occurrence n q, v) (coreResolution R D pub r S pi).
    Proof.
      intros; apply mem_coreResolution.
      left; exists n, v, q; repeat split; assumption.
    Qed.

    Lemma mem_coreResolution_intermediate :
      forall R D pub r S pi n v m vs q u,
        C.DepRel.In ((n, v), (m, vs)) D ->
        PkgSet.In q (potentialOrigins R D pub r) -> VSet.In u vs ->
        IsOrigin D pub r S q -> InSub pub pi q (n, v) ->
        Carried pub (n, v) m q -> ParentRel.In ((m, u), (n, v)) pi ->
        T.PkgSet.In (Name.Intermediate n v m q, u)
          (coreResolution R D pub r S pi).
    Proof.
      intros; apply mem_coreResolution.
      right; left; exists n, v, m, vs, q, u; repeat split; assumption.
    Qed.

    Lemma mem_coreResolution_agreement : forall R D pub r S pi n v m vs u,
        C.DepRel.In ((n, v), (m, vs)) D -> VSet.In u vs ->
        PkgSet.In (n, v) S -> ParentRel.In ((m, u), (n, v)) pi ->
        T.PkgSet.In (Name.Agreement n v m, u) (coreResolution R D pub r S pi).
    Proof.
      intros; apply mem_coreResolution.
      right; right; exists n, v, m, vs, u; repeat split; assumption.
    Qed.

    Theorem visibility_completeness :
      forall (R : PkgSet.t) (D : C.DepRel.t) (pub : PubRel.t) (r : Pkg.t)
             (S : PkgSet.t) (pi : ParentRel.t),
        C.FunctionalInName D ->
        IsResolution R D pub r S pi ->
        T.IsResolution (reduceReal R D pub r) (reduceDeps R D pub r)
          (embedRoot r) (coreResolution R D pub r S pi).
    Proof.
      intros R D pub r S pi Hfunc Hres.
      destruct Hres as [Hconc Hvv].
      destruct Hconc as [Hsub Hroot Hpc Hvg Hps].
      constructor.
      - intros y Hy; apply mem_coreResolution in Hy.
        destruct Hy as [Hy | [Hy | Hy]].
        + destruct Hy as [n [v [q [HS [Hq [_ [_ ->]]]]]]].
          exact (mem_reduceReal_occurrence R D pub r n v q (Hsub _ HS) Hq).
        + destruct Hy
            as [n [v [m [vs [q [u [HD [Hq [Hu [_ [_ [_ [_ ->]]]]]]]]]]]]].
          exact (mem_reduceReal_intermediate R D pub r n v m vs q u HD Hq Hu).
        + destruct Hy as [n [v [m [vs [u [HD [Hu [_ [_ ->]]]]]]]]].
          exact (mem_reduceReal_agreement R D pub r n v m vs u HD Hu).
      - destruct r as [rn rv].
        exact (mem_coreResolution_occurrence R D pub (rn, rv) S pi rn rv
                 (rn, rv) Hroot
                 (proj2 (mem_potentialOrigins R D pub (rn, rv) (rn, rv))
                    (or_introl eq_refl))
                 (or_introl eq_refl) (InSubSelf pub pi (rn, rv))).
      - intros y Hy tn tvs Hd.
        apply mem_coreResolution in Hy; apply mem_reduceDeps in Hd.
        destruct Hy as [Hy | [Hy | Hy]].
        + destruct Hy as [n [v [q [HS [Hq [Ho [Hins ->]]]]]]].
          destruct Hd as [Hd | [Hd | [Hd | Hd]]].
          * destruct Hd as [n1 [v1 [q1 [HR1 [Hq1 [Hpriv1 [Hne1 Heq]]]]]]].
            injection Heq as <- <- <- -> ->.
            exists v; split; [apply SOvv.singleton_in; reflexivity |].
            apply (mem_coreResolution_occurrence R D pub r S pi n v (n, v));
              [exact HS
              | apply mem_potentialOrigins; right; split; assumption
              | right; split; assumption
              | apply InSubSelf].
          * destruct Hd as [n1 [v1 [m1 [vs1 [q1 [HD1 [Hq1 [Hc1 Heq]]]]]]]].
            injection Heq as <- <- <- -> ->.
            destruct (Hpc (n, v) HS m1 vs1 HD1) as [u [[Hu [HmS Hpi]] _]].
            exists u; split; [apply mem_embedVS; exact Hu |].
            exact (mem_coreResolution_intermediate R D pub r S pi n v m1 vs1
                     q u HD1 Hq Hu Ho Hins Hc1 Hpi).
          * destruct Hd
              as [n1 [v1 [m1 [vs1 [q1 [u1 [_ [_ [_ [_ Heq]]]]]]]]]];
              discriminate Heq.
          * destruct Hd
              as [n1 [v1 [m1 [vs1 [q1 [u1 [_ [_ [_ [_ Heq]]]]]]]]]];
              discriminate Heq.
        + destruct Hy
            as [n [v [m [vs [q [u
                [HD [Hq [Hu [Ho [Hins [Hc [Hpi ->]]]]]]]]]]]]].
          destruct Hd as [Hd | [Hd | [Hd | Hd]]].
          * destruct Hd as [n1 [v1 [q1 [_ [_ [_ [_ Heq]]]]]]];
              discriminate Heq.
          * destruct Hd as [n1 [v1 [m1 [vs1 [q1 [_ [_ [_ Heq]]]]]]]];
              discriminate Heq.
          * destruct Hd
              as [n1 [v1 [m1 [vs1 [q1 [u1 [HD1 [Hq1 [Hc1 [Hu1 Heq]]]]]]]]]].
            injection Heq as <- <- <- <- <- -> ->.
            exists u; split; [apply SOvv.singleton_in; reflexivity |].
            apply (mem_coreResolution_occurrence R D pub r S pi m u q);
              [exact (proj1 (Hps _ _ Hpi)) | exact Hq | exact Ho |].
            destruct Hc as [Hpub | Heq0];
              [exact (InSubPubStep pub pi q (n, v) m u Hins Hpi Hpub) |].
            rewrite Heq0 in Hpi; exact (InSubChild pub pi q (m, u) Hpi).
          * destruct Hd
              as [n1 [v1 [m1 [vs1 [q1 [u1 [HD1 [Hq1 [Hc1 [Hu1 Heq]]]]]]]]]].
            injection Heq as <- <- <- <- <- -> ->.
            exists u; split; [apply SOvv.singleton_in; reflexivity |].
            exact (mem_coreResolution_agreement R D pub r S pi n v m vs1 u
                     HD1 Hu1 (proj2 (Hps _ _ Hpi)) Hpi).
        + destruct Hy as [n [v [m [vs [u [HD [Hu [HS [Hpi ->]]]]]]]]].
          destruct Hd as [Hd | [Hd | [Hd | Hd]]].
          * destruct Hd as [n1 [v1 [q1 [_ [_ [_ [_ Heq]]]]]]];
              discriminate Heq.
          * destruct Hd as [n1 [v1 [m1 [vs1 [q1 [_ [_ [_ Heq]]]]]]]];
              discriminate Heq.
          * destruct Hd
              as [n1 [v1 [m1 [vs1 [q1 [u1 [_ [_ [_ [_ Heq]]]]]]]]]];
              discriminate Heq.
          * destruct Hd
              as [n1 [v1 [m1 [vs1 [q1 [u1 [_ [_ [_ [_ Heq]]]]]]]]]];
              discriminate Heq.
      - intros nm w1 w2 H1 H2.
        apply mem_coreResolution in H1; apply mem_coreResolution in H2.
        destruct H1 as [H1 | [H1 | H1]]; destruct H2 as [H2 | [H2 | H2]].
        + destruct H1 as [n1 [v1 [q1 [HS1 [Hq1 [Ho1 [Hins1 Heq1]]]]]]].
          destruct H2 as [n2 [v2 [q2 [HS2 [Hq2 [Ho2 [Hins2 Heq2]]]]]]].
          injection Heq1 as -> <-; injection Heq2 as <- <- <-.
          exact (Hvv q1 (isOrigin_mem D pub r S q1 Ho1 Hroot) n1 w1 w2
                   Hins1 Hins2).
        + destruct H1 as [n1 [v1 [q1 [_ [_ [_ [_ Heq1]]]]]]].
          destruct H2
            as [n2 [v2 [m2 [vs2 [q2 [u2 [_ [_ [_ [_ [_ [_ [_ Heq2]]]]]]]]]]]]].
          injection Heq1 as -> <-; discriminate Heq2.
        + destruct H1 as [n1 [v1 [q1 [_ [_ [_ [_ Heq1]]]]]]].
          destruct H2 as [n2 [v2 [m2 [vs2 [u2 [_ [_ [_ [_ Heq2]]]]]]]]].
          injection Heq1 as -> <-; discriminate Heq2.
        + destruct H1
            as [n1 [v1 [m1 [vs1 [q1 [u1 [_ [_ [_ [_ [_ [_ [_ Heq1]]]]]]]]]]]]].
          destruct H2 as [n2 [v2 [q2 [_ [_ [_ [_ Heq2]]]]]]].
          injection Heq1 as -> <-; discriminate Heq2.
        + destruct H1
            as [n1 [v1 [m1 [vs1 [q1 [u1
                [HD1 [_ [Hu1 [_ [_ [_ [Hpi1 Heq1]]]]]]]]]]]]].
          destruct H2
            as [n2 [v2 [m2 [vs2 [q2 [u2
                [HD2 [_ [Hu2 [_ [_ [_ [Hpi2 Heq2]]]]]]]]]]]]].
          injection Heq1 as -> <-; injection Heq2 as <- <- <- <- <-.
          assert (vs2 = vs1) as -> by exact (Hfunc _ _ _ _ HD2 HD1).
          destruct (Hpc (n1, v1) (proj2 (Hps _ _ Hpi1)) m1 vs1 HD1)
            as [u0 [_ Huniq0]].
          pose proof (Huniq0 w1 (conj Hu1 (conj (proj1 (Hps _ _ Hpi1)) Hpi1)))
            as E1.
          pose proof (Huniq0 w2 (conj Hu2 (conj (proj1 (Hps _ _ Hpi2)) Hpi2)))
            as E2.
          congruence.
        + destruct H1
            as [n1 [v1 [m1 [vs1 [q1 [u1 [_ [_ [_ [_ [_ [_ [_ Heq1]]]]]]]]]]]]].
          destruct H2 as [n2 [v2 [m2 [vs2 [u2 [_ [_ [_ [_ Heq2]]]]]]]]].
          injection Heq1 as -> <-; discriminate Heq2.
        + destruct H1 as [n1 [v1 [m1 [vs1 [u1 [_ [_ [_ [_ Heq1]]]]]]]]].
          destruct H2 as [n2 [v2 [q2 [_ [_ [_ [_ Heq2]]]]]]].
          injection Heq1 as -> <-; discriminate Heq2.
        + destruct H1 as [n1 [v1 [m1 [vs1 [u1 [_ [_ [_ [_ Heq1]]]]]]]]].
          destruct H2
            as [n2 [v2 [m2 [vs2 [q2 [u2 [_ [_ [_ [_ [_ [_ [_ Heq2]]]]]]]]]]]]].
          injection Heq1 as -> <-; discriminate Heq2.
        + destruct H1
            as [n1 [v1 [m1 [vs1 [u1 [HD1 [Hu1 [HS1 [Hpi1 Heq1]]]]]]]]].
          destruct H2
            as [n2 [v2 [m2 [vs2 [u2 [HD2 [Hu2 [_ [Hpi2 Heq2]]]]]]]]].
          injection Heq1 as -> <-; injection Heq2 as <- <- <- <-.
          assert (vs2 = vs1) as -> by exact (Hfunc _ _ _ _ HD2 HD1).
          destruct (Hpc (n1, v1) HS1 m1 vs1 HD1) as [u0 [_ Huniq0]].
          pose proof (Huniq0 w1 (conj Hu1 (conj (proj1 (Hps _ _ Hpi1)) Hpi1)))
            as E1.
          pose proof (Huniq0 w2 (conj Hu2 (conj (proj1 (Hps _ _ Hpi2)) Hpi2)))
            as E2.
          congruence.
    Qed.

    Module Lookup.
      Module DepFibred :=
        FibredLabelledRel Pkg N VSet.AsUOT C.DepElt C.DepRel.
      Module PubFibred := FibredRel Pkg N PubElt PubRel.
      Module PkgPreimage := PreimageOfKeys Pkg Pkg PkgSet PkgSet.

      Definition realPreimage (R : PkgSet.t) (ps : PkgSet.t) : PkgSet.t :=
        PkgPreimage.ofKeys (fun p : Pkg.t => p) ps R.

      Lemma mem_realPreimage : forall R ps (p : Pkg.t),
          PkgSet.In p (realPreimage R ps) <-> PkgSet.In p R /\ PkgSet.In p ps.
      Proof.
        intros R ps p; unfold realPreimage.
        rewrite PkgPreimage.mem_ofKeys; reflexivity.
      Qed.

      Lemma realPreimage_subset : forall R ps,
          PkgSet.Subset (realPreimage R ps) R.
      Proof. intros R ps; apply PkgPreimage.ofKeys_subset. Qed.

      Definition depBlocks (D : C.DepRel.t) (p q : Pkg.t) : C.DepRel.t :=
        C.DepRel.union (DepFibred.tailFibre D p) (DepFibred.tailFibre D q).

      Definition pubBlocks (pub : PubRel.t) (p q : Pkg.t) : PubRel.t :=
        PubRel.union (PubFibred.tailFibre pub p) (PubFibred.tailFibre pub q).

      Lemma mem_depBlocks : forall D p q (x : Pkg.t) (m : N.t) (vs : VSet.t),
          C.DepRel.In (x, (m, vs)) (depBlocks D p q) <->
          C.DepRel.In (x, (m, vs)) D /\ (x = p \/ x = q).
      Proof.
        intros D p q x m vs; unfold depBlocks.
        rewrite C.DepRel.union_spec, !DepFibred.mem_tailFibre; tauto.
      Qed.

      Lemma mem_pubBlocks : forall pub p q (x : Pkg.t) (m : N.t),
          PubRel.In (x, m) (pubBlocks pub p q) <->
          PubRel.In (x, m) pub /\ (x = p \/ x = q).
      Proof.
        intros pub p q x m; unfold pubBlocks.
        rewrite PubRel.union_spec, !PubFibred.mem_tailFibre; tauto.
      Qed.

      Lemma depBlocks_subset : forall D p q,
          C.DepRel.Subset (depBlocks D p q) D.
      Proof.
        intros D p q [x [m vs]] H; apply mem_depBlocks in H; exact (proj1 H).
      Qed.

      Lemma pubBlocks_subset : forall pub p q,
          PubRel.Subset (pubBlocks pub p q) pub.
      Proof.
        intros pub p q [x m] H; apply mem_pubBlocks in H; exact (proj1 H).
      Qed.

      Lemma Priv_block : forall D D' pub pub' (p : Pkg.t),
          C.DepRel.Subset (DepFibred.tailFibre D p) D' ->
          C.DepRel.Subset D' D ->
          PubRel.Subset (PubFibred.tailFibre pub p) pub' ->
          PubRel.Subset pub' pub ->
          (Priv D' pub' p <-> Priv D pub p).
      Proof.
        intros D D' pub pub' p HDl HDr Hpl Hpr; split.
        - intros [n [vs [He Hn]]]; exists n, vs; split; [exact (HDr _ He) |].
          intro Hin; apply Hn, Hpl, PubFibred.mem_tailFibre.
          split; [exact Hin | reflexivity].
        - intros [n [vs [He Hn]]]; exists n, vs; split.
          + apply HDl, DepFibred.mem_tailFibre; split; [exact He | reflexivity].
          + intro Hin; exact (Hn (Hpr _ Hin)).
      Qed.

      Lemma priv_blocks : forall D pub (p q x : Pkg.t),
          x = p \/ x = q ->
          (Priv (depBlocks D p q) (pubBlocks pub p q) x <-> Priv D pub x).
      Proof.
        intros D pub p q x Hx; apply Priv_block.
        - intros [y [m vs]] He; apply DepFibred.mem_tailFibre in He.
          destruct He as [HD ->]; apply mem_depBlocks.
          split; [exact HD | exact Hx].
        - apply depBlocks_subset.
        - intros [y m] He; apply PubFibred.mem_tailFibre in He.
          destruct He as [Hp ->]; apply mem_pubBlocks.
          split; [exact Hp | exact Hx].
        - apply pubBlocks_subset.
      Qed.

      Lemma priv_blocks_mono : forall D pub (p q x : Pkg.t),
          Priv (depBlocks D p q) (pubBlocks pub p q) x -> Priv D pub x.
      Proof.
        intros D pub p q x Hpriv.
        assert (Hx : x = p \/ x = q).
        { destruct Hpriv as [n [vs [He _]]].
          exact (proj2 (proj1 (mem_depBlocks D p q x n vs) He)). }
        exact (proj1 (priv_blocks D pub p q x Hx) Hpriv).
      Qed.

      Lemma carried_blocks : forall pub (p : Pkg.t) (m : N.t) (q : Pkg.t),
          Carried pub p m q -> Carried (pubBlocks pub p q) p m q.
      Proof.
        intros pub p m q [Hin | ->]; [left | right; reflexivity].
        apply mem_pubBlocks; split; [exact Hin | left; reflexivity].
      Qed.

      Lemma carriedb_mono : forall pub pub' (p : Pkg.t) (m : N.t) (q : Pkg.t),
          PubRel.Subset pub' pub -> carriedb pub' p m q = true ->
          carriedb pub p m q = true.
      Proof.
        intros pub pub' p m q Hs Hb.
        apply carriedb_iff in Hb; apply carriedb_iff.
        destruct Hb as [Hb | ->]; [left; exact (Hs _ Hb) | right; reflexivity].
      Qed.

      Lemma potentialOrigins_mono : forall R R' D D' pub pub' r,
          PkgSet.Subset R' R ->
          (forall p, Priv D' pub' p -> Priv D pub p) ->
          PkgSet.Subset (potentialOrigins R' D' pub' r)
            (potentialOrigins R D pub r).
      Proof.
        intros R R' D D' pub pub' r HR Hpriv q Hq.
        apply mem_potentialOrigins in Hq; apply mem_potentialOrigins.
        destruct Hq as [-> | [HqR Hqp]]; [left; reflexivity |].
        right; split; [exact (HR _ HqR) | exact (Hpriv _ Hqp)].
      Qed.

      Lemma potentialOrigins_blocks : forall R D pub r ps (p q : Pkg.t),
          PkgSet.In q ps -> PkgSet.In q (potentialOrigins R D pub r) ->
          PkgSet.In q (potentialOrigins (realPreimage R ps) (depBlocks D p q)
                         (pubBlocks pub p q) r).
      Proof.
        intros R D pub r ps p q Hps Hq.
        apply mem_potentialOrigins in Hq; apply mem_potentialOrigins.
        destruct Hq as [-> | [HqR Hqp]]; [left; reflexivity |].
        right; split; [apply mem_realPreimage; split; assumption |].
        apply priv_blocks; [right; reflexivity | exact Hqp].
      Qed.

      (* Privacy is antitone in pub, so containment of the sliced pub does
         not by itself transfer the guards that read it; the premise carries
         what the slices in use establish instead. *)
      Lemma reduceDeps_mono : forall R R' D D' pub pub' r (y : T.DepElt.t),
          PkgSet.Subset R' R -> C.DepRel.Subset D' D ->
          PubRel.Subset pub' pub ->
          (forall p, Priv D' pub' p -> Priv D pub p) ->
          T.DepRel.In y (reduceDeps R' D' pub' r) ->
          T.DepRel.In y (reduceDeps R D pub r).
      Proof.
        intros R R' D D' pub pub' r y HR HD Hpub Hpriv; revert y.
        pose proof (potentialOrigins_mono R R' D D' pub pub' r HR Hpriv) as Ho.
        unfold reduceDeps, reduceDepsSelf, reduceDepsOccToInt,
          reduceDepsIntToOcc, reduceDepsIntToAgr.
        repeat apply SOdtd.union_subset.
        - apply SOptd.unionMap_mono; [exact HR |].
          intros [n v]; cbn beta iota.
          apply SOptd.filterMap_mono; [exact Ho |].
          intros q z Hz; cbn beta iota in Hz |- *.
          destruct (andb (privb D' pub' (n, v)) (negb (PkgEqb.eqb q (n, v))))
            eqn:Hb; [| discriminate Hz].
          apply Bool.andb_true_iff in Hb; destruct Hb as [H1 H2].
          assert (privb D pub (n, v) = true) as H1'
            by (apply privb_iff; apply Hpriv; apply privb_iff; exact H1).
          rewrite H1', H2; exact Hz.
        - apply SOdtd.unionMap_mono; [exact HD |].
          intros [[n v] [m vs]]; cbn beta iota.
          apply SOptd.filterMap_mono; [exact Ho |].
          intros q z Hz; cbn beta iota in Hz |- *.
          destruct (carriedb pub' (n, v) m q) eqn:Hb; [| discriminate Hz].
          assert (carriedb pub (n, v) m q = true) as ->
            by exact (carriedb_mono pub pub' (n, v) m q Hpub Hb).
          exact Hz.
        - apply SOdtd.unionMap_mono; [exact HD |].
          intros [[n v] [m vs]]; cbn beta iota.
          apply SOptd.unionMap_mono; [exact Ho |].
          intro q; cbn beta iota.
          destruct (carriedb pub' (n, v) m q) eqn:Hb;
            [| apply T.DepRel.empty_subset].
          assert (carriedb pub (n, v) m q = true) as ->
            by exact (carriedb_mono pub pub' (n, v) m q Hpub Hb).
          apply SOvtd.map_mono; [intros z Hz; exact Hz | intro; reflexivity].
        - apply SOdtd.unionMap_mono; [exact HD |].
          intros [[n v] [m vs]]; cbn beta iota.
          apply SOptd.unionMap_mono; [exact Ho |].
          intro q; cbn beta iota.
          destruct (carriedb pub' (n, v) m q) eqn:Hb;
            [| apply T.DepRel.empty_subset].
          assert (carriedb pub (n, v) m q = true) as ->
            by exact (carriedb_mono pub pub' (n, v) m q Hpub Hb).
          apply SOvtd.map_mono; [intros z Hz; exact Hz | intro; reflexivity].
      Qed.

      Theorem dependees_lookupOccurrence :
        forall R D pub r (n : N.t) (v : V.t) (q : Pkg.t),
          T.dependees (reduceDeps R D pub r) (Name.Occurrence n q, v) =
          T.dependees
            (reduceDeps
               (realPreimage R (PkgSet.add (n, v) (PkgSet.singleton q)))
               (depBlocks D (n, v) q) (pubBlocks pub (n, v) q) r)
            (Name.Occurrence n q, v).
      Proof.
        intros R D pub r n v q; apply T.dependees_ext; intros [tn tvs].
        split;
          [| intro H;
             exact (reduceDeps_mono R _ D _ pub _ r _
                      (realPreimage_subset R _) (depBlocks_subset D (n, v) q)
                      (pubBlocks_subset pub (n, v) q)
                      (priv_blocks_mono D pub (n, v) q) H)].
        intro H; apply mem_reduceDeps in H; apply mem_reduceDeps.
        destruct H as [H | [H | [H | H]]].
        - destruct H as [n1 [v1 [q1 [HR [Hq1 [Hpriv [Hne Heq]]]]]]].
          injection Heq as <- <- <- -> ->.
          left; exists n, v, q; repeat split.
          + apply mem_realPreimage; split;
              [exact HR | apply SOppp.add_in; left; reflexivity].
          + apply potentialOrigins_blocks; [| exact Hq1].
            apply SOppp.add_in; right; apply SOppp.singleton_in; reflexivity.
          + apply priv_blocks; [left; reflexivity | exact Hpriv].
          + exact Hne.
        - destruct H as [n1 [v1 [m [vs [q1 [HD1 [Hq1 [Hc Heq]]]]]]]].
          injection Heq as <- <- <- -> ->.
          right; left; exists n, v, m, vs, q; repeat split.
          + apply mem_depBlocks; split; [exact HD1 | left; reflexivity].
          + apply potentialOrigins_blocks; [| exact Hq1].
            apply SOppp.add_in; right; apply SOppp.singleton_in; reflexivity.
          + exact (carried_blocks pub (n, v) m q Hc).
        - destruct H as [n1 [v1 [m [vs [q1 [u [_ [_ [_ [_ Heq]]]]]]]]]];
            discriminate Heq.
        - destruct H as [n1 [v1 [m [vs [q1 [u [_ [_ [_ [_ Heq]]]]]]]]]];
            discriminate Heq.
      Qed.

      Theorem dependees_lookupIntermediate :
        forall R D pub r (n : N.t) (v : V.t) (m : N.t) (q : Pkg.t) (u : V.t),
          T.dependees (reduceDeps R D pub r) (Name.Intermediate n v m q, u) =
          T.dependees
            (reduceDeps (realPreimage R (PkgSet.singleton q))
               (depBlocks D (n, v) q) (pubBlocks pub (n, v) q) r)
            (Name.Intermediate n v m q, u).
      Proof.
        intros R D pub r n v m q u; apply T.dependees_ext; intros [tn tvs].
        split;
          [| intro H;
             exact (reduceDeps_mono R _ D _ pub _ r _
                      (realPreimage_subset R _) (depBlocks_subset D (n, v) q)
                      (pubBlocks_subset pub (n, v) q)
                      (priv_blocks_mono D pub (n, v) q) H)].
        intro H; apply mem_reduceDeps in H; apply mem_reduceDeps.
        destruct H as [H | [H | [H | H]]].
        - destruct H as [n1 [v1 [q1 [_ [_ [_ [_ Heq]]]]]]]; discriminate Heq.
        - destruct H as [n1 [v1 [m1 [vs [q1 [_ [_ [_ Heq]]]]]]]];
            discriminate Heq.
        - destruct H
            as [n1 [v1 [m1 [vs [q1 [u1 [HD1 [Hq1 [Hc [Hu1 Heq]]]]]]]]]].
          injection Heq as <- <- <- <- <- -> ->.
          right; right; left; exists n, v, m, vs, q, u; repeat split.
          + apply mem_depBlocks; split; [exact HD1 | left; reflexivity].
          + apply potentialOrigins_blocks;
              [apply SOppp.singleton_in; reflexivity | exact Hq1].
          + exact (carried_blocks pub (n, v) m q Hc).
          + exact Hu1.
        - destruct H
            as [n1 [v1 [m1 [vs [q1 [u1 [HD1 [Hq1 [Hc [Hu1 Heq]]]]]]]]]].
          injection Heq as <- <- <- <- <- -> ->.
          right; right; right; exists n, v, m, vs, q, u; repeat split.
          + apply mem_depBlocks; split; [exact HD1 | left; reflexivity].
          + apply potentialOrigins_blocks;
              [apply SOppp.singleton_in; reflexivity | exact Hq1].
          + exact (carried_blocks pub (n, v) m q Hc).
          + exact Hu1.
      Qed.

      Theorem dependees_lookupAgreement :
        forall R D pub r (n : N.t) (v : V.t) (m : N.t) (u : V.t),
          T.dependees (reduceDeps R D pub r) (Name.Agreement n v m, u) =
          T.DependeesSet.empty.
      Proof.
        intros R D pub r n v m u; apply T.dependees_empty_iff.
        intros [tn tvs] H; apply mem_reduceDeps in H.
        destruct H as [H | [H | [H | H]]].
        - destruct H as [n1 [v1 [q1 [_ [_ [_ [_ Heq]]]]]]]; discriminate Heq.
        - destruct H as [n1 [v1 [m1 [vs [q1 [_ [_ [_ Heq]]]]]]]];
            discriminate Heq.
        - destruct H as [n1 [v1 [m1 [vs [q1 [u1 [_ [_ [_ [_ Heq]]]]]]]]]];
            discriminate Heq.
        - destruct H as [n1 [v1 [m1 [vs [q1 [u1 [_ [_ [_ [_ Heq]]]]]]]]]];
            discriminate Heq.
      Qed.
    End Lookup.
  End Reduction.
End Visibility.
