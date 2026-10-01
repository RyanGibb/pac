From Stdlib Require Import MSets List Lia PeanoNat.
From PackageCalculus Require Import Prelude Core.

Create HintDb cmp_plc.
Create Rewrite HintDb cmp_plc.

Module Placement (N V : UsualOrderedType).
  Module C := Core N V.
  Module Pkg := C.Pkg.
  Module PkgSet := C.PkgSet.
  Module VSet := C.VSet.

  (* A path is stored deepest name first, so a location's parent is its tail. *)
  Module Path := ListUOT N.
  Module OccElt := PairUOT Path Pkg.
  Module Layout := FSetUOT OccElt.

  Definition par (l : Path.t) : Path.t :=
    match l with nil => nil | _ :: l' => l' end.

  Record Inst : Type :=
    { inst_repo : PkgSet.t
    ; inst_deps : C.DepRel.t
    ; inst_peers : C.DepRel.t
    ; inst_optDeps : C.DepRel.t
    ; inst_optPeers : C.DepRel.t
    ; inst_root : Pkg.t }.

  Definition rel (I : Inst) (peer optional : bool) : C.DepRel.t :=
    match peer, optional with
    | false, false => inst_deps I
    | true, false => inst_peers I
    | false, true => inst_optDeps I
    | true, true => inst_optPeers I
    end.

  Definition land (peer : bool) (l : Path.t) : Path.t :=
    if peer then par l else l.

  Module SOlp := SetOps OccElt Pkg Layout PkgSet.
  Definition occupants (L : Layout.t) (l : Path.t) (a : N.t) : VSet.t :=
    C.versions
      (SOlp.filterMap (fun '(l', p) =>
           if Path.eq_dec l' l then Some p else None) L)
      a.

  Lemma mem_occupants : forall L l a v,
      VSet.In v (occupants L l a) <-> Layout.In (l, (a, v)) L.
  Proof.
    intros L l a v; unfold occupants.
    rewrite C.mem_versions, SOlp.mem_filterMap; split.
    - intros [[l' p] [Hin H]]; cbn beta iota in H.
      destruct (Path.eq_dec l' l) as [-> |]; [| discriminate H].
      injection H as ->; exact Hin.
    - intro H; exists (l, (a, v)); split; [exact H | cbn beta iota].
      apply dec_refl.
  Qed.

  Fixpoint walk (L : Layout.t) (l : Path.t) (a : N.t)
      : option (Path.t * V.t) :=
    match VSet.choose (occupants L l a) with
    | Some v => Some (l, v)
    | None => match l with nil => None | _ :: l' => walk L l' a end
    end.

  Inductive Suffix (l' : Path.t) : Path.t -> Prop :=
  | SuffixRefl : Suffix l' l'
  | SuffixCons : forall b l, Suffix l' l -> Suffix l' (b :: l).

  Definition Resolves (L : Layout.t) (l la : Path.t) (n : N.t) (vs : VSet.t)
      : Prop :=
    exists l' u, walk L l n = Some (l', u) /\ Suffix l' la /\ VSet.In u vs.

  Definition Meets (L : Layout.t) (l la : Path.t) (n : N.t) (vs : VSet.t)
      (optional : bool) : Prop :=
    Resolves L l la n vs \/ (optional = true /\ walk L l n = None).

  Definition Holds (I : Inst) (L : Layout.t) (l : Path.t) (p : Pkg.t) : Prop :=
    forall peer optional n vs, C.DepRel.In (p, (n, vs)) (rel I peer optional) ->
      Meets L l (land peer l) n vs optional.

  Record IsResolution (I : Inst) (L : Layout.t) : Prop :=
    { res_subset :
        forall l p, Layout.In (l, p) L -> PkgSet.In p (inst_repo I)
    ; res_location_unique :
        forall l a v v', Layout.In (l, (a, v)) L -> Layout.In (l, (a, v')) L ->
        v = v'
    ; res_tree :
        forall b l p, Layout.In (b :: l, p) L ->
        exists u, Layout.In (l, (b, u)) L
    ; res_root : Holds I L nil (inst_root I)
    ; res_dep_resolution :
        forall l a v, Layout.In (l, (a, v)) L -> Holds I L (a :: l) (a, v) }.

  Definition Depth (depth : nat) (L : Layout.t) : Prop :=
    forall l p, Layout.In (l, p) L -> length l < depth.

  Lemma suffix_length : forall l' l, Suffix l' l -> length l' <= length l.
  Proof. induction 1; cbn [length]; lia. Qed.

  Lemma walk_found : forall L l a l' u,
      walk L l a = Some (l', u) -> Layout.In (l', (a, u)) L /\ Suffix l' l.
  Proof.
    intros L l a; induction l as [| b l IH]; intros l' u H; cbn [walk] in H.
    - destruct (VSet.choose (occupants L nil a)) as [v |] eqn:Hc;
        [| discriminate H].
      injection H as <- <-; split; [| constructor].
      apply mem_occupants, VSet.choose_spec1; exact Hc.
    - destruct (VSet.choose (occupants L (b :: l) a)) as [v |] eqn:Hc.
      + injection H as <- <-; split; [| constructor].
        apply mem_occupants, VSet.choose_spec1; exact Hc.
      + destruct (IH _ _ H) as [Hin Hs].
        split; [exact Hin | constructor; exact Hs].
  Qed.

  Lemma suffix_trans : forall l1 l2 l3,
      Suffix l1 l2 -> Suffix l2 l3 -> Suffix l1 l3.
  Proof.
    intros l1 l2 l3 H1 H2; induction H2; [exact H1 | constructor; assumption].
  Qed.

  Definition Edge (I : Inst) (p : Pkg.t) (n : N.t) : Prop :=
    exists peer optional vs, C.DepRel.In (p, (n, vs)) (rel I peer optional).

  Inductive Reaches (I : Inst) (L : Layout.t) : OccElt.t -> Prop :=
  | ReachesRoot : forall n l' u,
      Edge I (inst_root I) n -> walk L nil n = Some (l', u) ->
      Reaches I L (l', (n, u))
  | ReachesStep : forall l a v n l' u,
      Reaches I L (l, (a, v)) -> Edge I (a, v) n ->
      walk L (a :: l) n = Some (l', u) -> Reaches I L (l', (n, u)).

  Lemma reaches_in : forall I L o, Reaches I L o -> Layout.In o L.
  Proof.
    intros I L o H; destruct H as [n l' u _ Hw | l a v n l' u _ _ Hw];
      exact (proj1 (walk_found _ _ _ _ _ Hw)).
  Qed.

  Lemma reaches_parented : forall I L l a v, Reaches I L (l, (a, v)) ->
      forall b l', Suffix (b :: l') (a :: l) ->
      exists u, Layout.In (l', (b, u)) L.
  Proof.
    intros I L l a v H.
    assert (Hg : forall o, Reaches I L o ->
               forall b l', Suffix (b :: l') (fst (snd o) :: fst o) ->
               exists u, Layout.In (l', (b, u)) L).
    { intros o Ho; induction Ho as [n l0 u _ Hw | l1 a0 v0 n l0 u _ IH _ Hw];
        intros b l' Hs; cbn [fst snd] in *;
        apply walk_found in Hw; destruct Hw as [Hin Hs0];
        inversion Hs as [| b2 l2 Hs1]; subst;
        try (exists u; exact Hin).
      - inversion Hs0; subst; inversion Hs1.
      - exact (IH b l' (suffix_trans _ _ _ Hs1 Hs0)). }
    exact (Hg (l, (a, v)) H).
  Qed.

  Lemma walk_restrict : forall L L' l a l' u,
      (forall o, Layout.In o L' -> Layout.In o L) ->
      (forall l a v v', Layout.In (l, (a, v)) L -> Layout.In (l, (a, v')) L ->
         v = v') ->
      walk L l a = Some (l', u) -> Layout.In (l', (a, u)) L' ->
      walk L' l a = Some (l', u).
  Proof.
    intros L L' l a l' u Hsub Hocc.
    assert (Hnone : forall l, VSet.choose (occupants L l a) = None ->
               VSet.choose (occupants L' l a) = None).
    { intros l0 Hc; apply VSet.choose_spec2 in Hc.
      destruct (VSet.choose (occupants L' l0 a)) as [x |] eqn:Hc';
        [| reflexivity].
      apply VSet.choose_spec1, mem_occupants, Hsub in Hc'.
      destruct (Hc x); apply mem_occupants; exact Hc'. }
    assert (Hsome : forall l v, VSet.choose (occupants L l a) = Some v ->
               Layout.In (l, (a, v)) L' ->
               VSet.choose (occupants L' l a) = Some v).
    { intros l0 v Hc Hin; apply VSet.choose_spec1, mem_occupants in Hc.
      destruct (VSet.choose (occupants L' l0 a)) as [x |] eqn:Hc'.
      - apply VSet.choose_spec1, mem_occupants, Hsub in Hc'.
        rewrite (Hocc _ _ _ _ Hc' Hc); reflexivity.
      - apply VSet.choose_spec2 in Hc'; destruct (Hc' v).
        apply mem_occupants; exact Hin. }
    induction l as [| b l IH]; intros Hw Hin; cbn [walk] in Hw |- *.
    - destruct (VSet.choose (occupants L nil a)) as [v |] eqn:Hc;
        [| discriminate Hw].
      injection Hw as <- <-; rewrite (Hsome _ _ Hc Hin); reflexivity.
    - destruct (VSet.choose (occupants L (b :: l) a)) as [v |] eqn:Hc.
      + injection Hw as <- <-; rewrite (Hsome _ _ Hc Hin); reflexivity.
      + rewrite (Hnone _ Hc); exact (IH Hw Hin).
  Qed.

  Lemma walk_none_restrict : forall L L' l a,
      (forall o, Layout.In o L' -> Layout.In o L) ->
      walk L l a = None -> walk L' l a = None.
  Proof.
    intros L L' l a Hsub.
    assert (Hnone : forall l, VSet.choose (occupants L l a) = None ->
               VSet.choose (occupants L' l a) = None).
    { intros l0 Hc; apply VSet.choose_spec2 in Hc.
      destruct (VSet.choose (occupants L' l0 a)) as [x |] eqn:Hc';
        [| reflexivity].
      apply VSet.choose_spec1, mem_occupants, Hsub in Hc'.
      destruct (Hc x); apply mem_occupants; exact Hc'. }
    induction l as [| b l IH]; intro Hw; cbn [walk] in Hw |- *;
      destruct (VSet.choose (occupants L _ a)) eqn:Hc; try discriminate Hw;
      rewrite (Hnone _ Hc); [reflexivity | exact (IH Hw)].
  Qed.

  Definition Settled (I : Inst) (L : Layout.t) (l : Path.t) : Prop :=
    forall b l' u, Suffix (b :: l') l -> Layout.In (l', (b, u)) L ->
    Reaches I L (l', (b, u)).

  Lemma reaches_settled : forall I L,
      (forall l a v v', Layout.In (l, (a, v)) L -> Layout.In (l, (a, v')) L ->
         v = v') ->
      forall l a v, Reaches I L (l, (a, v)) -> Settled I L (a :: l).
  Proof.
    intros I L Hocc.
    assert (Hstep : forall w n l' u, Settled I L w ->
               walk L w n = Some (l', u) -> Reaches I L (l', (n, u)) ->
               Settled I L (n :: l')).
    { intros w n l' u Hset Hw Hr b m u' Hs Hin.
      inversion Hs as [| b0 l0 Hs']; subst.
      - assert (u' = u) as -> by exact (Hocc _ _ _ _ Hin (reaches_in _ _ _ Hr)).
        exact Hr.
      - apply (Hset b m u'); [| exact Hin].
        exact (suffix_trans _ _ _ Hs' (proj2 (walk_found _ _ _ _ _ Hw))). }
    enough (Hg : forall o, Reaches I L o -> Settled I L (fst (snd o) :: fst o))
      by (intros l a v H; exact (Hg _ H)).
    intros o H; induction H as [n l' u He Hw | l a v n l' u Hr IH He Hw];
      cbn [fst snd] in *.
    - apply (Hstep nil n l' u);
        [| exact Hw | exact (ReachesRoot I L n l' u He Hw)].
      intros b m u' Hs; inversion Hs.
    - apply (Hstep (a :: l) n l' u IH Hw).
      exact (ReachesStep I L l a v n l' u Hr He Hw).
  Qed.

  Lemma reaches_resolution : forall I L L',
      (forall l p, Layout.In (l, p) L -> PkgSet.In p (inst_repo I)) ->
      (forall l a v v', Layout.In (l, (a, v)) L -> Layout.In (l, (a, v')) L ->
         v = v') ->
      Holds I L nil (inst_root I) ->
      (forall l a v, Layout.In (l, (a, v)) L -> Holds I L (a :: l) (a, v)) ->
      (forall o, Layout.In o L' <-> Layout.In o L /\ Reaches I L o) ->
      IsResolution I L'.
  Proof.
    intros I L L' Hsub Hocc Hroot Hdeps HL'.
    assert (HinL : forall o, Layout.In o L' -> Layout.In o L)
      by (intros o H; exact (proj1 (proj1 (HL' o) H))).
    assert (Hin' : forall o, Reaches I L o -> Layout.In o L')
      by (intros o H; apply HL'; split; [exact (reaches_in _ _ _ H) | exact H]).
    assert (Hholds : forall w p, Holds I L w p ->
               (forall n l' u, Edge I p n -> walk L w n = Some (l', u) ->
                  Reaches I L (l', (n, u))) ->
               Holds I L' w p).
    { intros w p Hh Hr peer optional n vs HE.
      assert (He : Edge I p n) by (exists peer, optional, vs; exact HE).
      destruct (Hh _ _ _ _ HE) as [[l' [u [Hw [Hs Hu]]]] | [Ho Hw]].
      - left; exists l', u; split; [| split; assumption].
        apply (walk_restrict L L' w n l' u HinL Hocc Hw), Hin'.
        exact (Hr _ _ _ He Hw).
      - right; split; [exact Ho |].
        exact (walk_none_restrict L L' w n HinL Hw). }
    constructor.
    - intros l p H; exact (Hsub _ _ (HinL _ H)).
    - intros l a v v' H H'; exact (Hocc _ _ _ _ (HinL _ H) (HinL _ H')).
    - intros b l [a v] H; apply HL' in H; destruct H as [_ Hr].
      destruct (reaches_parented I L _ _ _ Hr b l) as [u Hu];
        [constructor; constructor |].
      exists u; apply Hin'.
      apply (reaches_settled I L Hocc _ _ _ Hr b l u); [| exact Hu].
      cbn [fst snd]; constructor; constructor.
    - apply (Hholds _ _ Hroot); intros n l' u He Hw.
      exact (ReachesRoot I L n l' u He Hw).
    - intros l a v H; apply HL' in H; destruct H as [HL Hr].
      apply (Hholds _ _ (Hdeps _ _ _ HL)); intros n l' u He Hw.
      exact (ReachesStep I L l a v n l' u Hr He Hw).
  Qed.

  Theorem reaches_restriction : forall I L L',
      IsResolution I L ->
      (forall o, Layout.In o L' <-> Layout.In o L /\ Reaches I L o) ->
      IsResolution I L'.
  Proof.
    intros I L L' [Hsub Hocc _ Hroot Hdeps].
    exact (reaches_resolution I L L' Hsub Hocc Hroot Hdeps).
  Qed.

  Definition allRel (I : Inst) : C.DepRel.t :=
    C.DepRel.union (C.DepRel.union (inst_deps I) (inst_peers I))
      (C.DepRel.union (inst_optDeps I) (inst_optPeers I)).

  Lemma mem_allRel : forall I p n vs,
      C.DepRel.In (p, (n, vs)) (allRel I) <->
      exists peer optional, C.DepRel.In (p, (n, vs)) (rel I peer optional).
  Proof.
    intros I p n vs; unfold allRel; rewrite !C.DepRel.union_spec; split.
    - intros [[H | H] | [H | H]];
        [exists false, false | exists true, false
        | exists false, true | exists true, true]; exact H.
    - intros [[|] [[|] H]]; cbn [rel] in H; tauto.
  Qed.

  Module SOdl := SetOps C.DepElt OccElt C.DepRel Layout.
  Definition landings (I : Inst) (L : Layout.t) (l : Path.t) (p : Pkg.t)
      : Layout.t :=
    SOdl.filterMap (fun '(q, (n, _)) =>
        if Pkg.eq_dec q p
        then match walk L l n with
             | Some (l', u) => Some (l', (n, u))
             | None => None
             end
        else None)
      (allRel I).

  Lemma mem_landings : forall I L l p o,
      Layout.In o (landings I L l p) <->
      exists n l' u, Edge I p n /\ walk L l n = Some (l', u) /\
        o = (l', (n, u)).
  Proof.
    intros I L l p o; unfold landings; rewrite SOdl.mem_filterMap; split.
    - intros [[q [n vs]] [Hin H]]; cbn beta iota in H.
      destruct (Pkg.eq_dec q p) as [-> |]; [| discriminate H].
      destruct (walk L l n) as [[l' u] |] eqn:Hw; [| discriminate H].
      injection H as <-; exists n, l', u.
      split; [| split; [exact Hw | reflexivity]].
      apply mem_allRel in Hin; destruct Hin as [peer [optional H]].
      exists peer, optional, vs; exact H.
    - intros [n [l' [u [[peer [optional [vs He]]] [Hw ->]]]]].
      exists (p, (n, vs)); split;
        [apply mem_allRel; exists peer, optional; exact He |].
      cbn beta iota; rewrite dec_refl, Hw; reflexivity.
  Qed.

  Module SOll := SetOps OccElt OccElt Layout Layout.
  Definition reachStep (I : Inst) (L os : Layout.t) : Layout.t :=
    Layout.union (landings I L nil (inst_root I))
      (SOll.unionMap (fun o => landings I L (fst (snd o) :: fst o) (snd o))
         os).

  Fixpoint reachN (I : Inst) (L : Layout.t) (k : nat) : Layout.t :=
    match k with
    | O => Layout.empty
    | S k' => reachStep I L (reachN I L k')
    end.

  (* Fixpoints recurse structurally, so the closure iterates on fuel: a
     round that adds an occupant of L grows the set, so S (cardinal L)
     rounds reach the fixpoint (reachN_grows). *)
  Definition reachable (I : Inst) (L : Layout.t) : Layout.t :=
    reachN I L (S (Layout.cardinal L)).

  Module LP := MSetProperties.WPropertiesOn OccElt Layout.

  Lemma mem_reachStep : forall I L os o,
      Layout.In o (reachStep I L os) <->
      Layout.In o (landings I L nil (inst_root I)) \/
      exists l a v, Layout.In (l, (a, v)) os /\
        Layout.In o (landings I L (a :: l) (a, v)).
  Proof.
    intros I L os o; unfold reachStep; rewrite Layout.union_spec,
      SOll.mem_unionMap; split.
    - intros [H | [[l [a v]] [Hx H]]]; [left; exact H |].
      right; exists l, a, v; split; [exact Hx | exact H].
    - intros [H | [l [a [v [Hx H]]]]]; [left; exact H |].
      right; exists (l, (a, v)); split; [exact Hx | exact H].
  Qed.

  Lemma reachStep_mono : forall I L os os',
      Layout.Subset os os' ->
      Layout.Subset (reachStep I L os) (reachStep I L os').
  Proof.
    intros I L os os' H o; rewrite !mem_reachStep.
    intros [Ho | [l [a [v [Hx Ho]]]]]; [left; exact Ho |].
    right; exists l, a, v; split; [exact (H _ Hx) | exact Ho].
  Qed.

  Lemma reachN_chain : forall I L k,
      Layout.Subset (reachN I L k) (reachN I L (S k)).
  Proof.
    intros I L k; induction k as [| k IH]; cbn [reachN].
    - exact (Layout.empty_subset _).
    - exact (reachStep_mono I L _ _ IH).
  Qed.

  Lemma reachN_reaches : forall I L k o,
      Layout.In o (reachN I L k) -> Reaches I L o.
  Proof.
    intros I L k; induction k as [| k IH]; intros o H; cbn [reachN] in H;
      [destruct (Layout.empty_spec H) |].
    apply mem_reachStep in H; destruct H as [H | [l [a [v [Hx H]]]]];
      apply mem_landings in H; destruct H as [n [l' [u [He [Hw ->]]]]].
    - exact (ReachesRoot I L n l' u He Hw).
    - exact (ReachesStep I L l a v n l' u (IH _ Hx) He Hw).
  Qed.

  Lemma reachN_stable : forall I L k,
      Layout.Subset (reachN I L (S k)) (reachN I L k) ->
      Layout.Subset (reachN I L (S (S k))) (reachN I L (S k)).
  Proof.
    intros I L k H.
    assert (E : reachN I L (S k) = reachN I L k)
      by (apply Layout.ext; intro o; split;
          [apply H | apply reachN_chain]).
    change (reachN I L (S (S k))) with (reachStep I L (reachN I L (S k))).
    rewrite E; exact H.
  Qed.

  Lemma reachN_grows : forall I L k,
      Layout.Subset (reachN I L (S k)) (reachN I L k) \/
      k <= Layout.cardinal (reachN I L k).
  Proof.
    intros I L k; induction k as [| k IH]; [right; apply Nat.le_0_l |].
    destruct IH as [IH | IH]; [left; exact (reachN_stable I L k IH) |].
    destruct (Layout.exists_ (fun o => negb (Layout.mem o (reachN I L k)))
                (reachN I L (S k))) eqn:Hx.
    - right; apply Layout.exists_spec' in Hx; destruct Hx as [o [Ho Hn]].
      apply Bool.negb_true_iff in Hn.
      assert (Hno : ~ Layout.In o (reachN I L k))
        by (intro Hin; apply Layout.mem_spec in Hin; congruence).
      assert (Hlt : Layout.cardinal (reachN I L k) <
                    Layout.cardinal (reachN I L (S k)))
        by (eapply LP.subset_cardinal_lt;
            [exact (reachN_chain I L k) | exact Ho | exact Hno]).
      lia.
    - left; apply reachN_stable; intros o Ho.
      destruct (Layout.mem o (reachN I L k)) eqn:Hm;
        [apply Layout.mem_spec; exact Hm |].
      assert (Layout.exists_ (fun o => negb (Layout.mem o (reachN I L k)))
                (reachN I L (S k)) = true) as C
        by (apply Layout.exists_spec'; exists o;
            split; [exact Ho | rewrite Hm; reflexivity]).
      congruence.
  Qed.

  Lemma reachN_in : forall I L k, Layout.Subset (reachN I L k) L.
  Proof.
    intros I L k o H; exact (reaches_in _ _ _ (reachN_reaches _ _ _ _ H)).
  Qed.

  Theorem mem_reachable : forall I L o,
      Layout.In o (reachable I L) <-> Layout.In o L /\ Reaches I L o.
  Proof.
    intros I L o; split.
    - intro H; pose proof (reachN_reaches _ _ _ _ H) as Hr.
      split; [exact (reaches_in _ _ _ Hr) | exact Hr].
    - intros [_ H]; unfold reachable.
      assert (Hfix : forall k, k = Layout.cardinal L ->
                 Layout.Subset (reachStep I L (reachN I L (S k)))
                   (reachN I L (S k))).
      { intros k ->.
        destruct (reachN_grows I L (S (Layout.cardinal L))) as [Hs | Hle];
          [exact Hs |].
        assert (Hc : Layout.cardinal (reachN I L (S (Layout.cardinal L))) <=
                     Layout.cardinal L)
          by (eapply LP.subset_cardinal; exact (reachN_in I L _)).
        lia. }
      specialize (Hfix _ eq_refl).
      induction H as [n l' u He Hw | l a v n l' u _ IH He Hw];
        apply Hfix, mem_reachStep.
      + left; apply mem_landings; exists n, l', u; auto.
      + right; exists l, a, v; split; [exact IH |].
        apply mem_landings; exists n, l', u; auto.
  Qed.

  (* reachable runs S (cardinal L) rounds, each over the whole relation, too
     slow for a driver to run.  reachableBy visits each occupant once, and
     reads its edges' directories from dirs, which a driver supplies from
     its lookups; given they are the instance's, the two agree. *)
  Definition landingsBy (dirs : Pkg.t -> list N.t) (L : Layout.t)
      (l : Path.t) (p : Pkg.t) : list OccElt.t :=
    List.fold_right (fun n acc =>
        match walk L l n with
        | Some (l', u) => (l', (n, u)) :: acc
        | None => acc
        end) nil (dirs p).

  Definition visit (st : Layout.t * list OccElt.t) (o : OccElt.t)
      : Layout.t * list OccElt.t :=
    if Layout.mem o (fst st) then st else (Layout.add o (fst st), o :: snd st).

  Fixpoint reachW (dirs : Pkg.t -> list N.t) (L : Layout.t) (fuel : nat)
      (seen : Layout.t) (todo : list OccElt.t) : Layout.t :=
    match fuel, todo with
    | O, _ | _, nil => seen
    | S k, (l, (a, v)) :: todo' =>
        let '(seen', todo'') :=
          List.fold_left visit (landingsBy dirs L (a :: l) (a, v))
            (seen, todo') in
        reachW dirs L k seen' todo''
    end.

  (* a round visits one occupant and queues only occupants of L not yet
     seen, so cardinal L rounds empty the queue (reachW_spec) *)
  Definition reachableBy (dirs : Pkg.t -> list N.t) (root : Pkg.t)
      (L : Layout.t) : Layout.t :=
    let '(seen, todo) :=
      List.fold_left visit (landingsBy dirs L nil root) (Layout.empty, nil) in
    reachW dirs L (Layout.cardinal L) seen todo.

  Lemma mem_landingsBy : forall dirs L l p o,
      List.In o (landingsBy dirs L l p) <->
      exists n l' u, List.In n (dirs p) /\ walk L l n = Some (l', u) /\
        o = (l', (n, u)).
  Proof.
    intros dirs L l p o; unfold landingsBy.
    induction (dirs p) as [| n ns IH]; cbn [List.fold_right].
    - split; [intros [] | intros [n [l' [u [[] _]]]]].
    - destruct (walk L l n) as [[l' u] |] eqn:Hw.
      + cbn [List.In]; rewrite IH; split.
        * intros [<- | [m [l1 [u1 [Hm [Hw1 ->]]]]]];
            [exists n, l', u | exists m, l1, u1]; cbn [List.In]; auto.
        * intros [m [l1 [u1 [[<- | Hm] [Hw1 ->]]]]].
          -- left; rewrite Hw in Hw1; injection Hw1 as -> ->; reflexivity.
          -- right; exists m, l1, u1; auto.
      + rewrite IH; split.
        * intros [m [l1 [u1 [Hm [Hw1 ->]]]]]; exists m, l1, u1.
          cbn [List.In]; auto.
        * intros [m [l1 [u1 [[<- | Hm] [Hw1 ->]]]]];
            [rewrite Hw in Hw1; discriminate Hw1 |].
          exists m, l1, u1; auto.
  Qed.

  Lemma visit_fold : forall xs s t s' t',
      List.fold_left visit xs (s, t) = (s', t') ->
      (forall o, Layout.In o s' <-> Layout.In o s \/ List.In o xs) /\
      (forall o, List.In o t' <->
         List.In o t \/ (List.In o xs /\ ~ Layout.In o s)) /\
      length t' + Layout.cardinal s = length t + Layout.cardinal s'.
  Proof.
    induction xs as [| x xs IH]; intros s t s' t' H; cbn [List.fold_left] in H.
    - injection H as <- <-; cbn [List.In]; split; [| split]; [tauto | tauto |].
      reflexivity.
    - assert (E : visit (s, t) x =
                  if Layout.mem x s then (s, t) else (Layout.add x s, x :: t))
        by reflexivity.
      rewrite E in H; clear E.
      destruct (Layout.mem x s) eqn:Hm.
      + apply Layout.mem_spec in Hm.
        destruct (IH _ _ _ _ H) as [Hs [Ht Hc]].
        split; [| split; [| exact Hc]]; intro o; [rewrite Hs | rewrite Ht];
          cbn [List.In]; split; try tauto.
        * intros [Ho | [<- | Ho]]; tauto.
        * intros [Ho | [[<- | Ho] Hn]]; tauto.
      + assert (Hn : ~ Layout.In x s)
          by (intro Hx; apply Layout.mem_spec in Hx; congruence).
        destruct (IH _ _ _ _ H) as [Hs [Ht Hc]].
        split; [| split].
        * intro o; rewrite Hs, Layout.add_spec; cbn [List.In].
          split; [intros [[-> | Ho] | Ho]; tauto | intros [Ho | [<- | Ho]]];
            auto.
        * intro o; rewrite Ht, Layout.add_spec; cbn [List.In].
          destruct (OccElt.eq_dec o x) as [-> | Hox]; [tauto |].
          assert (x <> o) by congruence; tauto.
        * rewrite (LP.add_cardinal_2 Hn) in Hc; cbn [length] in Hc; lia.
  Qed.

  Section ReachableBy.
    Variables (I : Inst) (L : Layout.t) (dirs : Pkg.t -> list N.t).
    Hypothesis Hdirs : forall p n,
        (p = inst_root I \/ exists l, Layout.In (l, p) L) ->
        List.In n (dirs p) <-> Edge I p n.

    Let Inv (seen : Layout.t) (todo : list OccElt.t) : Prop :=
      (forall o, Layout.In o seen -> Reaches I L o) /\
      (forall o, List.In o todo -> Layout.In o seen) /\
      (forall o, List.In o (landingsBy dirs L nil (inst_root I)) ->
         Layout.In o seen) /\
      (forall l a v o, Layout.In (l, (a, v)) seen ->
         ~ List.In (l, (a, v)) todo ->
         List.In o (landingsBy dirs L (a :: l) (a, v)) -> Layout.In o seen).

    Lemma landingsBy_root : forall o,
        List.In o (landingsBy dirs L nil (inst_root I)) <->
        exists n l' u, Edge I (inst_root I) n /\ walk L nil n = Some (l', u) /\
          o = (l', (n, u)).
    Proof.
      intro o; rewrite mem_landingsBy.
      split; intros [n [l' [u [He H]]]]; exists n, l', u;
        (split; [| exact H]); apply Hdirs; auto.
    Qed.

    Lemma landingsBy_occ : forall l a v o, Layout.In (l, (a, v)) L ->
        List.In o (landingsBy dirs L (a :: l) (a, v)) <->
        exists n l' u, Edge I (a, v) n /\ walk L (a :: l) n = Some (l', u) /\
          o = (l', (n, u)).
    Proof.
      intros l a v o Hl; rewrite mem_landingsBy.
      split; intros [n [l' [u [He H]]]]; exists n, l', u;
        (split; [| exact H]); apply Hdirs; eauto.
    Qed.

    Lemma reachW_done : forall seen, Inv seen nil ->
        forall o, Layout.In o seen <-> Reaches I L o.
    Proof.
      intros seen [Hr [_ [Hroot Hcl]]] o; split; [exact (Hr o) |].
      intro H; induction H as [n l' u He Hw | l a v n l' u Hrl IH He Hw].
      - apply Hroot, landingsBy_root; exists n, l', u; auto.
      - apply (Hcl l a v _ IH (fun H => H)).
        apply landingsBy_occ; [exact (reaches_in _ _ _ Hrl) |].
        exists n, l', u; auto.
    Qed.

    Lemma reachW_spec : forall fuel seen todo, Inv seen todo ->
        length todo + Layout.cardinal L <= fuel + Layout.cardinal seen ->
        forall o, Layout.In o (reachW dirs L fuel seen todo) <-> Reaches I L o.
    Proof.
      induction fuel as [| k IH]; intros seen todo Hinv Hc.
      - assert (Hle : Layout.cardinal seen <= Layout.cardinal L).
        { apply LP.subset_cardinal; intros x Hx.
          exact (reaches_in _ _ _ (proj1 Hinv _ Hx)). }
        destruct todo as [| x todo]; [| cbn [length] in Hc; lia].
        exact (reachW_done _ Hinv).
      - destruct todo as [| [l [a v]] todo']; [exact (reachW_done _ Hinv) |].
        cbn [reachW].
        destruct (List.fold_left visit (landingsBy dirs L (a :: l) (a, v))
                    (seen, todo')) as [seen' todo''] eqn:Hf.
        destruct (visit_fold _ _ _ _ _ Hf) as [Hs [Ht Hc']].
        destruct Hinv as [Hr [Htodo [Hroot Hcl]]].
        assert (Hx : Layout.In (l, (a, v)) seen)
          by (apply Htodo; left; reflexivity).
        apply IH; [| cbn [length] in Hc; lia].
        split; [| split; [| split]].
        + intros o Ho; apply Hs in Ho; destruct Ho as [Ho | Ho]; [exact (Hr _ Ho) |].
          pose proof (Hr _ Hx) as Hrx.
          apply (landingsBy_occ l a v o (reaches_in _ _ _ Hrx)) in Ho.
          destruct Ho as [n [l' [u [He [Hw ->]]]]].
          exact (ReachesStep I L l a v n l' u Hrx He Hw).
        + intros o Ho; apply Hs; apply Ht in Ho.
          destruct Ho as [Ho | [Ho _]]; [left; apply Htodo; right; exact Ho |].
          right; exact Ho.
        + intros o Ho; apply Hs; left; exact (Hroot _ Ho).
        + intros l1 a1 v1 o H1 Hn1 Ho; apply Hs.
          apply Hs in H1; destruct H1 as [H1 | H1].
          * destruct (OccElt.eq_dec (l1, (a1, v1)) (l, (a, v))) as [E | NE].
            -- injection E as -> -> ->; right; exact Ho.
            -- left; apply (Hcl l1 a1 v1 o H1); [| exact Ho].
               intros [E | Hin]; [exact (NE (eq_sym E)) |].
               apply Hn1, Ht; left; exact Hin.
          * destruct (Layout.mem (l1, (a1, v1)) seen) eqn:Hm.
            -- apply Layout.mem_spec in Hm.
               destruct (OccElt.eq_dec (l1, (a1, v1)) (l, (a, v))) as [E | NE].
               ++ injection E as -> -> ->; right; exact Ho.
               ++ left; apply (Hcl l1 a1 v1 o Hm); [| exact Ho].
                  intros [E | Hin]; [exact (NE (eq_sym E)) |].
                  apply Hn1, Ht; left; exact Hin.
            -- exfalso; apply Hn1, Ht; right; split; [exact H1 |].
               intro Hin; apply Layout.mem_spec in Hin; congruence.
    Qed.

    Theorem reachableBy_reachable :
        reachableBy dirs (inst_root I) L = reachable I L.
    Proof.
      apply Layout.ext; intro o; rewrite mem_reachable; unfold reachableBy.
      destruct (List.fold_left visit (landingsBy dirs L nil (inst_root I))
                  (Layout.empty, nil)) as [seen todo] eqn:Hf.
      destruct (visit_fold _ _ _ _ _ Hf) as [Hs [Ht Hc]].
      assert (Hseen : forall x, Layout.In x seen <->
                 List.In x (landingsBy dirs L nil (inst_root I))).
      { intro x; rewrite Hs; split; [| auto].
        intros [H | H]; [destruct (Layout.empty_spec H) | exact H]. }
      rewrite (reachW_spec (Layout.cardinal L) seen todo).
      - split; [intro H; split; [exact (reaches_in _ _ _ H) | exact H] |].
        intros [_ H]; exact H.
      - split; [| split; [| split]].
        + intros x Hx; apply Hseen, landingsBy_root in Hx.
          destruct Hx as [n [l' [u [He [Hw ->]]]]].
          exact (ReachesRoot I L n l' u He Hw).
        + intros x Hx; apply Ht in Hx; destruct Hx as [[] | [Hx _]].
          apply Hseen; exact Hx.
        + intros x Hx; apply Hseen; exact Hx.
        + intros l a v x H Hn; exfalso; apply Hn, Ht; right.
          split; [apply Hseen; exact H | exact (@Layout.empty_spec _)].
      - rewrite LP.empty_cardinal in Hc; cbn [length] in Hc; lia.
    Qed.
  End ReachableBy.

  Module Reduction.
    Module PathF := UOTCompareFacts Path.

    Module Shallow <: ComparableType.
      Definition t := Path.t.
      Definition compare (l1 l2 : t) : comparison :=
        lex (Nat.compare (length l2) (length l1)) (Path.compare l1 l2).

      Lemma compare_eq_iff : forall x y, compare x y = Eq <-> x = y.
      Proof.
        intros x y; unfold compare; rewrite lex_eq_iff, PathF.compare_eq_iff.
        split; [tauto | intros ->; split;
                        [apply Nat.compare_eq_iff | ]; reflexivity].
      Qed.

      Lemma compare_antisym : forall x y, compare y x = CompOpp (compare x y).
      Proof.
        intros x y; unfold compare.
        rewrite lex_opp, (Nat.compare_antisym (length y) (length x)).
        f_equal; apply PathF.compare_antisym.
      Qed.

      Lemma compare_lt_trans : forall x y z,
          compare x y = Lt -> compare y z = Lt -> compare x z = Lt.
      Proof.
        intros x y z; unfold compare.
        apply (@lex_lt_trans nat Path.t (fun n m => Nat.compare m n)
                 Path.compare (length x) (length y) (length z) x y z).
        - intros n m; rewrite Nat.compare_eq_iff; split; intro; congruence.
        - cbv beta; rewrite !Nat.compare_lt_iff; lia.
        - apply PathF.compare_lt_trans.
      Qed.
    End Shallow.
    Module ShallowOT := UOTFromCompare Shallow.

    Module PN := PairUOT Path N.
    Module SV := PairUOT ShallowOT V.
    Module PNF := UOTCompareFacts PN.
    Module SVF := UOTCompareFacts SV.
    Module VF := UOTCompareFacts V.
    #[local] Hint Rewrite PNF.compare_eq_iff SVF.compare_eq_iff
      VF.compare_eq_iff : cmp_plc.
    #[local] Hint Extern 1 => cmp_by PNF.compare_antisym : cmp_plc.
    #[local] Hint Extern 1 => cmp_by SVF.compare_antisym : cmp_plc.
    #[local] Hint Extern 1 => cmp_by VF.compare_antisym : cmp_plc.
    #[local] Hint Extern 1 => cmp_by PNF.compare_lt_trans : cmp_plc.
    #[local] Hint Extern 1 => cmp_by SVF.compare_lt_trans : cmp_plc.
    #[local] Hint Extern 1 => cmp_by VF.compare_lt_trans : cmp_plc.

    Module Name.
      Inductive name : Type :=
      | Root
      | Loc (l : Path.t) (a : N.t)
      | Walk (l : Path.t) (a : N.t).
      Definition t := name.

      Definition rank (x : t) : nat :=
        match x with Root => 0 | Loc _ _ => 1 | Walk _ _ => 2 end.

      Definition compare (x y : t) : comparison :=
        match Nat.compare (rank x) (rank y) with
        | Eq => match x, y with
                | Loc l1 a1, Loc l2 a2 => PN.compare (l1, a1) (l2, a2)
                | Walk l1 a1, Walk l2 a2 => PN.compare (l1, a1) (l2, a2)
                | _, _ => Eq
                end
        | c => c
        end.

      Lemma compare_eq_iff : forall x y, compare x y = Eq <-> x = y.
      Proof. cmp_eq_iff cmp_plc. Qed.

      Lemma compare_antisym : forall x y, compare y x = CompOpp (compare x y).
      Proof. cmp_antisym cmp_plc. Qed.

      Lemma compare_lt_trans : forall x y z,
          compare x y = Lt -> compare y z = Lt -> compare x z = Lt.
      Proof. cmp_lt_trans cmp_plc. Qed.
    End Name.

    Module Version.
      Inductive version : Type :=
      | Occ (v : V.t)
      | Found (l : Path.t) (v : V.t)
      | Bot.
      Definition t := version.

      Definition rank (x : t) : nat :=
        match x with Occ _ => 0 | Found _ _ => 1 | Bot => 2 end.

      Definition compare (x y : t) : comparison :=
        match Nat.compare (rank x) (rank y) with
        | Eq => match x, y with
                | Occ v1, Occ v2 => V.compare v1 v2
                | Found l1 v1, Found l2 v2 => SV.compare (l1, v1) (l2, v2)
                | _, _ => Eq
                end
        | c => c
        end.

      Lemma compare_eq_iff : forall x y, compare x y = Eq <-> x = y.
      Proof. cmp_eq_iff cmp_plc. Qed.

      Lemma compare_antisym : forall x y, compare y x = CompOpp (compare x y).
      Proof. cmp_antisym cmp_plc. Qed.

      Lemma compare_lt_trans : forall x y z,
          compare x y = Lt -> compare y z = Lt -> compare x z = Lt.
      Proof. cmp_lt_trans cmp_plc. Qed.
    End Version.

    Module NameOT := UOTFromCompare Name.
    Module VersionOT := UOTFromCompare Version.
    Module T := Core NameOT VersionOT.

    Module NSet := FSetUOT N.
    Module SOpn := SetOps Pkg N PkgSet NSet.
    Module SOdn := SetOps C.DepElt N C.DepRel NSet.
    Module SOnn := SetOps N N NSet NSet.
    Definition relNames (E : C.DepRel.t) : NSet.t :=
      SOdn.map (fun e => fst (snd e)) E.

    Definition locNames (I : Inst) : NSet.t :=
      NSet.union (SOpn.map fst (inst_repo I))
        (NSet.union
           (NSet.union (relNames (inst_deps I)) (relNames (inst_peers I)))
           (NSet.union (relNames (inst_optDeps I))
              (relNames (inst_optPeers I)))).

    Lemma locNames_repo : forall I a v,
        PkgSet.In (a, v) (inst_repo I) -> NSet.In a (locNames I).
    Proof.
      intros I a v H; apply NSet.union_spec; left.
      apply SOpn.mem_map; exists (a, v); split; [exact H | reflexivity].
    Qed.

    Lemma locNames_deps : forall I peer optional p n vs,
        C.DepRel.In (p, (n, vs)) (rel I peer optional) ->
          NSet.In n (locNames I).
    Proof.
      intros I peer optional p n vs H; apply NSet.union_spec; right.
      assert (Hn : NSet.In n (relNames (rel I peer optional)))
        by (apply SOdn.mem_map; exists (p, (n, vs)); split;
            [exact H | reflexivity]).
      rewrite !NSet.union_spec.
      destruct peer, optional; cbn [rel] in Hn; tauto.
    Qed.

    Definition LocPath (I : Inst) (l : Path.t) : Prop :=
      List.Forall (fun b => NSet.In b (locNames I)) l.

    Definition InRange (I : Inst) (depth : nat) (n : Name.t) : Prop :=
      match n with
      | Name.Root => True
      | Name.Loc l a | Name.Walk l a => length l <= depth /\ LocPath I (a :: l)
      end.

    (* The core's repository is a finite set, so the names under the depth
       bound are enumerated rather than characterised, and the reduction is
       its lookups aggregated over them (reduceReal, reduceDeps) rather than
       an inductive of reduced packages. *)
    Fixpoint within (ns : list N.t) (depth : nat) : list Path.t :=
      nil :: match depth with
             | O => nil
             | S d' => List.flat_map (fun l => List.map (fun a => a :: l) ns)
                         (within ns d')
             end.

    Lemma in_within : forall ns depth l,
        List.In l (within ns depth) <->
        length l <= depth /\ List.Forall (fun b => List.In b ns) l.
    Proof.
      intros ns depth; induction depth as [| depth IH]; intros [| a l];
        cbn [within List.In length].
      - split; [intros _; split; [lia | constructor] | left; reflexivity].
      - split; [intros [H | []]; discriminate H | intros [H _]; lia].
      - split; [intros _; split; [lia | constructor] | left; reflexivity].
      - rewrite List.in_flat_map, List.Forall_cons_iff; split.
        + intros [H | [l' [Hl' Ha]]]; [discriminate H |].
          apply List.in_map_iff in Ha; destruct Ha as [a' [E Ha']].
          injection E as <- <-; apply IH in Hl'; destruct Hl' as [Hlen Hk].
          split; [lia | split; assumption].
        + intros [Hlen [Ha Hk]]; right; exists l; split.
          * apply IH; split; [lia | exact Hk].
          * apply List.in_map_iff; exists a; split; [reflexivity | exact Ha].
    Qed.

    Definition rangeNames (I : Inst) (depth : nat) : list Name.t :=
      let ks := NSet.elements (locNames I) in
      Name.Root :: List.flat_map (fun l =>
          List.flat_map (fun a => Name.Loc l a :: Name.Walk l a :: nil) ks)
        (within ks depth).

    Lemma in_rangeNames : forall I depth n,
        List.In n (rangeNames I depth) <-> InRange I depth n.
    Proof.
      intros I depth n; unfold rangeNames, InRange, LocPath; cbn [List.In].
      assert (Hks : forall l,
                 List.Forall (fun b => List.In b (NSet.elements (locNames I))) l <->
                 List.Forall (fun b => NSet.In b (locNames I)) l).
      { intro l; rewrite !List.Forall_forall.
        setoid_rewrite SOnn.elements_in; reflexivity. }
      rewrite List.in_flat_map.
      destruct n as [| l a | l a]; cbn beta iota; split.
      1: intros _; exact Logic.I.
      1: intros _; left; reflexivity.
      1, 3: intros [H | [l' [Hl' H]]]; [discriminate H |];
        apply List.in_flat_map in H; destruct H as [a' [Ha' H]];
        destruct H as [H | [H | []]]; try discriminate H;
        injection H as <- <-; apply in_within in Hl';
        destruct Hl' as [Hlen Hk]; split; [exact Hlen |];
        apply List.Forall_cons;
        [apply SOnn.elements_in; exact Ha' | apply Hks; exact Hk].
      all: intros [Hlen Hk]; right; exists l; split;
        [apply in_within; split;
         [exact Hlen | apply Hks; exact (List.Forall_inv_tail Hk)] |];
        apply List.in_flat_map; exists a; split;
        [apply SOnn.elements_in; exact (List.Forall_inv Hk)
        | cbn [List.In]; first [left; reflexivity | right; left; reflexivity]].
    Qed.

    Module SOvt := SetOps V VersionOT VSet T.VSet.
    Fixpoint along (keep : Path.t -> bool) (l : Path.t) (vs : VSet.t)
        : T.VSet.t :=
      T.VSet.union
        (if keep l then SOvt.map (Version.Found l) vs else T.VSet.empty)
        (match l with nil => T.VSet.empty | _ :: l' => along keep l' vs end).

    Lemma mem_along : forall keep l vs v,
        T.VSet.In v (along keep l vs) <->
        exists l' u, Suffix l' l /\ keep l' = true /\ VSet.In u vs /\
          v = Version.Found l' u.
    Proof.
      intros keep l vs v; induction l as [| b l IH]; cbn [along];
        rewrite T.VSet.union_spec, SOvt.in_if_empty, SOvt.mem_map.
      - split.
        + intros [[Hk [u [Hu ->]]] | H]; [| destruct (T.VSet.empty_spec H)].
          exists nil, u; split; [constructor | auto].
        + intros [l' [u [Hs [Hk [Hu ->]]]]]; inversion Hs; subst.
          left; split; [exact Hk | exists u; auto].
      - rewrite IH; split.
        + intros [[Hk [u [Hu ->]]] | [l' [u [Hs H]]]].
          * exists (b :: l), u; split; [constructor | auto].
          * exists l', u; split; [constructor; exact Hs | exact H].
        + intros [l' [u [Hs [Hk [Hu ->]]]]]; inversion Hs; subst;
            [left; split; [exact Hk | exists u; auto]
            | right; exists l', u; auto].
    Qed.

    Definition versions (I : Inst) (depth : nat) (n : Name.t) : T.VSet.t :=
      match n with
      | Name.Root => T.VSet.singleton (Version.Occ (snd (inst_root I)))
      | Name.Loc l a =>
          T.VSet.add Version.Bot
            (if Nat.ltb (length l) depth
             then SOvt.map Version.Occ (C.versions (inst_repo I) a)
             else T.VSet.empty)
      | Name.Walk l a =>
          T.VSet.add Version.Bot
            (along (fun l' => Nat.ltb (length l') depth) l
               (C.versions (inst_repo I) a))
      end.

    Lemma mem_versions_loc : forall I depth l a u,
        T.VSet.In u (versions I depth (Name.Loc l a)) <->
        u = Version.Bot \/
        exists v, length l < depth /\ PkgSet.In (a, v) (inst_repo I) /\
          u = Version.Occ v.
    Proof.
      intros; cbn [versions].
      rewrite SOvt.add_in, SOvt.in_if_empty, SOvt.mem_map, Nat.ltb_lt.
      setoid_rewrite C.mem_versions; firstorder.
    Qed.

    Lemma mem_versions_walk : forall I depth l a v,
        T.VSet.In v (versions I depth (Name.Walk l a)) <->
        v = Version.Bot \/
        exists l' u, Suffix l' l /\ length l' < depth /\
          PkgSet.In (a, u) (inst_repo I) /\ v = Version.Found l' u.
    Proof.
      intros; cbn [versions]; rewrite SOvt.add_in, mem_along.
      setoid_rewrite Nat.ltb_lt; setoid_rewrite C.mem_versions; reflexivity.
    Qed.

    Module SOvp := SetOps VersionOT T.Pkg T.VSet T.PkgSet.
    Definition reduceReal (I : Inst) (depth : nat) : T.PkgSet.t :=
      T.PkgSet.unions
        (List.map (fun n => SOvp.map (fun v => (n, v)) (versions I depth n))
           (rangeNames I depth)).

    Lemma mem_reduceReal : forall I depth n v,
        T.PkgSet.In (n, v) (reduceReal I depth) <->
        InRange I depth n /\ T.VSet.In v (versions I depth n).
    Proof.
      intros I depth n v; unfold reduceReal; rewrite T.PkgSet.mem_unions; split.
      - intros [s [Hs Hv]]; apply List.in_map_iff in Hs.
        destruct Hs as [m [<- Hm]]; apply SOvp.mem_map in Hv.
        destruct Hv as [v' [Hv' E]]; injection E as -> ->.
        split; [apply in_rangeNames; exact Hm | exact Hv'].
      - intros [Hn Hv]; exists (SOvp.map (fun v => (n, v)) (versions I depth n)).
        split; [apply List.in_map_iff; exists n; split;
                [reflexivity | apply in_rangeNames; exact Hn] |].
        apply SOvp.mem_map; exists v; split; [exact Hv | reflexivity].
    Qed.

    Definition accept (l : Path.t) (vs : VSet.t) : T.VSet.t :=
      along (fun _ => true) l vs.

    Definition optAccept (optional : bool) (la : Path.t) (vs : VSet.t)
        : T.VSet.t :=
      if optional then T.VSet.add Version.Bot (accept la vs) else accept la vs.

    Lemma mem_optAccept : forall optional la vs v,
        T.VSet.In v (optAccept optional la vs) <->
        (optional = true /\ v = Version.Bot) \/ T.VSet.In v (accept la vs).
    Proof.
      intros [|] la vs v; cbn [optAccept].
      - rewrite SOvt.add_in; split.
        + intros [H | H]; [left; split; [reflexivity | exact H] |].
          right; exact H.
        + intros [[_ H] | H]; [left; exact H | right; exact H].
      - split; [intro H; right; exact H |].
        intros [[E _] | H]; [discriminate E | exact H].
    Qed.

    Module SOdh := SetOps C.DepElt T.Dependees C.DepRel T.DependeesSet.
    Definition atoms (optional : bool) (E : C.DepRel.t) (p : Pkg.t)
        (l la : Path.t) : T.DependeesSet.t :=
      SOdh.filterMap (fun '(q, (n, vs)) =>
          if Pkg.eq_dec q p then Some (Name.Walk l n, optAccept optional la vs)
          else None)
        E.

    Lemma mem_atoms : forall optional E p l la h,
        T.DependeesSet.In h (atoms optional E p l la) <->
        exists n vs, C.DepRel.In (p, (n, vs)) E /\
          h = (Name.Walk l n, optAccept optional la vs).
    Proof.
      intros optional E p l la h; unfold atoms; rewrite SOdh.mem_filterMap;
        split.
      - intros [[q [n vs]] [He H]]; cbn beta iota in H.
        destruct (Pkg.eq_dec q p) as [-> |]; [| discriminate H].
        injection H as <-; exists n, vs; split; [exact He | reflexivity].
      - intros [n [vs [He ->]]]; exists (p, (n, vs)); split; [exact He |].
        cbn beta iota; apply dec_refl.
    Qed.

    Definition kindAtoms (I : Inst) (peer optional : bool) (p : Pkg.t)
        (l : Path.t) : T.DependeesSet.t :=
      atoms optional (rel I peer optional) p l (land peer l).

    Definition edgeAtoms (I : Inst) (p : Pkg.t) (l : Path.t)
        : T.DependeesSet.t :=
      T.DependeesSet.union
        (T.DependeesSet.union (kindAtoms I false false p l)
           (kindAtoms I true false p l))
        (T.DependeesSet.union (kindAtoms I false true p l)
           (kindAtoms I true true p l)).

    Lemma mem_edgeAtoms : forall I p l h,
        T.DependeesSet.In h (edgeAtoms I p l) <->
        exists peer optional n vs,
          C.DepRel.In (p, (n, vs)) (rel I peer optional) /\
          h = (Name.Walk l n, optAccept optional (land peer l) vs).
    Proof.
      intros I p l h; unfold edgeAtoms, kindAtoms.
      rewrite !T.DependeesSet.union_spec, !mem_atoms; split.
      - intros [[H | H] | [H | H]]; destruct H as [n [vs H]];
          eexists _, _, n, vs; exact H.
      - intros [peer [optional [n [vs H]]]].
        destruct peer, optional;
          [right; right | left; right | right; left | left; left];
          exists n, vs; exact H.
    Qed.

    Definition walkDeps (l : Path.t) (a : N.t) (v : Version.t)
        : T.DependeesSet.t :=
      match v with
      | Version.Occ _ => T.DependeesSet.empty
      | Version.Found l' u =>
          if Path.eq_dec l' l
          then T.DependeesSet.singleton
                 (Name.Loc l a, T.VSet.singleton (Version.Occ u))
          else T.DependeesSet.add (Name.Loc l a, T.VSet.singleton Version.Bot)
                 (T.DependeesSet.singleton
                    (Name.Walk (par l) a, T.VSet.singleton v))
      | Version.Bot =>
          T.DependeesSet.add (Name.Loc l a, T.VSet.singleton Version.Bot)
            (match l with
             | nil => T.DependeesSet.empty
             | _ :: l' =>
                 T.DependeesSet.singleton
                   (Name.Walk l' a, T.VSet.singleton Version.Bot)
             end)
      end.

    Definition dependees (I : Inst) (q : T.Pkg.t) : T.DependeesSet.t :=
      match q with
      | (Name.Root, Version.Occ _) => edgeAtoms I (inst_root I) nil
      | (Name.Loc l a, Version.Occ v) => edgeAtoms I (a, v) (a :: l)
      | (Name.Walk l a, v) => walkDeps l a v
      | _ => T.DependeesSet.empty
      end.

    Module SOpd := SetOps T.Pkg T.DepElt T.PkgSet T.DepRel.
    Module SOhd := SetOps T.Dependees T.DepElt T.DependeesSet T.DepRel.
    Definition reduceDeps (I : Inst) (depth : nat) : T.DepRel.t :=
      SOpd.unionMap (fun q => SOhd.map (fun h => (q, h)) (dependees I q))
        (reduceReal I depth).

    Lemma mem_reduceDeps : forall I depth q h,
        T.DepRel.In (q, h) (reduceDeps I depth) <->
        T.PkgSet.In q (reduceReal I depth) /\ T.DependeesSet.In h (dependees I q).
    Proof.
      intros I depth q h; unfold reduceDeps; rewrite SOpd.mem_unionMap; split.
      - intros [q' [Hq H]]; apply SOhd.mem_map in H.
        destruct H as [h' [Hh E]]; injection E as -> ->; split; assumption.
      - intros [Hq Hh]; exists q; split; [exact Hq |].
        apply SOhd.mem_map; exists h; split; [exact Hh | reflexivity].
    Qed.

    Lemma dependees_reduceDeps : forall I depth q,
        T.PkgSet.In q (reduceReal I depth) ->
        T.dependees (reduceDeps I depth) q = dependees I q.
    Proof.
      intros I depth q Hq; apply T.DependeesSet.ext; intro h.
      rewrite T.mem_dependees, mem_reduceDeps; tauto.
    Qed.

    Definition rootPkg (I : Inst) : T.Pkg.t :=
      (Name.Root, Version.Occ (snd (inst_root I))).

    Definition tryOcc (q : T.Pkg.t) : option OccElt.t :=
      match q with
      | (Name.Loc l a, Version.Occ v) => Some (l, (a, v))
      | _ => None
      end.

    Definition embedOcc (o : OccElt.t) : T.Pkg.t :=
      (Name.Loc (fst o) (fst (snd o)), Version.Occ (snd (snd o))).

    Module SOpl := SetOps T.Pkg OccElt T.PkgSet Layout.
    Definition placementResolution (S : T.PkgSet.t) : Layout.t :=
      SOpl.filterMap tryOcc S.

    Lemma mem_placementResolution : forall S l a v,
        Layout.In (l, (a, v)) (placementResolution S) <->
        T.PkgSet.In (Name.Loc l a, Version.Occ v) S.
    Proof.
      intros S l a v; unfold placementResolution.
      apply (SOpl.mem_filterMap_inv tryOcc embedOcc).
      - intros [l' [a' v']]; reflexivity.
      - intros [[| l1 a1 | l1 a1] [v1 | l2 v2 |]] o H; try discriminate H.
        injection H as <-; reflexivity.
    Qed.

    Lemma choose_decode : forall S l a v,
        T.VersionUnique S -> T.PkgSet.In (Name.Loc l a, v) S ->
        VSet.choose (occupants (placementResolution S) l a) =
        match v with Version.Occ u => Some u | _ => None end.
    Proof.
      intros S l a v Huniq Hv.
      assert (Hocc : forall u,
                 VSet.In u (occupants (placementResolution S) l a) <->
                 v = Version.Occ u).
      { intro u; rewrite mem_occupants, mem_placementResolution.
        split; [intro H; exact (Huniq _ _ _ Hv H) | intros <-; exact Hv]. }
      destruct (VSet.choose (occupants (placementResolution S) l a))
        as [u |] eqn:Hc.
      - apply VSet.choose_spec1, Hocc in Hc; subst v; reflexivity.
      - apply VSet.choose_spec2 in Hc.
        destruct v as [u | |]; try reflexivity.
        exfalso; apply (Hc u), Hocc; reflexivity.
    Qed.

    Definition walkOf (v : Version.t) : option (Path.t * V.t) :=
      match v with Version.Found l u => Some (l, u) | _ => None end.

    Lemma walk_decode : forall I depth S,
        T.IsResolution (reduceReal I depth) (reduceDeps I depth) (rootPkg I) S ->
        forall l a v, T.PkgSet.In (Name.Walk l a, v) S ->
        walk (placementResolution S) l a = walkOf v.
    Proof.
      intros I depth S [Hsub _ Hdep Huniq] l a.
      assert (Hone : forall l0 w n x, T.PkgSet.In (Name.Walk l0 a, w) S ->
                 T.DependeesSet.In (n, T.VSet.singleton x) (walkDeps l0 a w) ->
                 T.PkgSet.In (n, x) S).
      { intros l0 w n x Hq Hh.
        destruct (Hdep _ Hq n (T.VSet.singleton x)) as [w' [Hw' HS]];
          [apply mem_reduceDeps; split; [exact (Hsub _ Hq) | exact Hh] |].
        apply T.VSet.singleton_spec in Hw'; subst w'; exact HS. }
      induction l as [| b l IH]; intros w Hw;
        pose proof (proj2 (proj1 (mem_reduceReal I depth _ _) (Hsub _ Hw))) as Hv;
        apply mem_versions_walk in Hv;
        destruct Hv as [-> | [l' [u [Hs [_ [_ ->]]]]]]; cbn [walk walkOf].
      - rewrite (choose_decode S nil a Version.Bot Huniq); [reflexivity |].
        apply (Hone _ _ _ _ Hw); cbn [walkDeps].
        apply T.DependeesSet.add_spec; left; reflexivity.
      - inversion Hs; subst.
        rewrite (choose_decode S nil a (Version.Occ u) Huniq); [reflexivity |].
        apply (Hone _ _ _ _ Hw); cbn [walkDeps]; rewrite dec_refl.
        apply T.DependeesSet.singleton_spec; reflexivity.
      - rewrite (choose_decode S (b :: l) a Version.Bot Huniq).
        + apply (IH Version.Bot), (Hone _ _ _ _ Hw); cbn [walkDeps].
          apply T.DependeesSet.add_spec; right.
          apply T.DependeesSet.singleton_spec; reflexivity.
        + apply (Hone _ _ _ _ Hw); cbn [walkDeps].
          apply T.DependeesSet.add_spec; left; reflexivity.
      - destruct (Path.eq_dec l' (b :: l)) as [-> | NE].
        + rewrite (choose_decode S (b :: l) a (Version.Occ u) Huniq);
            [reflexivity |].
          apply (Hone _ _ _ _ Hw); cbn [walkDeps]; rewrite dec_refl.
          apply T.DependeesSet.singleton_spec; reflexivity.
        + assert (Hd : walkDeps (b :: l) a (Version.Found l' u) =
                       T.DependeesSet.add
                         (Name.Loc (b :: l) a, T.VSet.singleton Version.Bot)
                         (T.DependeesSet.singleton
                            (Name.Walk l a,
                             T.VSet.singleton (Version.Found l' u))))
            by (cbn [walkDeps]; destruct (Path.eq_dec l' (b :: l));
                [contradiction | reflexivity]).
          rewrite (choose_decode S (b :: l) a Version.Bot Huniq).
          * apply (IH (Version.Found l' u)), (Hone _ _ _ _ Hw); rewrite Hd.
            apply T.DependeesSet.add_spec; right.
            apply T.DependeesSet.singleton_spec; reflexivity.
          * apply (Hone _ _ _ _ Hw); rewrite Hd.
            apply T.DependeesSet.add_spec; left; reflexivity.
    Qed.

    Lemma holds_decode : forall I depth S l p,
        T.IsResolution (reduceReal I depth) (reduceDeps I depth) (rootPkg I) S ->
        (forall n ws, T.DependeesSet.In (n, ws) (edgeAtoms I p l) ->
           exists v, T.VSet.In v ws /\ T.PkgSet.In (n, v) S) ->
        Holds I (placementResolution S) l p.
    Proof.
      intros I depth S l p Hres Hcl peer optional n vs HE.
      assert (Ha : T.DependeesSet.In
                     (Name.Walk l n, optAccept optional (land peer l) vs)
                     (edgeAtoms I p l))
        by (apply mem_edgeAtoms; exists peer, optional, n, vs;
            split; [exact HE | reflexivity]).
      destruct (Hcl _ _ Ha) as [w [Hw HS]].
      pose proof (walk_decode I depth S Hres _ _ _ HS) as Hwalk.
      apply mem_optAccept in Hw; destruct Hw as [[Ho ->] | Hw].
      - right; split; [exact Ho | exact Hwalk].
      - unfold accept in Hw; apply mem_along in Hw.
        destruct Hw as [l' [u [Hs [_ [Hu ->]]]]].
        left; exists l', u; split; [exact Hwalk |].
        split; [exact Hs | exact Hu].
    Qed.

    Lemma placementResolution_loc : forall I depth S,
        T.IsResolution (reduceReal I depth) (reduceDeps I depth) (rootPkg I) S ->
        forall l a v, Layout.In (l, (a, v)) (placementResolution S) ->
        length l < depth /\ PkgSet.In (a, v) (inst_repo I).
    Proof.
      intros I depth S [Hsub _ _ _] l a v H.
      apply mem_placementResolution, Hsub, mem_reduceReal in H.
      destruct H as [_ H]; apply mem_versions_loc in H.
      destruct H as [H | [v' [Hl [Hr E]]]]; [discriminate H |].
      injection E as <-; split; assumption.
    Qed.

    Theorem placement_soundness : forall I depth S,
        T.IsResolution (reduceReal I depth) (reduceDeps I depth) (rootPkg I) S ->
        IsResolution I (reachable I (placementResolution S)) /\
        Depth depth (reachable I (placementResolution S)).
    Proof.
      intros I depth S Hres; pose proof Hres as [Hsub Hroot Hdep Huniq].
      assert (Hcl : forall q n ws, T.PkgSet.In q S ->
                 T.DependeesSet.In (n, ws) (dependees I q) ->
                 exists w, T.VSet.In w ws /\ T.PkgSet.In (n, w) S)
        by (intros q n ws Hq Hh; apply (Hdep _ Hq), mem_reduceDeps;
            split; [exact (Hsub _ Hq) | exact Hh]).
      pose proof (placementResolution_loc I depth S Hres) as Hloc.
      split;
        [| intros l [a v] H; apply mem_reachable in H;
           exact (proj1 (Hloc _ _ _ (proj1 H)))].
      apply (reaches_resolution I (placementResolution S));
        [| | | | intro o; apply mem_reachable].
      - intros l [a v] H; exact (proj2 (Hloc _ _ _ H)).
      - intros l a v v' H H'; apply mem_placementResolution in H, H'.
        pose proof (Huniq _ _ _ H H') as E; injection E as E; exact E.
      - apply (holds_decode I depth S _ _ Hres); intros n ws Hh.
        exact (Hcl _ _ _ Hroot Hh).
      - intros l a v H; apply mem_placementResolution in H.
        apply (holds_decode I depth S _ _ Hres); intros n ws Hh.
        exact (Hcl _ _ _ H Hh).
    Qed.

    Definition value (I : Inst) (L : Layout.t) (n : Name.t) : Version.t :=
      match n with
      | Name.Root => Version.Occ (snd (inst_root I))
      | Name.Loc l a =>
          match VSet.choose (occupants L l a) with
          | Some v => Version.Occ v
          | None => Version.Bot
          end
      | Name.Walk l a =>
          match walk L l a with
          | Some (l', u) => Version.Found l' u
          | None => Version.Bot
          end
      end.

    Definition coreResolution (I : Inst) (depth : nat) (L : Layout.t)
        : T.PkgSet.t :=
      T.PkgSet.ofList (List.map (fun n => (n, value I L n)) (rangeNames I depth)).

    Lemma mem_coreResolution : forall I depth L n v,
        T.PkgSet.In (n, v) (coreResolution I depth L) <->
        InRange I depth n /\ v = value I L n.
    Proof.
      intros I depth L n v; unfold coreResolution.
      rewrite T.PkgSet.mem_ofList, List.in_map_iff, <- in_rangeNames; split.
      - intros [m [E Hm]]; injection E as <- <-; split; [exact Hm | reflexivity].
      - intros [Hn ->]; exists n; split; [reflexivity | exact Hn].
    Qed.

    Lemma choose_occupants : forall I L l a v, IsResolution I L ->
        Layout.In (l, (a, v)) L -> VSet.choose (occupants L l a) = Some v.
    Proof.
      intros I L l a v [_ Hocc _ _ _] H.
      destruct (VSet.choose (occupants L l a)) as [x |] eqn:Hc.
      - apply VSet.choose_spec1, mem_occupants in Hc.
        f_equal; exact (Hocc _ _ _ _ Hc H).
      - apply VSet.choose_spec2 in Hc.
        destruct (Hc v); apply mem_occupants; exact H.
    Qed.

    Lemma resolves_met : forall I depth L l la n vs,
        length l <= depth -> LocPath I (n :: l) -> Resolves L l la n vs ->
        exists v, T.VSet.In v (accept la vs) /\
          T.PkgSet.In (Name.Walk l n, v) (coreResolution I depth L).
    Proof.
      intros I depth L l la n vs Hlen Hk [l' [u [Hw [Hs Hu]]]].
      exists (Version.Found l' u); split.
      - apply mem_along; exists l', u.
        split; [exact Hs |].
        split; [reflexivity | split; [exact Hu | reflexivity]].
      - apply mem_coreResolution; split; [split; assumption |].
        cbn [value]; rewrite Hw; reflexivity.
    Qed.

    Lemma holds_met : forall I depth L l p,
        length l <= depth -> LocPath I l -> Holds I L l p ->
        forall n ws, T.DependeesSet.In (n, ws) (edgeAtoms I p l) ->
        exists v, T.VSet.In v ws /\ T.PkgSet.In (n, v) (coreResolution I depth L).
    Proof.
      intros I depth L l p Hlen Hk Hh n ws Hn.
      apply mem_edgeAtoms in Hn;
        destruct Hn as [peer [optional [m [vs [HE E]]]]].
      injection E as -> ->.
      assert (Hr : InRange I depth (Name.Walk l m))
        by (split; [exact Hlen |];
            apply List.Forall_cons;
            [exact (locNames_deps I peer optional p m vs HE) | exact Hk]).
      destruct (Hh _ _ _ _ HE) as [Hres | [Ho Hw]].
      - destruct (resolves_met I depth L l (land peer l) m vs Hlen
                    (proj2 Hr) Hres) as [w [Hw HS]].
        exists w; split; [apply mem_optAccept; right; exact Hw | exact HS].
      - exists Version.Bot; split; [apply mem_optAccept; left; split;
                                    [exact Ho | reflexivity] |].
        apply mem_coreResolution; split; [exact Hr |].
        cbn [value]; rewrite Hw; reflexivity.
    Qed.

    Lemma walk_par_inRange : forall I depth l a,
        InRange I depth (Name.Walk l a) -> InRange I depth (Name.Walk (par l) a).
    Proof.
      intros I depth [| b l] a [Hlen Hk]; [split; assumption |].
      cbn [par length] in *; split; [lia |].
      apply List.Forall_cons;
        [exact (List.Forall_inv Hk)
        | exact (List.Forall_inv_tail (List.Forall_inv_tail Hk))].
    Qed.

    Theorem placement_completeness : forall I depth L,
        IsResolution I L -> Depth depth L ->
        T.IsResolution (reduceReal I depth) (reduceDeps I depth) (rootPkg I)
          (coreResolution I depth L).
    Proof.
      intros I depth L [Hsub _ _ Hroot Hdeps] Hdepth.
      assert (Hmet : forall n ws, InRange I depth n -> T.VSet.In (value I L n) ws ->
                 exists w, T.VSet.In w ws /\
                   T.PkgSet.In (n, w) (coreResolution I depth L))
        by (intros n ws Hn Hw; exists (value I L n); split;
            [exact Hw | apply mem_coreResolution; split;
                        [exact Hn | reflexivity]]).
      constructor.
      - intros [n w] Hq; apply mem_coreResolution in Hq; destruct Hq as [Hn ->].
        apply mem_reduceReal; split; [exact Hn |].
        destruct n as [| l a | l a]; cbn [value].
        + apply T.VSet.singleton_spec; reflexivity.
        + apply mem_versions_loc.
          destruct (VSet.choose (occupants L l a)) as [v |] eqn:Hc;
            [right | left; reflexivity].
          apply VSet.choose_spec1, mem_occupants in Hc.
          exists v; split; [exact (Hdepth _ _ Hc) |].
          split; [exact (Hsub _ _ Hc) | reflexivity].
        + apply mem_versions_walk.
          destruct (walk L l a) as [[l' u] |] eqn:Hw;
            [right | left; reflexivity].
          apply walk_found in Hw; destruct Hw as [Hin Hs].
          exists l', u; split; [exact Hs |].
          split; [exact (Hdepth _ _ Hin) |].
          split; [exact (Hsub _ _ Hin) | reflexivity].
      - apply mem_coreResolution; split; [exact Logic.I | reflexivity].
      - intros [n w] Hq n' ws Hh; apply mem_coreResolution in Hq.
        destruct Hq as [Hn ->]; apply mem_reduceDeps in Hh.
        destruct Hh as [_ Hh].
        destruct n as [| l a | l a]; cbn [value dependees] in Hh.
        + apply (holds_met I depth L nil (inst_root I));
            [cbn [length]; lia | constructor | exact Hroot | exact Hh].
        + destruct (VSet.choose (occupants L l a)) as [v |] eqn:Hc;
            [| destruct (T.DependeesSet.empty_spec Hh)].
          apply VSet.choose_spec1, mem_occupants in Hc.
          destruct Hn as [Hlen Hk]; pose proof (Hdepth _ _ Hc).
          apply (holds_met I depth L (a :: l) (a, v));
            [cbn [length]; lia | exact Hk | exact (Hdeps _ _ _ Hc) | exact Hh].
        + assert (Hup := walk_par_inRange I depth l a Hn).
          destruct (VSet.choose (occupants L l a)) as [v |] eqn:Hc.
          * assert (Hw : walk L l a = Some (l, v))
              by (destruct l; cbn [walk]; rewrite Hc; reflexivity).
            rewrite Hw in Hh; cbn [walkDeps] in Hh; rewrite dec_refl in Hh.
            apply T.DependeesSet.singleton_spec in Hh; injection Hh as -> ->.
            apply Hmet; [exact Hn |].
            cbn [value]; rewrite Hc; apply T.VSet.singleton_spec; reflexivity.
          * assert (Hbot : forall ws', T.VSet.In Version.Bot ws' ->
                      exists w, T.VSet.In w ws' /\
                        T.PkgSet.In (Name.Loc l a, w) (coreResolution I depth L))
              by (intros ws' Hb; apply Hmet;
                  [exact Hn | cbn [value]; rewrite Hc; exact Hb]).
            destruct l as [| b l]; cbn [walk] in Hh; rewrite Hc in Hh.
            -- cbn [walkDeps] in Hh; apply T.DependeesSet.add_spec in Hh.
               destruct Hh as [Hh | Hh];
                 [| destruct (T.DependeesSet.empty_spec Hh)].
               injection Hh as -> ->.
               apply Hbot, T.VSet.singleton_spec; reflexivity.
            -- destruct (walk L l a) as [[l' u] |] eqn:Hw;
                 cbn [walkDeps par] in Hh, Hup.
               ++ destruct (Path.eq_dec l' (b :: l)) as [E | NE].
                  { apply walk_found in Hw; destruct Hw as [_ Hs].
                    apply suffix_length in Hs; subst l'.
                    cbn [length] in Hs; lia. }
                  apply T.DependeesSet.add_spec in Hh.
                  rewrite T.DependeesSet.singleton_spec in Hh.
                  destruct Hh as [Hh | Hh]; injection Hh as -> ->;
                    [apply Hbot, T.VSet.singleton_spec; reflexivity |].
                  apply Hmet; [exact Hup |].
                  cbn [value]; rewrite Hw; apply T.VSet.singleton_spec;
                    reflexivity.
               ++ apply T.DependeesSet.add_spec in Hh.
                  rewrite T.DependeesSet.singleton_spec in Hh.
                  destruct Hh as [Hh | Hh]; injection Hh as -> ->;
                    [apply Hbot, T.VSet.singleton_spec; reflexivity |].
                  apply Hmet; [exact Hup |].
                  cbn [value]; rewrite Hw; apply T.VSet.singleton_spec;
                    reflexivity.
      - intros n w w' H H'; apply mem_coreResolution in H, H'.
        destruct H as [_ ->], H' as [_ ->]; reflexivity.
    Qed.

    Lemma keyed_layout : forall I L l a v, IsResolution I L ->
        Layout.In (l, (a, v)) L -> LocPath I (a :: l).
    Proof.
      intros I L l; induction l as [| b l IH]; intros a v Hres H;
        pose proof Hres as [Hsub _ Htree _ _];
        apply List.Forall_cons; try exact (locNames_repo I _ _ (Hsub _ _ H));
        [constructor |].
      destruct (Htree _ _ _ H) as [u Hu]; exact (IH _ _ Hres Hu).
    Qed.

    Theorem placement_retraction : forall I depth L,
        IsResolution I L -> Depth depth L ->
        placementResolution (coreResolution I depth L) = L.
    Proof.
      intros I depth L Hres Hdepth; apply Layout.ext; intros [l [a v]].
      rewrite mem_placementResolution, mem_coreResolution; cbn [value].
      split.
      - intros [_ E].
        destruct (VSet.choose (occupants L l a)) as [x |] eqn:Hc;
          [| discriminate E].
        injection E as <-; apply mem_occupants, VSet.choose_spec1; exact Hc.
      - intro H; rewrite (choose_occupants I L l a v Hres H).
        split; [| reflexivity].
        pose proof (Hdepth _ _ H).
        split; [lia | exact (keyed_layout I L l a v Hres H)].
    Qed.

    Lemma edgeAtoms_inRange : forall I depth l p n ws,
        length l <= depth -> LocPath I l ->
        T.DependeesSet.In (n, ws) (edgeAtoms I p l) -> InRange I depth n.
    Proof.
      intros I depth l p n ws Hlen Hk Hh.
      apply mem_edgeAtoms in Hh;
        destruct Hh as [peer [optional [m [vs [HE E]]]]].
      injection E as -> _; split; [exact Hlen |].
      apply List.Forall_cons;
        [exact (locNames_deps I peer optional p m vs HE) | exact Hk].
    Qed.

    Lemma dependees_inRange : forall I depth q h,
        T.PkgSet.In q (reduceReal I depth) ->
        T.DependeesSet.In h (dependees I q) -> InRange I depth (fst h).
    Proof.
      intros I depth [m w] [n ws] Hq Hh; cbn [fst].
      apply mem_reduceReal in Hq; destruct Hq as [Hm Hw].
      destruct m as [| l a | l a].
      - destruct w; cbn [dependees] in Hh;
          try destruct (T.DependeesSet.empty_spec Hh).
        apply (edgeAtoms_inRange I depth nil (inst_root I) n ws);
          [cbn [length]; lia | constructor | exact Hh].
      - destruct Hm as [Hlen Hk]; apply mem_versions_loc in Hw.
        destruct Hw as [-> | [v [Hl [_ ->]]]]; cbn [dependees] in Hh;
          [destruct (T.DependeesSet.empty_spec Hh) |].
        apply (edgeAtoms_inRange I depth (a :: l) (a, v) n ws);
          [cbn [length]; lia | exact Hk | exact Hh].
      - pose proof (walk_par_inRange I depth l a Hm) as Hup.
        destruct w as [v | l' u |]; cbn [dependees walkDeps] in Hh;
          [destruct (T.DependeesSet.empty_spec Hh) | |].
        + destruct (Path.eq_dec l' l).
          * apply T.DependeesSet.singleton_spec in Hh; injection Hh as -> _.
            exact Hm.
          * apply T.DependeesSet.add_spec in Hh.
            rewrite T.DependeesSet.singleton_spec in Hh.
            destruct Hh as [Hh | Hh]; injection Hh as -> _;
              [exact Hm | exact Hup].
        + apply T.DependeesSet.add_spec in Hh.
          destruct Hh as [Hh | Hh]; [injection Hh as -> _; exact Hm |].
          destruct l as [| b l]; [destruct (T.DependeesSet.empty_spec Hh) |].
          apply T.DependeesSet.singleton_spec in Hh; injection Hh as -> _.
          exact Hup.
    Qed.

    Inductive Reached (I : Inst) (depth : nat) : T.Pkg.t -> Prop :=
    | reached_root : Reached I depth (rootPkg I)
    | reached_dependee : forall q n vs v,
        Reached I depth q -> T.DependeesSet.In (n, vs) (dependees I q) ->
        T.VSet.In v (versions I depth n) -> Reached I depth (n, v).

    Theorem reached_reduceReal : forall I depth q,
        Reached I depth q -> T.PkgSet.In q (reduceReal I depth).
    Proof.
      intros I depth q H; induction H as [| q n vs v _ IH Hh Hv];
        apply mem_reduceReal.
      - split; [exact Logic.I | apply T.VSet.singleton_spec; reflexivity].
      - split; [exact (dependees_inRange I depth q (n, vs) IH Hh) | exact Hv].
    Qed.

    Theorem lookup_resolution : forall I depth S,
        (forall q, T.PkgSet.In q S -> Reached I depth q) ->
        T.PkgSet.In (rootPkg I) S ->
        (forall q, T.PkgSet.In q S ->
         forall n vs, T.DependeesSet.In (n, vs) (dependees I q) ->
         exists v, T.VSet.In v vs /\ T.PkgSet.In (n, v) S) ->
        T.VersionUnique S ->
        T.IsResolution (reduceReal I depth) (reduceDeps I depth) (rootPkg I) S.
    Proof.
      intros I depth S Hreach HrS Hclo Huniq; constructor.
      - intros q Hs; exact (reached_reduceReal I depth q (Hreach q Hs)).
      - exact HrS.
      - intros q Hs n vs Hd; apply mem_reduceDeps in Hd.
        exact (Hclo q Hs n vs (proj2 Hd)).
      - exact Huniq.
    Qed.

    Module Lookup.
      Module PkgFibred := FibredRel N V Pkg PkgSet.
      Module DepFibred := FibredRel Pkg C.Dependees C.DepElt C.DepRel.

      Definition nameSubInst (I : Inst) (a : N.t) : Inst :=
        {| inst_repo := PkgFibred.tailFibre (inst_repo I) a
         ; inst_deps := C.DepRel.empty
         ; inst_peers := C.DepRel.empty
         ; inst_optDeps := C.DepRel.empty
         ; inst_optPeers := C.DepRel.empty
         ; inst_root := inst_root I |}.

      Definition occSubInst (I : Inst) (p : Pkg.t) : Inst :=
        {| inst_repo := PkgSet.empty
         ; inst_deps := DepFibred.tailFibre (inst_deps I) p
         ; inst_peers := DepFibred.tailFibre (inst_peers I) p
         ; inst_optDeps := DepFibred.tailFibre (inst_optDeps I) p
         ; inst_optPeers := DepFibred.tailFibre (inst_optPeers I) p
         ; inst_root := inst_root I |}.

      Definition Reached (I : Inst) (depth : nat) (n : Name.t) : Prop :=
        exists q h, T.DepRel.In (q, (n, h)) (reduceDeps I depth).

      Lemma versions_fibre : forall R a,
          C.versions (PkgFibred.tailFibre R a) a = C.versions R a.
      Proof.
        intros R a; apply C.versions_ext; intro v.
        rewrite PkgFibred.mem_tailFibre.
        split; [intros [H _]; exact H | intro H; split; [exact H | reflexivity]].
      Qed.

      Lemma atoms_fibre : forall optional E p l la,
          atoms optional (DepFibred.tailFibre E p) p l la =
            atoms optional E p l la.
      Proof.
        intros optional E p l la; apply T.DependeesSet.ext; intro h.
        rewrite !mem_atoms.
        split; intros [n [vs [HE ->]]]; exists n, vs; (split; [| reflexivity]).
        - apply DepFibred.mem_tailFibre in HE; exact (proj1 HE).
        - apply DepFibred.mem_tailFibre; split; [exact HE | reflexivity].
      Qed.

      Lemma edgeAtoms_sub : forall I l p,
          edgeAtoms (occSubInst I p) p l = edgeAtoms I p l.
      Proof.
        intros I l p; unfold edgeAtoms, kindAtoms; cbn [rel occSubInst
          inst_deps inst_peers inst_optDeps inst_optPeers].
        rewrite !atoms_fibre; reflexivity.
      Qed.

      Lemma reached_inRange : forall I depth n, Reached I depth n -> InRange I depth n.
      Proof.
        intros I depth n [q [h Hh]]; apply mem_reduceDeps in Hh.
        exact (dependees_inRange I depth q (n, h) (proj1 Hh) (proj2 Hh)).
      Qed.

      Lemma versions_reduceReal : forall I depth n, InRange I depth n ->
          T.versions (reduceReal I depth) n = versions I depth n.
      Proof.
        intros I depth n Hn; apply T.VSet.ext; intro w.
        rewrite T.mem_versions, mem_reduceReal; tauto.
      Qed.

      Theorem versions_lookupRoot : forall I depth,
          T.versions (reduceReal I depth) Name.Root =
          T.versions
            (reduceReal
               {| inst_repo := PkgSet.empty
                ; inst_deps := C.DepRel.empty
                ; inst_peers := C.DepRel.empty
                ; inst_optDeps := C.DepRel.empty
                ; inst_optPeers := C.DepRel.empty
                ; inst_root := inst_root I |} depth)
            Name.Root.
      Proof.
        intros I depth; rewrite !versions_reduceReal by exact Logic.I.
        reflexivity.
      Qed.

      Theorem versions_lookupLoc : forall I depth l a,
          Reached I depth (Name.Loc l a) ->
          T.versions (reduceReal I depth) (Name.Loc l a) =
          versions (nameSubInst I a) depth (Name.Loc l a).
      Proof.
        intros I depth l a H.
        rewrite (versions_reduceReal I depth _ (reached_inRange I depth _ H)).
        cbn [versions nameSubInst inst_repo]; rewrite versions_fibre.
        reflexivity.
      Qed.

      Theorem versions_lookupWalk : forall I depth l a,
          Reached I depth (Name.Walk l a) ->
          T.versions (reduceReal I depth) (Name.Walk l a) =
          versions (nameSubInst I a) depth (Name.Walk l a).
      Proof.
        intros I depth l a H.
        rewrite (versions_reduceReal I depth _ (reached_inRange I depth _ H)).
        cbn [versions nameSubInst inst_repo]; rewrite versions_fibre.
        reflexivity.
      Qed.

      Theorem dependees_lookupRoot : forall I depth,
          T.dependees (reduceDeps I depth) (rootPkg I) =
          dependees (occSubInst I (inst_root I)) (rootPkg I).
      Proof.
        intros I depth; rewrite dependees_reduceDeps.
        - exact (eq_sym (edgeAtoms_sub I nil (inst_root I))).
        - apply mem_reduceReal; split; [exact Logic.I |].
          apply T.VSet.singleton_spec; reflexivity.
      Qed.

      Theorem dependees_lookupLoc : forall I depth l a v,
          T.PkgSet.In (Name.Loc l a, Version.Occ v) (reduceReal I depth) ->
          T.dependees (reduceDeps I depth) (Name.Loc l a, Version.Occ v) =
          dependees (occSubInst I (a, v)) (Name.Loc l a, Version.Occ v).
      Proof.
        intros I depth l a v H; rewrite (dependees_reduceDeps I depth _ H).
        exact (eq_sym (edgeAtoms_sub I (a :: l) (a, v))).
      Qed.

      Theorem dependees_lookupAbsent : forall I depth l a,
          T.dependees (reduceDeps I depth) (Name.Loc l a, Version.Bot) =
          T.DependeesSet.empty.
      Proof.
        intros I depth l a; apply T.dependees_empty_iff; intros h H.
        apply mem_reduceDeps in H; destruct H as [_ H].
        destruct (T.DependeesSet.empty_spec H).
      Qed.

      Theorem dependees_lookupWalk : forall I depth l a w,
          T.PkgSet.In (Name.Walk l a, w) (reduceReal I depth) ->
          T.dependees (reduceDeps I depth) (Name.Walk l a, w) =
          dependees
            {| inst_repo := PkgSet.empty
             ; inst_deps := C.DepRel.empty
             ; inst_peers := C.DepRel.empty
             ; inst_optDeps := C.DepRel.empty
             ; inst_optPeers := C.DepRel.empty
             ; inst_root := inst_root I |}
            (Name.Walk l a, w).
      Proof.
        intros I depth l a w H; rewrite (dependees_reduceDeps I depth _ H).
        reflexivity.
      Qed.
    End Lookup.
  End Reduction.
End Placement.

