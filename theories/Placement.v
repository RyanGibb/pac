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

  (* An edge's kind: a peer refuses its declarer's own directory, and an
     optional edge is also met when its walk finds nothing, though a copy
     it finds must still be in range. *)
  Definition rel (I : Inst) (pe o : bool) : C.DepRel.t :=
    match pe, o with
    | false, false => inst_deps I
    | true, false => inst_peers I
    | false, true => inst_optDeps I
    | true, true => inst_optPeers I
    end.

  Definition land (pe : bool) (l : Path.t) : Path.t :=
    if pe then par l else l.

  (* Core's versions inserts one version at a time, quadratic in a name's
     versions; this sorts them in one go. *)
  Definition repoVersions (R : PkgSet.t) (a : N.t) : VSet.t :=
    C.SOpv.filterMap
      (fun '(m, v) => if N.eq_dec m a then Some v else None) R.

  Lemma mem_repoVersions : forall R a v,
      VSet.In v (repoVersions R a) <-> PkgSet.In (a, v) R.
  Proof.
    intros R a v; unfold repoVersions; rewrite C.SOpv.mem_filterMap; split.
    - intros [[m u] [H E]]; cbn beta iota in E.
      destruct (N.eq_dec m a) as [-> |]; [| discriminate E].
      injection E as ->; exact H.
    - intro H; exists (a, v); split; [exact H | cbn beta iota; apply dec_refl].
  Qed.

  Lemma repoVersions_ext : forall R R' a,
      (forall v, PkgSet.In (a, v) R <-> PkgSet.In (a, v) R') ->
      repoVersions R a = repoVersions R' a.
  Proof.
    intros R R' a H; apply VSet.ext; intro v.
    rewrite !mem_repoVersions; exact (H v).
  Qed.

  Module SOlp := SetOps OccElt Pkg Layout PkgSet.
  Definition occupants (L : Layout.t) (l : Path.t) (a : N.t) : VSet.t :=
    repoVersions
      (SOlp.filterMap (fun '(l', p) =>
           if Path.eq_dec l' l then Some p else None) L)
      a.

  Lemma mem_occupants : forall L l a v,
      VSet.In v (occupants L l a) <-> Layout.In (l, (a, v)) L.
  Proof.
    intros L l a v; unfold occupants.
    rewrite mem_repoVersions, SOlp.mem_filterMap; split.
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
      (o : bool) : Prop :=
    Resolves L l la n vs \/ (o = true /\ walk L l n = None).

  (* The root's peers may land in its own directory, as par nil is nil. *)
  Definition Holds (I : Inst) (L : Layout.t) (l : Path.t) (p : Pkg.t) : Prop :=
    forall pe o n vs, C.DepRel.In (p, (n, vs)) (rel I pe o) ->
      Meets L l (land pe l) n vs o.

  Record IsResolution (I : Inst) (L : Layout.t) : Prop :=
    { res_subset :
        forall l p, Layout.In (l, p) L -> PkgSet.In p (inst_repo I)
    ; res_occupancy :
        forall l a v v', Layout.In (l, (a, v)) L -> Layout.In (l, (a, v')) L ->
        v = v'
    ; res_tree :
        forall b l p, Layout.In (b :: l, p) L ->
        exists u, Layout.In (l, (b, u)) L
    ; res_root : Holds I L nil (inst_root I)
    ; res_deps :
        forall l p, Layout.In (l, p) L -> Holds I L (fst p :: l) p }.

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
    exists pe o vs, C.DepRel.In (p, (n, vs)) (rel I pe o).

  Inductive Reaches (I : Inst) (L : Layout.t) : OccElt.t -> Prop :=
  | ReachesRoot : forall n l' u,
      Edge I (inst_root I) n -> walk L nil n = Some (l', u) ->
      Reaches I L (l', (n, u))
  | ReachesStep : forall l p n l' u,
      Reaches I L (l, p) -> Edge I p n ->
      walk L (fst p :: l) n = Some (l', u) -> Reaches I L (l', (n, u)).

  Lemma reaches_in : forall I L o, Reaches I L o -> Layout.In o L.
  Proof.
    intros I L o H; destruct H as [n l' u _ Hw | l p n l' u _ _ Hw];
      exact (proj1 (walk_found _ _ _ _ _ Hw)).
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

  Definition Settled (I : Inst) (L : Layout.t) (w : Path.t) : Prop :=
    forall b l u, Suffix (b :: l) w -> Layout.In (l, (b, u)) L ->
    Reaches I L (l, (b, u)).

  Lemma reaches_settled : forall I L, IsResolution I L ->
      forall o, Reaches I L o -> Settled I L (fst (snd o) :: fst o).
  Proof.
    intros I L [_ Hocc _ _ _].
    assert (Hstep : forall w n l' u, Settled I L w ->
               walk L w n = Some (l', u) -> Reaches I L (l', (n, u)) ->
               Settled I L (n :: l')).
    { intros w n l' u Hset Hw Hr b m u' Hs Hin.
      inversion Hs as [| b0 l0 Hs']; subst.
      - assert (u' = u) as -> by exact (Hocc _ _ _ _ Hin (reaches_in _ _ _ Hr)).
        exact Hr.
      - apply (Hset b m u'); [| exact Hin].
        exact (suffix_trans _ _ _ Hs' (proj2 (walk_found _ _ _ _ _ Hw))). }
    intros o H; induction H as [n l' u He Hw | l p n l' u Hr IH He Hw];
      cbn [fst snd] in *.
    - apply (Hstep nil n l' u);
        [| exact Hw | exact (ReachesRoot I L n l' u He Hw)].
      intros b m u' Hs; inversion Hs.
    - apply (Hstep (fst p :: l) n l' u IH Hw).
      exact (ReachesStep I L l p n l' u Hr He Hw).
  Qed.

  Theorem reaches_restriction : forall I L L',
      IsResolution I L ->
      (forall o, Layout.In o L' <-> Layout.In o L /\ Reaches I L o) ->
      IsResolution I L'.
  Proof.
    intros I L L' Hres HL'; pose proof Hres as [Hsub Hocc Htree Hroot Hdeps].
    assert (HinL : forall o, Layout.In o L' -> Layout.In o L)
      by (intros o H; exact (proj1 (proj1 (HL' o) H))).
    assert (Hin' : forall o, Reaches I L o -> Layout.In o L')
      by (intros o H; apply HL'; split; [exact (reaches_in _ _ _ H) | exact H]).
    assert (Hholds : forall w p, Holds I L w p ->
               (forall n l' u, Edge I p n -> walk L w n = Some (l', u) ->
                  Reaches I L (l', (n, u))) ->
               Holds I L' w p).
    { intros w p Hh Hr pe o n vs HE.
      assert (He : Edge I p n) by (exists pe, o, vs; exact HE).
      destruct (Hh _ _ _ _ HE) as [[l' [u [Hw [Hs Hu]]]] | [Ho Hw]].
      - left; exists l', u; split; [| split; assumption].
        apply (walk_restrict L L' w n l' u HinL Hocc Hw), Hin'.
        exact (Hr _ _ _ He Hw).
      - right; split; [exact Ho |].
        exact (walk_none_restrict L L' w n HinL Hw). }
    constructor.
    - intros l p H; exact (Hsub _ _ (HinL _ H)).
    - intros l a v v' H H'; exact (Hocc _ _ _ _ (HinL _ H) (HinL _ H')).
    - intros b l [a v] H; apply HL' in H; destruct H as [HL Hr].
      destruct (Htree _ _ _ HL) as [u Hu]; exists u; apply Hin'.
      apply (reaches_settled I L Hres _ Hr b l u); [| exact Hu].
      cbn [fst snd]; constructor; constructor.
    - apply (Hholds _ _ Hroot); intros n l' u He Hw.
      exact (ReachesRoot I L n l' u He Hw).
    - intros l p H; apply HL' in H; destruct H as [HL Hr].
      apply (Hholds _ _ (Hdeps _ _ HL)); intros n l' u He Hw.
      exact (ReachesStep I L l p n l' u Hr He Hw).
  Qed.

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

    Lemma locNames_deps : forall I pe o p n vs,
        C.DepRel.In (p, (n, vs)) (rel I pe o) -> NSet.In n (locNames I).
    Proof.
      intros I pe o p n vs H; apply NSet.union_spec; right.
      assert (Hn : NSet.In n (relNames (rel I pe o)))
        by (apply SOdn.mem_map; exists (p, (n, vs)); split;
            [exact H | reflexivity]).
      rewrite !NSet.union_spec.
      destruct pe, o; cbn [rel] in Hn; tauto.
    Qed.

    Definition LocPath (I : Inst) (l : Path.t) : Prop :=
      List.Forall (fun b => NSet.In b (locNames I)) l.

    Lemma locPath_par : forall I depth l, length l <= depth -> LocPath I l ->
        length (par l) <= depth /\ LocPath I (par l).
    Proof.
      intros I depth [| b l] Hlen Hk; cbn [par length] in *;
        [split; [lia | exact Hk] |].
      split; [lia | exact (List.Forall_inv_tail Hk)].
    Qed.

    Definition InRange (I : Inst) (depth : nat) (n : Name.t) : Prop :=
      match n with
      | Name.Root => True
      | Name.Loc l a | Name.Walk l a => length l <= depth /\ LocPath I (a :: l)
      end.

    (* The core's repository is a finite set, so the names under the depth
       bound are enumerated rather than characterised, and the reduction is
       its lookups aggregated over them (reduceReal, reduceDeps) rather than
       an inductive of reduced packages. *)
    Fixpoint within (ks : list N.t) (d : nat) : list Path.t :=
      nil :: match d with
             | O => nil
             | S d' => List.flat_map (fun l => List.map (fun a => a :: l) ks)
                         (within ks d')
             end.

    Lemma in_within : forall ks d l,
        List.In l (within ks d) <->
        length l <= d /\ List.Forall (fun b => List.In b ks) l.
    Proof.
      intros ks d; induction d as [| d IH]; intros [| a l];
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

    Lemma mem_along : forall keep l vs w,
        T.VSet.In w (along keep l vs) <->
        exists l' u, Suffix l' l /\ keep l' = true /\ VSet.In u vs /\
          w = Version.Found l' u.
    Proof.
      intros keep l vs w; induction l as [| b l IH]; cbn [along];
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
             then SOvt.map Version.Occ (repoVersions (inst_repo I) a)
             else T.VSet.empty)
      | Name.Walk l a =>
          T.VSet.add Version.Bot
            (along (fun l' => Nat.ltb (length l') depth) l
               (repoVersions (inst_repo I) a))
      end.

    Lemma mem_versions_loc : forall I depth l a w,
        T.VSet.In w (versions I depth (Name.Loc l a)) <->
        w = Version.Bot \/
        exists v, length l < depth /\ PkgSet.In (a, v) (inst_repo I) /\
          w = Version.Occ v.
    Proof.
      intros; cbn [versions].
      rewrite SOvt.add_in, SOvt.in_if_empty, SOvt.mem_map, Nat.ltb_lt.
      setoid_rewrite mem_repoVersions; firstorder.
    Qed.

    Lemma mem_versions_walk : forall I depth l a w,
        T.VSet.In w (versions I depth (Name.Walk l a)) <->
        w = Version.Bot \/
        exists l' u, Suffix l' l /\ length l' < depth /\
          PkgSet.In (a, u) (inst_repo I) /\ w = Version.Found l' u.
    Proof.
      intros; cbn [versions]; rewrite SOvt.add_in, mem_along.
      setoid_rewrite Nat.ltb_lt; setoid_rewrite mem_repoVersions; reflexivity.
    Qed.

    Module SOvp := SetOps VersionOT T.Pkg T.VSet T.PkgSet.
    Definition reduceReal (I : Inst) (depth : nat) : T.PkgSet.t :=
      T.PkgSet.unions
        (List.map (fun n => SOvp.map (fun w => (n, w)) (versions I depth n))
           (rangeNames I depth)).

    Lemma mem_reduceReal : forall I depth n w,
        T.PkgSet.In (n, w) (reduceReal I depth) <->
        InRange I depth n /\ T.VSet.In w (versions I depth n).
    Proof.
      intros I depth n w; unfold reduceReal; rewrite T.PkgSet.mem_unions; split.
      - intros [s [Hs Hw]]; apply List.in_map_iff in Hs.
        destruct Hs as [m [<- Hm]]; apply SOvp.mem_map in Hw.
        destruct Hw as [w' [Hw' E]]; injection E as -> ->.
        split; [apply in_rangeNames; exact Hm | exact Hw'].
      - intros [Hn Hw]; exists (SOvp.map (fun w => (n, w)) (versions I depth n)).
        split; [apply List.in_map_iff; exists n; split;
                [reflexivity | apply in_rangeNames; exact Hn] |].
        apply SOvp.mem_map; exists w; split; [exact Hw | reflexivity].
    Qed.

    Definition accept (l : Path.t) (vs : VSet.t) : T.VSet.t :=
      along (fun _ => true) l vs.

    (* An optional edge's walk may also find nothing. *)
    Definition admit (o : bool) (la : Path.t) (vs : VSet.t) : T.VSet.t :=
      if o then T.VSet.add Version.Bot (accept la vs) else accept la vs.

    Lemma mem_admit : forall o la vs w,
        T.VSet.In w (admit o la vs) <->
        (o = true /\ w = Version.Bot) \/ T.VSet.In w (accept la vs).
    Proof.
      intros [|] la vs w; cbn [admit].
      - rewrite SOvt.add_in; split.
        + intros [H | H]; [left; split; [reflexivity | exact H] |].
          right; exact H.
        + intros [[_ H] | H]; [left; exact H | right; exact H].
      - split; [intro H; right; exact H |].
        intros [[E _] | H]; [discriminate E | exact H].
    Qed.

    Module SOdh := SetOps C.DepElt T.Dependees C.DepRel T.DependeesSet.
    Definition atoms (o : bool) (E : C.DepRel.t) (p : Pkg.t) (l la : Path.t)
        : T.DependeesSet.t :=
      SOdh.filterMap (fun '(q, (n, vs)) =>
          if Pkg.eq_dec q p then Some (Name.Walk l n, admit o la vs) else None)
        E.

    Lemma mem_atoms : forall o E p l la h,
        T.DependeesSet.In h (atoms o E p l la) <->
        exists n vs, C.DepRel.In (p, (n, vs)) E /\
          h = (Name.Walk l n, admit o la vs).
    Proof.
      intros o E p l la h; unfold atoms; rewrite SOdh.mem_filterMap; split.
      - intros [[q [n vs]] [He H]]; cbn beta iota in H.
        destruct (Pkg.eq_dec q p) as [-> |]; [| discriminate H].
        injection H as <-; exists n, vs; split; [exact He | reflexivity].
      - intros [n [vs [He ->]]]; exists (p, (n, vs)); split; [exact He |].
        cbn beta iota; apply dec_refl.
    Qed.

    Definition kindAtoms (I : Inst) (pe o : bool) (p : Pkg.t) (l : Path.t)
        : T.DependeesSet.t :=
      atoms o (rel I pe o) p l (land pe l).

    Definition edgeAtoms (I : Inst) (p : Pkg.t) (l : Path.t)
        : T.DependeesSet.t :=
      T.DependeesSet.union
        (T.DependeesSet.union (kindAtoms I false false p l)
           (kindAtoms I true false p l))
        (T.DependeesSet.union (kindAtoms I false true p l)
           (kindAtoms I true true p l)).

    Lemma mem_edgeAtoms : forall I p l h,
        T.DependeesSet.In h (edgeAtoms I p l) <->
        exists pe o n vs, C.DepRel.In (p, (n, vs)) (rel I pe o) /\
          h = (Name.Walk l n, admit o (land pe l) vs).
    Proof.
      intros I p l h; unfold edgeAtoms, kindAtoms.
      rewrite !T.DependeesSet.union_spec, !mem_atoms; split.
      - intros [[H | H] | [H | H]]; destruct H as [n [vs H]];
          eexists _, _, n, vs; exact H.
      - intros [pe [o [n [vs H]]]].
        destruct pe, o; [right; right | left; right | right; left | left; left];
          exists n, vs; exact H.
    Qed.

    Definition treeAtom (R : PkgSet.t) (l : Path.t) : T.DependeesSet.t :=
      match l with
      | nil => T.DependeesSet.empty
      | b :: l' =>
          T.DependeesSet.singleton
            (Name.Loc l' b, SOvt.map Version.Occ (repoVersions R b))
      end.

    Definition occDeps (I : Inst) (l : Path.t) (p : Pkg.t)
        : T.DependeesSet.t :=
      T.DependeesSet.union (treeAtom (inst_repo I) (par l)) (edgeAtoms I p l).

    Definition walkDeps (l : Path.t) (a : N.t) (w : Version.t)
        : T.DependeesSet.t :=
      match w with
      | Version.Occ _ => T.DependeesSet.empty
      | Version.Found l' u =>
          if Path.eq_dec l' l
          then T.DependeesSet.singleton
                 (Name.Loc l a, T.VSet.singleton (Version.Occ u))
          else T.DependeesSet.add (Name.Loc l a, T.VSet.singleton Version.Bot)
                 (T.DependeesSet.singleton
                    (Name.Walk (par l) a, T.VSet.singleton w))
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
      | (Name.Root, Version.Occ _) => occDeps I nil (inst_root I)
      | (Name.Loc l a, Version.Occ v) => occDeps I (a :: l) (a, v)
      | (Name.Walk l a, w) => walkDeps l a w
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

    Lemma choose_decode : forall S l a w,
        T.VersionUnique S -> T.PkgSet.In (Name.Loc l a, w) S ->
        VSet.choose (occupants (placementResolution S) l a) =
        match w with Version.Occ u => Some u | _ => None end.
    Proof.
      intros S l a w Huniq Hw.
      assert (Hocc : forall v,
                 VSet.In v (occupants (placementResolution S) l a) <->
                 w = Version.Occ v).
      { intro v; rewrite mem_occupants, mem_placementResolution.
        split; [intro H; exact (Huniq _ _ _ Hw H) | intros <-; exact Hw]. }
      destruct (VSet.choose (occupants (placementResolution S) l a))
        as [x |] eqn:Hc.
      - apply VSet.choose_spec1, Hocc in Hc; subst w; reflexivity.
      - apply VSet.choose_spec2 in Hc.
        destruct w as [u | |]; try reflexivity.
        exfalso; apply (Hc u), Hocc; reflexivity.
    Qed.

    Definition walkOf (w : Version.t) : option (Path.t * V.t) :=
      match w with Version.Found l u => Some (l, u) | _ => None end.

    Lemma walk_decode : forall I depth S,
        T.IsResolution (reduceReal I depth) (reduceDeps I depth) (rootPkg I) S ->
        forall l a w, T.PkgSet.In (Name.Walk l a, w) S ->
        walk (placementResolution S) l a = walkOf w.
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
        (forall n ws, T.DependeesSet.In (n, ws) (occDeps I l p) ->
           exists w, T.VSet.In w ws /\ T.PkgSet.In (n, w) S) ->
        Holds I (placementResolution S) l p.
    Proof.
      intros I depth S l p Hres Hcl pe o n vs HE.
      assert (Ha : T.DependeesSet.In (Name.Walk l n, admit o (land pe l) vs)
                     (occDeps I l p)).
      { apply T.DependeesSet.union_spec; right; apply mem_edgeAtoms.
        exists pe, o, n, vs; split; [exact HE | reflexivity]. }
      destruct (Hcl _ _ Ha) as [w [Hw HS]].
      pose proof (walk_decode I depth S Hres _ _ _ HS) as Hwalk.
      apply mem_admit in Hw; destruct Hw as [[Ho ->] | Hw].
      - right; split; [exact Ho | exact Hwalk].
      - unfold accept in Hw; apply mem_along in Hw.
        destruct Hw as [l' [u [Hs [_ [Hu ->]]]]].
        left; exists l', u; split; [exact Hwalk |].
        split; [exact Hs | exact Hu].
    Qed.

    Theorem placement_soundness : forall I depth S,
        T.IsResolution (reduceReal I depth) (reduceDeps I depth) (rootPkg I) S ->
        IsResolution I (placementResolution S) /\
        Depth depth (placementResolution S).
    Proof.
      intros I depth S Hres; pose proof Hres as [Hsub Hroot Hdep Huniq].
      assert (Hcl : forall q n ws, T.PkgSet.In q S ->
                 T.DependeesSet.In (n, ws) (dependees I q) ->
                 exists w, T.VSet.In w ws /\ T.PkgSet.In (n, w) S)
        by (intros q n ws Hq Hh; apply (Hdep _ Hq), mem_reduceDeps;
            split; [exact (Hsub _ Hq) | exact Hh]).
      assert (Hloc : forall l a v,
                 Layout.In (l, (a, v)) (placementResolution S) ->
                 length l < depth /\ PkgSet.In (a, v) (inst_repo I)).
      { intros l a v H.
        apply mem_placementResolution, Hsub, mem_reduceReal in H.
        destruct H as [_ H]; apply mem_versions_loc in H.
        destruct H as [H | [v' [Hl [Hr E]]]]; [discriminate H |].
        injection E as <-; split; assumption. }
      split; [| intros l [a v] H; exact (proj1 (Hloc _ _ _ H))].
      constructor.
      - intros l [a v] H; exact (proj2 (Hloc _ _ _ H)).
      - intros l a v v' H H'; apply mem_placementResolution in H, H'.
        pose proof (Huniq _ _ _ H H') as E; injection E as E; exact E.
      - intros b l [a v] H; apply mem_placementResolution in H.
        destruct (Hcl _ (Name.Loc l b)
                    (SOvt.map Version.Occ (repoVersions (inst_repo I) b)) H)
          as [w [Hw HS]].
        { cbn [dependees occDeps par treeAtom].
          apply T.DependeesSet.union_spec; left.
          apply T.DependeesSet.singleton_spec; reflexivity. }
        apply SOvt.mem_map in Hw; destruct Hw as [u [_ ->]].
        exists u; apply mem_placementResolution; exact HS.
      - apply (holds_decode I depth S _ _ Hres); intros n ws Hh.
        exact (Hcl _ _ _ Hroot Hh).
      - intros l [a v] H; apply mem_placementResolution in H.
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

    Lemma mem_coreResolution : forall I depth L n w,
        T.PkgSet.In (n, w) (coreResolution I depth L) <->
        InRange I depth n /\ w = value I L n.
    Proof.
      intros I depth L n w; unfold coreResolution.
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
        exists w, T.VSet.In w (accept la vs) /\
          T.PkgSet.In (Name.Walk l n, w) (coreResolution I depth L).
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
        exists w, T.VSet.In w ws /\ T.PkgSet.In (n, w) (coreResolution I depth L).
    Proof.
      intros I depth L l p Hlen Hk Hh n ws Hn.
      apply mem_edgeAtoms in Hn; destruct Hn as [pe [o [m [vs [HE E]]]]].
      injection E as -> ->.
      assert (Hr : InRange I depth (Name.Walk l m))
        by (split; [exact Hlen |];
            apply List.Forall_cons;
            [exact (locNames_deps I pe o p m vs HE) | exact Hk]).
      destruct (Hh _ _ _ _ HE) as [Hres | [Ho Hw]].
      - destruct (resolves_met I depth L l (land pe l) m vs Hlen
                    (proj2 Hr) Hres) as [w [Hw HS]].
        exists w; split; [apply mem_admit; right; exact Hw | exact HS].
      - exists Version.Bot; split; [apply mem_admit; left; split;
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
      intros I depth L Hres Hdepth.
      pose proof Hres as [Hsub Hocc Htree Hroot Hdeps].
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
        + unfold occDeps in Hh; cbn [par treeAtom] in Hh.
          apply T.DependeesSet.union_spec in Hh; destruct Hh as [Hh | Hh];
            [destruct (T.DependeesSet.empty_spec Hh) |].
          apply (holds_met I depth L nil (inst_root I));
            [cbn [length]; lia | constructor | exact Hroot | exact Hh].
        + destruct (VSet.choose (occupants L l a)) as [v |] eqn:Hc;
            [| destruct (T.DependeesSet.empty_spec Hh)].
          apply VSet.choose_spec1, mem_occupants in Hc.
          destruct Hn as [Hlen Hk].
          unfold occDeps in Hh; cbn [par] in Hh.
          apply T.DependeesSet.union_spec in Hh; destruct Hh as [Hh | Hh].
          * destruct l as [| b l]; cbn [treeAtom] in Hh;
              [destruct (T.DependeesSet.empty_spec Hh) |].
            apply T.DependeesSet.singleton_spec in Hh; injection Hh as -> ->.
            destruct (Htree _ _ _ Hc) as [u Hu].
            apply Hmet.
            -- cbn [length] in Hlen.
               split; [lia | exact (List.Forall_inv_tail Hk)].
            -- cbn [value]; rewrite (choose_occupants I L l b u Hres Hu).
               apply SOvt.mem_map; exists u; split; [| reflexivity].
               apply mem_repoVersions; exact (Hsub _ _ Hu).
          * pose proof (Hdepth _ _ Hc).
            apply (holds_met I depth L (a :: l) (a, v));
              [cbn [length]; lia | exact Hk | exact (Hdeps _ _ Hc) | exact Hh].
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

    Theorem placementResolution_coreResolution : forall I depth L,
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

      Definition occSubInst (I : Inst) (l : Path.t) (p : Pkg.t) : Inst :=
        {| inst_repo := match l with
                        | nil => PkgSet.empty
                        | b :: _ => PkgFibred.tailFibre (inst_repo I) b
                        end
         ; inst_deps := DepFibred.tailFibre (inst_deps I) p
         ; inst_peers := DepFibred.tailFibre (inst_peers I) p
         ; inst_optDeps := DepFibred.tailFibre (inst_optDeps I) p
         ; inst_optPeers := DepFibred.tailFibre (inst_optPeers I) p
         ; inst_root := inst_root I |}.

      Definition Reached (I : Inst) (depth : nat) (n : Name.t) : Prop :=
        exists q h, T.DepRel.In (q, (n, h)) (reduceDeps I depth).

      Lemma versions_fibre : forall R a,
          repoVersions (PkgFibred.tailFibre R a) a = repoVersions R a.
      Proof.
        intros R a; apply repoVersions_ext; intro v.
        rewrite PkgFibred.mem_tailFibre.
        split; [intros [H _]; exact H | intro H; split; [exact H | reflexivity]].
      Qed.

      Lemma atoms_fibre : forall o E p l la,
          atoms o (DepFibred.tailFibre E p) p l la = atoms o E p l la.
      Proof.
        intros o E p l la; apply T.DependeesSet.ext; intro h.
        rewrite !mem_atoms.
        split; intros [n [vs [HE ->]]]; exists n, vs; (split; [| reflexivity]).
        - apply DepFibred.mem_tailFibre in HE; exact (proj1 HE).
        - apply DepFibred.mem_tailFibre; split; [exact HE | reflexivity].
      Qed.

      Lemma edgeAtoms_sub : forall I l' l p,
          edgeAtoms (occSubInst I l' p) p l = edgeAtoms I p l.
      Proof.
        intros I l' l p; unfold edgeAtoms, kindAtoms; cbn [rel occSubInst
          inst_deps inst_peers inst_optDeps inst_optPeers].
        rewrite !atoms_fibre; reflexivity.
      Qed.

      Lemma occDeps_sub : forall I l p,
          occDeps (occSubInst I (par l) p) l p = occDeps I l p.
      Proof.
        intros I l p; unfold occDeps; rewrite edgeAtoms_sub; f_equal.
        cbn [occSubInst inst_repo].
        destruct l as [| a [| b l]]; cbn [par treeAtom]; try reflexivity.
        rewrite versions_fibre; reflexivity.
      Qed.

      Lemma occDeps_inRange : forall I depth l p n ws,
          length l <= depth -> LocPath I l ->
          T.DependeesSet.In (n, ws) (occDeps I l p) -> InRange I depth n.
      Proof.
        intros I depth l p n ws Hlen Hk Hh.
        destruct (locPath_par I depth l Hlen Hk) as [Htlen Htk].
        unfold occDeps in Hh; rewrite T.DependeesSet.union_spec in Hh.
        destruct Hh as [Hh | Hh].
        - destruct l as [| a [| b l]]; cbn [par treeAtom length] in *;
            try destruct (T.DependeesSet.empty_spec Hh).
          apply T.DependeesSet.singleton_spec in Hh; injection Hh as -> _.
          split; [lia | exact Htk].
        - apply mem_edgeAtoms in Hh; destruct Hh as [pe [o [m [vs [HE E]]]]].
          injection E as -> _; split; [exact Hlen |].
          apply List.Forall_cons;
            [exact (locNames_deps I pe o p m vs HE) | exact Hk].
      Qed.

      Lemma reached_inRange : forall I depth n, Reached I depth n -> InRange I depth n.
      Proof.
        intros I depth n [[m w] [h Hh]]; apply mem_reduceDeps in Hh.
        destruct Hh as [Hq Hh]; apply mem_reduceReal in Hq.
        destruct Hq as [Hm Hw].
        destruct m as [| l a | l a].
        - destruct w; cbn [dependees] in Hh;
            try destruct (T.DependeesSet.empty_spec Hh).
          apply (occDeps_inRange I depth nil (inst_root I) n h);
            [cbn [length]; lia | constructor | exact Hh].
        - destruct Hm as [Hlen Hk]; apply mem_versions_loc in Hw.
          destruct Hw as [-> | [v [Hl [_ ->]]]]; cbn [dependees] in Hh;
            [destruct (T.DependeesSet.empty_spec Hh) |].
          apply (occDeps_inRange I depth (a :: l) (a, v) n h);
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

      Lemma versions_reduceReal : forall I depth n, InRange I depth n ->
          T.versions (reduceReal I depth) n = versions I depth n.
      Proof.
        intros I depth n Hn; apply T.VSet.ext; intro w.
        rewrite T.mem_versions, mem_reduceReal; tauto.
      Qed.

      Theorem versions_lookupRoot : forall I depth,
          T.versions (reduceReal I depth) Name.Root =
          T.VSet.singleton (Version.Occ (snd (inst_root I))).
      Proof. intros I depth; exact (versions_reduceReal I depth Name.Root Logic.I). Qed.

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
          dependees (occSubInst I nil (inst_root I)) (rootPkg I).
      Proof.
        intros I depth; rewrite dependees_reduceDeps.
        - exact (eq_sym (occDeps_sub I nil (inst_root I))).
        - apply mem_reduceReal; split; [exact Logic.I |].
          apply T.VSet.singleton_spec; reflexivity.
      Qed.

      Theorem dependees_lookupLoc : forall I depth l a v,
          T.PkgSet.In (Name.Loc l a, Version.Occ v) (reduceReal I depth) ->
          T.dependees (reduceDeps I depth) (Name.Loc l a, Version.Occ v) =
          dependees (occSubInst I l (a, v)) (Name.Loc l a, Version.Occ v).
      Proof.
        intros I depth l a v H; rewrite (dependees_reduceDeps I depth _ H).
        exact (eq_sym (occDeps_sub I (a :: l) (a, v))).
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
          T.dependees (reduceDeps I depth) (Name.Walk l a, w) = walkDeps l a w.
      Proof. intros I depth l a w H; exact (dependees_reduceDeps I depth _ H). Qed.
    End Lookup.
  End Reduction.
End Placement.

