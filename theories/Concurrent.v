From Stdlib Require Import MSets.
From PackageCalculus Require Import Prelude Core.

Create HintDb cmp_conc.
Create Rewrite HintDb cmp_conc.

Module Concurrent (N V : UsualOrderedType) (G : UsualOrderedType).
  Module Source := Core N V.
  Module Package := Source.Package.
  Module PackageSet := Source.PackageSet.
  Module VSet := Source.VSet.

  Module ParentElt := PairUOT Package Package.
  Module ParentRel := FSetUOT ParentElt.

  Record IsResolution
      (R : PackageSet.t) (D : Source.DependencyRel.t) (g : V.t -> G.t) (r : Package.t)
      (S : PackageSet.t) (pi : ParentRel.t) : Prop :=
    { res_subset : PackageSet.Subset S R
    ; res_root_mem : PackageSet.In r S
    ; res_parent_closure :
        forall p, PackageSet.In p S ->
        forall (n : N.t) (vs : VSet.t),
          Source.DependencyRel.In (p, (n, vs)) D ->
          exists v, VSet.In v vs /\
            PackageSet.In (n, v) S /\ ParentRel.In ((n, v), p) pi
    ; res_pi_functional :
        forall n v v' p,
          ParentRel.In ((n, v), p) pi -> ParentRel.In ((n, v'), p) pi -> v = v'
    ; res_version_granularity :
        forall (n : N.t) (v v' : V.t),
          PackageSet.In (n, v) S -> PackageSet.In (n, v') S -> v <> v' -> g v <> g v'
    ; res_parent_subset :
        forall q p, ParentRel.In (q, p) pi -> PackageSet.In q S /\ PackageSet.In p S }.

  Definition ParentDependency (D : Source.DependencyRel.t) (pi : ParentRel.t) : Prop :=
    forall m u n v, ParentRel.In ((m, u), (n, v)) pi ->
      exists vs, Source.DependencyRel.In ((n, v), (m, vs)) D /\ VSet.In u vs.

  Module Reduction.
    Definition IsSplit (g : V.t -> G.t) (vs : VSet.t) : Prop :=
      exists u u', VSet.In u vs /\ VSet.In u' vs /\ g u <> g u'.

    Definition IsDirect (g : V.t -> G.t) (vs : VSet.t) : Prop :=
      forall u u', VSet.In u vs -> VSet.In u' vs -> g u = g u'.

    Module GEqb := UOTEqb G.
    Definition granEqb : G.t -> G.t -> bool := GEqb.eqb.

    Lemma granEqb_iff : forall a b, granEqb a b = true <-> a = b.
    Proof. exact GEqb.eqb_true_iff. Qed.

    Definition isSplitb (g : V.t -> G.t) (vs : VSet.t) : bool :=
      VSet.exists_ (fun u1 =>
        VSet.exists_ (fun u2 => negb (granEqb (g u1) (g u2))) vs) vs.

    Definition isDirectb (g : V.t -> G.t) (vs : VSet.t) : bool :=
      VSet.for_all (fun u1 =>
        VSet.for_all (fun u2 => granEqb (g u1) (g u2)) vs) vs.

    Lemma isSplitb_iff : forall g vs, isSplitb g vs = true <-> IsSplit g vs.
    Proof.
      intros g vs; unfold isSplitb, IsSplit.
      rewrite VSet.exists_spec'.
      split.
      - intros [u1 [Hu1 H1]].
        rewrite VSet.exists_spec' in H1.
        destruct H1 as [u2 [Hu2 H2]].
        exists u1, u2; repeat split; try assumption.
        apply Bool.negb_true_iff in H2.
        intro E; rewrite <- granEqb_iff in E; congruence.
      - intros [u1 [u2 [Hu1 [Hu2 Hne]]]].
        exists u1; split; [exact Hu1 |].
        rewrite VSet.exists_spec'.
        exists u2; split; [exact Hu2 |].
        apply Bool.negb_true_iff, Bool.not_true_iff_false.
        intro E; exact (Hne (proj1 (granEqb_iff _ _) E)).
    Qed.

    Lemma isSplitb_false_iff : forall g vs,
        isSplitb g vs = false <-> IsDirect g vs.
    Proof.
      intros g vs; split.
      - intros H u1 u2 Hu1 Hu2.
        destruct (G.eq_dec (g u1) (g u2)) as [E | NE]; [exact E |].
        assert (isSplitb g vs = true) as Ht
          by (apply isSplitb_iff; exists u1, u2; auto).
        congruence.
      - intro H; destruct (isSplitb g vs) eqn:E; [| reflexivity].
        apply isSplitb_iff in E; destruct E as [u1 [u2 [Hu1 [Hu2 Hne]]]].
        contradiction (Hne (H u1 u2 Hu1 Hu2)).
    Qed.

    Lemma isDirectb_iff : forall g vs, isDirectb g vs = true <-> IsDirect g vs.
    Proof.
      intros g vs; unfold isDirectb, IsDirect.
      rewrite VSet.for_all_spec'.
      split.
      - intros H u1 u2 Hu1 Hu2.
        specialize (H u1 Hu1).
        rewrite VSet.for_all_spec' in H.
        exact (proj1 (granEqb_iff _ _) (H u2 Hu2)).
      - intros H u1 Hu1.
        rewrite VSet.for_all_spec'.
        intros u2 Hu2; apply granEqb_iff; apply H; assumption.
    Qed.

    Module GranularName := PairUOT N G.
    Module IntermediateName := TripleUOT N V N.
    Module NGF := UOTCompareFacts GranularName.
    Module NVNF := UOTCompareFacts IntermediateName.
    #[local] Hint Rewrite NGF.compare_eq_iff NVNF.compare_eq_iff : cmp_conc.
    #[local] Hint Extern 1 => cmp_by NGF.compare_antisym : cmp_conc.
    #[local] Hint Extern 1 => cmp_by NVNF.compare_antisym : cmp_conc.
    #[local] Hint Extern 1 => cmp_by NGF.compare_lt_trans : cmp_conc.
    #[local] Hint Extern 1 => cmp_by NVNF.compare_lt_trans : cmp_conc.

    Module Name.
      Inductive name : Type :=
      | Granular (n : N.t) (w : G.t)
      | Intermediate (n : N.t) (v : V.t) (m : N.t).
      Definition t := name.

      Definition compare (x y : t) : comparison :=
        match x, y with
        | Granular n1 w1, Granular n2 w2 => GranularName.compare (n1, w1) (n2, w2)
        | Granular _ _, Intermediate _ _ _ => Lt
        | Intermediate _ _ _, Granular _ _ => Gt
        | Intermediate n1 v1 m1, Intermediate n2 v2 m2 =>
            IntermediateName.compare (n1, (v1, m1)) (n2, (v2, m2))
        end.

      Lemma compare_eq_iff : forall x y, compare x y = Eq <-> x = y.
      Proof. cmp_eq_iff cmp_conc. Qed.

      Lemma compare_antisym : forall x y, compare y x = CompOpp (compare x y).
      Proof. cmp_antisym cmp_conc. Qed.

      Lemma compare_lt_trans : forall x y z,
          compare x y = Lt -> compare y z = Lt -> compare x z = Lt.
      Proof. cmp_lt_trans cmp_conc. Qed.
    End Name.

    Module GF := UOTCompareFacts G.
    Module VF := UOTCompareFacts V.
    #[local] Hint Rewrite GF.compare_eq_iff VF.compare_eq_iff : cmp_conc.
    #[local] Hint Extern 1 => cmp_by GF.compare_antisym : cmp_conc.
    #[local] Hint Extern 1 => cmp_by VF.compare_antisym : cmp_conc.
    #[local] Hint Extern 1 => cmp_by GF.compare_lt_trans : cmp_conc.
    #[local] Hint Extern 1 => cmp_by VF.compare_lt_trans : cmp_conc.

    Module Version.
      Inductive version : Type :=
      | Orig (v : V.t)
      | Gran (w : G.t).
      Definition t := version.

      Definition compare (x y : t) : comparison :=
        match x, y with
        | Orig v1, Orig v2 => V.compare v1 v2
        | Orig _, Gran _ => Lt
        | Gran _, Orig _ => Gt
        | Gran w1, Gran w2 => G.compare w1 w2
        end.

      Lemma compare_eq_iff : forall x y, compare x y = Eq <-> x = y.
      Proof. cmp_eq_iff cmp_conc. Qed.

      Lemma compare_antisym : forall x y, compare y x = CompOpp (compare x y).
      Proof. cmp_antisym cmp_conc. Qed.

      Lemma compare_lt_trans : forall x y z,
          compare x y = Lt -> compare y z = Lt -> compare x z = Lt.
      Proof. cmp_lt_trans cmp_conc. Qed.
    End Version.

    Module NameOT := UOTFromCompare Name.
    Module VersionOT := UOTFromCompare Version.
    Module Reduced := Core NameOT VersionOT.

    Definition embedPkg (g : V.t -> G.t) (p : Package.t) : Reduced.Package.t :=
      (Name.Granular (fst p) (g (snd p)), Version.Orig (snd p)).

    Module SOptp := SetOps Package Reduced.Package PackageSet Reduced.PackageSet.
    Definition embedSet (g : V.t -> G.t) (R : PackageSet.t) : Reduced.PackageSet.t :=
      SOptp.map (embedPkg g) R.

    Module SOvcv := SetOps V VersionOT VSet Reduced.VSet.
    Definition embedVS (vs : VSet.t) : Reduced.VSet.t :=
      SOvcv.map Version.Orig vs.

    Definition gransOfVS (g : V.t -> G.t) (vs : VSet.t) : Reduced.VSet.t :=
      SOvcv.map (fun u => Version.Gran (g u)) vs.

    Definition filterGran (g : V.t -> G.t) (w : V.t) (vs : VSet.t) : VSet.t :=
      VSet.filter (fun u => granEqb (g u) (g w)) vs.

    Module SOvtp := SetOps V Reduced.Package VSet Reduced.PackageSet.
    Module SOdtp := SetOps Source.DependencyElt Reduced.Package Source.DependencyRel Reduced.PackageSet.
    Definition reduceReal (R : PackageSet.t) (D : Source.DependencyRel.t) (g : V.t -> G.t) :
        Reduced.PackageSet.t :=
      Reduced.PackageSet.union (embedSet g R)
        (SOdtp.unionMap (fun '((n, v), (m, vs)) =>
             if isSplitb g vs
             then SOvtp.map (fun u =>
                      (Name.Intermediate n v m, Version.Gran (g u)))
                    vs
             else Reduced.PackageSet.empty)
           D).

    Module SOvtd := SetOps V Reduced.DependencyElt VSet Reduced.DependencyRel.
    Module SOdtd := SetOps Source.DependencyElt Reduced.DependencyElt Source.DependencyRel Reduced.DependencyRel.
    Definition reduceDepsDirect (D : Source.DependencyRel.t) (g : V.t -> G.t) :
        Reduced.DependencyRel.t :=
      SOdtd.unionMap (fun '((n, v), (m, vs)) =>
          if isDirectb g vs
          then SOvtd.map (fun u =>
                   ((Name.Granular n (g v), Version.Orig v),
                    (Name.Granular m (g u), embedVS vs)))
                 vs
          else Reduced.DependencyRel.empty)
        D.

    Definition reduceDepsSplitEntry (D : Source.DependencyRel.t) (g : V.t -> G.t) :
        Reduced.DependencyRel.t :=
      SOdtd.filterMap (fun '((n, v), (m, vs)) =>
          if isSplitb g vs
          then Some ((Name.Granular n (g v), Version.Orig v),
                     (Name.Intermediate n v m, gransOfVS g vs))
          else None)
        D.

    Definition reduceDepsSplitFanout (D : Source.DependencyRel.t) (g : V.t -> G.t) :
        Reduced.DependencyRel.t :=
      SOdtd.unionMap (fun '((n, v), (m, vs)) =>
          if isSplitb g vs
          then SOvtd.map (fun u =>
                   ((Name.Intermediate n v m, Version.Gran (g u)),
                    (Name.Granular m (g u), embedVS (filterGran g u vs))))
                 vs
          else Reduced.DependencyRel.empty)
        D.

    Definition reduceDepsEmpty (D : Source.DependencyRel.t) (g : V.t -> G.t) : Reduced.DependencyRel.t :=
      SOdtd.filterMap (fun '((n, v), (m, vs)) =>
          if VSet.is_empty vs
          then Some ((Name.Granular n (g v), Version.Orig v),
                     (Name.Intermediate n v m, Reduced.VSet.empty))
          else None)
        D.

    Definition reduceDeps (D : Source.DependencyRel.t) (g : V.t -> G.t) : Reduced.DependencyRel.t :=
      Reduced.DependencyRel.union (reduceDepsDirect D g)
        (Reduced.DependencyRel.union (reduceDepsSplitEntry D g)
           (Reduced.DependencyRel.union (reduceDepsSplitFanout D g) (reduceDepsEmpty D g))).

    Lemma mem_filterGran : forall g w vs u,
        VSet.In u (filterGran g w vs) <-> VSet.In u vs /\ g u = g w.
    Proof.
      intros g w vs u; unfold filterGran.
      rewrite VSet.filter_spec'.
      rewrite granEqb_iff; reflexivity.
    Qed.
    Inductive ReducedPkg (R : PackageSet.t) (D : Source.DependencyRel.t) (g : V.t -> G.t) :
        Reduced.Package.t -> Prop :=
    | PkgEmbed : forall n v, PackageSet.In (n, v) R ->
        ReducedPkg R D g (Name.Granular n (g v), Version.Orig v)
    | PkgIntermediate : forall n v m vs u,
        Source.DependencyRel.In ((n, v), (m, vs)) D -> IsSplit g vs -> VSet.In u vs ->
        ReducedPkg R D g (Name.Intermediate n v m, Version.Gran (g u)).

    Lemma mem_reduceReal : forall R D g q,
        Reduced.PackageSet.In q (reduceReal R D g) <-> ReducedPkg R D g q.
    Proof.
      intros R D g q; unfold reduceReal, embedSet.
      rewrite Reduced.PackageSet.union_spec, SOptp.mem_map, SOdtp.mem_unionMap.
      split.
      - intros [[[n v] [Hp ->]] | [[[n v] [m vs]] [HD Hh]]];
          [apply PkgEmbed; exact Hp |].
        cbn beta iota in Hh; apply SOdtp.in_if_empty in Hh as [Hs Hm].
        apply SOvtp.mem_map in Hm; destruct Hm as [u [Hu ->]].
        apply isSplitb_iff in Hs; eapply PkgIntermediate; eassumption.
      - destruct 1 as [n v Hp | n v m vs u HD Hs Hu];
          [left; exists (n, v); auto | right].
        exists ((n, v), (m, vs)); split; [exact HD | cbn beta iota].
        apply SOdtp.in_if_empty; rewrite isSplitb_iff, SOvtp.mem_map; eauto.
    Qed.

    Inductive ReducedEdge (D : Source.DependencyRel.t) (g : V.t -> G.t) :
        Reduced.DependencyElt.t -> Prop :=
    | EdgeDirect : forall n v m vs u,
        Source.DependencyRel.In ((n, v), (m, vs)) D -> IsDirect g vs -> VSet.In u vs ->
        ReducedEdge D g ((Name.Granular n (g v), Version.Orig v),
                         (Name.Granular m (g u), embedVS vs))
    | EdgeSplitEntry : forall n v m vs,
        Source.DependencyRel.In ((n, v), (m, vs)) D -> IsSplit g vs ->
        ReducedEdge D g ((Name.Granular n (g v), Version.Orig v),
                         (Name.Intermediate n v m, gransOfVS g vs))
    | EdgeSplitFanout : forall n v m vs u,
        Source.DependencyRel.In ((n, v), (m, vs)) D -> IsSplit g vs -> VSet.In u vs ->
        ReducedEdge D g ((Name.Intermediate n v m, Version.Gran (g u)),
                         (Name.Granular m (g u),
                          embedVS (filterGran g u vs)))
    | EdgeEmpty : forall n v m,
        Source.DependencyRel.In ((n, v), (m, VSet.empty)) D ->
        ReducedEdge D g ((Name.Granular n (g v), Version.Orig v),
                         (Name.Intermediate n v m, Reduced.VSet.empty)).

    Lemma mem_reduceDeps : forall D g y,
        Reduced.DependencyRel.In y (reduceDeps D g) <-> ReducedEdge D g y.
    Proof.
      intros D g y; unfold reduceDeps, reduceDepsDirect, reduceDepsSplitEntry,
        reduceDepsSplitFanout, reduceDepsEmpty.
      rewrite !Reduced.DependencyRel.union_spec, !SOdtd.mem_unionMap, !SOdtd.mem_filterMap.
      split.
      - intros [H | [H | [H | H]]]; destruct H as [[[n v] [m vs]] [HD H]];
          cbn beta iota in H.
        + apply SOdtd.in_if_empty in H as [Hd Hm].
          apply SOvtd.mem_map in Hm; destruct Hm as [u [Hu ->]].
          apply isDirectb_iff in Hd; apply EdgeDirect; assumption.
        + destruct (isSplitb g vs) eqn:Hs; [| discriminate].
          injection H as <-; apply isSplitb_iff in Hs.
          apply EdgeSplitEntry; assumption.
        + apply SOdtd.in_if_empty in H as [Hs Hm].
          apply SOvtd.mem_map in Hm; destruct Hm as [u [Hu ->]].
          apply isSplitb_iff in Hs; apply EdgeSplitFanout; assumption.
        + destruct (VSet.is_empty vs) eqn:He; [| discriminate].
          injection H as <-; apply VSet.is_empty_iff in He; subst vs.
          apply EdgeEmpty; assumption.
      - destruct 1 as [n v m vs u HD Hd Hu | n v m vs HD Hs
                      | n v m vs u HD Hs Hu | n v m HD];
          [left | right; left | right; right; left | right; right; right].
        + exists ((n, v), (m, vs)); split; [exact HD | cbn beta iota].
          apply SOdtd.in_if_empty; rewrite isDirectb_iff, SOvtd.mem_map; eauto.
        + exists ((n, v), (m, vs)); split; [exact HD | cbn beta iota].
          apply isSplitb_iff in Hs; rewrite Hs; reflexivity.
        + exists ((n, v), (m, vs)); split; [exact HD | cbn beta iota].
          apply SOdtd.in_if_empty; rewrite isSplitb_iff, SOvtd.mem_map; eauto.
        + exists ((n, v), (m, VSet.empty)); split; [exact HD | simpl];
            reflexivity.
    Qed.

    Definition tryInvPkg (g : V.t -> G.t) (p' : Reduced.Package.t) : option Package.t :=
      match p' with
      | (Name.Granular n w, Version.Orig v) =>
          if G.eq_dec w (g v) then Some (n, v) else None
      | _ => None
      end.

    Lemma tryInvPkg_embed : forall g p, tryInvPkg g (embedPkg g p) = Some p.
    Proof.
      intros g [n v]; unfold tryInvPkg, embedPkg; cbn [fst snd].
      apply dec_refl.
    Qed.

    Lemma tryInvPkg_some : forall g (p' : Reduced.Package.t) (p : Package.t),
        tryInvPkg g p' = Some p -> embedPkg g p = p'.
    Proof.
      intros g [[n w | n v m] [v' | w']] p H; cbn [tryInvPkg] in H;
        try discriminate.
      destruct (G.eq_dec w (g v')) as [-> | NE]; [| discriminate].
      injection H as <-; reflexivity.
    Qed.

    Module SOtpp := SetOps Reduced.Package Package Reduced.PackageSet PackageSet.
    Lemma embedPkg_injective : forall g (p q : Package.t),
        embedPkg g p = embedPkg g q -> p = q.
    Proof.
      intro g;
        exact (SOtpp.emb_injective (tryInvPkg g) (embedPkg g)
                 (tryInvPkg_embed g)).
    Qed.

    Definition concurrentResolution (g : V.t -> G.t) (S : Reduced.PackageSet.t)
        : PackageSet.t :=
      SOtpp.filterMap (tryInvPkg g) S.

    Lemma mem_concurrentResolution : forall g (S : Reduced.PackageSet.t) (p : Package.t),
        PackageSet.In p (concurrentResolution g S) <-> Reduced.PackageSet.In (embedPkg g p) S.
    Proof.
      intro g; unfold concurrentResolution.
      exact (SOtpp.mem_filterMap_inv (tryInvPkg g) (embedPkg g)
               (tryInvPkg_embed g) (tryInvPkg_some g)).
    Qed.

    Definition piGuardb (g : V.t -> G.t) (S : Reduced.PackageSet.t)
        (n : N.t) (v : V.t) (m : N.t) (vs : VSet.t) (u : V.t) : bool :=
      andb (Reduced.PackageSet.mem (Name.Granular m (g u), Version.Orig u) S)
        (andb (Reduced.PackageSet.mem (Name.Granular n (g v), Version.Orig v) S)
           (implb (isSplitb g vs)
              (VSet.exists_ (fun u0 =>
                   andb (Reduced.PackageSet.mem
                           (Name.Intermediate n v m, Version.Gran (g u0)) S)
                     (granEqb (g u) (g u0)))
                 vs))).

    Lemma piGuardb_iff : forall g S n v m vs u,
        piGuardb g S n v m vs u = true <->
        Reduced.PackageSet.In (Name.Granular m (g u), Version.Orig u) S /\
        Reduced.PackageSet.In (Name.Granular n (g v), Version.Orig v) S /\
        (IsSplit g vs ->
           exists u0, VSet.In u0 vs /\
             Reduced.PackageSet.In (Name.Intermediate n v m, Version.Gran (g u0)) S /\
             g u = g u0).
    Proof.
      intros g S n v m vs u; unfold piGuardb.
      rewrite !Bool.andb_true_iff, Bool.implb_true_iff, !Reduced.PackageSet.mem_spec,
        isSplitb_iff.
      rewrite VSet.exists_spec'.
      split.
      - intros [H1 [H2 H3]]; repeat split; try assumption.
        intro Hs; destruct (H3 Hs) as [u0 [Hu0 Hb]].
        apply Bool.andb_true_iff in Hb; destruct Hb as [Hm Hg].
        apply Reduced.PackageSet.mem_spec in Hm.
        exists u0; repeat split; try assumption.
        exact (proj1 (granEqb_iff _ _) Hg).
      - intros [H1 [H2 H3]]; repeat split; try assumption.
        intro Hs; destruct (H3 Hs) as [u0 [Hu0 [Hm Hg]]].
        exists u0; split; [exact Hu0 |].
        apply Bool.andb_true_iff; split.
        + apply Reduced.PackageSet.mem_spec; exact Hm.
        + apply granEqb_iff; exact Hg.
    Qed.

    Module SOvpp := SetOps V ParentElt VSet ParentRel.
    Module SOdpp := SetOps Source.DependencyElt ParentElt Source.DependencyRel ParentRel.
    Definition parents (D : Source.DependencyRel.t) (g : V.t -> G.t) (S : Reduced.PackageSet.t) :
        ParentRel.t :=
      SOdpp.unionMap (fun '((n, v), (m, vs)) =>
          SOvpp.filterMap (fun u =>
              if piGuardb g S n v m vs u then Some ((m, u), (n, v)) else None)
            vs)
        D.

    Lemma mem_parents : forall D g S m u n v,
        ParentRel.In ((m, u), (n, v)) (parents D g S) <->
        exists vs, Source.DependencyRel.In ((n, v), (m, vs)) D /\
          VSet.In u vs /\
          Reduced.PackageSet.In (Name.Granular n (g v), Version.Orig v) S /\
          Reduced.PackageSet.In (Name.Granular m (g u), Version.Orig u) S /\
          (IsSplit g vs ->
             Reduced.PackageSet.In (Name.Intermediate n v m, Version.Gran (g u)) S).
    Proof.
      intros D g S m u n v; unfold parents; rewrite SOdpp.mem_unionMap.
      split.
      - intros [[[n' v'] [m' vs]] [HeD Hh]]; cbn beta iota in Hh.
        apply SOvpp.mem_filterMap_if in Hh; destruct Hh as [u' [Hu [Hg E]]].
        injection E as <- <- <- <-.
        apply piGuardb_iff in Hg; destruct Hg as (HuS & HvS & Hsc).
        exists vs; repeat split; try assumption.
        intro Hs; destruct (Hsc Hs) as (u0 & _ & Hi & ->); exact Hi.
      - intros (vs & HD & Hu & HvS & HuS & Hsc).
        exists ((n, v), (m, vs)); split; [exact HD | cbn beta iota].
        apply SOvpp.mem_filterMap_if; exists u; rewrite piGuardb_iff.
        split; [exact Hu | split; [| reflexivity]].
        split; [exact HuS | split; [exact HvS |]].
        intro Hs; exists u; auto.
    Qed.

    Lemma embedPkg_mem_reduceReal : forall g (p : Package.t) R D,
        Reduced.PackageSet.In (embedPkg g p) (reduceReal R D g) -> PackageSet.In p R.
    Proof.
      intros g [n v] R D H; apply mem_reduceReal in H.
      unfold embedPkg in H; cbn [fst snd] in H.
      inversion H; subst; assumption.
    Qed.

    Lemma mem_reduceDeps_direct : forall D g n v m vs u,
        Source.DependencyRel.In ((n, v), (m, vs)) D -> IsDirect g vs -> VSet.In u vs ->
        Reduced.DependencyRel.In ((Name.Granular n (g v), Version.Orig v),
                     (Name.Granular m (g u), embedVS vs))
          (reduceDeps D g).
    Proof. intros; apply mem_reduceDeps, EdgeDirect; assumption. Qed.

    Lemma mem_reduceDeps_split1 : forall D g n v m vs,
        Source.DependencyRel.In ((n, v), (m, vs)) D -> IsSplit g vs ->
        Reduced.DependencyRel.In ((Name.Granular n (g v), Version.Orig v),
                     (Name.Intermediate n v m, gransOfVS g vs))
          (reduceDeps D g).
    Proof. intros; apply mem_reduceDeps, EdgeSplitEntry; assumption. Qed.

    Lemma mem_reduceDeps_split2 : forall D g n v m vs u,
        Source.DependencyRel.In ((n, v), (m, vs)) D -> IsSplit g vs -> VSet.In u vs ->
        Reduced.DependencyRel.In ((Name.Intermediate n v m, Version.Gran (g u)),
                     (Name.Granular m (g u), embedVS (filterGran g u vs)))
          (reduceDeps D g).
    Proof. intros; apply mem_reduceDeps, EdgeSplitFanout; assumption. Qed.

    Lemma mem_reduceDeps_empty : forall D g n v m,
        Source.DependencyRel.In ((n, v), (m, VSet.empty)) D ->
        Reduced.DependencyRel.In ((Name.Granular n (g v), Version.Orig v),
                     (Name.Intermediate n v m, Reduced.VSet.empty))
          (reduceDeps D g).
    Proof. intros; apply mem_reduceDeps, EdgeEmpty; assumption. Qed.

    Theorem concurrent_soundness :
      forall (R : PackageSet.t) (D : Source.DependencyRel.t) (g : V.t -> G.t) (r : Package.t)
             (S : Reduced.PackageSet.t),
        Source.FunctionalInName D ->
        Reduced.IsResolution (reduceReal R D g) (reduceDeps D g) (embedPkg g r) S ->
        IsResolution R D g r (concurrentResolution g S) (parents D g S).
    Proof.
      intros R D g r S Hfunc Hres.
      destruct Hres as [Hsub Hroot Hdep Huniq].
      constructor.
      - intros p Hp; apply mem_concurrentResolution in Hp.
        exact (embedPkg_mem_reduceReal g p R D (Hsub _ Hp)).
      - apply mem_concurrentResolution; exact Hroot.
      - intros [pn pv] Hp m vs Hdep0.
        apply mem_concurrentResolution in Hp;
          unfold embedPkg in Hp; simpl in Hp.
        destruct (VSet.is_empty vs) eqn:Hemp.
        + apply VSet.is_empty_iff in Hemp; subst vs.
          destruct (Hdep _ Hp _ _ (mem_reduceDeps_empty D g pn pv m Hdep0))
            as [cv [Hcv _]].
          destruct (SOvcv.empty_in _ Hcv).
        + destruct (isSplitb g vs) eqn:Hs.
          * apply isSplitb_iff in Hs.
            destruct (Hdep _ Hp _ _
                (mem_reduceDeps_split1 D g pn pv m vs Hdep0 Hs))
              as [cv0 [Hcv0 Hcv0S]].
            unfold gransOfVS in Hcv0; apply SOvcv.mem_map in Hcv0;
              destruct Hcv0 as [u0 [Hu0 ->]].
            destruct (Hdep _ Hcv0S _ _
                (mem_reduceDeps_split2 D g pn pv m vs u0 Hdep0 Hs Hu0))
              as [cv [Hcv HcvS]].
            unfold embedVS in Hcv; apply SOvcv.mem_map in Hcv;
              destruct Hcv as [u [Hu ->]].
            apply mem_filterGran in Hu; destruct Hu as [Hu Hgu].
            assert (Reduced.PackageSet.In (Name.Granular m (g u), Version.Orig u) S)
              as HuS
              by (rewrite Hgu; exact HcvS).
            exists u; split; [exact Hu | split].
            -- apply mem_concurrentResolution; exact HuS.
            -- apply mem_parents.
               exists vs.
               repeat split; try assumption.
               intros _; rewrite Hgu; exact Hcv0S.
          * pose proof (proj1 (isSplitb_false_iff g vs) Hs) as Hdir.
            destruct (VSet.choose vs) as [u0 |] eqn:Hch.
            2:{ apply VSet.choose_spec2 in Hch.
                rewrite <- VSet.is_empty_spec in Hch; congruence. }
            pose proof (VSet.choose_spec1 Hch) as Hu0.
            destruct (Hdep _ Hp _ _
                (mem_reduceDeps_direct D g pn pv m vs u0 Hdep0 Hdir Hu0))
              as [cv [Hcv HcvS]].
            unfold embedVS in Hcv; apply SOvcv.mem_map in Hcv;
              destruct Hcv as [u [Hu ->]].
            pose proof (Hdir u u0 Hu Hu0) as Hgu.
            assert (Reduced.PackageSet.In (Name.Granular m (g u), Version.Orig u) S)
              as HuS
              by (rewrite Hgu; exact HcvS).
            exists u; split; [exact Hu | split].
            -- apply mem_concurrentResolution; exact HuS.
            -- apply mem_parents.
               exists vs.
               repeat split; try assumption.
               intro Hsplit; exfalso.
               destruct Hsplit as [u1 [u2 [Hu1 [Hu2 Hne]]]].
               exact (Hne (Hdir u1 u2 Hu1 Hu2)).
      - intros m u u' [pn pv] H1 H2.
        apply mem_parents in H1, H2.
        destruct H1 as (vs & HD1 & Hu & _ & HuS & Hsc).
        destruct H2 as (vs' & HD2 & Hu' & _ & Hu'S & Hsc').
        assert (vs' = vs) as -> by exact (Hfunc _ _ _ _ HD2 HD1).
        assert (g u' = g u) as Hg.
        { destruct (isSplitb g vs) eqn:Hs.
          - apply isSplitb_iff in Hs.
            assert (Version.Gran (g u') = Version.Gran (g u)) as Hg0
              by exact (Huniq _ _ _ (Hsc' Hs) (Hsc Hs)).
            injection Hg0 as Hg0; exact Hg0.
          - exact (proj1 (isSplitb_false_iff g vs) Hs u' u Hu' Hu). }
        rewrite Hg in Hu'S.
        pose proof (Huniq _ _ _ HuS Hu'S) as He.
        injection He as He; exact He.
      - intros n v v' Hv Hv' Hne Hg.
        apply mem_concurrentResolution in Hv, Hv'; unfold embedPkg in Hv, Hv';
          simpl in Hv, Hv'.
        rewrite Hg in Hv.
        pose proof (Huniq _ _ _ Hv Hv') as He.
        injection He as He; exact (Hne He).
      - intros [m u] [n v] Hcp.
        apply mem_parents in Hcp.
        destruct Hcp as (vs & _ & _ & HvS & HuS & _).
        split; apply mem_concurrentResolution; [exact HuS | exact HvS].
    Qed.

    Definition coreResolution (D : Source.DependencyRel.t) (g : V.t -> G.t)
        (S : PackageSet.t) (pi : ParentRel.t) : Reduced.PackageSet.t :=
      Reduced.PackageSet.union (SOptp.map (embedPkg g) S)
        (SOdtp.unionMap (fun '((n, v), (m, vs)) =>
             if andb (isSplitb g vs) (PackageSet.mem (n, v) S)
             then SOvtp.filterMap (fun u =>
                      if andb (PackageSet.mem (m, u) S)
                           (ParentRel.mem ((m, u), (n, v)) pi)
                      then Some (Name.Intermediate n v m, Version.Gran (g u))
                      else None)
                    vs
             else Reduced.PackageSet.empty)
           D).

    Inductive CorePkg (S : PackageSet.t) (pi : ParentRel.t) (D : Source.DependencyRel.t)
        (g : V.t -> G.t) : Reduced.Package.t -> Prop :=
    | CoreGranular : forall n v, PackageSet.In (n, v) S ->
        CorePkg S pi D g (Name.Granular n (g v), Version.Orig v)
    | CoreIntermediate : forall n v m vs u,
        Source.DependencyRel.In ((n, v), (m, vs)) D -> PackageSet.In (n, v) S ->
        IsSplit g vs -> PackageSet.In (m, u) S -> VSet.In u vs ->
        ParentRel.In ((m, u), (n, v)) pi ->
        CorePkg S pi D g (Name.Intermediate n v m, Version.Gran (g u)).

    Lemma mem_coreResolution : forall S pi D g (q : Reduced.Package.t),
        Reduced.PackageSet.In q (coreResolution D g S pi) <-> CorePkg S pi D g q.
    Proof.
      intros S pi D g q; unfold coreResolution.
      rewrite Reduced.PackageSet.union_spec, SOptp.mem_map, SOdtp.mem_unionMap.
      split.
      - intros [[[n v] [HpS ->]] | [[[n v] [m vs]] [HD Hh]]];
          [apply CoreGranular; exact HpS |].
        cbn beta iota in Hh; apply SOdtp.in_if_empty in Hh as [Hg Hm].
        apply SOvtp.mem_filterMap_if in Hm; destruct Hm as [u [Hu [Hb ->]]].
        rewrite Bool.andb_true_iff, isSplitb_iff, PackageSet.mem_spec in Hg.
        rewrite Bool.andb_true_iff, PackageSet.mem_spec, ParentRel.mem_spec in Hb.
        eapply CoreIntermediate; try eassumption; tauto.
      - destruct 1 as [n v HpS | n v m vs u HD Hnv Hs Hmu Hu Hpi];
          [left; exists (n, v); auto | right].
        exists ((n, v), (m, vs)); split; [exact HD | cbn beta iota].
        apply SOdtp.in_if_empty; rewrite SOvtp.mem_filterMap_if.
        rewrite Bool.andb_true_iff, isSplitb_iff, PackageSet.mem_spec.
        split; [tauto |]; exists u.
        rewrite Bool.andb_true_iff, PackageSet.mem_spec, ParentRel.mem_spec.
        repeat split; auto.
    Qed.

    Lemma mem_coreResolution_granular : forall S pi D g n v,
        PackageSet.In (n, v) S ->
        Reduced.PackageSet.In (Name.Granular n (g v), Version.Orig v)
          (coreResolution D g S pi).
    Proof. intros; apply mem_coreResolution, CoreGranular; assumption. Qed.

    Lemma mem_coreResolution_intermediate : forall S pi D g n v m vs u,
        Source.DependencyRel.In ((n, v), (m, vs)) D -> PackageSet.In (n, v) S ->
        IsSplit g vs -> PackageSet.In (m, u) S -> VSet.In u vs ->
        ParentRel.In ((m, u), (n, v)) pi ->
        Reduced.PackageSet.In (Name.Intermediate n v m, Version.Gran (g u))
          (coreResolution D g S pi).
    Proof. intros; apply mem_coreResolution; econstructor; eassumption. Qed.

    Theorem concurrent_completeness :
      forall (R : PackageSet.t) (D : Source.DependencyRel.t) (g : V.t -> G.t) (r : Package.t)
             (S : PackageSet.t) (pi : ParentRel.t),
        IsResolution R D g r S pi ->
        Reduced.IsResolution (reduceReal R D g) (reduceDeps D g)
          (embedPkg g r) (coreResolution D g S pi).
    Proof.
      intros R D g r S pi Hres.
      destruct Hres as [Hsub Hroot Hpc Hpif Hvg Hps].
      constructor.
      - intros q Hq; apply mem_reduceReal; apply mem_coreResolution in Hq.
        destruct Hq as [n v Hnv | n v m vs u HD Hnv Hs Hmu Hu Hpi];
          [apply PkgEmbed, Hsub, Hnv | eapply PkgIntermediate; eassumption].
      - destruct r as [rn rv].
        exact (mem_coreResolution_granular S pi D g rn rv Hroot).
      - intros q Hq md vsd Hd.
        apply mem_coreResolution in Hq; apply mem_reduceDeps in Hd.
        destruct Hq as [n v Hnv | n v m vs u HD Hnv Hs Hmu Hu Hpi].
        + inversion Hd as [n' v' m' vs' u' HD' Hdir' Hu' | n' v' m' vs' HD' Hs'
                          | | n' v' m' HD']; subst.
          * destruct (Hpc _ Hnv _ _ HD') as [u [Huv [HmuS Hpiu]]].
            exists (Version.Orig u); split.
            { unfold embedVS; apply SOvcv.mem_map;
                exists u; split; [exact Huv | reflexivity]. }
            { rewrite <- (Hdir' u u' Huv Hu').
              exact (mem_coreResolution_granular S pi D g m' u HmuS). }
          * destruct (Hpc _ Hnv _ _ HD') as [u [Huv [HmuS Hpiu]]].
            exists (Version.Gran (g u)); split.
            { unfold gransOfVS; apply SOvcv.mem_map;
                exists u; split; [exact Huv | reflexivity]. }
            { exact (mem_coreResolution_intermediate S pi D g n v m' vs' u
                       HD' Hnv Hs' HmuS Huv Hpiu). }
          * destruct (Hpc _ Hnv _ _ HD') as [u [Huv _]].
            destruct (VSet.empty_spec Huv).
        + inversion Hd as [| | n' v' m' vs' u' HD' Hs' Hu' |]; subst.
          match goal with Hg : g u' = g u |- _ => rename Hg into Hgu end.
          destruct (Hpc _ Hnv _ _ HD') as [w [Hw [_ Hpiw]]].
          assert (w = u) as -> by exact (Hpif _ _ _ _ Hpiw Hpi).
          exists (Version.Orig u); split.
          { unfold embedVS; apply SOvcv.mem_map; exists u; split;
              [| reflexivity].
            apply mem_filterGran; split; [exact Hw | symmetry; exact Hgu]. }
          { rewrite Hgu.
            exact (mem_coreResolution_granular S pi D g m u Hmu). }
      - intros n cv1 cv2 H1 H2.
        apply mem_coreResolution in H1, H2.
        inversion H1
          as [n1 v1 Hm1 | n1 v1 m1 vs1 u1 Hd1 Hnv1 Hs1 Hmu1 Hu1 Hpi1]; subst;
          inversion H2
          as [n2 v2 Hm2 | n2 v2 m2 vs2 u2 Hd2 Hnv2 Hs2 Hmu2 Hu2 Hpi2]; subst.
        + destruct (V.eq_dec v1 v2) as [-> | NE]; [reflexivity | exfalso].
          apply (Hvg n1 v1 v2 Hm1 Hm2 NE); congruence.
        + rewrite (Hpif _ _ _ _ Hpi1 Hpi2); reflexivity.
    Qed.

    Lemma concurrentResolution_coreResolution : forall S pi D g,
        concurrentResolution g (coreResolution D g S pi) = S.
    Proof.
      intros S pi D g; apply PackageSet.ext; intros [n v].
      rewrite mem_concurrentResolution, mem_coreResolution.
      unfold embedPkg; cbn [fst snd].
      split; [intro H; inversion H; assumption | apply CoreGranular].
    Qed.

    Lemma coreResolution_granular_inv : forall S pi D g n v,
        Reduced.PackageSet.In (Name.Granular n (g v), Version.Orig v)
          (coreResolution D g S pi) ->
        PackageSet.In (n, v) S.
    Proof.
      intros S pi D g n v H; apply mem_coreResolution in H.
      inversion H; assumption.
    Qed.

    Lemma coreResolution_intermediate_inv : forall S pi D g n v m w,
        Reduced.PackageSet.In (Name.Intermediate n v m, Version.Gran w)
          (coreResolution D g S pi) ->
        exists u, PackageSet.In (m, u) S /\ ParentRel.In ((m, u), (n, v)) pi /\
          g u = w.
    Proof.
      intros S pi D g n v m w H; apply mem_coreResolution in H.
      inversion H; subst; eauto.
    Qed.

    Lemma parents_coreResolution_iff : forall R D g r S pi,
        IsResolution R D g r S pi ->
        forall m u n v,
          ParentRel.In ((m, u), (n, v)) (parents D g (coreResolution D g S pi))
          <-> ParentRel.In ((m, u), (n, v)) pi /\
              exists vs, Source.DependencyRel.In ((n, v), (m, vs)) D /\ VSet.In u vs.
    Proof.
      intros R D g r S pi [_ _ Hpc _ Hvg Hps] m u n v; rewrite mem_parents.
      split.
      - intros (vs & HD & Hu & Hnv & Hmu & Hsplit).
        split; [| exists vs; split; assumption].
        apply coreResolution_granular_inv in Hnv, Hmu.
        destruct (isSplitb g vs) eqn:Es.
        + apply isSplitb_iff in Es.
          pose proof (Hsplit Es) as Hint.
          apply coreResolution_intermediate_inv in Hint.
          destruct Hint as (u1 & Hmu1 & Hpi1 & Hg1).
          destruct (V.eq_dec u u1) as [-> | NE]; [exact Hpi1 | exfalso].
          apply (Hvg m u u1 Hmu Hmu1 NE); congruence.
        + apply isSplitb_false_iff in Es.
          destruct (Hpc _ Hnv _ _ HD) as (w & Hw & HwS & Hpiw).
          destruct (V.eq_dec u w) as [-> | NE]; [exact Hpiw | exfalso].
          exact (Hvg m u w Hmu HwS NE (Es u w Hu Hw)).
      - intros [Hpi (vs & HD & Hu)].
        destruct (Hps _ _ Hpi) as [HmS HnS].
        exists vs.
        split; [exact HD |].
        split; [exact Hu |].
        split; [exact (mem_coreResolution_granular S pi D g n v HnS) |].
        split; [exact (mem_coreResolution_granular S pi D g m u HmS) |].
        intro Hs.
        exact (mem_coreResolution_intermediate S pi D g n v m vs u
                 HD HnS Hs HmS Hu Hpi).
    Qed.

    Theorem concurrent_retraction : forall R D g r S pi,
        IsResolution R D g r S pi -> ParentDependency D pi ->
        concurrentResolution g (coreResolution D g S pi) = S /\
        parents D g (coreResolution D g S pi) = pi.
    Proof.
      intros R D g r S pi Hres Hdep.
      split; [apply concurrentResolution_coreResolution |].
      apply ParentRel.ext; intros [[m u] [n v]].
      rewrite (parents_coreResolution_iff _ _ _ _ _ _ Hres).
      split; [intros [H _]; exact H | intro H; exact (conj H (Hdep _ _ _ _ H))].
    Qed.

    Module Lookup.
      Lemma reduceDeps_mono : forall D D' g (y : Reduced.DependencyElt.t),
          Source.DependencyRel.Subset D' D ->
          Reduced.DependencyRel.In y (reduceDeps D' g) ->
          Reduced.DependencyRel.In y (reduceDeps D g).
      Proof.
        intros D D' g y HD; revert y.
        unfold reduceDeps, reduceDepsDirect, reduceDepsSplitEntry,
          reduceDepsSplitFanout, reduceDepsEmpty.
        repeat apply SOdtd.union_subset.
        - apply SOdtd.unionMap_mono; [exact HD | intros x z Hz; exact Hz].
        - apply SOdtd.filterMap_mono; [exact HD | intros x z Hz; exact Hz].
        - apply SOdtd.unionMap_mono; [exact HD | intros x z Hz; exact Hz].
        - apply SOdtd.filterMap_mono; [exact HD | intros x z Hz; exact Hz].
      Qed.

      Module DependencyRelFibred :=
        FibredLabelledRel Package N VSet.AsUOT Source.DependencyElt Source.DependencyRel.
      Include GranularityFibre N V G Package PackageSet.

      Theorem versions_lookupGranular :
        forall R D g (n : N.t) (w : G.t),
          Reduced.versions (reduceReal R D g) (Name.Granular n w) =
          Reduced.versions (reduceReal (granFibre g R n w) Source.DependencyRel.empty g)
            (Name.Granular n w).
      Proof.
        intros R D g n w; apply Reduced.versions_ext; intro v.
        rewrite !mem_reduceReal.
        split; intro H; inversion H as [qn qv HR |]; subst; apply PkgEmbed.
        - apply mem_granFibre; auto.
        - apply mem_granFibre in HR; tauto.
      Qed.

      Theorem dependees_lookupGranular : forall D g n v,
          Reduced.dependees (reduceDeps D g) (Name.Granular n (g v), Version.Orig v) =
          Reduced.dependees (reduceDeps (DependencyRelFibred.tailFibre D (n, v)) g)
            (Name.Granular n (g v), Version.Orig v).
      Proof.
        intros D g n v; apply Reduced.dependees_ext; intros [m ws].
        split; [| apply reduceDeps_mono, DependencyRelFibred.tailFibre_subset].
        intro H; apply mem_reduceDeps in H; apply mem_reduceDeps.
        inversion H; subst;
          [apply EdgeDirect | apply EdgeSplitEntry | apply EdgeEmpty];
          try assumption;
          apply DependencyRelFibred.mem_tailFibre; (split; [assumption | reflexivity]).
      Qed.

      Theorem dependees_lookupGranularGran : forall D g n (w w' : G.t),
          Reduced.dependees (reduceDeps D g) (Name.Granular n w, Version.Gran w') =
          Reduced.DependeeSet.empty.
      Proof.
        intros D g n w w'; apply Reduced.dependees_empty_iff; intros [m ws] H.
        apply mem_reduceDeps in H; inversion H.
      Qed.

      Theorem versions_lookupIntermediate : forall R D g n v m,
          Reduced.versions (reduceReal R D g) (Name.Intermediate n v m) =
          Reduced.versions
            (reduceReal PackageSet.empty (DependencyRelFibred.endsFibre D (n, v) m) g)
            (Name.Intermediate n v m).
      Proof.
        intros R D g n v m; apply Reduced.versions_ext; intro w.
        rewrite !mem_reduceReal.
        split; intro H; inversion H as [| n' v' m' vs u HD Hs Hu]; subst;
          apply (PkgIntermediate _ _ _ n v m vs u); try assumption.
        - apply DependencyRelFibred.mem_endsFibre.
          split; [exact HD | split; reflexivity].
        - apply DependencyRelFibred.mem_endsFibre in HD; tauto.
      Qed.

      Theorem dependees_lookupIntermediate : forall D g n v m w,
          Reduced.dependees (reduceDeps D g)
            (Name.Intermediate n v m, Version.Gran w) =
          Reduced.dependees (reduceDeps (DependencyRelFibred.endsFibre D (n, v) m) g)
            (Name.Intermediate n v m, Version.Gran w).
      Proof.
        intros D g n v m w; apply Reduced.dependees_ext; intros [m0 ws].
        split; [| apply reduceDeps_mono, DependencyRelFibred.endsFibre_subset].
        intro H; apply mem_reduceDeps in H; apply mem_reduceDeps.
        inversion H as [| | n' v' m' vs u HD Hs Hu |]; subst.
        apply EdgeSplitFanout; try assumption.
        apply DependencyRelFibred.mem_endsFibre.
        split; [exact HD | split; reflexivity].
      Qed.

      Theorem dependees_lookupIntermediateOrig : forall D g n v m u,
          Reduced.dependees (reduceDeps D g)
            (Name.Intermediate n v m, Version.Orig u) =
          Reduced.DependeeSet.empty.
      Proof.
        intros D g n v m u; apply Reduced.dependees_empty_iff; intros [m0 ws] H.
        apply mem_reduceDeps in H; inversion H.
      Qed.

    End Lookup.
  End Reduction.

End Concurrent.
