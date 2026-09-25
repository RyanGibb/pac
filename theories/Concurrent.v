From Stdlib Require Import MSets.
From PackageCalculus Require Import Prelude Core.

Create HintDb cmp_conc.
Create Rewrite HintDb cmp_conc.

Module Concurrent (N V : UsualOrderedType) (G : UsualOrderedType).
  Module C := Core N V.
  Module Pkg := C.Pkg.
  Module PkgSet := C.PkgSet.
  Module VSet := C.VSet.

  Module ParentElt := PairUOT Pkg Pkg.
  Module ParentRel := FSetUOT ParentElt.

  Record IsResolution
      (R : PkgSet.t) (D : C.DepRel.t) (g : V.t -> G.t) (r : Pkg.t)
      (S : PkgSet.t) (pi : ParentRel.t) : Prop :=
    { res_subset : PkgSet.Subset S R
    ; res_root_mem : PkgSet.In r S
    ; res_parent_closure :
        forall p, PkgSet.In p S ->
        forall (n : N.t) (vs : VSet.t),
          C.DepRel.In (p, (n, vs)) D ->
          exists! v, VSet.In v vs /\
            PkgSet.In (n, v) S /\ ParentRel.In ((n, v), p) pi
    ; res_version_granularity :
        forall (n : N.t) (v v' : V.t),
          PkgSet.In (n, v) S -> PkgSet.In (n, v') S -> v <> v' -> g v <> g v'
    ; res_parent_subset :
        forall c p, ParentRel.In (c, p) pi -> PkgSet.In c S /\ PkgSet.In p S }.

  Module Reduction.
    Definition IsSplit (g : V.t -> G.t) (vs : VSet.t) : Prop :=
      exists u1 u2, VSet.In u1 vs /\ VSet.In u2 vs /\ g u1 <> g u2.

    Definition IsDirect (g : V.t -> G.t) (vs : VSet.t) : Prop :=
      forall u1 u2, VSet.In u1 vs -> VSet.In u2 vs -> g u1 = g u2.

    Module GEqb := UOTEqb G.
    (* kept as an alias: "same granularity" is what the guards below mean *)
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

    Module NG := PairUOT N G.
    Module NVN := TripleUOT N V N.
    Module NVS := PairUOT N VSet.AsUOT.
    Module NGNVS := TripleUOT N G NVS.
    Module NGF := UOTCompareFacts NG.
    Module NVNF := UOTCompareFacts NVN.
    Module NGNVSF := UOTCompareFacts NGNVS.
    #[local] Hint Rewrite NGF.compare_eq_iff NVNF.compare_eq_iff
      NGNVSF.compare_eq_iff : cmp_conc.
    #[local] Hint Extern 1 => cmp_by NGF.compare_antisym : cmp_conc.
    #[local] Hint Extern 1 => cmp_by NVNF.compare_antisym : cmp_conc.
    #[local] Hint Extern 1 => cmp_by NGNVSF.compare_antisym : cmp_conc.
    #[local] Hint Extern 1 => cmp_by NGF.compare_lt_trans : cmp_conc.
    #[local] Hint Extern 1 => cmp_by NVNF.compare_lt_trans : cmp_conc.
    #[local] Hint Extern 1 => cmp_by NGNVSF.compare_lt_trans : cmp_conc.

    Module Name.
      (* The reduction's intermediate is GranIntermediate, keyed by the
         depender's granularity: versions of one granularity never coexist,
         so they can share it, and a conflict learned against it then holds
         for all of them.  The declared range stays in the key because two
         of them may declare m differently, and the intermediate's edges
         must be a function of its name.  Intermediate, keyed by the
         depender's version, is the peer and npm reductions' own: a peer
         constraint reads the depender's other dependencies, which versions
         of one granularity need not share. *)
      Inductive name : Type :=
      | Granular (n : N.t) (w : G.t)
      | Intermediate (n : N.t) (v : V.t) (m : N.t)
      | GranIntermediate (n : N.t) (w : G.t) (m : N.t) (vs : VSet.t).
      Definition t := name.

      Definition rank (x : t) : nat :=
        match x with
        | Granular _ _ => 0 | Intermediate _ _ _ => 1
        | GranIntermediate _ _ _ _ => 2
        end.

      Definition compare (x y : t) : comparison :=
        match Nat.compare (rank x) (rank y) with
        | Eq =>
            match x, y with
            | Granular n1 w1, Granular n2 w2 => NG.compare (n1, w1) (n2, w2)
            | Intermediate n1 v1 m1, Intermediate n2 v2 m2 =>
                NVN.compare (n1, (v1, m1)) (n2, (v2, m2))
            | GranIntermediate n1 w1 m1 vs1, GranIntermediate n2 w2 m2 vs2 =>
                NGNVS.compare (n1, (w1, (m1, vs1))) (n2, (w2, (m2, vs2)))
            | _, _ => Eq
            end
        | c => c
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
    Module T := Core NameOT VersionOT.

    Definition embedPkg (g : V.t -> G.t) (p : Pkg.t) : T.Pkg.t :=
      (Name.Granular (fst p) (g (snd p)), Version.Orig (snd p)).

    Module SOptp := SetOps Pkg T.Pkg PkgSet T.PkgSet.
    Definition embedSet (g : V.t -> G.t) (R : PkgSet.t) : T.PkgSet.t :=
      SOptp.map (embedPkg g) R.

    Module SOvcv := SetOps V VersionOT VSet T.VSet.
    Definition embedVS (vs : VSet.t) : T.VSet.t :=
      SOvcv.map Version.Orig vs.

    Definition gransOfVS (g : V.t -> G.t) (vs : VSet.t) : T.VSet.t :=
      SOvcv.map (fun u => Version.Gran (g u)) vs.

    Definition filterGran (g : V.t -> G.t) (w : G.t) (vs : VSet.t) : VSet.t :=
      VSet.filter (fun u => granEqb (g u) w) vs.

    Module SOvtp := SetOps V T.Pkg VSet T.PkgSet.
    Module SOdtp := SetOps C.DepElt T.Pkg C.DepRel T.PkgSet.
    Definition reduceReal (R : PkgSet.t) (D : C.DepRel.t) (g : V.t -> G.t) :
        T.PkgSet.t :=
      T.PkgSet.union (embedSet g R)
        (SOdtp.unionMap (fun '((n, v), (m, vs)) =>
             if isSplitb g vs
             then SOvtp.map (fun u =>
                      (Name.GranIntermediate n (g v) m vs, Version.Gran (g u)))
                    vs
             else T.PkgSet.empty)
           D).

    Module SOvtd := SetOps V T.DepElt VSet T.DepRel.
    Module SOdtd := SetOps C.DepElt T.DepElt C.DepRel T.DepRel.
    Definition reduceDepsDirect (D : C.DepRel.t) (g : V.t -> G.t) :
        T.DepRel.t :=
      SOdtd.unionMap (fun '((n, v), (m, vs)) =>
          if isDirectb g vs
          then SOvtd.map (fun u =>
                   ((Name.Granular n (g v), Version.Orig v),
                    (Name.Granular m (g u), embedVS vs)))
                 vs
          else T.DepRel.empty)
        D.

    Definition reduceDepsSplitEntry (D : C.DepRel.t) (g : V.t -> G.t) :
        T.DepRel.t :=
      SOdtd.filterMap (fun '((n, v), (m, vs)) =>
          if isSplitb g vs
          then Some ((Name.Granular n (g v), Version.Orig v),
                     (Name.GranIntermediate n (g v) m vs, gransOfVS g vs))
          else None)
        D.

    Definition reduceDepsSplitFanout (D : C.DepRel.t) (g : V.t -> G.t) :
        T.DepRel.t :=
      SOdtd.unionMap (fun '((n, v), (m, vs)) =>
          if isSplitb g vs
          then SOvtd.map (fun u =>
                   ((Name.GranIntermediate n (g v) m vs, Version.Gran (g u)),
                    (Name.Granular m (g u), embedVS (filterGran g (g u) vs))))
                 vs
          else T.DepRel.empty)
        D.

    Definition reduceDepsEmpty (D : C.DepRel.t) (g : V.t -> G.t) : T.DepRel.t :=
      SOdtd.filterMap (fun '((n, v), (m, vs)) =>
          if VSet.is_empty vs
          then Some ((Name.Granular n (g v), Version.Orig v),
                     (Name.GranIntermediate n (g v) m vs, T.VSet.empty))
          else None)
        D.

    Definition reduceDeps (D : C.DepRel.t) (g : V.t -> G.t) : T.DepRel.t :=
      T.DepRel.union (reduceDepsDirect D g)
        (T.DepRel.union (reduceDepsSplitEntry D g)
           (T.DepRel.union (reduceDepsSplitFanout D g) (reduceDepsEmpty D g))).

    Lemma mem_filterGran : forall g w vs u,
        VSet.In u (filterGran g w vs) <-> VSet.In u vs /\ g u = w.
    Proof.
      intros g w vs u; unfold filterGran.
      rewrite VSet.filter_spec'.
      rewrite granEqb_iff; reflexivity.
    Qed.

    Lemma mem_reduceReal : forall R D g q,
        T.PkgSet.In q (reduceReal R D g) <->
        (exists p, PkgSet.In p R /\ q = embedPkg g p) \/
        (exists n v m vs u,
            C.DepRel.In ((n, v), (m, vs)) D /\ IsSplit g vs /\ VSet.In u vs /\
            q = (Name.GranIntermediate n (g v) m vs, Version.Gran (g u))).
    Proof.
      intros R D g q; unfold reduceReal, embedSet.
      rewrite T.PkgSet.union_spec, SOptp.mem_map, SOdtp.mem_unionMap.
      apply or_iff_compat_l; split.
      - intros [[[n v] [m vs]] [HeD Hh]]; cbn beta iota in Hh.
        destruct (isSplitb g vs) eqn:Hs; [| destruct (SOdtp.empty_in _ Hh)].
        apply SOvtp.mem_map in Hh; destruct Hh as [u [Hu ->]].
        exists n, v, m, vs, u; repeat split; try assumption.
        apply isSplitb_iff; exact Hs.
      - intros [n [v [m [vs [u [HD [Hspl [Hu ->]]]]]]]].
        exists ((n, v), (m, vs)); split; [exact HD | cbn beta iota].
        apply isSplitb_iff in Hspl; rewrite Hspl.
        apply SOvtp.mem_map; exists u; split; [exact Hu | reflexivity].
    Qed.

    Lemma mem_reduceDepsDirect : forall D g y,
        T.DepRel.In y (reduceDepsDirect D g) <->
        exists n v m vs u,
          C.DepRel.In ((n, v), (m, vs)) D /\ IsDirect g vs /\ VSet.In u vs /\
          y = ((Name.Granular n (g v), Version.Orig v),
               (Name.Granular m (g u), embedVS vs)).
    Proof.
      intros D g y; unfold reduceDepsDirect; rewrite SOdtd.mem_unionMap.
      split.
      - intros [[[n v] [m vs]] [HeD Hh]]; cbn beta iota in Hh.
        destruct (isDirectb g vs) eqn:Hd; [| destruct (SOdtd.empty_in _ Hh)].
        apply SOvtd.mem_map in Hh; destruct Hh as [u [Hu ->]].
        exists n, v, m, vs, u; repeat split; try assumption.
        apply isDirectb_iff; exact Hd.
      - intros [n [v [m [vs [u [HD [Hdir [Hu ->]]]]]]]].
        exists ((n, v), (m, vs)); split; [exact HD | cbn beta iota].
        apply isDirectb_iff in Hdir; rewrite Hdir.
        apply SOvtd.mem_map; exists u; split; [exact Hu | reflexivity].
    Qed.

    Lemma mem_reduceDepsSplitEntry : forall D g y,
        T.DepRel.In y (reduceDepsSplitEntry D g) <->
        exists n v m vs,
          C.DepRel.In ((n, v), (m, vs)) D /\ IsSplit g vs /\
          y = ((Name.Granular n (g v), Version.Orig v),
               (Name.GranIntermediate n (g v) m vs, gransOfVS g vs)).
    Proof.
      intros D g y; unfold reduceDepsSplitEntry; rewrite SOdtd.mem_filterMap.
      split.
      - intros [[[n v] [m vs]] [HeD Hh]]; cbn beta iota in Hh.
        destruct (isSplitb g vs) eqn:Hs; [| discriminate].
        injection Hh as <-.
        exists n, v, m, vs; repeat split; try assumption.
        apply isSplitb_iff; exact Hs.
      - intros [n [v [m [vs [HD [Hspl ->]]]]]].
        exists ((n, v), (m, vs)); split; [exact HD | cbn beta iota].
        apply isSplitb_iff in Hspl; rewrite Hspl; reflexivity.
    Qed.

    Lemma mem_reduceDepsSplitFanout : forall D g y,
        T.DepRel.In y (reduceDepsSplitFanout D g) <->
        exists n v m vs u,
          C.DepRel.In ((n, v), (m, vs)) D /\ IsSplit g vs /\ VSet.In u vs /\
          y = ((Name.GranIntermediate n (g v) m vs, Version.Gran (g u)),
               (Name.Granular m (g u), embedVS (filterGran g (g u) vs))).
    Proof.
      intros D g y; unfold reduceDepsSplitFanout; rewrite SOdtd.mem_unionMap.
      split.
      - intros [[[n v] [m vs]] [HeD Hh]]; cbn beta iota in Hh.
        destruct (isSplitb g vs) eqn:Hs; [| destruct (SOdtd.empty_in _ Hh)].
        apply SOvtd.mem_map in Hh; destruct Hh as [u [Hu ->]].
        exists n, v, m, vs, u; repeat split; try assumption.
        apply isSplitb_iff; exact Hs.
      - intros [n [v [m [vs [u [HD [Hspl [Hu ->]]]]]]]].
        exists ((n, v), (m, vs)); split; [exact HD | cbn beta iota].
        apply isSplitb_iff in Hspl; rewrite Hspl.
        apply SOvtd.mem_map; exists u; split; [exact Hu | reflexivity].
    Qed.

    Lemma mem_reduceDepsEmpty : forall D g y,
        T.DepRel.In y (reduceDepsEmpty D g) <->
        exists n v m,
          C.DepRel.In ((n, v), (m, VSet.empty)) D /\
          y = ((Name.Granular n (g v), Version.Orig v),
               (Name.GranIntermediate n (g v) m VSet.empty, T.VSet.empty)).
    Proof.
      intros D g y; unfold reduceDepsEmpty; rewrite SOdtd.mem_filterMap.
      split.
      - intros [[[n v] [m vs]] [HeD Hh]]; cbn beta iota in Hh.
        destruct (VSet.is_empty vs) eqn:He; [| discriminate].
        injection Hh as <-.
        apply VSet.is_empty_iff in He; subst vs.
        exists n, v, m; split; [assumption | reflexivity].
      - intros [n [v [m [HD ->]]]].
        exists ((n, v), (m, VSet.empty)); split; [exact HD | simpl];
          reflexivity.
    Qed.

    Lemma mem_reduceDeps : forall D g y,
        T.DepRel.In y (reduceDeps D g) <->
        (exists n v m vs u,
            C.DepRel.In ((n, v), (m, vs)) D /\ IsDirect g vs /\ VSet.In u vs /\
            y = ((Name.Granular n (g v), Version.Orig v),
                 (Name.Granular m (g u), embedVS vs))) \/
        ((exists n v m vs,
             C.DepRel.In ((n, v), (m, vs)) D /\ IsSplit g vs /\
             y = ((Name.Granular n (g v), Version.Orig v),
                  (Name.GranIntermediate n (g v) m vs, gransOfVS g vs))) \/
         ((exists n v m vs u,
              C.DepRel.In ((n, v), (m, vs)) D /\ IsSplit g vs /\ VSet.In u vs /\
              y = ((Name.GranIntermediate n (g v) m vs, Version.Gran (g u)),
                   (Name.Granular m (g u), embedVS (filterGran g (g u) vs)))) \/
          (exists n v m,
              C.DepRel.In ((n, v), (m, VSet.empty)) D /\
              y = ((Name.Granular n (g v), Version.Orig v),
                   (Name.GranIntermediate n (g v) m VSet.empty, T.VSet.empty))))).
    Proof.
      intros D g y; unfold reduceDeps.
      rewrite !T.DepRel.union_spec.
      rewrite mem_reduceDepsDirect, mem_reduceDepsSplitEntry,
        mem_reduceDepsSplitFanout, mem_reduceDepsEmpty.
      reflexivity.
    Qed.

    Definition tryInvPkg (g : V.t -> G.t) (p' : T.Pkg.t) : option Pkg.t :=
      match p' with
      | (Name.Granular n w, Version.Orig v) =>
          if G.eq_dec w (g v) then Some (n, v) else None
      | _ => None
      end.

    Lemma tryInvPkg_embed : forall g p, tryInvPkg g (embedPkg g p) = Some p.
    Proof.
      intros g [n v]; unfold tryInvPkg, embedPkg; cbn [fst snd].
      destruct (G.eq_dec (g v) (g v)) as [_ | NE];
        [reflexivity | contradiction NE; reflexivity].
    Qed.

    Lemma tryInvPkg_some : forall g (p' : T.Pkg.t) (p : Pkg.t),
        tryInvPkg g p' = Some p -> embedPkg g p = p'.
    Proof.
      intros g [[n w | n v m | n w m vs] [v' | w']] p H; cbn [tryInvPkg] in H;
        try discriminate.
      destruct (G.eq_dec w (g v')) as [-> | NE]; [| discriminate].
      injection H as <-; reflexivity.
    Qed.

    Module SOtpp := SetOps T.Pkg Pkg T.PkgSet PkgSet.
    Lemma embedPkg_injective : forall g (p q : Pkg.t),
        embedPkg g p = embedPkg g q -> p = q.
    Proof.
      intro g;
        exact (SOtpp.emb_injective (tryInvPkg g) (embedPkg g)
                 (tryInvPkg_embed g)).
    Qed.

    Definition concurrentResolution (g : V.t -> G.t) (S : T.PkgSet.t)
        : PkgSet.t :=
      SOtpp.filterMap (tryInvPkg g) S.

    Lemma mem_concurrentResolution : forall g (S : T.PkgSet.t) (p : Pkg.t),
        PkgSet.In p (concurrentResolution g S) <-> T.PkgSet.In (embedPkg g p) S.
    Proof.
      intro g; unfold concurrentResolution.
      exact (SOtpp.mem_filterMap_inv (tryInvPkg g) (embedPkg g)
               (tryInvPkg_embed g) (tryInvPkg_some g)).
    Qed.

    Definition piGuardb (g : V.t -> G.t) (S : T.PkgSet.t)
        (n : N.t) (v : V.t) (m : N.t) (vs : VSet.t) (u : V.t) : bool :=
      andb (T.PkgSet.mem (Name.Granular m (g u), Version.Orig u) S)
        (andb (T.PkgSet.mem (Name.Granular n (g v), Version.Orig v) S)
           (implb (isSplitb g vs)
              (VSet.exists_ (fun u0 =>
                   andb (T.PkgSet.mem
                           (Name.GranIntermediate n (g v) m vs, Version.Gran (g u0)) S)
                     (granEqb (g u) (g u0)))
                 vs))).

    Lemma piGuardb_iff : forall g S n v m vs u,
        piGuardb g S n v m vs u = true <->
        T.PkgSet.In (Name.Granular m (g u), Version.Orig u) S /\
        T.PkgSet.In (Name.Granular n (g v), Version.Orig v) S /\
        (IsSplit g vs ->
           exists u0, VSet.In u0 vs /\
             T.PkgSet.In (Name.GranIntermediate n (g v) m vs, Version.Gran (g u0)) S /\
             g u = g u0).
    Proof.
      intros g S n v m vs u; unfold piGuardb.
      rewrite !Bool.andb_true_iff, Bool.implb_true_iff, !T.PkgSet.mem_spec,
        isSplitb_iff.
      rewrite VSet.exists_spec'.
      split.
      - intros [H1 [H2 H3]]; repeat split; try assumption.
        intro Hs; destruct (H3 Hs) as [u0 [Hu0 Hb]].
        apply Bool.andb_true_iff in Hb; destruct Hb as [Hm Hg].
        apply T.PkgSet.mem_spec in Hm.
        exists u0; repeat split; try assumption.
        exact (proj1 (granEqb_iff _ _) Hg).
      - intros [H1 [H2 H3]]; repeat split; try assumption.
        intro Hs; destruct (H3 Hs) as [u0 [Hu0 [Hm Hg]]].
        exists u0; split; [exact Hu0 |].
        apply Bool.andb_true_iff; split.
        + apply T.PkgSet.mem_spec; exact Hm.
        + apply granEqb_iff; exact Hg.
    Qed.

    Module SOvpp := SetOps V ParentElt VSet ParentRel.
    Module SOdpp := SetOps C.DepElt ParentElt C.DepRel ParentRel.
    Definition parents (D : C.DepRel.t) (g : V.t -> G.t) (S : T.PkgSet.t) :
        ParentRel.t :=
      SOdpp.unionMap (fun '((n, v), (m, vs)) =>
          SOvpp.filterMap (fun u =>
              if piGuardb g S n v m vs u then Some ((m, u), (n, v)) else None)
            vs)
        D.

    Lemma mem_parents : forall D g S (pair : ParentElt.t),
        ParentRel.In pair (parents D g S) <->
        exists n v m vs u,
          C.DepRel.In ((n, v), (m, vs)) D /\
          T.PkgSet.In (Name.Granular n (g v), Version.Orig v) S /\
          VSet.In u vs /\
          T.PkgSet.In (Name.Granular m (g u), Version.Orig u) S /\
          (IsSplit g vs ->
             exists u0, VSet.In u0 vs /\
               T.PkgSet.In (Name.GranIntermediate n (g v) m vs, Version.Gran (g u0)) S /\
               g u = g u0) /\
          pair = ((m, u), (n, v)).
    Proof.
      intros D g S pair; unfold parents; rewrite SOdpp.mem_unionMap.
      split.
      - intros [[[n v] [m vs]] [HeD Hh]]; cbn beta iota in Hh.
        apply SOvpp.mem_filterMap in Hh; destruct Hh as [u [Hu Hc]];
          cbn beta iota in Hc.
        destruct (piGuardb g S n v m vs u) eqn:Hg; [| discriminate].
        injection Hc as <-.
        apply piGuardb_iff in Hg; destruct Hg as [H1 [H2 H3]].
        exists n, v, m, vs, u; repeat split; assumption.
      - intros [n [v [m [vs [u [HD [HvS [Hu [HuS [Hsc ->]]]]]]]]]].
        exists ((n, v), (m, vs)); split; [exact HD | cbn beta iota].
        apply SOvpp.mem_filterMap; exists u; split; [exact Hu | cbn beta iota].
        assert (Hg : piGuardb g S n v m vs u = true)
          by (apply piGuardb_iff; repeat split; assumption).
        rewrite Hg; reflexivity.
    Qed.

    Lemma embedPkg_mem_reduceReal : forall g (p : Pkg.t) R D,
        T.PkgSet.In (embedPkg g p) (reduceReal R D g) -> PkgSet.In p R.
    Proof.
      intros g p R D H; apply mem_reduceReal in H.
      destruct H as [[q [HqR Hq]] | [n [v [m [vs [u [_ [_ [_ Hq]]]]]]]]].
      - apply embedPkg_injective in Hq; subst q; exact HqR.
      - destruct p as [pn pv]; unfold embedPkg in Hq; simpl in Hq.
        injection Hq as Hq _; discriminate.
    Qed.

    Lemma mem_reduceDeps_direct : forall D g n v m vs u0,
        C.DepRel.In ((n, v), (m, vs)) D -> IsDirect g vs -> VSet.In u0 vs ->
        T.DepRel.In ((Name.Granular n (g v), Version.Orig v),
                     (Name.Granular m (g u0), embedVS vs))
          (reduceDeps D g).
    Proof.
      intros; apply mem_reduceDeps.
      left; exists n, v, m, vs, u0; repeat split; assumption.
    Qed.

    Lemma mem_reduceDeps_split1 : forall D g n v m vs,
        C.DepRel.In ((n, v), (m, vs)) D -> IsSplit g vs ->
        T.DepRel.In ((Name.Granular n (g v), Version.Orig v),
                     (Name.GranIntermediate n (g v) m vs, gransOfVS g vs))
          (reduceDeps D g).
    Proof.
      intros; apply mem_reduceDeps.
      right; left; exists n, v, m, vs; repeat split; assumption.
    Qed.

    Lemma mem_reduceDeps_split2 : forall D g n v m vs u0,
        C.DepRel.In ((n, v), (m, vs)) D -> IsSplit g vs -> VSet.In u0 vs ->
        T.DepRel.In ((Name.GranIntermediate n (g v) m vs, Version.Gran (g u0)),
                     (Name.Granular m (g u0), embedVS (filterGran g (g u0) vs)))
          (reduceDeps D g).
    Proof.
      intros; apply mem_reduceDeps.
      right; right; left; exists n, v, m, vs, u0; repeat split; assumption.
    Qed.

    Lemma mem_reduceDeps_empty : forall D g n v m,
        C.DepRel.In ((n, v), (m, VSet.empty)) D ->
        T.DepRel.In ((Name.Granular n (g v), Version.Orig v),
                     (Name.GranIntermediate n (g v) m VSet.empty, T.VSet.empty))
          (reduceDeps D g).
    Proof.
      intros; apply mem_reduceDeps.
      right; right; right; exists n, v, m; split; [assumption | reflexivity].
    Qed.

    Theorem concurrent_soundness :
      forall (R : PkgSet.t) (D : C.DepRel.t) (g : V.t -> G.t) (r : Pkg.t)
             (S : T.PkgSet.t),
        C.FunctionalInName D ->
        T.IsResolution (reduceReal R D g) (reduceDeps D g) (embedPkg g r) S ->
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
            assert (T.PkgSet.In (Name.Granular m (g u), Version.Orig u) S)
              as HuS
              by (rewrite Hgu; exact HcvS).
            exists u; split.
            { split; [exact Hu | split].
              - apply mem_concurrentResolution; exact HuS.
              - apply mem_parents.
                exists pn, pv, m, vs, u.
                repeat split; try assumption.
                intros _; exists u0; repeat split; assumption. }
            { intros u' [Hu' [Hu'S Hpi']].
              apply mem_concurrentResolution in Hu'S; unfold embedPkg in Hu'S;
                simpl in Hu'S.
              apply mem_parents in Hpi'.
              destruct Hpi'
                as [n' [v' [m' [vs' [u'' [Hdep' [_ [_ [_ [Hsc Heq]]]]]]]]]].
              injection Heq as <- <- <- <-.
              assert (vs' = vs) as -> by (exact (Hfunc _ _ _ _ Hdep' Hdep0)).
              destruct (Hsc Hs) as [u0' [Hu0' [Hu0'S Hgu']]].
              assert (Version.Gran (g u0') = Version.Gran (g u0)) as Hg0
                by (exact (Huniq _ _ _ Hu0'S Hcv0S)).
              injection Hg0 as Hg0.
              rewrite Hg0 in Hgu'; rewrite Hgu' in Hu'S.
              assert (T.PkgSet.In (Name.Granular m (g u0), Version.Orig u) S)
                as HuS0
                by (rewrite <- Hgu; exact HuS).
              pose proof (Huniq _ _ _ Hu'S HuS0) as He.
              injection He as He; congruence. }
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
            assert (T.PkgSet.In (Name.Granular m (g u), Version.Orig u) S)
              as HuS
              by (rewrite Hgu; exact HcvS).
            exists u; split.
            { split; [exact Hu | split].
              - apply mem_concurrentResolution; exact HuS.
              - apply mem_parents.
                exists pn, pv, m, vs, u.
                repeat split; try assumption.
                intro Hsplit; exfalso.
                destruct Hsplit as [u1 [u2 [Hu1 [Hu2 Hne]]]].
                exact (Hne (Hdir u1 u2 Hu1 Hu2)). }
            { intros u' [Hu' [Hu'S _]].
              apply mem_concurrentResolution in Hu'S; unfold embedPkg in Hu'S;
                simpl in Hu'S.
              pose proof (Hdir u' u0 Hu' Hu0) as Hgu'.
              rewrite Hgu' in Hu'S.
              pose proof (Huniq _ _ _ Hu'S HcvS) as He.
              injection He as He; congruence. }
      - intros n v v' Hv Hv' Hne Hg.
        apply mem_concurrentResolution in Hv, Hv'; unfold embedPkg in Hv, Hv';
          simpl in Hv, Hv'.
        rewrite Hg in Hv.
        pose proof (Huniq _ _ _ Hv Hv') as He.
        injection He as He; exact (Hne He).
      - intros c p Hcp.
        apply mem_parents in Hcp.
        destruct Hcp as [n [v [m [vs [u [_ [HvS [_ [HuS [_ Heq]]]]]]]]]].
        injection Heq as -> ->.
        split; apply mem_concurrentResolution; [exact HuS | exact HvS].
    Qed.

    Definition coreResolution (S : PkgSet.t) (pi : ParentRel.t)
        (D : C.DepRel.t) (g : V.t -> G.t) : T.PkgSet.t :=
      T.PkgSet.union (SOptp.map (embedPkg g) S)
        (SOdtp.unionMap (fun '((n, v), (m, vs)) =>
             if andb (isSplitb g vs) (PkgSet.mem (n, v) S)
             then SOvtp.filterMap (fun u =>
                      if andb (PkgSet.mem (m, u) S)
                           (ParentRel.mem ((m, u), (n, v)) pi)
                      then Some (Name.GranIntermediate n (g v) m vs, Version.Gran (g u))
                      else None)
                    vs
             else T.PkgSet.empty)
           D).

    Lemma mem_coreResolution : forall S pi D g (q : T.Pkg.t),
        T.PkgSet.In q (coreResolution S pi D g) <->
        (exists n v, PkgSet.In (n, v) S /\
           q = (Name.Granular n (g v), Version.Orig v)) \/
        (exists n v m vs u,
           C.DepRel.In ((n, v), (m, vs)) D /\ PkgSet.In (n, v) S /\
           IsSplit g vs /\ PkgSet.In (m, u) S /\ VSet.In u vs /\
           ParentRel.In ((m, u), (n, v)) pi /\
           q = (Name.GranIntermediate n (g v) m vs, Version.Gran (g u))).
    Proof.
      intros S pi D g q; unfold coreResolution.
      rewrite T.PkgSet.union_spec, SOptp.mem_map, SOdtp.mem_unionMap.
      assert (Hfst :
        (exists p, PkgSet.In p S /\ q = embedPkg g p) <->
        (exists n v, PkgSet.In (n, v) S /\
           q = (Name.Granular n (g v), Version.Orig v))).
      { split.
        - intros [[n v] [HpS ->]];
            exists n, v; split; [exact HpS | reflexivity].
        - intros [n [v [HnS ->]]]; exists (n, v); auto. }
      rewrite Hfst; apply or_iff_compat_l.
      split.
      - intros [[[n v] [m vs]] [HeD Hh]]; cbn beta iota in Hh.
        destruct (andb (isSplitb g vs) (PkgSet.mem (n, v) S)) eqn:Hg;
          [| destruct (SOdtp.empty_in _ Hh)].
        apply Bool.andb_true_iff in Hg; destruct Hg as [Hs Hnv].
        apply isSplitb_iff in Hs; apply PkgSet.mem_spec in Hnv.
        apply SOvtp.mem_filterMap in Hh; destruct Hh as [u [Hu Hc]];
          cbn beta iota in Hc.
        destruct (andb (PkgSet.mem (m, u) S)
                    (ParentRel.mem ((m, u), (n, v)) pi)) eqn:Hb;
          [| discriminate].
        injection Hc as <-.
        apply Bool.andb_true_iff in Hb; destruct Hb as [Hmu Hpi].
        apply PkgSet.mem_spec in Hmu; apply ParentRel.mem_spec in Hpi.
        exists n, v, m, vs, u; repeat split; assumption.
      - intros [n [v [m [vs [u [HD [Hnv [Hs [Hmu [Hu [Hpi ->]]]]]]]]]]].
        exists ((n, v), (m, vs)); split; [exact HD | cbn beta iota].
        assert (andb (isSplitb g vs) (PkgSet.mem (n, v) S) = true) as ->.
        { apply Bool.andb_true_iff; split;
            [apply isSplitb_iff; exact Hs | apply PkgSet.mem_spec; exact Hnv]. }
        apply SOvtp.mem_filterMap; exists u; split; [exact Hu | cbn beta iota].
        assert (andb (PkgSet.mem (m, u) S)
                  (ParentRel.mem ((m, u), (n, v)) pi) = true) as ->.
        { apply Bool.andb_true_iff; split;
            [apply PkgSet.mem_spec; exact Hmu
            | apply ParentRel.mem_spec; exact Hpi]. }
        reflexivity.
    Qed.

    Lemma mem_coreResolution_granular : forall S pi D g n v,
        PkgSet.In (n, v) S ->
        T.PkgSet.In (Name.Granular n (g v), Version.Orig v)
          (coreResolution S pi D g).
    Proof.
      intros; apply mem_coreResolution.
      left; exists n, v; split; [assumption | reflexivity].
    Qed.

    Lemma mem_coreResolution_intermediate : forall S pi D g n v m vs u,
        C.DepRel.In ((n, v), (m, vs)) D -> PkgSet.In (n, v) S ->
        IsSplit g vs -> PkgSet.In (m, u) S -> VSet.In u vs ->
        ParentRel.In ((m, u), (n, v)) pi ->
        T.PkgSet.In (Name.GranIntermediate n (g v) m vs, Version.Gran (g u))
          (coreResolution S pi D g).
    Proof.
      intros; apply mem_coreResolution.
      right; exists n, v, m, vs, u; repeat split; assumption.
    Qed.

    Theorem concurrent_completeness :
      forall (R : PkgSet.t) (D : C.DepRel.t) (g : V.t -> G.t) (r : Pkg.t)
             (S : PkgSet.t) (pi : ParentRel.t),
        C.FunctionalInName D ->
        IsResolution R D g r S pi ->
        T.IsResolution (reduceReal R D g) (reduceDeps D g)
          (embedPkg g r) (coreResolution S pi D g).
    Proof.
      intros R D g r S pi Hfunc Hres.
      destruct Hres as [Hsub Hroot Hpc Hvg Hps].
      constructor.
      - intros q Hq; apply mem_coreResolution in Hq.
        apply mem_reduceReal.
        destruct Hq as
          [[n [v [Hnv ->]]]
          | [n [v [m [vs [u [HD [Hnv [Hs [Hmu [Hu [Hpi ->]]]]]]]]]]]].
        + left; exists (n, v); split; [apply Hsub; exact Hnv | reflexivity].
        + right; exists n, v, m, vs, u; repeat split; try assumption.
      - destruct r as [rn rv].
        exact (mem_coreResolution_granular S pi D g rn rv Hroot).
      - intros q Hq md vsd Hd.
        apply mem_coreResolution in Hq.
        apply mem_reduceDeps in Hd.
        destruct Hq as
          [[n [v [Hnv ->]]]
          | [n [v [m [vs [u [HD [Hnv [Hs [Hmu [Hu [Hpi ->]]]]]]]]]]]].
        + destruct Hd as [Hd | [Hd | [Hd | Hd]]].
          * destruct Hd as [n' [v' [m' [vs' [u' [HD' [Hdir' [Hu' Heq]]]]]]]].
            injection Heq as <- Hgv <- -> ->.
            destruct (Hpc _ Hnv _ _ HD') as [u [[Huv [HmuS Hpiu]] _]].
            exists (Version.Orig u); split.
            { unfold embedVS; apply SOvcv.mem_map;
                exists u; split; [exact Huv | reflexivity]. }
            { rewrite <- (Hdir' u u' Huv Hu').
              exact (mem_coreResolution_granular S pi D g m' u HmuS). }
          * destruct Hd as [n' [v' [m' [vs' [HD' [Hs' Heq]]]]]].
            injection Heq as <- Hgv <- -> ->.
            destruct (Hpc _ Hnv _ _ HD') as [u [[Huv [HmuS Hpiu]] _]].
            exists (Version.Gran (g u)); split.
            { unfold gransOfVS; apply SOvcv.mem_map;
                exists u; split; [exact Huv | reflexivity]. }
            { exact (mem_coreResolution_intermediate S pi D g n v m' vs' u
                       HD' Hnv Hs' HmuS Huv Hpiu). }
          * destruct Hd as [n' [v' [m' [vs' [u' [HD' [Hs' [Hu' Heq]]]]]]]].
            discriminate Heq.
          * destruct Hd as [n' [v' [m' [HD' Heq]]]].
            injection Heq as <- Hgv <- -> ->.
            destruct (Hpc _ Hnv _ _ HD') as [u [[Huv _] _]].
            destruct (VSet.empty_spec Huv).
        + destruct Hd as [Hd | [Hd | [Hd | Hd]]].
          * destruct Hd as [n' [v' [m' [vs' [u' [HD' [Hdir' [Hu' Heq]]]]]]]].
            discriminate Heq.
          * destruct Hd as [n' [v' [m' [vs' [HD' [Hs' Heq]]]]]].
            discriminate Heq.
          * destruct Hd as [n' [v' [m' [vs' [u'' [HD' [Hs' [Hu'' Heq]]]]]]]].
            injection Heq as <- Hgv <- <- Hgu -> ->.
            exists (Version.Orig u); split.
            { unfold embedVS; apply SOvcv.mem_map; exists u; split;
                [| reflexivity].
              apply mem_filterGran; split; [exact Hu | exact Hgu]. }
            { rewrite <- Hgu.
              exact (mem_coreResolution_granular S pi D g m u Hmu). }
          * destruct Hd as [n' [v' [m' [HD' Heq]]]].
            discriminate Heq.
      - intros n cv1 cv2 H1 H2.
        apply mem_coreResolution in H1, H2.
        destruct H1 as
          [[n1 [v1 [Hm1 He1]]]
          | [n1 [v1 [m1 [vs1 [u1
              [Hd1 [Hnv1 [Hs1 [Hmu1 [Hu1 [Hpi1 He1]]]]]]]]]]]];
        destruct H2 as
          [[n2 [v2 [Hm2 He2]]]
          | [n2 [v2 [m2 [vs2 [u2
              [Hd2 [Hnv2 [Hs2 [Hmu2 [Hu2 [Hpi2 He2]]]]]]]]]]]].
        + injection He1 as -> ->; injection He2 as <- Hg ->.
          destruct (V.eq_dec v1 v2) as [-> | NE]; [reflexivity |].
          exfalso; exact (Hvg n1 v1 v2 Hm1 Hm2 NE Hg).
        + injection He1 as -> ->; discriminate He2.
        + injection He1 as -> ->; discriminate He2.
        + injection He1 as -> ->; injection He2 as <- Hg12 <- <- ->.
          destruct (V.eq_dec v1 v2) as [<- | NE];
            [| exfalso; exact (Hvg n1 v1 v2 Hnv1 Hnv2 NE Hg12)].
          destruct (Hpc _ Hnv1 _ _ Hd1) as [w [_ Huniq]].
          pose proof (Huniq u1 (conj Hu1 (conj Hmu1 Hpi1))) as E1.
          pose proof (Huniq u2 (conj Hu2 (conj Hmu2 Hpi2))) as E2.
          congruence.
    Qed.

    Module Lookup.
      Lemma reduceDeps_mono : forall D D' g (y : T.DepElt.t),
          C.DepRel.Subset D' D ->
          T.DepRel.In y (reduceDeps D' g) ->
          T.DepRel.In y (reduceDeps D g).
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

      Module DepRelFibred :=
        FibredLabelledRel Pkg N VSet.AsUOT C.DepElt C.DepRel.
      Definition granFibre (g : V.t -> G.t) (R : PkgSet.t) (n : N.t) (w : G.t)
          : PkgSet.t :=
        PkgSet.filter (fun '(m, v) =>
            if N.eq_dec m n then granEqb (g v) w else false)
          R.

      Lemma mem_granFibre : forall g R (n m : N.t) (w : G.t) (v : V.t),
          PkgSet.In (m, v) (granFibre g R n w) <->
          PkgSet.In (m, v) R /\ m = n /\ g v = w.
      Proof.
        intros g R n m w v; unfold granFibre.
        rewrite PkgSet.filter_spec'; cbn beta iota.
        destruct (N.eq_dec m n) as [-> | NE];
          [rewrite granEqb_iff | ]; intuition congruence.
      Qed.

      Theorem versions_lookupGranular :
        forall R D g (r : Pkg.t) (n : N.t) (w : G.t),
          (exists p h,
              T.DepRel.In (p, (Name.Granular n w, h)) (reduceDeps D g)) \/
          Name.Granular n w = Name.Granular (fst r) (g (snd r)) ->
          T.versions (reduceReal R D g) (Name.Granular n w) =
          T.versions (reduceReal (granFibre g R n w) C.DepRel.empty g)
            (Name.Granular n w).
      Proof.
        intros R D g r n w _; apply T.versions_ext; intro y.
        rewrite !mem_reduceReal.
        split.
        - intros [[[qn qv] [HR Hq]]
                 | [n' [v' [m' [vs [u [_ [_ [_ Heq]]]]]]]]];
            [| discriminate Heq].
          unfold embedPkg in Hq; cbn [fst snd] in Hq.
          injection Hq as -> -> ->.
          left; exists (qn, qv); split;
            [apply mem_granFibre; split;
               [exact HR | split; reflexivity]
            | reflexivity].
        - intros [[[qn qv] [HR Hq]] | [n' [v' [m' [vs [u [HD _]]]]]]].
          + apply mem_granFibre in HR; destruct HR as [HR _].
            left; exists (qn, qv); split; [exact HR | exact Hq].
          + destruct (C.DepRel.empty_spec HD).
      Qed.

      Theorem dependees_lookupGranular : forall R D g n v,
          T.PkgSet.In (Name.Granular n (g v), Version.Orig v)
            (reduceReal R D g) ->
          T.dependees (reduceDeps D g) (Name.Granular n (g v), Version.Orig v) =
          T.dependees (reduceDeps (DepRelFibred.tailFibre D (n, v)) g)
            (Name.Granular n (g v), Version.Orig v).
      Proof.
        intros R D g n v _; apply T.dependees_ext; intros [m ws].
        split; [| apply reduceDeps_mono, DepRelFibred.tailFibre_subset].
        intro H; apply mem_reduceDeps in H; apply mem_reduceDeps.
        destruct H as [H | [H | [H | H]]].
        - destruct H as [n' [v' [m' [vs [u [HD [Hdir [Hu Heq]]]]]]]].
          injection Heq as <- Hgv <- -> ->.
          left; exists n, v, m', vs, u.
          split; [apply DepRelFibred.mem_tailFibre;
                  split; [exact HD | reflexivity] |].
          split; [exact Hdir | split; [exact Hu | reflexivity]].
        - destruct H as [n' [v' [m' [vs [HD [Hs Heq]]]]]].
          injection Heq as <- Hgv <- -> ->.
          right; left; exists n, v, m', vs.
          split; [apply DepRelFibred.mem_tailFibre;
                  split; [exact HD | reflexivity] |].
          split; [exact Hs | reflexivity].
        - destruct H as [n' [v' [m' [vs [u [HD [Hs [Hu Heq]]]]]]]];
            discriminate Heq.
        - destruct H as [n' [v' [m' [HD Heq]]]].
          injection Heq as <- Hgv <- -> ->.
          right; right; right; exists n, v, m'.
          split;
            [apply DepRelFibred.mem_tailFibre; split; [exact HD | reflexivity]
            | reflexivity].
      Qed.

      Theorem dependees_lookupGranularGran : forall D g n (w w' : G.t),
          T.dependees (reduceDeps D g) (Name.Granular n w, Version.Gran w') =
          T.DependeesSet.empty.
      Proof.
        intros D g n w w'; apply T.dependees_empty_iff; intros [m ws] H.
        apply mem_reduceDeps in H.
        destruct H as [H | [H | [H | H]]].
        - destruct H as [n' [v' [m' [vs [u [_ [_ [_ Heq]]]]]]]];
            discriminate Heq.
        - destruct H as [n' [v' [m' [vs [_ [_ Heq]]]]]]; discriminate Heq.
        - destruct H as [n' [v' [m' [vs [u [_ [_ [_ Heq]]]]]]]];
            discriminate Heq.
        - destruct H as [n' [v' [m' [_ Heq]]]]; discriminate Heq.
      Qed.

      (* The name carries the depender's granularity and the declared
         range, so the answer reads nothing of the instance; reachability
         only rules out a name no declaration introduces. *)
      Theorem versions_lookupIntermediate : forall R D g n w m vs,
          (exists p h,
              T.DepRel.In (p, (Name.GranIntermediate n w m vs, h))
                (reduceDeps D g)) ->
          T.versions (reduceReal R D g) (Name.GranIntermediate n w m vs) =
          (if isSplitb g vs then gransOfVS g vs else T.VSet.empty).
      Proof.
        intros R D g n w m vs [p [h Hreach]].
        assert (Hw : exists v, C.DepRel.In ((n, v), (m, vs)) D /\ g v = w).
        { apply mem_reduceDeps in Hreach.
          destruct Hreach as [H | [H | [H | H]]].
          - destruct H as [n' [v' [m' [vs' [u [_ [_ [_ Heq]]]]]]]];
              discriminate Heq.
          - destruct H as [n' [v' [m' [vs' [HD [_ Heq]]]]]].
            injection Heq as _ <- Ew <- <- _.
            exists v'; split; [exact HD | symmetry; exact Ew].
          - destruct H as [n' [v' [m' [vs' [u [_ [_ [_ Heq]]]]]]]];
              discriminate Heq.
          - destruct H as [n' [v' [m' [HD Heq]]]].
            injection Heq as _ <- Ew <- -> _.
            exists v'; split; [exact HD | symmetry; exact Ew]. }
        destruct Hw as [v [HD <-]].
        apply T.VSet.ext; intro y.
        rewrite T.mem_versions, mem_reduceReal.
        destruct (isSplitb g vs) eqn:Hs.
        - unfold gransOfVS; rewrite SOvcv.mem_map; split.
          + intros [[[qn qv] [_ Hq]]
                   | [n' [v' [m' [vs' [u [_ [_ [Hu Heq]]]]]]]]].
            * unfold embedPkg in Hq; cbn [fst snd] in Hq; discriminate Hq.
            * injection Heq as _ _ _ <- ->.
              exists u; split; [exact Hu | reflexivity].
          + intros [u [Hu ->]].
            right; exists n, v, m, vs, u; repeat split; try assumption.
            apply isSplitb_iff; exact Hs.
        - split; [| intro Hy; destruct (T.VSet.empty_spec Hy)].
          intros [[[qn qv] [_ Hq]]
                 | [n' [v' [m' [vs' [u [_ [Hs' [_ Heq]]]]]]]]].
          + unfold embedPkg in Hq; cbn [fst snd] in Hq; discriminate Hq.
          + injection Heq as _ _ _ <- _.
            apply isSplitb_iff in Hs'; congruence.
      Qed.

      Theorem dependees_lookupIntermediate : forall R D g n w m vs w',
          T.PkgSet.In (Name.GranIntermediate n w m vs, Version.Gran w')
            (reduceReal R D g) ->
          T.dependees (reduceDeps D g)
            (Name.GranIntermediate n w m vs, Version.Gran w') =
          T.DependeesSet.singleton
            (Name.Granular m w', embedVS (filterGran g w' vs)).
      Proof.
        intros R D g n w m vs w' Hin.
        apply mem_reduceReal in Hin.
        destruct Hin as [[[qn qv] [_ Hq]]
                        | [n' [v [m' [vs' [u [HD [Hs [Hu Heq]]]]]]]]].
        { unfold embedPkg in Hq; cbn [fst snd] in Hq; discriminate Hq. }
        injection Heq as <- -> <- <- ->.
        apply T.DependeesSet.ext; intros [m0 ws].
        rewrite T.mem_dependees, T.DependeesSet.singleton_spec,
          mem_reduceDeps.
        split.
        - intros [H | [H | [H | H]]].
          + destruct H as [n2 [v2 [m2 [vs2 [u2 [_ [_ [_ Heq2]]]]]]]];
              discriminate Heq2.
          + destruct H as [n2 [v2 [m2 [vs2 [_ [_ Heq2]]]]]];
              discriminate Heq2.
          + destruct H as [n2 [v2 [m2 [vs2 [u2 [_ [_ [_ Heq2]]]]]]]].
            injection Heq2 as _ _ <- <- Egu -> ->.
            rewrite Egu; reflexivity.
          + destruct H as [n2 [v2 [m2 [_ Heq2]]]]; discriminate Heq2.
        - intro E; injection E as -> ->.
          right; right; left; exists n, v, m, vs, u.
          repeat split; assumption.
      Qed.

      Theorem dependees_lookupIntermediateOrig : forall D g n w m vs u,
          T.dependees (reduceDeps D g)
            (Name.GranIntermediate n w m vs, Version.Orig u) =
          T.DependeesSet.empty.
      Proof.
        intros D g n w m vs u; apply T.dependees_empty_iff; intros [m0 ws] H.
        apply mem_reduceDeps in H.
        destruct H as [H | [H | [H | H]]].
        - destruct H as [n' [v' [m' [vs' [u' [_ [_ [_ Heq]]]]]]]];
            discriminate Heq.
        - destruct H as [n' [v' [m' [vs' [_ [_ Heq]]]]]]; discriminate Heq.
        - destruct H as [n' [v' [m' [vs' [u' [_ [_ [_ Heq]]]]]]]];
            discriminate Heq.
        - destruct H as [n' [v' [m' [_ Heq]]]]; discriminate Heq.
      Qed.

    End Lookup.
  End Reduction.

End Concurrent.
