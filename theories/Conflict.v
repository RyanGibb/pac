From Stdlib Require Import Orders.
From PackageCalculus Require Import Prelude Core.

Create HintDb cmp_conf.
Create Rewrite HintDb cmp_conf.

Module Conflict (N V : UsualOrderedType).
  Module C := Core N V.
  Module Pkg := C.Pkg.
  Module PkgSet := C.PkgSet.
  Module VSet := C.VSet.

  Module ConfElt := PairUOT Pkg C.Dependees.
  Module ConflictRel := FSetUOT ConfElt.

  Record IsResolution
      (R : PkgSet.t) (D : C.DepRel.t) (G : ConflictRel.t)
      (r : Pkg.t) (S : PkgSet.t) : Prop :=
    { res_core : C.IsResolution R D r S
    ; res_conflict_avoidance :
        forall p, PkgSet.In p S ->
        forall (n : N.t) (vs : VSet.t),
          ConflictRel.In (p, (n, vs)) G ->
          ~ (exists v, VSet.In v vs /\ PkgSet.In (n, v) S) }.

  Module Reduction.
    Module NF := UOTCompareFacts N.
    Module DF := UOTCompareFacts C.Dependees.
    Module VF := UOTCompareFacts V.
    #[local] Hint Rewrite NF.compare_eq_iff DF.compare_eq_iff
      VF.compare_eq_iff : cmp_conf.
    #[local] Hint Extern 1 => cmp_by NF.compare_antisym : cmp_conf.
    #[local] Hint Extern 1 => cmp_by DF.compare_antisym : cmp_conf.
    #[local] Hint Extern 1 => cmp_by VF.compare_antisym : cmp_conf.
    #[local] Hint Extern 1 => cmp_by NF.compare_lt_trans : cmp_conf.
    #[local] Hint Extern 1 => cmp_by DF.compare_lt_trans : cmp_conf.
    #[local] Hint Extern 1 => cmp_by VF.compare_lt_trans : cmp_conf.

    Module Name.
      Inductive name : Type :=
      | Orig (n : N.t)
      | Synthetic (n : N.t) (vs : VSet.t).
      Definition t := name.

      Definition rank (x : t) : nat :=
        match x with Orig _ => 0 | Synthetic _ _ => 1 end.

      Definition compare (x y : t) : comparison :=
        match Nat.compare (rank x) (rank y) with
        | Eq =>
            match x, y with
            | Orig n1, Orig n2 => N.compare n1 n2
            | Synthetic n1 vs1, Synthetic n2 vs2 =>
                C.Dependees.compare (n1, vs1) (n2, vs2)
            | _, _ => Eq
            end
        | c => c
        end.

      Lemma compare_eq_iff : forall x y, compare x y = Eq <-> x = y.
      Proof. cmp_eq_iff cmp_conf. Qed.

      Lemma compare_antisym : forall x y, compare y x = CompOpp (compare x y).
      Proof. cmp_antisym cmp_conf. Qed.

      Lemma compare_lt_trans : forall x y z,
          compare x y = Lt -> compare y z = Lt -> compare x z = Lt.
      Proof. cmp_lt_trans cmp_conf. Qed.
    End Name.

    Module Version.
      Inductive version : Type :=
      | Orig (v : V.t)
      | Zero
      | One.
      Definition t := version.

      Definition rank (x : t) : nat :=
        match x with Orig _ => 0 | Zero => 1 | One => 2 end.

      Definition compare (x y : t) : comparison :=
        match Nat.compare (rank x) (rank y) with
        | Eq => match x, y with
                | Orig v1, Orig v2 => V.compare v1 v2
                | _, _ => Eq
                end
        | c => c
        end.

      Lemma compare_eq_iff : forall x y, compare x y = Eq <-> x = y.
      Proof. cmp_eq_iff cmp_conf. Qed.

      Lemma compare_antisym : forall x y, compare y x = CompOpp (compare x y).
      Proof. cmp_antisym cmp_conf. Qed.

      Lemma compare_lt_trans : forall x y z,
          compare x y = Lt -> compare y z = Lt -> compare x z = Lt.
      Proof. cmp_lt_trans cmp_conf. Qed.
    End Version.

    Module NameOT := UOTFromCompare Name.
    Module VersionOT := UOTFromCompare Version.
    (* The target core: the instance the reduction emits into. *)
    Module T := Core NameOT VersionOT.

    Definition embedPkg (p : Pkg.t) : T.Pkg.t :=
      (Name.Orig (fst p), Version.Orig (snd p)).

    Module SOpt := SetOps Pkg T.Pkg PkgSet T.PkgSet.
    Definition embedSet (S : PkgSet.t) : T.PkgSet.t := SOpt.map embedPkg S.

    Module SOvt := SetOps V VersionOT VSet T.VSet.
    Definition embedVS (vs : VSet.t) : T.VSet.t := SOvt.map Version.Orig vs.

    Module SOdt := SetOps ConfElt T.Pkg ConflictRel T.PkgSet.
    Definition synthReal (G : ConflictRel.t) : T.PkgSet.t :=
      SOdt.unionMap (fun '(_, (n, vs)) =>
          T.PkgSet.add (Name.Synthetic n vs, Version.Zero)
            (T.PkgSet.singleton (Name.Synthetic n vs, Version.One)))
        G.

    Lemma mem_synthReal : forall (G : ConflictRel.t) (y : T.Pkg.t),
        T.PkgSet.In y (synthReal G) <->
        exists p n vs, ConflictRel.In (p, (n, vs)) G /\
          (y = (Name.Synthetic n vs, Version.Zero) \/
           y = (Name.Synthetic n vs, Version.One)).
    Proof.
      intros G y; unfold synthReal; rewrite SOdt.mem_unionMap.
      split.
      - intros [[q [n vs]] [HG Hy]]; cbn beta iota in Hy.
        rewrite SOdt.add_in, SOdt.singleton_in in Hy.
        exists q, n, vs; tauto.
      - intros [p [n [vs [HG Hy]]]].
        exists (p, (n, vs)); split; [exact HG | cbn beta iota].
        rewrite SOdt.add_in, SOdt.singleton_in; tauto.
    Qed.

    Definition reduceReal (R : PkgSet.t) (G : ConflictRel.t) : T.PkgSet.t :=
      T.PkgSet.union (embedSet R) (synthReal G).

    Lemma mem_reduceReal :
      forall (R : PkgSet.t) (G : ConflictRel.t) (y : T.Pkg.t),
        T.PkgSet.In y (reduceReal R G) <->
        (exists p, PkgSet.In p R /\ y = embedPkg p) \/
        (exists p n vs, ConflictRel.In (p, (n, vs)) G /\
           (y = (Name.Synthetic n vs, Version.Zero) \/
            y = (Name.Synthetic n vs, Version.One))).
    Proof.
      intros; unfold reduceReal, embedSet.
      rewrite T.PkgSet.union_spec, SOpt.mem_map, mem_synthReal; reflexivity.
    Qed.

    Module SOdtd := SetOps C.DepElt T.DepElt C.DepRel T.DepRel.
    Definition origEdges (D : C.DepRel.t) : T.DepRel.t :=
      SOdtd.map (fun '(p, (n, vs)) => (embedPkg p, (Name.Orig n, embedVS vs)))
        D.

    Module SOctd := SetOps ConfElt T.DepElt ConflictRel T.DepRel.
    Definition declarerEdges (G : ConflictRel.t) : T.DepRel.t :=
      SOctd.map (fun '(p, (n, vs)) =>
          (embedPkg p, (Name.Synthetic n vs, T.VSet.singleton Version.One)))
        G.

    Module SOvtd := SetOps V T.DepElt VSet T.DepRel.
    Definition conflicteeEdges (G : ConflictRel.t) : T.DepRel.t :=
      SOctd.unionMap (fun '(_, (n, vs)) =>
          SOvtd.map (fun u =>
              ((Name.Orig n, Version.Orig u),
               (Name.Synthetic n vs, T.VSet.singleton Version.Zero)))
            vs)
        G.

    Definition reduceDeps (D : C.DepRel.t) (G : ConflictRel.t) : T.DepRel.t :=
      T.DepRel.union (origEdges D)
        (T.DepRel.union (declarerEdges G) (conflicteeEdges G)).

    Lemma mem_origEdges : forall (D : C.DepRel.t) (y : T.DepElt.t),
        T.DepRel.In y (origEdges D) <->
        exists p n vs, C.DepRel.In (p, (n, vs)) D /\
          y = (embedPkg p, (Name.Orig n, embedVS vs)).
    Proof.
      intros D y; unfold origEdges; rewrite SOdtd.mem_map.
      split.
      - intros [[q [n vs]] [HD Hy]]; cbn beta iota in Hy.
        exists q, n, vs; split; [exact HD | exact Hy].
      - intros [p [n [vs [HD ->]]]].
        exists (p, (n, vs)); split; [exact HD | reflexivity].
    Qed.

    Lemma mem_declarerEdges : forall (G : ConflictRel.t) (y : T.DepElt.t),
        T.DepRel.In y (declarerEdges G) <->
        exists p n vs, ConflictRel.In (p, (n, vs)) G /\
          y = (embedPkg p,
               (Name.Synthetic n vs, T.VSet.singleton Version.One)).
    Proof.
      intros G y; unfold declarerEdges; rewrite SOctd.mem_map.
      split.
      - intros [[q [n vs]] [HG Hy]]; cbn beta iota in Hy.
        exists q, n, vs; split; [exact HG | exact Hy].
      - intros [p [n [vs [HG ->]]]].
        exists (p, (n, vs)); split; [exact HG | reflexivity].
    Qed.

    Lemma mem_conflicteeEdges : forall (G : ConflictRel.t) (y : T.DepElt.t),
        T.DepRel.In y (conflicteeEdges G) <->
        exists p n vs u, ConflictRel.In (p, (n, vs)) G /\ VSet.In u vs /\
          y = ((Name.Orig n, Version.Orig u),
               (Name.Synthetic n vs, T.VSet.singleton Version.Zero)).
    Proof.
      intros G y; unfold conflicteeEdges; rewrite SOctd.mem_unionMap.
      split.
      - intros [[q [n vs]] [HG Hy]]; cbn beta iota in Hy.
        apply SOvtd.mem_map in Hy; destruct Hy as [u [Hu ->]].
        exists q, n, vs, u; auto.
      - intros [p [n [vs [u [HG [Hu ->]]]]]].
        exists (p, (n, vs)); split; [exact HG | cbn beta iota].
        apply SOvtd.mem_map; exists u; split; [exact Hu | reflexivity].
    Qed.

    Lemma mem_reduceDeps :
      forall (D : C.DepRel.t) (G : ConflictRel.t) (y : T.DepElt.t),
        T.DepRel.In y (reduceDeps D G) <->
        (exists p n vs, C.DepRel.In (p, (n, vs)) D /\
           y = (embedPkg p, (Name.Orig n, embedVS vs))) \/
        (exists p n vs, ConflictRel.In (p, (n, vs)) G /\
           y = (embedPkg p,
                (Name.Synthetic n vs, T.VSet.singleton Version.One))) \/
        (exists p n vs u, ConflictRel.In (p, (n, vs)) G /\ VSet.In u vs /\
           y = ((Name.Orig n, Version.Orig u),
                (Name.Synthetic n vs, T.VSet.singleton Version.Zero))).
    Proof.
      intros D G y; unfold reduceDeps.
      rewrite !T.DepRel.union_spec,
        mem_origEdges, mem_declarerEdges, mem_conflicteeEdges.
      tauto.
    Qed.

    Definition reduce (R : PkgSet.t) (D : C.DepRel.t) (G : ConflictRel.t) :
        T.PkgSet.t * T.DepRel.t :=
      (reduceReal R G, reduceDeps D G).

    Definition tryInvPkg (p : T.Pkg.t) : option Pkg.t :=
      match p with
      | (Name.Orig n, Version.Orig v) => Some (n, v)
      | _ => None
      end.

    Lemma tryInvPkg_embed : forall p, tryInvPkg (embedPkg p) = Some p.
    Proof. intros [n v]; reflexivity. Qed.

    Lemma tryInvPkg_some : forall (p' : T.Pkg.t) (p : Pkg.t),
        tryInvPkg p' = Some p -> embedPkg p = p'.
    Proof.
      intros [[n | n vs] [v | | ]] p H; simpl in H; try discriminate.
      injection H as <-; reflexivity.
    Qed.

    Module SOtp := SetOps T.Pkg Pkg T.PkgSet PkgSet.
    Lemma embedPkg_injective :
      forall p q : Pkg.t, embedPkg p = embedPkg q -> p = q.
    Proof. exact (SOtp.emb_injective tryInvPkg embedPkg tryInvPkg_embed). Qed.

    Definition conflictResolution (S : T.PkgSet.t) : PkgSet.t :=
      SOtp.filterMap tryInvPkg S.

    Lemma mem_conflictResolution : forall (S : T.PkgSet.t) (p : Pkg.t),
        PkgSet.In p (conflictResolution S) <-> T.PkgSet.In (embedPkg p) S.
    Proof.
      unfold conflictResolution.
      exact (SOtp.mem_filterMap_inv tryInvPkg embedPkg tryInvPkg_embed
               tryInvPkg_some).
    Qed.

    Lemma embedPkg_mem_real :
      forall (p : Pkg.t) (R : PkgSet.t) (G : ConflictRel.t),
        T.PkgSet.In (embedPkg p) (reduceReal R G) -> PkgSet.In p R.
    Proof.
      intros p R G H; apply mem_reduceReal in H.
      destruct H as [[q [HqR Hq]] | [q [n [vs [_ [Hy | Hy]]]]]].
      - apply embedPkg_injective in Hq; subst q; exact HqR.
      - destruct p; unfold embedPkg in Hy; simpl in Hy; congruence.
      - destruct p; unfold embedPkg in Hy; simpl in Hy; congruence.
    Qed.

    Theorem conflict_soundness :
      forall (R : PkgSet.t) (D : C.DepRel.t) (G : ConflictRel.t)
             (r : Pkg.t) (S : T.PkgSet.t),
        T.IsResolution (reduceReal R G) (reduceDeps D G) (embedPkg r) S ->
        IsResolution R D G r (conflictResolution S).
    Proof.
      intros R D G r S [Hsub Hroot Hdep Huniq].
      constructor.
      - constructor.
        + intros p Hp; apply mem_conflictResolution in Hp.
          exact (embedPkg_mem_real p R G (Hsub _ Hp)).
        + apply mem_conflictResolution; exact Hroot.
        + intros p Hp m vs HD; apply mem_conflictResolution in Hp.
          assert (Hd : T.DepRel.In (embedPkg p, (Name.Orig m, embedVS vs))
                         (reduceDeps D G))
            by (apply mem_reduceDeps; left; exists p, m, vs;
                split; [exact HD | reflexivity]).
          destruct (Hdep _ Hp _ _ Hd) as [v' [Hv' Hv'S]].
          unfold embedVS in Hv'; apply SOvt.mem_map in Hv';
            destruct Hv' as [v [Hv ->]].
          exists v; split;
            [exact Hv | apply mem_conflictResolution; exact Hv'S].
        + intros n v v' Hv Hv'; apply mem_conflictResolution in Hv, Hv'.
          assert (E : Version.Orig v = Version.Orig v')
            by (apply (Huniq (Name.Orig n)); assumption).
          injection E as E; exact E.
      - intros p Hp n vs Hg [u [Hu HuS]].
        apply mem_conflictResolution in Hp, HuS.
        assert (Hd1 : T.DepRel.In
                        (embedPkg p,
                         (Name.Synthetic n vs, T.VSet.singleton Version.One))
                        (reduceDeps D G))
          by (apply mem_reduceDeps; right; left; exists p, n, vs;
              split; [exact Hg | reflexivity]).
        destruct (Hdep _ Hp _ _ Hd1) as [v1 [Hv1 Hv1S]].
        rewrite SOvt.singleton_in in Hv1; subst v1.
        assert (Hd2 : T.DepRel.In
                        (embedPkg (n, u),
                         (Name.Synthetic n vs, T.VSet.singleton Version.Zero))
                        (reduceDeps D G))
          by (apply mem_reduceDeps; right; right; exists p, n, vs, u;
              split; [exact Hg | split; [exact Hu | reflexivity]]).
        destruct (Hdep _ HuS _ _ Hd2) as [v2 [Hv2 Hv2S]].
        rewrite SOvt.singleton_in in Hv2; subst v2.
        assert (E : Version.One = Version.Zero)
          by (apply (Huniq (Name.Synthetic n vs)); assumption).
        discriminate E.
    Qed.

    Definition coreResolution (S : PkgSet.t) (G : ConflictRel.t) :
        T.PkgSet.t :=
      T.PkgSet.union (embedSet S)
        (T.PkgSet.union
           (SOdt.filterMap (fun '(p, (n, vs)) =>
                if PkgSet.mem p S
                then Some (Name.Synthetic n vs, Version.One)
                else None)
              G)
           (SOdt.filterMap (fun '(_, (n, vs)) =>
                if VSet.exists_ (fun u => PkgSet.mem (n, u) S) vs
                then Some (Name.Synthetic n vs, Version.Zero)
                else None)
              G)).

    Lemma mem_coreResolution :
      forall (S : PkgSet.t) (G : ConflictRel.t) (y : T.Pkg.t),
        T.PkgSet.In y (coreResolution S G) <->
        (exists p, PkgSet.In p S /\ y = embedPkg p) \/
        (exists p n vs, ConflictRel.In (p, (n, vs)) G /\ PkgSet.In p S /\
           y = (Name.Synthetic n vs, Version.One)) \/
        (exists p n vs, ConflictRel.In (p, (n, vs)) G /\
           (exists u, VSet.In u vs /\ PkgSet.In (n, u) S) /\
           y = (Name.Synthetic n vs, Version.Zero)).
    Proof.
      intros S G y; unfold coreResolution, embedSet.
      rewrite !T.PkgSet.union_spec, SOpt.mem_map, !SOdt.mem_filterMap.
      split.
      - intros [H | [H | H]]; [left; exact H | right; left | right; right].
        + destruct H as [[q [n vs]] [HeG He]]; cbn beta iota in He.
          destruct (PkgSet.mem q S) eqn:Hm; [| discriminate].
          injection He as <-.
          exists q, n, vs; split; [exact HeG |].
          split; [apply PkgSet.mem_spec; exact Hm | reflexivity].
        + destruct H as [[q [n vs]] [HeG He]]; cbn beta iota in He.
          destruct (VSet.exists_ (fun u => PkgSet.mem (n, u) S) vs) eqn:Hm;
            [| discriminate].
          injection He as <-.
          rewrite VSet.exists_spec' in Hm.
          destruct Hm as [u [Hu Hmu]].
          exists q, n, vs; split; [exact HeG | split; [| reflexivity]].
          exists u; split; [exact Hu | apply PkgSet.mem_spec; exact Hmu].
      - intros [H | [[p [n [vs [HG [HpS ->]]]]] | [p [n [vs [HG [Hex ->]]]]]]].
        + left; exact H.
        + right; left; exists (p, (n, vs)); split; [exact HG |].
          assert (Hm : PkgSet.mem p S = true)
            by (apply PkgSet.mem_spec; exact HpS).
          cbn beta iota; rewrite Hm; reflexivity.
        + right; right; exists (p, (n, vs)); split; [exact HG |].
          assert (Hm : VSet.exists_ (fun u => PkgSet.mem (n, u) S) vs = true).
          { rewrite VSet.exists_spec'.
            destruct Hex as [u [Hu HuS]]; exists u; split;
              [exact Hu | apply PkgSet.mem_spec; exact HuS]. }
          cbn beta iota; rewrite Hm; reflexivity.
    Qed.

    Lemma mem_coreResolution_embed :
      forall (S : PkgSet.t) (G : ConflictRel.t) (p : Pkg.t),
        PkgSet.In p S -> T.PkgSet.In (embedPkg p) (coreResolution S G).
    Proof.
      intros S G p Hp; apply mem_coreResolution.
      left; exists p; split; [exact Hp | reflexivity].
    Qed.

    Lemma mem_coreResolution_one :
      forall (S : PkgSet.t) (G : ConflictRel.t) (p : Pkg.t) (n : N.t)
             (vs : VSet.t),
        ConflictRel.In (p, (n, vs)) G -> PkgSet.In p S ->
        T.PkgSet.In (Name.Synthetic n vs, Version.One) (coreResolution S G).
    Proof.
      intros S G p n vs Hg Hp; apply mem_coreResolution.
      right; left; exists p, n, vs; auto.
    Qed.

    Lemma mem_coreResolution_zero :
      forall (S : PkgSet.t) (G : ConflictRel.t) (p : Pkg.t) (n : N.t)
             (vs : VSet.t),
        ConflictRel.In (p, (n, vs)) G ->
        (exists u, VSet.In u vs /\ PkgSet.In (n, u) S) ->
        T.PkgSet.In (Name.Synthetic n vs, Version.Zero) (coreResolution S G).
    Proof.
      intros S G p n vs Hg Hex; apply mem_coreResolution.
      right; right; exists p, n, vs; auto.
    Qed.

    Lemma embed_mem_coreResolution_inv :
      forall (S : PkgSet.t) (G : ConflictRel.t) (p : Pkg.t),
        T.PkgSet.In (embedPkg p) (coreResolution S G) -> PkgSet.In p S.
    Proof.
      intros S G p H; apply mem_coreResolution in H.
      destruct H as [[q [HqS Hq]] | [[q [n [vs [_ [_ Hq]]]]]
                    | [q [n [vs [_ [_ Hq]]]]]]].
      - apply embedPkg_injective in Hq; subst q; exact HqS.
      - destruct p; unfold embedPkg in Hq; simpl in Hq; congruence.
      - destruct p; unfold embedPkg in Hq; simpl in Hq; congruence.
    Qed.

    Theorem conflict_completeness :
      forall (R : PkgSet.t) (D : C.DepRel.t) (G : ConflictRel.t)
             (r : Pkg.t) (S : PkgSet.t),
        IsResolution R D G r S ->
        T.IsResolution (reduceReal R G) (reduceDeps D G) (embedPkg r)
          (coreResolution S G).
    Proof.
      intros R D G r S [[Hsub Hroot Hdep Huniq] Havoid].
      constructor.
      - intros y Hy; apply mem_coreResolution in Hy; apply mem_reduceReal.
        destruct Hy as [[p [HpS ->]] | [[p [n [vs [HG [_ ->]]]]]
                       | [p [n [vs [HG [_ ->]]]]]]].
        + left; exists p; split; [apply Hsub; exact HpS | reflexivity].
        + right; exists p, n, vs; auto.
        + right; exists p, n, vs; auto.
      - apply mem_coreResolution_embed; exact Hroot.
      - intros q Hq m ws Hd; apply mem_reduceDeps in Hd.
        destruct Hd as [[p [m0 [vs [HD Hy]]]] | [[p [n [vs [HG Hy]]]]
                       | [p [n [vs [u [HG [Hu Hy]]]]]]]];
          injection Hy as -> -> ->.
        + assert (HpS : PkgSet.In p S)
            by (apply (embed_mem_coreResolution_inv S G p); exact Hq).
          destruct (Hdep p HpS m0 vs HD) as [v [Hv HvS]].
          exists (Version.Orig v); split.
          * unfold embedVS; apply SOvt.mem_map; exists v; auto.
          * exact (mem_coreResolution_embed S G (m0, v) HvS).
        + assert (HpS : PkgSet.In p S)
            by (apply (embed_mem_coreResolution_inv S G p); exact Hq).
          exists Version.One; split.
          * apply SOvt.singleton_in; reflexivity.
          * exact (mem_coreResolution_one S G p n vs HG HpS).
        + assert (HuS : PkgSet.In (n, u) S)
            by (apply (embed_mem_coreResolution_inv S G (n, u)); exact Hq).
          exists Version.Zero; split.
          * apply SOvt.singleton_in; reflexivity.
          * apply (mem_coreResolution_zero S G p n vs HG).
            exists u; auto.
      - intros nm w w' Hw Hw'.
        apply mem_coreResolution in Hw, Hw'.
        destruct Hw as [[p [HpS Hp]] | [[p [n [vs [HG [HpS Hp]]]]]
                       | [p [n [vs [HG [Hex Hp]]]]]]];
          destruct Hw' as [[p' [Hp'S Hp']] | [[p' [n' [vs' [HG' [Hp'S Hp']]]]]
                          | [p' [n' [vs' [HG' [Hex' Hp']]]]]]].
        + destruct p as [pn pv]; destruct p' as [pn' pv'];
            unfold embedPkg in Hp, Hp'; simpl in Hp, Hp'.
          injection Hp as -> ->; injection Hp' as -> ->.
          assert (pv = pv') as -> by (apply (Huniq pn'); assumption);
            reflexivity.
        + destruct p; unfold embedPkg in Hp; simpl in Hp; congruence.
        + destruct p; unfold embedPkg in Hp; simpl in Hp; congruence.
        + destruct p'; unfold embedPkg in Hp'; simpl in Hp'; congruence.
        + congruence.
        + exfalso.
          assert (E : Name.Synthetic n vs = Name.Synthetic n' vs')
            by congruence.
          injection E as <- <-.
          exact (Havoid p HpS n vs HG Hex').
        + destruct p'; unfold embedPkg in Hp'; simpl in Hp'; congruence.
        + exfalso.
          assert (E : Name.Synthetic n vs = Name.Synthetic n' vs')
            by congruence.
          injection E as <- <-.
          exact (Havoid p' Hp'S n vs HG' Hex).
        + congruence.
    Qed.
  End Reduction.
End Conflict.
