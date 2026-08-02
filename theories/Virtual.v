From Stdlib Require Import MSets.
From PackageCalculus Require Import Prelude Core.

Create HintDb cmp_virt.
Create Rewrite HintDb cmp_virt.

Module Virtual (N V : UsualOrderedType).
  Module C := Core N V.
  Module Pkg := C.Pkg.
  Module PkgSet := C.PkgSet.
  Module VSet := C.VSet.

  Inductive VTop : Type :=
  | VTVal (v : V.t)
  | VTTop.

  Module VF := UOTCompareFacts V.
  #[local] Hint Rewrite VF.compare_eq_iff : cmp_virt.
  #[local] Hint Extern 1 => cmp_by VF.compare_antisym : cmp_virt.
  #[local] Hint Extern 1 => cmp_by VF.compare_lt_trans : cmp_virt.

  Module VTComp <: ComparableType.
    Definition t := VTop.
    Definition compare (x y : t) : comparison :=
      match x, y with
      | VTVal v1, VTVal v2 => V.compare v1 v2
      | VTVal _, VTTop => Lt
      | VTTop, VTVal _ => Gt
      | VTTop, VTTop => Eq
      end.

    Lemma compare_eq_iff : forall x y, compare x y = Eq <-> x = y.
    Proof. cmp_eq_iff cmp_virt. Qed.

    Lemma compare_antisym : forall x y, compare y x = CompOpp (compare x y).
    Proof. cmp_antisym cmp_virt. Qed.

    Lemma compare_lt_trans : forall x y z,
        compare x y = Lt -> compare y z = Lt -> compare x z = Lt.
    Proof. cmp_lt_trans cmp_virt. Qed.
  End VTComp.
  Module VTOT := UOTFromCompare VTComp.

  Module Provided := PairUOT N VTOT.
  Module ProvElt := PairUOT Pkg Provided.
  Module ProvidesRel := FSetUOT ProvElt.

  Module Depender := PairUOT N Pkg.
  Module RhoElt := PairUOT Pkg Depender.
  Module RhoRel := FSetUOT RhoElt.

  Definition MemTop (v : VTop) (vs : VSet.t) : Prop :=
    match v with
    | VTTop => True
    | VTVal v' => VSet.In v' vs
    end.

  Definition memTopb (v : VTop) (vs : VSet.t) : bool :=
    match v with
    | VTTop => true
    | VTVal v' => VSet.mem v' vs
    end.

  Lemma memTopb_iff : forall v vs, memTopb v vs = true <-> MemTop v vs.
  Proof.
    intros [v' |] vs; simpl.
    - apply VSet.mem_spec.
    - split; [intros _; exact I | reflexivity].
  Qed.

  Record IsResolution
      (R : PkgSet.t) (D : C.DepRel.t) (Pi : ProvidesRel.t)
      (r : Pkg.t) (S : PkgSet.t) (rho : RhoRel.t) : Prop :=
    { res_subset : PkgSet.Subset S R
    ; res_root_mem : PkgSet.In r S
    ; res_virtual_dep_closure :
        forall p, PkgSet.In p S ->
        forall (n : N.t) (vs : VSet.t),
          C.DepRel.In (p, (n, vs)) D ->
          (exists v, VSet.In v vs /\ PkgSet.In (n, v) S) \/
          (exists! q, PkgSet.In q S /\
             exists v, MemTop v vs /\ ProvidesRel.In (q, (n, v)) Pi /\
               RhoRel.In (q, (n, p)) rho)
    ; res_version_unique : C.VersionUnique S
    ; res_provider_subset :
        forall (q : Pkg.t) (n : N.t) (p : Pkg.t),
          RhoRel.In (q, (n, p)) rho -> PkgSet.In q S /\ PkgSet.In p S }.

  Module Reduction.

    Module PkgN := PairUOT Pkg N.
    Module PkgNF := UOTCompareFacts PkgN.
    Module NF := UOTCompareFacts N.
    #[local] Hint Rewrite PkgNF.compare_eq_iff NF.compare_eq_iff : cmp_virt.
    #[local] Hint Extern 1 => cmp_by PkgNF.compare_antisym : cmp_virt.
    #[local] Hint Extern 1 => cmp_by NF.compare_antisym : cmp_virt.
    #[local] Hint Extern 1 => cmp_by PkgNF.compare_lt_trans : cmp_virt.
    #[local] Hint Extern 1 => cmp_by NF.compare_lt_trans : cmp_virt.

    Module Name.
      Inductive name : Type :=
      | Orig (n : N.t)
      | Selector (p : Pkg.t) (m : N.t).
      Definition t := name.

      Definition compare (x y : t) : comparison :=
        match x, y with
        | Orig n1, Orig n2 => N.compare n1 n2
        | Orig _, Selector _ _ => Lt
        | Selector _ _, Orig _ => Gt
        | Selector p1 m1, Selector p2 m2 => PkgN.compare (p1, m1) (p2, m2)
        end.

      Lemma compare_eq_iff : forall x y, compare x y = Eq <-> x = y.
      Proof. cmp_eq_iff cmp_virt. Qed.

      Lemma compare_antisym : forall x y, compare y x = CompOpp (compare x y).
      Proof. cmp_antisym cmp_virt. Qed.

      Lemma compare_lt_trans : forall x y z,
          compare x y = Lt -> compare y z = Lt -> compare x z = Lt.
      Proof. cmp_lt_trans cmp_virt. Qed.
    End Name.

    Module NV := PairUOT N V.
    Module NVF := UOTCompareFacts NV.
    #[local] Hint Rewrite NVF.compare_eq_iff : cmp_virt.
    #[local] Hint Extern 1 => cmp_by NVF.compare_antisym : cmp_virt.
    #[local] Hint Extern 1 => cmp_by NVF.compare_lt_trans : cmp_virt.

    Module Version.
      Inductive version : Type :=
      | Orig (v : V.t)
      | Provider (n : N.t) (w : V.t).
      Definition t := version.

      Definition compare (x y : t) : comparison :=
        match x, y with
        | Orig v1, Orig v2 => V.compare v1 v2
        | Orig _, Provider _ _ => Lt
        | Provider _ _, Orig _ => Gt
        | Provider n1 w1, Provider n2 w2 => NV.compare (n1, w1) (n2, w2)
        end.

      Lemma compare_eq_iff : forall x y, compare x y = Eq <-> x = y.
      Proof. cmp_eq_iff cmp_virt. Qed.

      Lemma compare_antisym : forall x y, compare y x = CompOpp (compare x y).
      Proof. cmp_antisym cmp_virt. Qed.

      Lemma compare_lt_trans : forall x y z,
          compare x y = Lt -> compare y z = Lt -> compare x z = Lt.
      Proof. cmp_lt_trans cmp_virt. Qed.
    End Version.

    Module NameOT := UOTFromCompare Name.
    Module VersionOT := UOTFromCompare Version.
    Module T := Core NameOT VersionOT.

    Definition embedPkg (p : Pkg.t) : T.Pkg.t :=
      let '(n, v) := p in (Name.Orig n, Version.Orig v).

    Module SOsp := SetOps Pkg T.Pkg PkgSet T.PkgSet.
    Definition embedSet (S : PkgSet.t) : T.PkgSet.t :=
      SOsp.map embedPkg S.

    Module SOvv := SetOps V VersionOT VSet T.VSet.
    Definition embedVS (vs : VSet.t) : T.VSet.t :=
      SOvv.map Version.Orig vs.

    Definition HasProvider
        (Pi : ProvidesRel.t) (n : N.t) (vs : VSet.t) : Prop :=
      exists q v, ProvidesRel.In (q, (n, v)) Pi /\ MemTop v vs.

    Module NEqb := UOTEqb N.

    Definition hasProviderb
        (Pi : ProvidesRel.t) (n : N.t) (vs : VSet.t) : bool :=
      ProvidesRel.exists_ (fun '(_, (m, v)) =>
          andb (NEqb.eqb m n) (memTopb v vs))
        Pi.

    Lemma hasProviderb_iff : forall Pi n vs,
        hasProviderb Pi n vs = true <-> HasProvider Pi n vs.
    Proof.
      intros Pi n vs; unfold hasProviderb, HasProvider.
      rewrite ProvidesRel.exists_spec'.
      unfold ProvidesRel.Exists; split.
      - intros [t [Ht Hb]]; destruct t as [q [n' v]]; cbn beta iota in Hb.
        apply andb_prop in Hb; destruct Hb as [He Hm].
        apply NEqb.eqb_true_iff in He as ->.
        exists q, v; split; [exact Ht | apply memTopb_iff; exact Hm].
      - intros [q [v [Hin Hm]]].
        exists (q, (n, v)); split; [exact Hin | cbn beta iota].
        rewrite NEqb.eqb_refl; cbn [andb]; apply memTopb_iff; exact Hm.
    Qed.

    Module SOpp := SetOps ProvElt T.Pkg ProvidesRel T.PkgSet.
    Definition realProviderBlock (Pi : ProvidesRel.t) (p : Pkg.t) (n : N.t)
        (vs : VSet.t) : T.PkgSet.t :=
      SOpp.filterMap (fun '(q, (n', v)) =>
          if andb (NEqb.eqb n' n) (memTopb v vs)
          then Some (Name.Selector p n, Version.Provider (fst q) (snd q))
          else None)
        Pi.

    Lemma mem_realProviderBlock :
      forall Pi (p : Pkg.t) (n : N.t) (vs : VSet.t) n' v',
        T.PkgSet.In (n', v') (realProviderBlock Pi p n vs) <->
        exists m u v, ProvidesRel.In ((m, u), (n, v)) Pi /\ MemTop v vs /\
          n' = Name.Selector p n /\ v' = Version.Provider m u.
    Proof.
      intros Pi p n vs n' v'; unfold realProviderBlock.
      rewrite SOpp.mem_filterMap.
      split.
      - intros [[[m u] [m0 v]] [Ht Hy]]; cbn [fst snd] in Hy.
        destruct (andb (NEqb.eqb m0 n) (memTopb v vs)) eqn:Hc;
          [| discriminate].
        apply andb_prop in Hc; destruct Hc as [He Hm].
        apply NEqb.eqb_true_iff in He as ->.
        injection Hy as <- <-.
        exists m, u, v; split; [exact Ht |].
        split; [apply memTopb_iff; exact Hm | split; reflexivity].
      - intros [m [u [v [Hin [Hm [-> ->]]]]]].
        exists ((m, u), (n, v)); split; [exact Hin | cbn [fst snd]].
        rewrite NEqb.eqb_refl; cbn [andb].
        apply memTopb_iff in Hm; rewrite Hm; reflexivity.
    Qed.

    Module SOvp := SetOps V T.Pkg VSet T.PkgSet.
    Definition realDirectBlock (R : PkgSet.t) (p : Pkg.t) (n : N.t)
        (vs : VSet.t) : T.PkgSet.t :=
      SOvp.filterMap (fun u =>
          if PkgSet.mem (n, u) R
          then Some (Name.Selector p n, Version.Provider n u)
          else None)
        vs.

    Lemma mem_realDirectBlock :
      forall R (p : Pkg.t) (n : N.t) (vs : VSet.t) n' v',
        T.PkgSet.In (n', v') (realDirectBlock R p n vs) <->
        exists u, VSet.In u vs /\ PkgSet.In (n, u) R /\
          n' = Name.Selector p n /\ v' = Version.Provider n u.
    Proof.
      intros R p n vs n' v'; unfold realDirectBlock.
      rewrite SOvp.mem_filterMap.
      split.
      - intros [u [Hu Hy]]; cbn beta iota in Hy.
        destruct (PkgSet.mem (n, u) R) eqn:Hm; [| discriminate].
        injection Hy as <- <-.
        exists u; split; [exact Hu |].
        split; [apply PkgSet.mem_spec; exact Hm | split; reflexivity].
      - intros [u [Hu [HR [-> ->]]]].
        exists u; split; [exact Hu | cbn beta iota].
        match goal with
        | |- (if ?b then _ else _) = _ =>
            replace b with true by (symmetry; apply PkgSet.mem_spec; exact HR)
        end.
        reflexivity.
    Qed.

    Module SOdp := SetOps C.DepElt T.Pkg C.DepRel T.PkgSet.
    Definition reduceReal (R : PkgSet.t) (D : C.DepRel.t) (Pi : ProvidesRel.t) :
        T.PkgSet.t :=
      T.PkgSet.union (embedSet R)
        (T.PkgSet.union
           (SOdp.unionMap (fun '(p, (n, vs)) =>
                realProviderBlock Pi p n vs)
              D)
           (SOdp.unionMap (fun '(p, (n, vs)) =>
                if hasProviderb Pi n vs
                then realDirectBlock R p n vs
                else T.PkgSet.empty)
              D)).

    Lemma mem_reduceReal : forall R D Pi n' v',
        T.PkgSet.In (n', v') (reduceReal R D Pi) <->
        (exists n v,
           PkgSet.In (n, v) R /\ n' = Name.Orig n /\ v' = Version.Orig v) \/
        (exists p n vs m u v, C.DepRel.In (p, (n, vs)) D /\
           ProvidesRel.In ((m, u), (n, v)) Pi /\ MemTop v vs /\
           n' = Name.Selector p n /\ v' = Version.Provider m u) \/
        (exists p n vs u, C.DepRel.In (p, (n, vs)) D /\ HasProvider Pi n vs /\
           VSet.In u vs /\ PkgSet.In (n, u) R /\
           n' = Name.Selector p n /\ v' = Version.Provider n u).
    Proof.
      intros R D Pi n' v'; unfold reduceReal, embedSet.
      rewrite !T.PkgSet.union_spec, SOsp.mem_map, !SOdp.mem_unionMap.
      split.
      - intros [Hemb | [[[p [n vs]] [HeD He]] | [[p [n vs]] [HeD He]]]].
        + left; destruct Hemb as [[n v] [HR Hy]].
          unfold embedPkg in Hy; injection Hy as -> ->.
          exists n, v; split; [exact HR | split; reflexivity].
        + cbn beta iota in He; apply mem_realProviderBlock in He.
          destruct He as [m [u [v [Hin [Hm [-> ->]]]]]].
          right; left; exists p, n, vs, m, u, v.
          split; [exact HeD | split; [exact Hin |]].
          split; [exact Hm | split; reflexivity].
        + cbn beta iota in He.
          destruct (hasProviderb Pi n vs) eqn:Hb;
            [| exfalso; exact (SOvp.empty_in _ He)].
          apply mem_realDirectBlock in He.
          destruct He as [u [Hu [HR [-> ->]]]].
          right; right; exists p, n, vs, u.
          split; [exact HeD |].
          split; [apply hasProviderb_iff; exact Hb |].
          split; [exact Hu | split; [exact HR | split; reflexivity]].
      - intros [Hemb | [Hsel | Hdir]].
        + left; destruct Hemb as [n [v [HR [-> ->]]]].
          exists (n, v); split; [exact HR | reflexivity].
        + right; left.
          destruct Hsel as [p [n [vs [m [u [v [HD [Hin [Hm [-> ->]]]]]]]]]].
          exists (p, (n, vs)); split; [exact HD | cbn beta iota].
          apply mem_realProviderBlock.
          exists m, u, v; split; [exact Hin |].
          split; [exact Hm | split; reflexivity].
        + right; right.
          destruct Hdir as [p [n [vs [u [HD [Hb [Hu [HR [-> ->]]]]]]]]].
          exists (p, (n, vs)); split; [exact HD | cbn beta iota].
          apply hasProviderb_iff in Hb; rewrite Hb.
          apply mem_realDirectBlock.
          exists u; split; [exact Hu | split; [exact HR | split; reflexivity]].
    Qed.

    Module SOpv := SetOps ProvElt VersionOT ProvidesRel T.VSet.
    Definition selectorVersions (R : PkgSet.t) (Pi : ProvidesRel.t)
        (n : N.t) (vs : VSet.t) : T.VSet.t :=
      T.VSet.union
        (SOpv.filterMap (fun '(q, (n', v)) =>
             if andb (NEqb.eqb n' n) (memTopb v vs)
             then Some (Version.Provider (fst q) (snd q))
             else None)
           Pi)
        (SOvv.filterMap (fun u =>
             if PkgSet.mem (n, u) R
             then Some (Version.Provider n u)
             else None)
           vs).

    Lemma mem_selectorVersions : forall R Pi n vs y,
        T.VSet.In y (selectorVersions R Pi n vs) <->
        (exists m u v, ProvidesRel.In ((m, u), (n, v)) Pi /\ MemTop v vs /\
           y = Version.Provider m u) \/
        (exists u,
           VSet.In u vs /\ PkgSet.In (n, u) R /\ y = Version.Provider n u).
    Proof.
      intros R Pi n vs y; unfold selectorVersions.
      rewrite T.VSet.union_spec, SOpv.mem_filterMap, SOvv.mem_filterMap.
      split.
      - intros [[[[m u] [n' v]] [Ht Hy]] | [u [Hu Hy]]]; cbn [fst snd] in Hy.
        + destruct (andb (NEqb.eqb n' n) (memTopb v vs)) eqn:Hc;
            [| discriminate].
          apply andb_prop in Hc; destruct Hc as [He Hm].
          apply NEqb.eqb_true_iff in He as ->.
          injection Hy as <-.
          left; exists m, u, v; repeat split;
            [exact Ht | apply memTopb_iff; exact Hm].
        + destruct (PkgSet.mem (n, u) R) eqn:Hm; [| discriminate].
          injection Hy as <-.
          right; exists u; repeat split;
            [exact Hu | apply PkgSet.mem_spec; exact Hm].
      - intros [[m [u [v [Hin [Hm ->]]]]] | [u [Hu [HR ->]]]].
        + left; exists ((m, u), (n, v)).
          split; [exact Hin | cbn [fst snd]].
          rewrite NEqb.eqb_refl; cbn [andb].
          apply memTopb_iff in Hm; rewrite Hm; reflexivity.
        + right; exists u; split; [exact Hu | cbn beta iota].
          match goal with
          | |- (if ?b then _ else _) = _ =>
              replace b with true by (symmetry; apply PkgSet.mem_spec; exact HR)
          end.
          reflexivity.
    Qed.

    Module SOpd := SetOps ProvElt T.DepElt ProvidesRel T.DepRel.
    Definition depsProviderBlock (Pi : ProvidesRel.t) (p : Pkg.t) (n : N.t)
        (vs : VSet.t) : T.DepRel.t :=
      SOpd.filterMap (fun '(q, (n', v)) =>
          if andb (NEqb.eqb n' n) (memTopb v vs)
          then Some ((Name.Selector p n, Version.Provider (fst q) (snd q)),
                     (Name.Orig (fst q),
                      T.VSet.singleton (Version.Orig (snd q))))
          else None)
        Pi.

    Lemma mem_depsProviderBlock :
      forall Pi (p : Pkg.t) (n : N.t) (vs : VSet.t) p' n' ws,
        T.DepRel.In (p', (n', ws)) (depsProviderBlock Pi p n vs) <->
        exists m u v, ProvidesRel.In ((m, u), (n, v)) Pi /\ MemTop v vs /\
          p' = (Name.Selector p n, Version.Provider m u) /\ n' = Name.Orig m /\
          ws = T.VSet.singleton (Version.Orig u).
    Proof.
      intros Pi p n vs p' n' ws; unfold depsProviderBlock.
      rewrite SOpd.mem_filterMap.
      split.
      - intros [[[m u] [m0 v]] [Ht Hy]]; cbn [fst snd] in Hy.
        destruct (andb (NEqb.eqb m0 n) (memTopb v vs)) eqn:Hc;
          [| discriminate].
        apply andb_prop in Hc; destruct Hc as [He Hm].
        apply NEqb.eqb_true_iff in He as ->.
        injection Hy as <- <- <-.
        exists m, u, v; split; [exact Ht |].
        split; [apply memTopb_iff; exact Hm |].
        split; [reflexivity | split; reflexivity].
      - intros [m [u [v [Hin [Hm [-> [-> ->]]]]]]].
        exists ((m, u), (n, v)); split; [exact Hin | cbn [fst snd]].
        rewrite NEqb.eqb_refl; cbn [andb].
        apply memTopb_iff in Hm; rewrite Hm; reflexivity.
    Qed.

    Module SOvd := SetOps V T.DepElt VSet T.DepRel.
    Definition depsDirectBlock (R : PkgSet.t) (p : Pkg.t) (n : N.t)
        (vs : VSet.t) : T.DepRel.t :=
      SOvd.filterMap (fun u =>
          if PkgSet.mem (n, u) R
          then Some ((Name.Selector p n, Version.Provider n u),
                     (Name.Orig n, T.VSet.singleton (Version.Orig u)))
          else None)
        vs.

    Lemma mem_depsDirectBlock :
      forall R (p : Pkg.t) (n : N.t) (vs : VSet.t) p' n' ws,
        T.DepRel.In (p', (n', ws)) (depsDirectBlock R p n vs) <->
        exists u, VSet.In u vs /\ PkgSet.In (n, u) R /\
          p' = (Name.Selector p n, Version.Provider n u) /\ n' = Name.Orig n /\
          ws = T.VSet.singleton (Version.Orig u).
    Proof.
      intros R p n vs p' n' ws; unfold depsDirectBlock.
      rewrite SOvd.mem_filterMap.
      split.
      - intros [u [Hu Hy]]; cbn beta iota in Hy.
        destruct (PkgSet.mem (n, u) R) eqn:Hm; [| discriminate].
        injection Hy as <- <- <-.
        exists u; split; [exact Hu |].
        split; [apply PkgSet.mem_spec; exact Hm |].
        split; [reflexivity | split; reflexivity].
      - intros [u [Hu [HR [-> [-> ->]]]]].
        exists u; split; [exact Hu | cbn beta iota].
        match goal with
        | |- (if ?b then _ else _) = _ =>
            replace b with true by (symmetry; apply PkgSet.mem_spec; exact HR)
        end.
        reflexivity.
    Qed.

    Module SOdd := SetOps C.DepElt T.DepElt C.DepRel T.DepRel.
    Definition reduceDeps (R : PkgSet.t) (D : C.DepRel.t) (Pi : ProvidesRel.t) :
        T.DepRel.t :=
      T.DepRel.union
        (SOdd.filterMap (fun '(p, (n, vs)) =>
             if hasProviderb Pi n vs then None
             else Some (embedPkg p, (Name.Orig n, embedVS vs)))
           D)
        (T.DepRel.union
           (SOdd.filterMap (fun '(p, (n, vs)) =>
                if hasProviderb Pi n vs
                then Some (embedPkg p,
                           (Name.Selector p n, selectorVersions R Pi n vs))
                else None)
              D)
           (T.DepRel.union
              (SOdd.unionMap (fun '(p, (n, vs)) =>
                   depsProviderBlock Pi p n vs)
                 D)
              (SOdd.unionMap (fun '(p, (n, vs)) =>
                   if hasProviderb Pi n vs
                   then depsDirectBlock R p n vs
                   else T.DepRel.empty)
                 D))).

    Lemma mem_reduceDeps : forall R D Pi p' n' ws,
        T.DepRel.In (p', (n', ws)) (reduceDeps R D Pi) <->
        (exists p n vs, C.DepRel.In (p, (n, vs)) D /\ ~ HasProvider Pi n vs /\
           p' = embedPkg p /\ n' = Name.Orig n /\ ws = embedVS vs) \/
        (exists p n vs, C.DepRel.In (p, (n, vs)) D /\ HasProvider Pi n vs /\
           p' = embedPkg p /\ n' = Name.Selector p n /\
           ws = selectorVersions R Pi n vs) \/
        (exists p n vs m u v, C.DepRel.In (p, (n, vs)) D /\
           ProvidesRel.In ((m, u), (n, v)) Pi /\ MemTop v vs /\
           p' = (Name.Selector p n, Version.Provider m u) /\ n' = Name.Orig m /\
           ws = T.VSet.singleton (Version.Orig u)) \/
        (exists p n vs u, C.DepRel.In (p, (n, vs)) D /\ HasProvider Pi n vs /\
           VSet.In u vs /\ PkgSet.In (n, u) R /\
           p' = (Name.Selector p n, Version.Provider n u) /\ n' = Name.Orig n /\
           ws = T.VSet.singleton (Version.Orig u)).
    Proof.
      intros R D Pi p' n' ws; unfold reduceDeps.
      rewrite !T.DepRel.union_spec, !SOdd.mem_filterMap, !SOdd.mem_unionMap.
      split.
      - intros [[[p [n vs]] [HeD He]] |
                [[[p [n vs]] [HeD He]] |
                 [[[p [n vs]] [HeD He]] | [[p [n vs]] [HeD He]]]]];
          cbn beta iota in He.
        + destruct (hasProviderb Pi n vs) eqn:Hb; [discriminate |].
          injection He as <- <- <-.
          left; exists p, n, vs; split; [exact HeD |].
          split; [intros Hp; apply hasProviderb_iff in Hp; congruence |].
          split; [reflexivity | split; reflexivity].
        + destruct (hasProviderb Pi n vs) eqn:Hb; [| discriminate].
          injection He as <- <- <-.
          right; left; exists p, n, vs; split; [exact HeD |].
          split; [apply hasProviderb_iff; exact Hb |].
          split; [reflexivity | split; reflexivity].
        + apply mem_depsProviderBlock in He.
          destruct He as [m [u [v [Hin [Hm [-> [-> ->]]]]]]].
          right; right; left; exists p, n, vs, m, u, v.
          split; [exact HeD | split; [exact Hin |]].
          split; [exact Hm | split; [reflexivity | split; reflexivity]].
        + destruct (hasProviderb Pi n vs) eqn:Hb;
            [| exfalso; exact (SOvd.empty_in _ He)].
          apply mem_depsDirectBlock in He.
          destruct He as [u [Hu [HR [-> [-> ->]]]]].
          right; right; right; exists p, n, vs, u.
          split; [exact HeD |].
          split; [apply hasProviderb_iff; exact Hb |].
          split; [exact Hu | split; [exact HR |]].
          split; [reflexivity | split; reflexivity].
      - intros [H1 | [H2 | [H3 | H4]]].
        + destruct H1 as [p [n [vs [HD [Hb [-> [-> ->]]]]]]].
          left; exists (p, (n, vs)); split; [exact HD | cbn beta iota].
          destruct (hasProviderb Pi n vs) eqn:Hb'.
          * exfalso; apply Hb, hasProviderb_iff; exact Hb'.
          * reflexivity.
        + destruct H2 as [p [n [vs [HD [Hb [-> [-> ->]]]]]]].
          right; left; exists (p, (n, vs)); split; [exact HD | cbn beta iota].
          apply hasProviderb_iff in Hb; rewrite Hb; reflexivity.
        + destruct H3 as [p [n [vs [m [u [v [HD [Hin [Hm [-> [-> ->]]]]]]]]]]].
          right; right; left.
          exists (p, (n, vs)); split; [exact HD | cbn beta iota].
          apply mem_depsProviderBlock.
          exists m, u, v; split; [exact Hin |].
          split; [exact Hm | split; [reflexivity | split; reflexivity]].
        + destruct H4 as [p [n [vs [u [HD [Hb [Hu [HR [-> [-> ->]]]]]]]]]].
          right; right; right.
          exists (p, (n, vs)); split; [exact HD | cbn beta iota].
          apply hasProviderb_iff in Hb; rewrite Hb.
          apply mem_depsDirectBlock.
          exists u; split; [exact Hu |].
          split; [exact HR | split; [reflexivity | split; reflexivity]].
    Qed.

    Definition tryInvPkg (p' : T.Pkg.t) : option Pkg.t :=
      match p' with
      | (Name.Orig n, Version.Orig v) => Some (n, v)
      | _ => None
      end.

    Lemma tryInvPkg_embed : forall p, tryInvPkg (embedPkg p) = Some p.
    Proof. intros [n v]; reflexivity. Qed.

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

    Definition virtualResolution (S : T.PkgSet.t) : PkgSet.t :=
      SOtp.filterMap tryInvPkg S.

    Lemma mem_virtualResolution : forall (S : T.PkgSet.t) (p : Pkg.t),
        PkgSet.In p (virtualResolution S) <-> T.PkgSet.In (embedPkg p) S.
    Proof.
      unfold virtualResolution.
      exact (SOtp.mem_filterMap_inv tryInvPkg embedPkg tryInvPkg_embed
               tryInvPkg_some).
    Qed.

    Lemma embedPkg_mem_real : forall (p : Pkg.t) R D Pi,
        T.PkgSet.In (embedPkg p) (reduceReal R D Pi) -> PkgSet.In p R.
    Proof.
      intros [n v] R D Pi H; apply mem_reduceReal in H.
      destruct H as [[m [w [HR [Hn Hv]]]] | [Hsel | Hdir]].
      - injection Hn as ->; injection Hv as ->; exact HR.
      - destruct Hsel as [p [n0 [vs [m [u [w [_ [_ [_ [Hn _]]]]]]]]]].
        discriminate Hn.
      - destruct Hdir as [p [n0 [vs [u [_ [_ [_ [_ [Hn _]]]]]]]]].
        discriminate Hn.
    Qed.

    Module SOpr := SetOps ProvElt RhoElt ProvidesRel RhoRel.
    Definition rhoBlock (Pi : ProvidesRel.t) (S : T.PkgSet.t) (p : Pkg.t)
        (n : N.t) (vs : VSet.t) : RhoRel.t :=
      SOpr.filterMap (fun '(q, (n', v)) =>
          if andb (NEqb.eqb n' n)
               (andb (memTopb v vs)
                  (andb (T.PkgSet.mem (embedPkg p) S)
                     (T.PkgSet.mem
                        (Name.Selector p n,
                         Version.Provider (fst q) (snd q)) S)))
          then Some (q, (n, p))
          else None)
        Pi.

    Lemma mem_rhoBlock :
      forall Pi (S : T.PkgSet.t) (p : Pkg.t) (n : N.t) (vs : VSet.t)
             (m : N.t) (u : V.t) (m' : N.t) (p' : Pkg.t),
        RhoRel.In ((m, u), (m', p')) (rhoBlock Pi S p n vs) <->
        (exists v, ProvidesRel.In ((m, u), (n, v)) Pi /\ MemTop v vs /\
           T.PkgSet.In (embedPkg p) S /\
           T.PkgSet.In (Name.Selector p n, Version.Provider m u) S /\
           m' = n /\ p' = p).
    Proof.
      intros Pi S p n vs m u m' p'; unfold rhoBlock.
      rewrite SOpr.mem_filterMap.
      split.
      - intros [[[m0 u0] [m1 v]] [Ht Hy]]; cbn [fst snd] in Hy.
        destruct (andb (NEqb.eqb m1 n)
                    (andb (memTopb v vs)
                       (andb (T.PkgSet.mem (embedPkg p) S)
                          (T.PkgSet.mem
                             (Name.Selector p n,
                              Version.Provider m0 u0) S)))) eqn:Hc;
          [| discriminate].
        apply andb_prop in Hc; destruct Hc as [He Hc].
        apply andb_prop in Hc; destruct Hc as [Hm Hc].
        apply andb_prop in Hc; destruct Hc as [HpS HselS].
        apply NEqb.eqb_true_iff in He as ->.
        injection Hy as <- <- <- <-.
        exists v; split; [exact Ht |].
        split; [apply memTopb_iff; exact Hm |].
        split; [apply T.PkgSet.mem_spec; exact HpS |].
        split; [apply T.PkgSet.mem_spec; exact HselS | split; reflexivity].
      - intros [v [Hin [Hm [HpS [HselS [-> ->]]]]]].
        exists ((m, u), (n, v)); split; [exact Hin | cbn [fst snd]].
        rewrite NEqb.eqb_refl; cbn [andb].
        apply memTopb_iff in Hm; rewrite Hm.
        apply T.PkgSet.mem_spec in HpS; rewrite HpS.
        apply T.PkgSet.mem_spec in HselS; rewrite HselS; reflexivity.
    Qed.

    Module SOdr := SetOps C.DepElt RhoElt C.DepRel RhoRel.
    Definition providers (D : C.DepRel.t) (Pi : ProvidesRel.t)
        (S : T.PkgSet.t) : RhoRel.t :=
      SOdr.unionMap (fun '(p, (n, vs)) => rhoBlock Pi S p n vs) D.

    Lemma mem_providers :
      forall D Pi S (m : N.t) (u : V.t) (p : Pkg.t) (n : N.t),
        RhoRel.In ((m, u), (n, p)) (providers D Pi S) <->
        exists vs, C.DepRel.In (p, (n, vs)) D /\
          exists v, MemTop v vs /\ ProvidesRel.In ((m, u), (n, v)) Pi /\
            T.PkgSet.In (embedPkg p) S /\
            T.PkgSet.In (Name.Selector p n, Version.Provider m u) S.
    Proof.
      intros D Pi S m u p n; unfold providers; rewrite SOdr.mem_unionMap.
      split.
      - intros [[p0 [n0 vs]] [HeD He]]; cbn beta iota in He.
        apply mem_rhoBlock in He.
        destruct He as [v [Hin [Hm [HpS [HselS [-> ->]]]]]].
        exists vs; split; [exact HeD |].
        exists v; repeat split; assumption.
      - intros [vs [HD [v [Hm [HP [HpS HselS]]]]]].
        exists (p, (n, vs)); split; [exact HD | cbn beta iota].
        apply mem_rhoBlock.
        exists v; split; [exact HP |].
        split; [exact Hm | split; [exact HpS | split; [exact HselS |]]].
        split; reflexivity.
    Qed.

    Theorem virtual_soundness :
      forall (R : PkgSet.t) (D : C.DepRel.t) (Pi : ProvidesRel.t)
             (r : Pkg.t) (S : T.PkgSet.t),
        T.IsResolution (reduceReal R D Pi) (reduceDeps R D Pi)
          (embedPkg r) S ->
        IsResolution R D Pi r (virtualResolution S) (providers D Pi S).
    Proof.
      intros R D Pi r S [Hsub Hroot Hdep Huniq].
      assert (Hsel_emb : forall (m0 : N.t) (u0 : V.t) (p0 : Pkg.t)
                                (n0 : N.t) v0 vs0,
          C.DepRel.In (p0, (n0, vs0)) D ->
          ProvidesRel.In ((m0, u0), (n0, v0)) Pi -> MemTop v0 vs0 ->
          T.PkgSet.In (Name.Selector p0 n0, Version.Provider m0 u0) S ->
          T.PkgSet.In (embedPkg (m0, u0)) S).
      { intros m0 u0 p0 n0 v0 vs0 HD HP HM HselS.
        assert (Hd3 : T.DepRel.In
            ((Name.Selector p0 n0, Version.Provider m0 u0),
             (Name.Orig m0, T.VSet.singleton (Version.Orig u0)))
            (reduceDeps R D Pi)).
        { apply mem_reduceDeps; right; right; left.
          exists p0, n0, vs0, m0, u0, v0.
          split; [exact HD | split; [exact HP |]].
          split; [exact HM | split; [reflexivity | split; reflexivity]]. }
        destruct (Hdep _ HselS _ _ Hd3) as [w [Hw HwS]].
        apply T.VSet.singleton_spec in Hw; rewrite Hw in HwS.
        exact HwS. }
      constructor.
      - intros p Hp; apply mem_virtualResolution in Hp.
        exact (embedPkg_mem_real _ _ _ _ (Hsub _ Hp)).
      - apply mem_virtualResolution; exact Hroot.
      - intros p Hp n vs HD.
        apply mem_virtualResolution in Hp.
        destruct (hasProviderb Pi n vs) eqn:Hb.
        + assert (Hd2 : T.DepRel.In
              (embedPkg p, (Name.Selector p n, selectorVersions R Pi n vs))
              (reduceDeps R D Pi)).
          { apply mem_reduceDeps; right; left.
            exists p, n, vs; split; [exact HD |].
            split; [apply hasProviderb_iff; exact Hb |].
            split; [reflexivity | split; reflexivity]. }
          destruct (Hdep _ Hp _ _ Hd2) as [sv [Hsv HsvS]].
          apply mem_selectorVersions in Hsv.
          destruct Hsv as [[m [u [v [HP [Hm Hsv]]]]] | [u [Hu [HuR Hsv]]]].
          * subst sv; right.
            assert (HqS := Hsel_emb m u p n v vs HD HP Hm HsvS).
            exists (m, u); split.
            { split; [apply mem_virtualResolution; exact HqS |].
              exists v; split; [exact Hm |]; split; [exact HP |].
              apply mem_providers.
              exists vs; split; [exact HD |].
              exists v; repeat split; assumption. }
            { intros [m' u'] [Hq'S [v' [Hm' [HP' Hrho']]]].
              apply mem_providers in Hrho'.
              destruct Hrho' as [vs' [HD' [v0 [Hm0 [HP0 [HpS0 HselS0]]]]]].
              assert (Hveq := Huniq (Name.Selector p n)
                                (Version.Provider m u)
                                (Version.Provider m' u') HsvS HselS0).
              injection Hveq as H1 H2.
              rewrite H1, H2; reflexivity. }
          * subst sv.
            assert (Hd4 : T.DepRel.In
                ((Name.Selector p n, Version.Provider n u),
                 (Name.Orig n, T.VSet.singleton (Version.Orig u)))
                (reduceDeps R D Pi)).
            { apply mem_reduceDeps; right; right; right.
              exists p, n, vs, u; split; [exact HD |].
              split; [apply hasProviderb_iff; exact Hb |].
              split; [exact Hu | split; [exact HuR |]].
              split; [reflexivity | split; reflexivity]. }
            destruct (Hdep _ HsvS _ _ Hd4) as [w [Hw HwS]].
            apply T.VSet.singleton_spec in Hw; rewrite Hw in HwS.
            left; exists u; split;
              [exact Hu | apply mem_virtualResolution; exact HwS].
        + assert (Hd1 : T.DepRel.In
              (embedPkg p, (Name.Orig n, embedVS vs)) (reduceDeps R D Pi)).
          { apply mem_reduceDeps; left.
            exists p, n, vs; split; [exact HD |].
            split; [intros Hp0; apply hasProviderb_iff in Hp0; congruence |].
            split; [reflexivity | split; reflexivity]. }
          destruct (Hdep _ Hp _ _ Hd1) as [w [Hw HwS]].
          unfold embedVS in Hw; apply SOvv.mem_map in Hw;
            destruct Hw as [u [Hu ->]].
          left; exists u; split;
            [exact Hu | apply mem_virtualResolution; exact HwS].
      - intros n v v' Hv Hv'.
        apply mem_virtualResolution in Hv; apply mem_virtualResolution in Hv'.
        assert (H := Huniq (Name.Orig n)
                       (Version.Orig v) (Version.Orig v') Hv Hv').
        injection H as H; exact H.
      - intros [m u] n p Hrho.
        apply mem_providers in Hrho.
        destruct Hrho as [vs [HD [v [Hm [HP [HpS HselS]]]]]].
        split; apply mem_virtualResolution.
        + exact (Hsel_emb m u p n v vs HD HP Hm HselS).
        + exact HpS.
    Qed.

    Module PkgEqb := UOTEqb Pkg.
    Module SOkp := SetOps Pkg ProvElt PkgSet ProvidesRel.
    Definition rhoProviders (S_Pi : PkgSet.t) (rho : RhoRel.t)
        (Pi : ProvidesRel.t) (p : Pkg.t) (n : N.t) (vs : VSet.t) : PkgSet.t :=
      SOkp.filterExists
        (fun q '(q', (m, v)) =>
            andb (PkgEqb.eqb q' q)
              (andb (NEqb.eqb m n)
                 (andb (memTopb v vs) (RhoRel.mem (q, (n, p)) rho))))
        Pi S_Pi.

    Lemma mem_rhoProviders :
      forall S_Pi rho Pi (p : Pkg.t) (n : N.t) vs (q : Pkg.t),
        PkgSet.In q (rhoProviders S_Pi rho Pi p n vs) <->
        PkgSet.In q S_Pi /\
        exists v, MemTop v vs /\ ProvidesRel.In (q, (n, v)) Pi /\
          RhoRel.In (q, (n, p)) rho.
    Proof.
      intros S_Pi rho Pi p n vs q; unfold rhoProviders.
      rewrite SOkp.mem_filterExists.
      split.
      - intros [HqS [t [Ht Hb]]]; split; [exact HqS |].
        destruct t as [q' [m v]]; cbn beta iota in Hb.
        apply andb_prop in Hb; destruct Hb as [Hq Hb].
        apply andb_prop in Hb; destruct Hb as [Hn Hb].
        apply andb_prop in Hb; destruct Hb as [Hm Hr].
        apply PkgEqb.eqb_true_iff in Hq as ->.
        apply NEqb.eqb_true_iff in Hn as ->.
        exists v; split; [apply memTopb_iff; exact Hm |].
        split; [exact Ht | apply RhoRel.mem_spec; exact Hr].
      - intros [HqS [v [Hm [HP Hr]]]]; split; [exact HqS |].
        exists (q, (n, v)); split; [exact HP | cbn [fst snd]].
        rewrite PkgEqb.eqb_refl, NEqb.eqb_refl; cbn [andb].
        apply memTopb_iff in Hm; rewrite Hm.
        apply RhoRel.mem_spec in Hr; exact Hr.
    Qed.

    (* Any element of the first nonempty candidate class works; min_elt makes
       the choice deterministic and computable. *)
    Definition chooseSelector (S_Pi : PkgSet.t) (rho : RhoRel.t)
        (Pi : ProvidesRel.t) (p : Pkg.t) (n : N.t) (vs : VSet.t) :
        Version.t :=
      match PkgSet.min_elt (rhoProviders S_Pi rho Pi p n vs) with
      | Some q => Version.Provider (fst q) (snd q)
      | None =>
          let cand2 := VSet.filter (fun u => PkgSet.mem (n, u) S_Pi) vs in
          match VSet.min_elt cand2 with
          | Some u => Version.Provider n u
          | None => Version.Orig (snd p) (* unreachable under HasProvider *)
          end
      end.

    Lemma chooseSelector_spec :
      forall S_Pi rho Pi (p : Pkg.t) (n : N.t) vs,
        ((exists q, PkgSet.In q S_Pi /\ exists v, MemTop v vs /\
            ProvidesRel.In (q, (n, v)) Pi /\ RhoRel.In (q, (n, p)) rho) \/
         (exists u, VSet.In u vs /\ PkgSet.In (n, u) S_Pi)) ->
        exists m w, chooseSelector S_Pi rho Pi p n vs = Version.Provider m w /\
          PkgSet.In (m, w) S_Pi /\
          ((exists v, MemTop v vs /\ ProvidesRel.In ((m, w), (n, v)) Pi) \/
           (m = n /\ VSet.In w vs)).
    Proof.
      intros S_Pi rho Pi p n vs Hcase; unfold chooseSelector.
      match goal with
      | |- context [PkgSet.min_elt ?c] =>
          destruct (PkgSet.min_elt c) as [q1 |] eqn:H1
      end.
      - apply PkgSet.min_elt_spec1 in H1.
        apply mem_rhoProviders in H1.
        destruct H1 as [Hq1S [v [Hm [HP Hr]]]].
        exists (fst q1), (snd q1).
        split; [reflexivity |].
        split; [rewrite <- surjective_pairing; exact Hq1S |].
        left; exists v; split; [exact Hm |].
        rewrite <- surjective_pairing; exact HP.
      - match goal with
        | |- context [VSet.min_elt ?c] =>
            destruct (VSet.min_elt c) as [u1 |] eqn:H2
        end.
        + apply VSet.min_elt_spec1 in H2.
          rewrite VSet.filter_spec' in H2.
          destruct H2 as [Hu1 Hmem]; apply PkgSet.mem_spec in Hmem.
          exists n, u1.
          split; [reflexivity |].
          split; [exact Hmem |].
          right; split; [reflexivity | exact Hu1].
        + exfalso.
          destruct Hcase as [[q [HqS [v [Hm [HP Hr]]]]] | [u [Hu HuS]]].
          * pose proof (PkgSet.min_elt_spec3 H1) as Hemp.
            apply (Hemp q).
            apply mem_rhoProviders.
            split; [exact HqS |].
            exists v; repeat split; assumption.
          * pose proof (VSet.min_elt_spec3 H2) as Hemp.
            apply (Hemp u).
            rewrite VSet.filter_spec'.
            split; [exact Hu | apply PkgSet.mem_spec; exact HuS].
    Qed.

    Definition coreResolution (D : C.DepRel.t) (Pi : ProvidesRel.t)
        (S_Pi : PkgSet.t) (rho : RhoRel.t) : T.PkgSet.t :=
      T.PkgSet.union (embedSet S_Pi)
        (SOdp.filterMap (fun '(p, (n, vs)) =>
             if andb (PkgSet.mem p S_Pi) (hasProviderb Pi n vs)
             then Some (Name.Selector p n, chooseSelector S_Pi rho Pi p n vs)
             else None)
           D).

    Lemma mem_coreResolution : forall D Pi S_Pi rho (y : T.Pkg.t),
        T.PkgSet.In y (coreResolution D Pi S_Pi rho) <->
        (exists p, PkgSet.In p S_Pi /\ y = embedPkg p) \/
        (exists p n vs, C.DepRel.In (p, (n, vs)) D /\ PkgSet.In p S_Pi /\
           hasProviderb Pi n vs = true /\
           y = (Name.Selector p n, chooseSelector S_Pi rho Pi p n vs)).
    Proof.
      intros D Pi S_Pi rho y; unfold coreResolution, embedSet.
      rewrite T.PkgSet.union_spec, SOsp.mem_map, SOdp.mem_filterMap.
      apply or_iff_compat_l; split.
      - intros [[p [n vs]] [HeD He]]; cbn beta iota in He.
        destruct (andb (PkgSet.mem p S_Pi) (hasProviderb Pi n vs)) eqn:Hc;
          [| discriminate].
        apply andb_prop in Hc; destruct Hc as [HpS Hb].
        injection He as <-.
        exists p, n, vs.
        split; [exact HeD |].
        split; [apply PkgSet.mem_spec; exact HpS |].
        split; [exact Hb | reflexivity].
      - intros [p [n [vs [HD [HpS [Hb ->]]]]]].
        exists (p, (n, vs)); split; [exact HD | cbn beta iota].
        apply PkgSet.mem_spec in HpS; rewrite HpS, Hb; reflexivity.
    Qed.

    Lemma mem_coreResolution_embed : forall D Pi S_Pi rho (p : Pkg.t),
        PkgSet.In p S_Pi ->
        T.PkgSet.In (embedPkg p) (coreResolution D Pi S_Pi rho).
    Proof.
      intros D Pi S_Pi rho p Hp.
      apply mem_coreResolution; left.
      exists p; split; [exact Hp | reflexivity].
    Qed.

    Lemma mem_coreResolution_selector :
      forall D Pi S_Pi rho (p : Pkg.t) n vs,
        PkgSet.In p S_Pi -> C.DepRel.In (p, (n, vs)) D -> HasProvider Pi n vs ->
        T.PkgSet.In (Name.Selector p n, chooseSelector S_Pi rho Pi p n vs)
          (coreResolution D Pi S_Pi rho).
    Proof.
      intros D Pi S_Pi rho p n vs Hp Hd Hprov.
      apply mem_coreResolution; right.
      exists p, n, vs.
      split; [exact Hd |].
      split; [exact Hp |].
      split; [apply hasProviderb_iff; exact Hprov | reflexivity].
    Qed.

    Theorem virtual_completeness :
      forall (R : PkgSet.t) (D : C.DepRel.t) (Pi : ProvidesRel.t)
             (r : Pkg.t) (S_Pi : PkgSet.t) (rho : RhoRel.t),
        C.FunctionalInName D ->
        IsResolution R D Pi r S_Pi rho ->
        T.IsResolution (reduceReal R D Pi) (reduceDeps R D Pi)
          (embedPkg r) (coreResolution D Pi S_Pi rho).
    Proof.
      intros R D Pi r S_Pi rho Hfn [Hsub Hroot Hclo Huniq Hps].
      assert (Hsel : forall (p : Pkg.t) (n : N.t) vs,
          PkgSet.In p S_Pi -> C.DepRel.In (p, (n, vs)) D ->
          exists m w,
            chooseSelector S_Pi rho Pi p n vs = Version.Provider m w /\
            PkgSet.In (m, w) S_Pi /\
            ((exists v, MemTop v vs /\ ProvidesRel.In ((m, w), (n, v)) Pi) \/
             (m = n /\ VSet.In w vs))).
      { intros p n vs HpS HD.
        apply chooseSelector_spec.
        destruct (Hclo p HpS n vs HD)
          as [[v [Hv HvS]] | [q [[HqS [v [Hm [HP Hr]]]] _]]].
        - right; exists v; split; assumption.
        - left; exists q; split; [exact HqS |].
          exists v; repeat split; assumption. }
      constructor.
      - intros y Hy.
        apply mem_coreResolution in Hy.
        destruct Hy as [[[n v] [HpS ->]] | [p [n [vs [HD [HpS [Hb ->]]]]]]];
          apply mem_reduceReal.
        + left; exists n, v.
          split; [apply Hsub; exact HpS | split; reflexivity].
        + destruct (Hsel p n vs HpS HD) as [m [w [Heqv [HmwS Hcase]]]].
          rewrite Heqv.
          destruct Hcase as [[v [Hm HP]] | [-> Hw]].
          * right; left; exists p, n, vs, m, w, v.
            split; [exact HD | split; [exact HP |]].
            split; [exact Hm | split; reflexivity].
          * right; right; exists p, n, vs, w.
            split; [exact HD |].
            split; [apply hasProviderb_iff; exact Hb |].
            split; [exact Hw | split; [apply Hsub; exact HmwS |]].
            split; reflexivity.
      - apply mem_coreResolution_embed; exact Hroot.
      - intros y Hy m' ws Hd.
        apply mem_coreResolution in Hy.
        apply mem_reduceDeps in Hd.
        destruct Hy as [[p0 [HpS0 ->]] |
                        [p0 [n0 [vs0 [HD0 [HpS0 [Hb0 ->]]]]]]].
        + destruct Hd as [C1 | [C2 | [C3 | C4]]].
          * destruct C1 as [p [n [vs [HD [Hb [Hp [-> ->]]]]]]].
            apply embedPkg_injective in Hp as ->.
            destruct (Hclo p HpS0 n vs HD)
              as [[v [Hv HvS]] | [q [[HqS [v [Hm [HP Hr]]]] _]]].
            { exists (Version.Orig v); split.
              - unfold embedVS; apply SOvv.mem_map;
                  exists v; split; [exact Hv | reflexivity].
              - exact (mem_coreResolution_embed _ _ _ _ (n, v) HvS). }
            { exfalso; apply Hb; exists q, v; split; assumption. }
          * destruct C2 as [p [n [vs [HD [Hb [Hp [-> ->]]]]]]].
            apply embedPkg_injective in Hp as ->.
            exists (chooseSelector S_Pi rho Pi p n vs); split.
            { destruct (Hsel p n vs HpS0 HD) as [m [w [Heqv [HmwS Hcase]]]].
              rewrite Heqv.
              apply mem_selectorVersions.
              destruct Hcase as [[v [Hm HP]] | [-> Hw]].
              - left; exists m, w, v.
                split; [exact HP |]; split; [exact Hm | reflexivity].
              - right; exists w; split; [exact Hw |].
                split; [apply Hsub; exact HmwS | reflexivity]. }
            { exact (mem_coreResolution_selector _ _ _ _ _ _ _
                       HpS0 HD Hb). }
          * destruct C3 as [p [n [vs [m [u [v [HD [HP [Hm [Hp [-> ->]]]]]]]]]]].
            exfalso; destruct p0; discriminate Hp.
          * destruct C4 as [p [n [vs [u [HD [Hb [Hu [HuR [Hp [-> ->]]]]]]]]]].
            exfalso; destruct p0; discriminate Hp.
        + destruct Hd as [C1 | [C2 | [C3 | C4]]].
          * destruct C1 as [p [n [vs [HD [Hb [Hp [-> ->]]]]]]].
            exfalso; destruct p; discriminate Hp.
          * destruct C2 as [p [n [vs [HD [Hb [Hp [-> ->]]]]]]].
            exfalso; destruct p; discriminate Hp.
          * destruct C3 as [p [n [vs [m [u [v [HD [HP [Hm [Hp [-> ->]]]]]]]]]]].
            injection Hp as -> -> Hv.
            destruct (Hsel p n vs0 HpS0 HD0) as [m0 [w [Heqv [HmwS _]]]].
            rewrite Heqv in Hv; injection Hv as -> ->.
            exists (Version.Orig u); split.
            { apply T.VSet.singleton_spec; reflexivity. }
            { exact (mem_coreResolution_embed _ _ _ _ (m, u) HmwS). }
          * destruct C4 as [p [n [vs [u [HD [Hb [Hu [HuR [Hp [-> ->]]]]]]]]]].
            injection Hp as -> -> Hv.
            destruct (Hsel p n vs0 HpS0 HD0) as [m0 [w [Heqv [HmwS _]]]].
            rewrite Heqv in Hv; injection Hv as -> ->.
            exists (Version.Orig u); split.
            { apply T.VSet.singleton_spec; reflexivity. }
            { exact (mem_coreResolution_embed _ _ _ _ (n, u) HmwS). }
      - intros nm cv1 cv2 H1 H2.
        apply mem_coreResolution in H1.
        apply mem_coreResolution in H2.
        destruct H1 as [[[p1n p1v] [Hp1 He1]] |
                        [p1 [n1 [vs1 [HD1 [HpS1 [Hb1 He1]]]]]]];
          destruct H2 as [[[p2n p2v] [Hp2 He2]] |
                          [p2 [n2 [vs2 [HD2 [HpS2 [Hb2 He2]]]]]]].
        + unfold embedPkg in He1, He2.
          injection He1 as -> ->; injection He2 as Hn Hv.
          subst p2n cv2.
          assert (Hveq := Huniq p1n p1v p2v Hp1 Hp2).
          rewrite Hveq; reflexivity.
        + unfold embedPkg in He1.
          injection He1 as -> ->; injection He2 as Hn Hv.
          discriminate Hn.
        + unfold embedPkg in He2.
          injection He1 as -> ->; injection He2 as Hn Hv.
          discriminate Hn.
        + injection He1 as -> ->; injection He2 as Hp Hn Hv.
          subst p2 n2 cv2.
          assert (vs1 = vs2) as <- by (apply (Hfn p1 n1); assumption).
          reflexivity.
    Qed.
  End Reduction.

End Virtual.
