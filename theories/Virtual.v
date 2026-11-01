From Stdlib Require Import MSets.
From PackageCalculus Require Import Prelude Core.

Create HintDb cmp_virt.
Create Rewrite HintDb cmp_virt.

Module Virtual (N V : UsualOrderedType).
  Module Source := Core N V.
  Module Package := Source.Package.
  Module PackageSet := Source.PackageSet.
  Module VSet := Source.VSet.

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
  Module ProvidesElt := PairUOT Package Provided.
  Module ProvidesRel := FSetUOT ProvidesElt.

  Module Depender := PairUOT N Package.
  Module ProviderElt := PairUOT Package Depender.
  Module ProviderRel := FSetUOT ProviderElt.

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
      (R : PackageSet.t) (D : Source.DependencyRel.t) (Pi : ProvidesRel.t)
      (r : Package.t) (S : PackageSet.t) (rho : ProviderRel.t) : Prop :=
    { res_subset : PackageSet.Subset S R
    ; res_root_mem : PackageSet.In r S
    ; res_virtual_dep_closure :
        forall p, PackageSet.In p S ->
        forall (n : N.t) (vs : VSet.t),
          Source.DependencyRel.In (p, (n, vs)) D ->
          (exists v, VSet.In v vs /\ PackageSet.In (n, v) S) \/
          (exists m w, PackageSet.In (m, w) S /\
             exists v, MemTop v vs /\ ProvidesRel.In ((m, w), (n, v)) Pi /\
               ProviderRel.In ((m, w), (n, p)) rho)
    ; res_version_unique : Source.VersionUnique S
    ; res_provider_subset :
        forall (m : N.t) (w : V.t) (n : N.t) (p : Package.t),
          ProviderRel.In ((m, w), (n, p)) rho ->
          PackageSet.In (m, w) S /\ PackageSet.In p S
    ; res_rho_functional :
        forall (m : N.t) (w : V.t) (m' : N.t) (w' : V.t) (n : N.t)
               (p : Package.t),
          ProviderRel.In ((m, w), (n, p)) rho -> ProviderRel.In ((m', w'), (n, p)) rho ->
          (m, w) = (m', w') }.

  Definition ProviderDependency (D : Source.DependencyRel.t) (Pi : ProvidesRel.t)
      (rho : ProviderRel.t) : Prop :=
    forall m w n p, ProviderRel.In ((m, w), (n, p)) rho ->
      exists vs, Source.DependencyRel.In (p, (n, vs)) D /\
        exists v, MemTop v vs /\ ProvidesRel.In ((m, w), (n, v)) Pi.

  Module Reduction.

    Module PkgN := PairUOT Package N.
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
      | Selector (p : Package.t) (m : N.t).
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
    Module Reduced := Core NameOT VersionOT.

    Definition embedPkg (p : Package.t) : Reduced.Package.t :=
      let '(n, v) := p in (Name.Orig n, Version.Orig v).

    Module SOsp := SetOps Package Reduced.Package PackageSet Reduced.PackageSet.
    Definition embedSet (S : PackageSet.t) : Reduced.PackageSet.t :=
      SOsp.map embedPkg S.

    Module SOvv := SetOps V VersionOT VSet Reduced.VSet.
    Definition embedVS (vs : VSet.t) : Reduced.VSet.t :=
      SOvv.map Version.Orig vs.

    Definition Prov
        (Pi : ProvidesRel.t) (n : N.t) (vs : VSet.t) : Prop :=
      exists q v, ProvidesRel.In (q, (n, v)) Pi /\ MemTop v vs.

    Module NEqb := UOTEqb N.

    Definition provb
        (Pi : ProvidesRel.t) (n : N.t) (vs : VSet.t) : bool :=
      ProvidesRel.exists_ (fun '(_, (m, v)) =>
          andb (NEqb.eqb m n) (memTopb v vs))
        Pi.

    Lemma provb_iff : forall Pi n vs,
        provb Pi n vs = true <-> Prov Pi n vs.
    Proof.
      intros Pi n vs; unfold provb, Prov.
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

    Module SOpp := SetOps ProvidesElt Reduced.Package ProvidesRel Reduced.PackageSet.
    Definition realProviderBlock (Pi : ProvidesRel.t) (p : Package.t) (n : N.t)
        (vs : VSet.t) : Reduced.PackageSet.t :=
      SOpp.filterMap (fun '(q, (n', v)) =>
          if andb (NEqb.eqb n' n) (memTopb v vs)
          then Some (Name.Selector p n, Version.Provider (fst q) (snd q))
          else None)
        Pi.

    Lemma mem_realProviderBlock :
      forall Pi (p : Package.t) (n : N.t) (vs : VSet.t) q,
        Reduced.PackageSet.In q (realProviderBlock Pi p n vs) <->
        exists m w v, ProvidesRel.In ((m, w), (n, v)) Pi /\ MemTop v vs /\
          q = (Name.Selector p n, Version.Provider m w).
    Proof.
      intros Pi p n vs q; unfold realProviderBlock.
      rewrite SOpp.mem_filterMap.
      split.
      - intros [[[m w] [m0 v]] [Ht Hy]]; cbn [fst snd] in Hy.
        apply if_some_iff in Hy; destruct Hy as [Hc <-].
        rewrite Bool.andb_true_iff, NEqb.eqb_true_iff, memTopb_iff in Hc.
        destruct Hc as [-> Hm]; exists m, w, v; auto.
      - intros (m & w & v & Hin & Hm & ->).
        exists ((m, w), (n, v)); split; [exact Hin | cbn [fst snd]].
        apply if_some_iff; rewrite Bool.andb_true_iff, NEqb.eqb_true_iff,
          memTopb_iff; auto.
    Qed.

    Module SOvp := SetOps V Reduced.Package VSet Reduced.PackageSet.
    Definition realDirectBlock (R : PackageSet.t) (p : Package.t) (n : N.t)
        (vs : VSet.t) : Reduced.PackageSet.t :=
      SOvp.filterMap (fun u =>
          if PackageSet.mem (n, u) R
          then Some (Name.Selector p n, Version.Orig u)
          else None)
        vs.

    Lemma mem_realDirectBlock :
      forall R (p : Package.t) (n : N.t) (vs : VSet.t) q,
        Reduced.PackageSet.In q (realDirectBlock R p n vs) <->
        exists u, VSet.In u vs /\ PackageSet.In (n, u) R /\
          q = (Name.Selector p n, Version.Orig u).
    Proof.
      intros R p n vs q; unfold realDirectBlock.
      rewrite SOvp.mem_filterMap_if; cbn beta.
      setoid_rewrite PackageSet.mem_spec; reflexivity.
    Qed.

    Module SOdp := SetOps Source.DependencyElt Reduced.Package Source.DependencyRel Reduced.PackageSet.
    Definition reduceReal (R : PackageSet.t) (D : Source.DependencyRel.t) (Pi : ProvidesRel.t) :
        Reduced.PackageSet.t :=
      Reduced.PackageSet.union (embedSet R)
        (Reduced.PackageSet.union
           (SOdp.unionMap (fun '(p, (n, vs)) =>
                realProviderBlock Pi p n vs)
              D)
           (SOdp.unionMap (fun '(p, (n, vs)) =>
                if provb Pi n vs
                then realDirectBlock R p n vs
                else Reduced.PackageSet.empty)
              D)).

    Inductive RealSpec (R : PackageSet.t) (D : Source.DependencyRel.t) (Pi : ProvidesRel.t)
        : Reduced.Package.t -> Prop :=
    | RealOrig : forall n v,
        PackageSet.In (n, v) R -> RealSpec R D Pi (Name.Orig n, Version.Orig v)
    | RealProvider : forall p n vs m w v,
        Source.DependencyRel.In (p, (n, vs)) D -> ProvidesRel.In ((m, w), (n, v)) Pi ->
        MemTop v vs ->
        RealSpec R D Pi (Name.Selector p n, Version.Provider m w)
    | RealDirect : forall p n vs u,
        Source.DependencyRel.In (p, (n, vs)) D -> Prov Pi n vs -> VSet.In u vs ->
        PackageSet.In (n, u) R ->
        RealSpec R D Pi (Name.Selector p n, Version.Orig u).

    Lemma mem_reduceReal : forall R D Pi q,
        Reduced.PackageSet.In q (reduceReal R D Pi) <-> RealSpec R D Pi q.
    Proof.
      intros R D Pi q; unfold reduceReal, embedSet.
      rewrite !Reduced.PackageSet.union_spec, SOsp.mem_map, !SOdp.mem_unionMap.
      split.
      - intros [([n v] & HR & ->) | [([p [n vs]] & HD & He)
                                   | ([p [n vs]] & HD & He)]].
        + exact (RealOrig R D Pi n v HR).
        + cbn beta iota in He; apply mem_realProviderBlock in He.
          mem_destruct; eapply RealProvider; eassumption.
        + cbn beta iota in He; apply SOdp.in_if_empty in He.
          destruct He as [Hb He]; apply provb_iff in Hb.
          apply mem_realDirectBlock in He; mem_destruct.
          eapply RealDirect; eassumption.
      - destruct 1 as [n v HR | p n vs m u v HD HP Hm | p n vs u HD Hb Hu HR].
        + left; exists (n, v); auto.
        + right; left; exists (p, (n, vs)); split; [exact HD | cbn beta iota].
          apply mem_realProviderBlock; exists m, u, v; auto.
        + right; right; exists (p, (n, vs)); split; [exact HD | cbn beta iota].
          apply SOdp.in_if_empty; rewrite provb_iff.
          split; [exact Hb | apply mem_realDirectBlock; exists u; auto].
    Qed.

    Module SOpv := SetOps ProvidesElt VersionOT ProvidesRel Reduced.VSet.
    Definition selectorVersions (R : PackageSet.t) (Pi : ProvidesRel.t)
        (n : N.t) (vs : VSet.t) : Reduced.VSet.t :=
      Reduced.VSet.union
        (SOpv.filterMap (fun '(q, (n', v)) =>
             if andb (NEqb.eqb n' n) (memTopb v vs)
             then Some (Version.Provider (fst q) (snd q))
             else None)
           Pi)
        (SOvv.filterMap (fun u =>
             if PackageSet.mem (n, u) R
             then Some (Version.Orig u)
             else None)
           vs).

    Lemma mem_selectorVersions : forall R Pi n vs u',
        Reduced.VSet.In u' (selectorVersions R Pi n vs) <->
        (exists m w v, ProvidesRel.In ((m, w), (n, v)) Pi /\ MemTop v vs /\
           u' = Version.Provider m w) \/
        (exists u,
           VSet.In u vs /\ PackageSet.In (n, u) R /\ u' = Version.Orig u).
    Proof.
      intros R Pi n vs u'; unfold selectorVersions.
      rewrite Reduced.VSet.union_spec, SOpv.mem_filterMap, SOvv.mem_filterMap_if.
      cbn beta; setoid_rewrite PackageSet.mem_spec; apply or_iff_compat_r.
      split.
      - intros [[[m u] [n' v]] [Ht Hy]]; cbn [fst snd] in Hy.
        apply if_some_iff in Hy; destruct Hy as [Hc <-].
        rewrite Bool.andb_true_iff, NEqb.eqb_true_iff, memTopb_iff in Hc.
        destruct Hc as [-> Hm]; exists m, u, v; auto.
      - intros (m & u & v & Hin & Hm & ->).
        exists ((m, u), (n, v)); split; [exact Hin | cbn [fst snd]].
        apply if_some_iff; rewrite Bool.andb_true_iff, NEqb.eqb_true_iff,
          memTopb_iff; auto.
    Qed.

    Module SOpd := SetOps ProvidesElt Reduced.DependencyElt ProvidesRel Reduced.DependencyRel.
    Definition depsProviderBlock (Pi : ProvidesRel.t) (p : Package.t) (n : N.t)
        (vs : VSet.t) : Reduced.DependencyRel.t :=
      SOpd.filterMap (fun '(q, (n', v)) =>
          if andb (NEqb.eqb n' n) (memTopb v vs)
          then Some ((Name.Selector p n, Version.Provider (fst q) (snd q)),
                     (Name.Orig (fst q),
                      Reduced.VSet.singleton (Version.Orig (snd q))))
          else None)
        Pi.

    Lemma mem_depsProviderBlock :
      forall Pi (p : Package.t) (n : N.t) (vs : VSet.t) y,
        Reduced.DependencyRel.In y (depsProviderBlock Pi p n vs) <->
        exists m w v, ProvidesRel.In ((m, w), (n, v)) Pi /\ MemTop v vs /\
          y = ((Name.Selector p n, Version.Provider m w),
               (Name.Orig m, Reduced.VSet.singleton (Version.Orig w))).
    Proof.
      intros Pi p n vs y; unfold depsProviderBlock.
      rewrite SOpd.mem_filterMap.
      split.
      - intros [[[m w] [m0 v]] [Ht Hy]]; cbn [fst snd] in Hy.
        apply if_some_iff in Hy; destruct Hy as [Hc <-].
        rewrite Bool.andb_true_iff, NEqb.eqb_true_iff, memTopb_iff in Hc.
        destruct Hc as [-> Hm]; exists m, w, v; auto.
      - intros (m & w & v & Hin & Hm & ->).
        exists ((m, w), (n, v)); split; [exact Hin | cbn [fst snd]].
        apply if_some_iff; rewrite Bool.andb_true_iff, NEqb.eqb_true_iff,
          memTopb_iff; auto.
    Qed.

    Module SOvd := SetOps V Reduced.DependencyElt VSet Reduced.DependencyRel.
    Definition depsDirectBlock (R : PackageSet.t) (p : Package.t) (n : N.t)
        (vs : VSet.t) : Reduced.DependencyRel.t :=
      SOvd.filterMap (fun u =>
          if PackageSet.mem (n, u) R
          then Some ((Name.Selector p n, Version.Orig u),
                     (Name.Orig n, Reduced.VSet.singleton (Version.Orig u)))
          else None)
        vs.

    Lemma mem_depsDirectBlock :
      forall R (p : Package.t) (n : N.t) (vs : VSet.t) y,
        Reduced.DependencyRel.In y (depsDirectBlock R p n vs) <->
        exists u, VSet.In u vs /\ PackageSet.In (n, u) R /\
          y = ((Name.Selector p n, Version.Orig u),
               (Name.Orig n, Reduced.VSet.singleton (Version.Orig u))).
    Proof.
      intros R p n vs y; unfold depsDirectBlock.
      rewrite SOvd.mem_filterMap_if; cbn beta.
      setoid_rewrite PackageSet.mem_spec; reflexivity.
    Qed.

    Module SOdd := SetOps Source.DependencyElt Reduced.DependencyElt Source.DependencyRel Reduced.DependencyRel.
    Definition reduceDeps (R : PackageSet.t) (D : Source.DependencyRel.t) (Pi : ProvidesRel.t) :
        Reduced.DependencyRel.t :=
      Reduced.DependencyRel.union
        (SOdd.filterMap (fun '(p, (n, vs)) =>
             if provb Pi n vs then None
             else Some (embedPkg p, (Name.Orig n, embedVS vs)))
           D)
        (Reduced.DependencyRel.union
           (SOdd.filterMap (fun '(p, (n, vs)) =>
                if provb Pi n vs
                then Some (embedPkg p,
                           (Name.Selector p n, selectorVersions R Pi n vs))
                else None)
              D)
           (Reduced.DependencyRel.union
              (SOdd.unionMap (fun '(p, (n, vs)) =>
                   depsProviderBlock Pi p n vs)
                 D)
              (SOdd.unionMap (fun '(p, (n, vs)) =>
                   if provb Pi n vs
                   then depsDirectBlock R p n vs
                   else Reduced.DependencyRel.empty)
                 D))).

    (* Embedded packages are written as pairs of constructors so that
       inversion can tell the four kinds of edge apart by their source. *)
    Inductive DepsSpec (R : PackageSet.t) (D : Source.DependencyRel.t) (Pi : ProvidesRel.t)
        : Reduced.DependencyElt.t -> Prop :=
    | DepsOrig : forall pn pv n vs,
        Source.DependencyRel.In ((pn, pv), (n, vs)) D -> ~ Prov Pi n vs ->
        DepsSpec R D Pi
          ((Name.Orig pn, Version.Orig pv), (Name.Orig n, embedVS vs))
    | DepsSelector : forall pn pv n vs,
        Source.DependencyRel.In ((pn, pv), (n, vs)) D -> Prov Pi n vs ->
        DepsSpec R D Pi
          ((Name.Orig pn, Version.Orig pv),
           (Name.Selector (pn, pv) n, selectorVersions R Pi n vs))
    | DepsProvider : forall p n vs m w v,
        Source.DependencyRel.In (p, (n, vs)) D -> ProvidesRel.In ((m, w), (n, v)) Pi ->
        MemTop v vs ->
        DepsSpec R D Pi
          ((Name.Selector p n, Version.Provider m w),
           (Name.Orig m, Reduced.VSet.singleton (Version.Orig w)))
    | DepsDirect : forall p n vs u,
        Source.DependencyRel.In (p, (n, vs)) D -> Prov Pi n vs -> VSet.In u vs ->
        PackageSet.In (n, u) R ->
        DepsSpec R D Pi
          ((Name.Selector p n, Version.Orig u),
           (Name.Orig n, Reduced.VSet.singleton (Version.Orig u))).

    Lemma mem_reduceDeps : forall R D Pi y,
        Reduced.DependencyRel.In y (reduceDeps R D Pi) <-> DepsSpec R D Pi y.
    Proof.
      intros R D Pi y; unfold reduceDeps.
      rewrite !Reduced.DependencyRel.union_spec, !SOdd.mem_filterMap, !SOdd.mem_unionMap.
      split.
      - intros [([[pn pv] [n vs]] & HD & He)
               | [([[pn pv] [n vs]] & HD & He)
                 | [([p [n vs]] & HD & He) | ([p [n vs]] & HD & He)]]];
          cbn beta iota in He.
        + destruct (provb Pi n vs) eqn:Hb; [discriminate |].
          injection He as <-; apply DepsOrig; [exact HD |].
          rewrite <- provb_iff, Hb; discriminate.
        + destruct (provb Pi n vs) eqn:Hb; [| discriminate].
          injection He as <-; apply provb_iff in Hb.
          apply DepsSelector; assumption.
        + apply mem_depsProviderBlock in He; mem_destruct.
          eapply DepsProvider; eassumption.
        + apply SOdd.in_if_empty in He; destruct He as [Hb He].
          apply provb_iff in Hb; apply mem_depsDirectBlock in He.
          mem_destruct; eapply DepsDirect; eassumption.
      - destruct 1 as [pn pv n vs HD Hb | pn pv n vs HD Hb
                      | p n vs m u v HD HP Hm | p n vs u HD Hb Hu HR].
        + left; exists ((pn, pv), (n, vs)); split; [exact HD | cbn beta iota].
          destruct (provb Pi n vs) eqn:Hb'; [| reflexivity].
          apply provb_iff in Hb'; contradiction.
        + right; left; exists ((pn, pv), (n, vs)).
          split; [exact HD | cbn beta iota].
          apply provb_iff in Hb; rewrite Hb; reflexivity.
        + right; right; left; exists (p, (n, vs)).
          split; [exact HD | cbn beta iota].
          apply mem_depsProviderBlock; exists m, u, v; auto.
        + right; right; right; exists (p, (n, vs)).
          split; [exact HD | cbn beta iota].
          apply SOdd.in_if_empty; rewrite provb_iff.
          split; [exact Hb | apply mem_depsDirectBlock; exists u; auto].
    Qed.

    Definition tryInvPkg (p' : Reduced.Package.t) : option Package.t :=
      match p' with
      | (Name.Orig n, Version.Orig v) => Some (n, v)
      | _ => None
      end.

    Lemma tryInvPkg_embed : forall p, tryInvPkg (embedPkg p) = Some p.
    Proof. intros [n v]; reflexivity. Qed.

    Lemma tryInvPkg_some : forall (p' : Reduced.Package.t) (p : Package.t),
        tryInvPkg p' = Some p -> embedPkg p = p'.
    Proof.
      intros [n' v'] p H; destruct n', v'; cbn [tryInvPkg] in H;
        try discriminate.
      injection H as <-; reflexivity.
    Qed.

    Module SOtp := SetOps Reduced.Package Package Reduced.PackageSet PackageSet.
    Lemma embedPkg_injective : forall p q : Package.t,
        embedPkg p = embedPkg q -> p = q.
    Proof. exact (SOtp.emb_injective tryInvPkg embedPkg tryInvPkg_embed). Qed.

    Definition virtualResolution (S : Reduced.PackageSet.t) : PackageSet.t :=
      SOtp.filterMap tryInvPkg S.

    Lemma mem_virtualResolution : forall (S : Reduced.PackageSet.t) (p : Package.t),
        PackageSet.In p (virtualResolution S) <-> Reduced.PackageSet.In (embedPkg p) S.
    Proof.
      unfold virtualResolution.
      exact (SOtp.mem_filterMap_inv tryInvPkg embedPkg tryInvPkg_embed
               tryInvPkg_some).
    Qed.

    Lemma embedPkg_mem_real : forall (p : Package.t) R D Pi,
        Reduced.PackageSet.In (embedPkg p) (reduceReal R D Pi) -> PackageSet.In p R.
    Proof.
      intros [n v] R D Pi H; apply mem_reduceReal in H.
      cbn [embedPkg] in H; inversion H; assumption.
    Qed.

    Module SOpr := SetOps ProvidesElt ProviderElt ProvidesRel ProviderRel.
    Definition rhoBlock (Pi : ProvidesRel.t) (S : Reduced.PackageSet.t) (p : Package.t)
        (n : N.t) (vs : VSet.t) : ProviderRel.t :=
      SOpr.filterMap (fun '(q, (n', v)) =>
          if andb (NEqb.eqb n' n)
               (andb (memTopb v vs)
                  (andb (Reduced.PackageSet.mem (embedPkg p) S)
                     (Reduced.PackageSet.mem
                        (Name.Selector p n,
                         Version.Provider (fst q) (snd q)) S)))
          then Some (q, (n, p))
          else None)
        Pi.

    Lemma mem_rhoBlock :
      forall Pi (S : Reduced.PackageSet.t) (p : Package.t) (n : N.t) (vs : VSet.t)
             (m : N.t) (w : V.t) (m' : N.t) (p' : Package.t),
        ProviderRel.In ((m, w), (m', p')) (rhoBlock Pi S p n vs) <->
        (exists v, ProvidesRel.In ((m, w), (n, v)) Pi /\ MemTop v vs /\
           Reduced.PackageSet.In (embedPkg p) S /\
           Reduced.PackageSet.In (Name.Selector p n, Version.Provider m w) S /\
           m' = n /\ p' = p).
    Proof.
      intros Pi S p n vs m w m' p'; unfold rhoBlock.
      rewrite SOpr.mem_filterMap.
      split.
      - intros [[[m0 u0] [m1 v]] [Ht Hy]]; cbn [fst snd] in Hy.
        apply if_some_iff in Hy; destruct Hy as [Hc Hy].
        injection Hy as <- <- <- <-.
        rewrite !Bool.andb_true_iff, NEqb.eqb_true_iff, memTopb_iff,
          !Reduced.PackageSet.mem_spec in Hc.
        destruct Hc as (-> & Hm & HpS & HselS); exists v; auto 8.
      - intros (v & Hin & Hm & HpS & HselS & -> & ->).
        exists ((m, w), (n, v)); split; [exact Hin | cbn [fst snd]].
        apply if_some_iff; rewrite !Bool.andb_true_iff, NEqb.eqb_true_iff,
          memTopb_iff, !Reduced.PackageSet.mem_spec; auto 8.
    Qed.

    Module SOdr := SetOps Source.DependencyElt ProviderElt Source.DependencyRel ProviderRel.
    Definition providers (D : Source.DependencyRel.t) (Pi : ProvidesRel.t)
        (S : Reduced.PackageSet.t) : ProviderRel.t :=
      SOdr.unionMap (fun '(p, (n, vs)) => rhoBlock Pi S p n vs) D.

    Lemma mem_providers :
      forall D Pi S (m : N.t) (w : V.t) (p : Package.t) (n : N.t),
        ProviderRel.In ((m, w), (n, p)) (providers D Pi S) <->
        exists vs, Source.DependencyRel.In (p, (n, vs)) D /\
          exists v, MemTop v vs /\ ProvidesRel.In ((m, w), (n, v)) Pi /\
            Reduced.PackageSet.In (embedPkg p) S /\
            Reduced.PackageSet.In (Name.Selector p n, Version.Provider m w) S.
    Proof.
      intros D Pi S m w p n; unfold providers; rewrite SOdr.mem_unionMap.
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
      forall (R : PackageSet.t) (D : Source.DependencyRel.t) (Pi : ProvidesRel.t)
             (r : Package.t) (S : Reduced.PackageSet.t),
        Reduced.IsResolution (reduceReal R D Pi) (reduceDeps R D Pi)
          (embedPkg r) S ->
        IsResolution R D Pi r (virtualResolution S) (providers D Pi S).
    Proof.
      intros R D Pi r S [Hsub Hroot Hdep Huniq].
      assert (Hsel_emb : forall (m0 : N.t) (u0 : V.t) (p0 : Package.t)
                                (n0 : N.t) v0 vs0,
          Source.DependencyRel.In (p0, (n0, vs0)) D ->
          ProvidesRel.In ((m0, u0), (n0, v0)) Pi -> MemTop v0 vs0 ->
          Reduced.PackageSet.In (Name.Selector p0 n0, Version.Provider m0 u0) S ->
          Reduced.PackageSet.In (embedPkg (m0, u0)) S).
      { intros m0 u0 p0 n0 v0 vs0 HD HP HM HselS.
        assert (Hd3 : Reduced.DependencyRel.In
            ((Name.Selector p0 n0, Version.Provider m0 u0),
             (Name.Orig m0, Reduced.VSet.singleton (Version.Orig u0)))
            (reduceDeps R D Pi))
          by (apply mem_reduceDeps; eapply DepsProvider; eassumption).
        destruct (Hdep _ HselS _ _ Hd3) as [w [Hw HwS]].
        apply Reduced.VSet.singleton_spec in Hw; rewrite Hw in HwS.
        exact HwS. }
      constructor.
      - intros p Hp; apply mem_virtualResolution in Hp.
        exact (embedPkg_mem_real _ _ _ _ (Hsub _ Hp)).
      - apply mem_virtualResolution; exact Hroot.
      - intros [pn pv] Hp n vs HD.
        apply mem_virtualResolution in Hp.
        destruct (provb Pi n vs) eqn:Hb.
        + apply provb_iff in Hb.
          assert (Hd2 : Reduced.DependencyRel.In
              (embedPkg (pn, pv),
               (Name.Selector (pn, pv) n, selectorVersions R Pi n vs))
              (reduceDeps R D Pi))
            by (apply mem_reduceDeps; apply DepsSelector; assumption).
          destruct (Hdep _ Hp _ _ Hd2) as [sv [Hsv HsvS]].
          apply mem_selectorVersions in Hsv.
          destruct Hsv as [[m [u [v [HP [Hm Hsv]]]]] | [u [Hu [HuR Hsv]]]].
          * subst sv; right.
            assert (HqS := Hsel_emb m u (pn, pv) n v vs HD HP Hm HsvS).
            exists m, u.
            split; [apply mem_virtualResolution; exact HqS |].
            exists v; split; [exact Hm |]; split; [exact HP |].
            apply mem_providers.
            exists vs; split; [exact HD |].
            exists v; repeat split; assumption.
          * subst sv.
            assert (Hd4 : Reduced.DependencyRel.In
                ((Name.Selector (pn, pv) n, Version.Orig u),
                 (Name.Orig n, Reduced.VSet.singleton (Version.Orig u)))
                (reduceDeps R D Pi))
              by (apply mem_reduceDeps; eapply DepsDirect; eassumption).
            destruct (Hdep _ HsvS _ _ Hd4) as [w [Hw HwS]].
            apply Reduced.VSet.singleton_spec in Hw; rewrite Hw in HwS.
            left; exists u; split;
              [exact Hu | apply mem_virtualResolution; exact HwS].
        + assert (Hd1 : Reduced.DependencyRel.In
              (embedPkg (pn, pv), (Name.Orig n, embedVS vs))
              (reduceDeps R D Pi)).
          { apply mem_reduceDeps; apply DepsOrig; [exact HD |].
            rewrite <- provb_iff, Hb; discriminate. }
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
      - intros m u n p Hrho.
        apply mem_providers in Hrho.
        destruct Hrho as [vs [HD [v [Hm [HP [HpS HselS]]]]]].
        split; apply mem_virtualResolution.
        + exact (Hsel_emb m u p n v vs HD HP Hm HselS).
        + exact HpS.
      - intros m u m' u' n p H1 H2; apply mem_providers in H1, H2.
        destruct H1 as (vs1 & _ & v1 & _ & _ & _ & Hsel1).
        destruct H2 as (vs2 & _ & v2 & _ & _ & _ & Hsel2).
        assert (E := Huniq _ _ _ Hsel1 Hsel2); injection E as -> ->.
        reflexivity.
    Qed.

    Module PkgEqb := UOTEqb Package.
    Module SOkp := SetOps Package ProvidesElt PackageSet ProvidesRel.
    Definition rhoProviders (S_Pi : PackageSet.t) (rho : ProviderRel.t)
        (Pi : ProvidesRel.t) (p : Package.t) (n : N.t) (vs : VSet.t) : PackageSet.t :=
      SOkp.filterExists
        (fun q '(q', (m, v)) =>
            andb (PkgEqb.eqb q' q)
              (andb (NEqb.eqb m n)
                 (andb (memTopb v vs) (ProviderRel.mem (q, (n, p)) rho))))
        Pi S_Pi.

    Lemma mem_rhoProviders :
      forall S_Pi rho Pi (p : Package.t) (n : N.t) vs (q : Package.t),
        PackageSet.In q (rhoProviders S_Pi rho Pi p n vs) <->
        PackageSet.In q S_Pi /\
        exists v, MemTop v vs /\ ProvidesRel.In (q, (n, v)) Pi /\
          ProviderRel.In (q, (n, p)) rho.
    Proof.
      intros S_Pi rho Pi p n vs q; unfold rhoProviders.
      rewrite SOkp.mem_filterExists; apply and_iff_compat_l.
      split.
      - intros [[q' [m v]] [Ht Hb]]; cbn beta iota in Hb.
        rewrite !Bool.andb_true_iff, PkgEqb.eqb_true_iff, NEqb.eqb_true_iff,
          memTopb_iff, ProviderRel.mem_spec in Hb.
        destruct Hb as (-> & -> & Hm & Hr); exists v; auto.
      - intros (v & Hm & HP & Hr).
        exists (q, (n, v)); split; [exact HP | cbn beta iota].
        rewrite !Bool.andb_true_iff, PkgEqb.eqb_true_iff, NEqb.eqb_true_iff,
          memTopb_iff, ProviderRel.mem_spec; auto.
    Qed.

    (* Any element of the first nonempty candidate class works; min_elt makes
       the choice deterministic and computable. *)
    Definition chooseSelector (S_Pi : PackageSet.t) (rho : ProviderRel.t)
        (Pi : ProvidesRel.t) (p : Package.t) (n : N.t) (vs : VSet.t) :
        Version.t :=
      match PackageSet.min_elt (rhoProviders S_Pi rho Pi p n vs) with
      | Some q => Version.Provider (fst q) (snd q)
      | None =>
          let cand2 := VSet.filter (fun u => PackageSet.mem (n, u) S_Pi) vs in
          match VSet.min_elt cand2 with
          | Some u => Version.Orig u
          | None => Version.Orig (snd p) (* unreachable under
                                            chooseSelector_spec's premise *)
          end
      end.

    Lemma chooseSelector_spec :
      forall S_Pi rho Pi (p : Package.t) (n : N.t) vs,
        ((exists m w, PackageSet.In (m, w) S_Pi /\ exists v, MemTop v vs /\
            ProvidesRel.In ((m, w), (n, v)) Pi /\
            ProviderRel.In ((m, w), (n, p)) rho) \/
         (exists u, VSet.In u vs /\ PackageSet.In (n, u) S_Pi)) ->
        (exists m w v,
           chooseSelector S_Pi rho Pi p n vs = Version.Provider m w /\
           PackageSet.In (m, w) S_Pi /\ MemTop v vs /\
           ProvidesRel.In ((m, w), (n, v)) Pi) \/
        (exists u, chooseSelector S_Pi rho Pi p n vs = Version.Orig u /\
           VSet.In u vs /\ PackageSet.In (n, u) S_Pi).
    Proof.
      intros S_Pi rho Pi p n vs Hcase; unfold chooseSelector.
      match goal with
      | |- context [PackageSet.min_elt ?c] =>
          destruct (PackageSet.min_elt c) as [q1 |] eqn:H1
      end.
      - apply PackageSet.min_elt_spec1 in H1.
        apply mem_rhoProviders in H1.
        destruct H1 as [Hq1S [v [Hm [HP Hr]]]].
        left; exists (fst q1), (snd q1), v.
        rewrite <- surjective_pairing; auto.
      - match goal with
        | |- context [VSet.min_elt ?c] =>
            destruct (VSet.min_elt c) as [u1 |] eqn:H2
        end.
        + apply VSet.min_elt_spec1 in H2.
          rewrite VSet.filter_spec' in H2.
          destruct H2 as [Hu1 Hmem]; apply PackageSet.mem_spec in Hmem.
          right; exists u1; auto.
        + exfalso.
          destruct Hcase as [[m [w [HqS [v [Hm [HP Hr]]]]]] | [u [Hu HuS]]].
          * pose proof (PackageSet.min_elt_spec3 H1) as Hemp.
            apply (Hemp (m, w)).
            apply mem_rhoProviders.
            split; [exact HqS |].
            exists v; repeat split; assumption.
          * pose proof (VSet.min_elt_spec3 H2) as Hemp.
            apply (Hemp u).
            rewrite VSet.filter_spec'.
            split; [exact Hu | apply PackageSet.mem_spec; exact HuS].
    Qed.

    Definition coreResolution (D : Source.DependencyRel.t) (Pi : ProvidesRel.t)
        (S_Pi : PackageSet.t) (rho : ProviderRel.t) : Reduced.PackageSet.t :=
      Reduced.PackageSet.union (embedSet S_Pi)
        (SOdp.filterMap (fun '(p, (n, vs)) =>
             if andb (PackageSet.mem p S_Pi) (provb Pi n vs)
             then Some (Name.Selector p n, chooseSelector S_Pi rho Pi p n vs)
             else None)
           D).

    Inductive CoreSpec (D : Source.DependencyRel.t) (Pi : ProvidesRel.t)
        (S_Pi : PackageSet.t) (rho : ProviderRel.t) : Reduced.Package.t -> Prop :=
    | CoreOrig : forall n v,
        PackageSet.In (n, v) S_Pi ->
        CoreSpec D Pi S_Pi rho (Name.Orig n, Version.Orig v)
    | CoreSelector : forall p n vs,
        Source.DependencyRel.In (p, (n, vs)) D -> PackageSet.In p S_Pi ->
        Prov Pi n vs ->
        CoreSpec D Pi S_Pi rho
          (Name.Selector p n, chooseSelector S_Pi rho Pi p n vs).

    Lemma mem_coreResolution : forall D Pi S_Pi rho (q : Reduced.Package.t),
        Reduced.PackageSet.In q (coreResolution D Pi S_Pi rho) <->
        CoreSpec D Pi S_Pi rho q.
    Proof.
      intros D Pi S_Pi rho q; unfold coreResolution, embedSet.
      rewrite Reduced.PackageSet.union_spec, SOsp.mem_map, SOdp.mem_filterMap.
      split.
      - intros [([n v] & HS & ->) | ([p [n vs]] & HD & He)].
        + exact (CoreOrig D Pi S_Pi rho n v HS).
        + cbn beta iota in He; apply if_some_iff in He.
          destruct He as [Hc <-].
          rewrite Bool.andb_true_iff, PackageSet.mem_spec, provb_iff in Hc.
          destruct Hc; constructor; assumption.
      - destruct 1 as [n v HS | p n vs HD HS Hb].
        + left; exists (n, v); auto.
        + right; exists (p, (n, vs)); split; [exact HD | cbn beta iota].
          apply if_some_iff; rewrite Bool.andb_true_iff, PackageSet.mem_spec,
            provb_iff; auto.
    Qed.

    Lemma mem_coreResolution_embed : forall D Pi S_Pi rho (p : Package.t),
        PackageSet.In p S_Pi ->
        Reduced.PackageSet.In (embedPkg p) (coreResolution D Pi S_Pi rho).
    Proof.
      intros D Pi S_Pi rho [n v] Hp.
      apply mem_coreResolution; exact (CoreOrig D Pi S_Pi rho n v Hp).
    Qed.

    Lemma mem_coreResolution_selector :
      forall D Pi S_Pi rho (p : Package.t) n vs,
        PackageSet.In p S_Pi -> Source.DependencyRel.In (p, (n, vs)) D -> Prov Pi n vs ->
        Reduced.PackageSet.In (Name.Selector p n, chooseSelector S_Pi rho Pi p n vs)
          (coreResolution D Pi S_Pi rho).
    Proof. intros; apply mem_coreResolution; constructor; assumption. Qed.

    Theorem virtual_completeness :
      forall (R : PackageSet.t) (D : Source.DependencyRel.t) (Pi : ProvidesRel.t)
             (r : Package.t) (S_Pi : PackageSet.t) (rho : ProviderRel.t),
        Source.FunctionalInName D ->
        IsResolution R D Pi r S_Pi rho ->
        Reduced.IsResolution (reduceReal R D Pi) (reduceDeps R D Pi)
          (embedPkg r) (coreResolution D Pi S_Pi rho).
    Proof.
      intros R D Pi r S_Pi rho Hfn [Hsub Hroot Hclo Huniq Hps _].
      assert (Hsel : forall (p : Package.t) (n : N.t) vs,
          PackageSet.In p S_Pi -> Source.DependencyRel.In (p, (n, vs)) D ->
          (exists m w v,
             chooseSelector S_Pi rho Pi p n vs = Version.Provider m w /\
             PackageSet.In (m, w) S_Pi /\ MemTop v vs /\
             ProvidesRel.In ((m, w), (n, v)) Pi) \/
          (exists u, chooseSelector S_Pi rho Pi p n vs = Version.Orig u /\
             VSet.In u vs /\ PackageSet.In (n, u) S_Pi)).
      { intros p n vs HpS HD.
        apply chooseSelector_spec.
        destruct (Hclo p HpS n vs HD)
          as [[v [Hv HvS]] | [m [w [HqS [v [Hm [HP Hr]]]]]]].
        - right; exists v; split; assumption.
        - left; exists m, w; split; [exact HqS |].
          exists v; repeat split; assumption. }
      constructor.
      - intros p' Hp'; apply mem_coreResolution in Hp'; apply mem_reduceReal.
        destruct Hp' as [n v HpS | p n vs HD HpS Hb].
        + constructor; apply Hsub; exact HpS.
        + destruct (Hsel p n vs HpS HD)
            as [(m & w & v & -> & HmwS & Hm & HP) | (u & -> & Hu & HuS)].
          * eapply RealProvider; eassumption.
          * eapply RealDirect;
              [exact HD | exact Hb | exact Hu | apply Hsub; exact HuS].
      - apply mem_coreResolution_embed; exact Hroot.
      - intros p' Hp'; apply mem_coreResolution in Hp'.
        destruct Hp' as [pn pv HpS | p0 n0 vs0 HD0 HpS0 Hb0];
          intros m' ws Hd; apply mem_reduceDeps in Hd.
        + inversion Hd as [pn1 pv1 n vs HD Hb | pn1 pv1 n vs HD Hb | |];
            subst.
          * destruct (Hclo _ HpS _ _ HD)
              as [[v [Hv HvS]] | [m [w [HqS [v [Hm [HP Hr]]]]]]];
              [| exfalso; apply Hb; exists (m, w), v; split; assumption].
            exists (Version.Orig v); split.
            -- unfold embedVS; apply SOvv.mem_map; exists v; auto.
            -- exact (mem_coreResolution_embed _ _ _ _ _ HvS).
          * eexists; split;
              [| exact (mem_coreResolution_selector _ _ _ _ _ _ _ HpS HD Hb)].
            destruct (Hsel _ _ _ HpS HD)
              as [(m & w & v & -> & HmwS & Hm & HP) | (u & -> & Hu & HuS)];
              apply mem_selectorVersions;
              [left; exists m, w, v; auto | right; exists u].
            split; [exact Hu | split; [apply Hsub; exact HuS | reflexivity]].
        + destruct (Hsel p0 n0 vs0 HpS0 HD0)
            as [(m0 & w & v & Heqv & HmwS & _) | (u & Heqv & _ & HuS)];
            rewrite Heqv in Hd; inversion Hd; subst;
            (eexists; split; [apply SOvv.singleton_in; reflexivity |]).
          * exact (mem_coreResolution_embed _ _ _ _ _ HmwS).
          * exact (mem_coreResolution_embed _ _ _ _ _ HuS).
      - intros n cv1 cv2 H1 H2.
        apply mem_coreResolution in H1; apply mem_coreResolution in H2.
        inversion H1 as [n1 v1 HS1 | p1 n1 vs1 HD1 _ _]; subst;
          inversion H2 as [n2 v2 HS2 | p2 n2 vs2 HD2 _ _]; subst.
        + f_equal; exact (Huniq _ _ _ HS1 HS2).
        + rewrite (Hfn _ _ _ _ HD1 HD2); reflexivity.
    Qed.

    Lemma virtualResolution_coreResolution : forall D Pi S_Pi rho,
        virtualResolution (coreResolution D Pi S_Pi rho) = S_Pi.
    Proof.
      intros D Pi S_Pi rho; apply PackageSet.ext; intros [n v].
      rewrite mem_virtualResolution, mem_coreResolution; cbn [embedPkg].
      split; [intro H; inversion H; assumption | apply CoreOrig].
    Qed.

    Lemma providers_coreResolution_iff : forall R D Pi r S_Pi rho,
        IsResolution R D Pi r S_Pi rho ->
        forall m w n p,
          ProviderRel.In ((m, w), (n, p))
            (providers D Pi (coreResolution D Pi S_Pi rho))
          <-> ProviderRel.In ((m, w), (n, p)) rho /\
              exists vs, Source.DependencyRel.In (p, (n, vs)) D /\
                exists v, MemTop v vs /\ ProvidesRel.In ((m, w), (n, v)) Pi.
    Proof.
      intros R D Pi r S_Pi rho [_ _ _ _ Hps Hfun] m w n p.
      rewrite mem_providers; split.
      - intros (vs & HD & v & Hm & HP & _ & Hsel).
        split; [| exists vs; split; [exact HD | exists v; split; assumption]].
        apply mem_coreResolution in Hsel.
        inversion Hsel as [| p' n' vs' _ _ _]; subst.
        match goal with E : chooseSelector _ _ _ _ _ _ = _ |- _ =>
          rename E into Ec end.
        unfold chooseSelector in Ec.
        match type of Ec with context [PackageSet.min_elt ?c] =>
          destruct (PackageSet.min_elt c) as [q |] eqn:H1 end.
        + injection Ec as <- <-; rewrite <- surjective_pairing.
          apply PackageSet.min_elt_spec1, mem_rhoProviders in H1.
          destruct H1 as (_ & _ & _ & _ & Hq); exact Hq.
        + match type of Ec with context [VSet.min_elt ?c] =>
            destruct (VSet.min_elt c) end; discriminate.
      - intros [Hr (vs & HD & v & Hm & HP)].
        destruct (Hps _ _ _ _ Hr) as [HqS HpS].
        exists vs; split; [exact HD |]; exists v; split; [exact Hm |].
        split; [exact HP |].
        split; [exact (mem_coreResolution_embed _ _ _ _ _ HpS) |].
        replace (Version.Provider m w)
          with (chooseSelector S_Pi rho Pi p n vs).
        { apply mem_coreResolution_selector; [exact HpS | exact HD |].
          exists (m, w), v; split; assumption. }
        unfold chooseSelector.
        destruct (PackageSet.min_elt (rhoProviders S_Pi rho Pi p n vs))
          as [q |] eqn:H1.
        + destruct q as [m1 w1].
          apply PackageSet.min_elt_spec1, mem_rhoProviders in H1.
          destruct H1 as (_ & _ & _ & _ & Hq).
          rewrite (Hfun _ _ _ _ _ _ Hq Hr); reflexivity.
        + exfalso; apply PackageSet.min_elt_spec3 in H1.
          apply (H1 (m, w)), mem_rhoProviders.
          split; [exact HqS | exists v; auto].
    Qed.

    Theorem virtual_retraction : forall R D Pi r S_Pi rho,
        IsResolution R D Pi r S_Pi rho -> ProviderDependency D Pi rho ->
        virtualResolution (coreResolution D Pi S_Pi rho) = S_Pi /\
        providers D Pi (coreResolution D Pi S_Pi rho) = rho.
    Proof.
      intros R D Pi r S_Pi rho Hres Hdep.
      split; [apply virtualResolution_coreResolution |].
      apply ProviderRel.ext; intros [[m w] [n p]].
      rewrite (providers_coreResolution_iff R D Pi r S_Pi rho Hres).
      split;
        [intros [H _]; exact H | intro H; exact (conj H (Hdep _ _ _ _ H))].
    Qed.

    Module Lookup.
      Module ProvidesRelFibred := FibredLabelledRel Package N VTOT ProvidesElt ProvidesRel.
      Lemma prov_nodeFibre : forall Pi n vs,
          Prov (ProvidesRelFibred.nodeFibre Pi n) n vs <-> Prov Pi n vs.
      Proof.
        intros Pi n vs; unfold Prov; split.
        - intros [q [v [Hin Hm]]]; exists q, v;
            split; [exact (ProvidesRelFibred.nodeFibre_subset _ _ _ Hin) | exact Hm].
        - intros [q [v [Hin Hm]]]; exists q, v; split; [| exact Hm].
          apply ProvidesRelFibred.mem_nodeFibre; split; [exact Hin | reflexivity].
      Qed.

      Module DependencyRelFibred :=
        FibredLabelledRel Package N Source.VSet.AsUOT Source.DependencyElt Source.DependencyRel.
      Module DependencyRelKeys := RelKeys N Source.DependencyElt Source.DependencyRel.
      Definition hasDepNameb (Dp : Source.DependencyRel.t) (n : N.t) : bool :=
        DependencyRelKeys.hasKey DependencyRelFibred.node Dp n.

      Lemma hasDepNameb_iff : forall Dp n,
          hasDepNameb Dp n = true <-> exists q vs, Source.DependencyRel.In (q, (n, vs)) Dp.
      Proof.
        intros Dp n; unfold hasDepNameb; rewrite DependencyRelKeys.hasKey_iff; split.
        - intros [[q [m vs]] [He Hm]]; cbn [DependencyRelFibred.node] in Hm;
            subst m; exists q, vs; exact He.
        - intros [q [vs He]]; exists (q, (n, vs));
            split; [exact He | reflexivity].
      Qed.

      Module PackageSetPreimage := Preimage Package PackageSet.
      Definition realPreimage (R : PackageSet.t) (Dp : Source.DependencyRel.t) : PackageSet.t :=
        PackageSetPreimage.preimage fst (hasDepNameb Dp) R.

      Lemma mem_realPreimage : forall R Dp (n : N.t) (v : V.t),
          PackageSet.In (n, v) (realPreimage R Dp) <->
          PackageSet.In (n, v) R /\ hasDepNameb Dp n = true.
      Proof. intros R Dp n v; apply PackageSetPreimage.mem_preimage. Qed.

      Module ProvidesRelPreimage := Preimage ProvidesElt ProvidesRel.
      Definition provPreimage (Pi : ProvidesRel.t) (Dp : Source.DependencyRel.t) :
          ProvidesRel.t :=
        ProvidesRelPreimage.preimage ProvidesRelFibred.node (hasDepNameb Dp) Pi.

      Lemma mem_provPreimage : forall Pi Dp (q : Package.t) (n : N.t) (v : VTop),
          ProvidesRel.In (q, (n, v)) (provPreimage Pi Dp) <->
          ProvidesRel.In (q, (n, v)) Pi /\ hasDepNameb Dp n = true.
      Proof. intros Pi Dp q n v; apply ProvidesRelPreimage.mem_preimage. Qed.

      Lemma prov_provPreimage : forall Pi Dp n vs,
          hasDepNameb Dp n = true ->
          (Prov (provPreimage Pi Dp) n vs <-> Prov Pi n vs).
      Proof.
        intros Pi Dp n vs Hn; unfold Prov; split.
        - intros [q [v [Hin Hm]]]; apply mem_provPreimage in Hin.
          destruct Hin as [Hin _]; exists q, v; split; assumption.
        - intros [q [v [Hin Hm]]]; exists q, v; split; [| exact Hm].
          apply mem_provPreimage; split; [exact Hin | exact Hn].
      Qed.

      Lemma selectorVersions_preimage : forall R Pi Dp n vs,
          hasDepNameb Dp n = true ->
          selectorVersions (realPreimage R Dp) (provPreimage Pi Dp) n vs =
          selectorVersions R Pi n vs.
      Proof.
        intros R Pi Dp n vs Hn; apply Reduced.VSet.ext; intro u'.
        rewrite !mem_selectorVersions; split.
        - intros [[m [u [v [Hin [Hm ->]]]]] | [u [Hu [HR ->]]]].
          + apply mem_provPreimage in Hin; destruct Hin as [Hin _].
            left; exists m, u, v;
              split; [exact Hin | split; [exact Hm | reflexivity]].
          + apply mem_realPreimage in HR; destruct HR as [HR _].
            right; exists u;
              split; [exact Hu | split; [exact HR | reflexivity]].
        - intros [[m [u [v [Hin [Hm ->]]]]] | [u [Hu [HR ->]]]].
          + left; exists m, u, v.
            split; [apply mem_provPreimage; split; [exact Hin | exact Hn] |].
            split; [exact Hm | reflexivity].
          + right; exists u; split; [exact Hu |].
            split;
              [apply mem_realPreimage; split; [exact HR | exact Hn]
              | reflexivity].
      Qed.

      Module PackageSetFibred := FibredRel N V Package PackageSet.
      Theorem versions_lookupOrig : forall R D Pi (n : N.t),
          Reduced.versions (reduceReal R D Pi) (Name.Orig n) =
          Reduced.versions
            (reduceReal (PackageSetFibred.tailFibre R n) Source.DependencyRel.empty
               ProvidesRel.empty)
            (Name.Orig n).
      Proof.
        intros R D Pi n; apply Reduced.versions_ext; intro v.
        rewrite !mem_reduceReal.
        split; intro H; inversion H as [n1 v1 HR | |]; subst; constructor.
        - apply PackageSetFibred.mem_tailFibre; split; [exact HR | reflexivity].
        - exact (PackageSetFibred.tailFibre_subset _ _ _ HR).
      Qed.

      Theorem dependees_lookupOrig : forall R D Pi (p : Package.t),
          let Dp := DependencyRelFibred.tailFibre D p in
          Reduced.dependees (reduceDeps R D Pi) (embedPkg p) =
          Reduced.dependees (reduceDeps (realPreimage R Dp) Dp (provPreimage Pi Dp))
            (embedPkg p).
      Proof.
        intros R D Pi [pn pv]; cbv zeta; cbn [embedPkg].
        assert (Hn : forall n vs, Source.DependencyRel.In ((pn, pv), (n, vs)) D ->
                  hasDepNameb (DependencyRelFibred.tailFibre D (pn, pv)) n = true).
        { intros n vs HD; apply hasDepNameb_iff; exists (pn, pv), vs.
          apply DependencyRelFibred.mem_tailFibre; split; [exact HD | reflexivity]. }
        apply Reduced.dependees_ext; intros [m ws]; rewrite !mem_reduceDeps.
        split; intro H;
          inversion H as [pn1 pv1 n vs HD Hb | pn1 pv1 n vs HD Hb | |]; subst.
        - apply DepsOrig;
            [apply DependencyRelFibred.mem_tailFibre; split; [exact HD | reflexivity]
            |].
          rewrite (prov_provPreimage Pi _ n vs (Hn _ _ HD)); exact Hb.
        - rewrite <- (selectorVersions_preimage R Pi _ n vs (Hn _ _ HD)).
          apply DepsSelector;
            [apply DependencyRelFibred.mem_tailFibre; split; [exact HD | reflexivity]
            |].
          apply (prov_provPreimage Pi _ n vs (Hn _ _ HD)); exact Hb.
        - pose proof (DependencyRelFibred.tailFibre_subset _ _ _ HD) as HD'.
          apply DepsOrig; [exact HD' |].
          rewrite <- (prov_provPreimage Pi _ n vs (Hn _ _ HD')).
          exact Hb.
        - pose proof (DependencyRelFibred.tailFibre_subset _ _ _ HD) as HD'.
          rewrite (selectorVersions_preimage R Pi _ n vs (Hn _ _ HD')).
          apply DepsSelector; [exact HD' |].
          apply (prov_provPreimage Pi _ n vs (Hn _ _ HD')); exact Hb.
      Qed.

      Theorem versions_lookupSelector : forall R D Pi (p : Package.t) (n : N.t),
          Reduced.versions (reduceReal R D Pi) (Name.Selector p n) =
          Reduced.versions
            (reduceReal (PackageSetFibred.tailFibre R n)
               (DependencyRelFibred.endsFibre D p n) (ProvidesRelFibred.nodeFibre Pi n))
            (Name.Selector p n).
      Proof.
        intros R D Pi p n; apply Reduced.versions_ext; intro w.
        rewrite !mem_reduceReal.
        split; intro H;
          inversion H as [| q n' vs m u v HD HP Hm | q n' vs u HD Hb Hu HuR];
          subst.
        - eapply RealProvider; [| | exact Hm].
          + apply DependencyRelFibred.mem_endsFibre;
              split; [exact HD | split; reflexivity].
          + apply ProvidesRelFibred.mem_nodeFibre; split; [exact HP | reflexivity].
        - eapply RealDirect; [| | exact Hu |].
          + apply DependencyRelFibred.mem_endsFibre;
              split; [exact HD | split; reflexivity].
          + apply (proj2 (prov_nodeFibre _ _ _)); exact Hb.
          + apply PackageSetFibred.mem_tailFibre; split; [exact HuR | reflexivity].
        - eapply RealProvider;
            [exact (DependencyRelFibred.endsFibre_subset _ _ _ _ HD)
            | exact (ProvidesRelFibred.nodeFibre_subset _ _ _ HP) | exact Hm].
        - eapply RealDirect;
            [exact (DependencyRelFibred.endsFibre_subset _ _ _ _ HD)
            | apply (proj1 (prov_nodeFibre _ _ _)); exact Hb
            | exact Hu | exact (PackageSetFibred.tailFibre_subset _ _ _ HuR)].
      Qed.

      Theorem dependees_lookupSelector : forall R D Pi (p : Package.t) n v,
          Reduced.dependees (reduceDeps R D Pi) (Name.Selector p n, v) =
          Reduced.dependees
            (reduceDeps (PackageSetFibred.tailFibre R n) (DependencyRelFibred.tailFibre D p)
                        (ProvidesRelFibred.nodeFibre Pi n))
            (Name.Selector p n, v).
      Proof.
        intros R D Pi p n v; apply Reduced.dependees_ext; intros [m0 ws];
          rewrite !mem_reduceDeps.
        split; intro H;
          inversion H as [| | q n' vs m' u v' HD HP Hm
                         | q n' vs u HD Hb Hu HuR]; subst.
        - eapply DepsProvider; [| | exact Hm].
          + apply DependencyRelFibred.mem_tailFibre; split; [exact HD | reflexivity].
          + apply ProvidesRelFibred.mem_nodeFibre; split; [exact HP | reflexivity].
        - eapply DepsDirect; [| | exact Hu |].
          + apply DependencyRelFibred.mem_tailFibre; split; [exact HD | reflexivity].
          + apply (proj2 (prov_nodeFibre _ _ _)); exact Hb.
          + apply PackageSetFibred.mem_tailFibre; split; [exact HuR | reflexivity].
        - eapply DepsProvider;
            [exact (DependencyRelFibred.tailFibre_subset _ _ _ HD)
            | exact (ProvidesRelFibred.nodeFibre_subset _ _ _ HP) | exact Hm].
        - eapply DepsDirect;
            [exact (DependencyRelFibred.tailFibre_subset _ _ _ HD)
            | apply (proj1 (prov_nodeFibre _ _ _)); exact Hb
            | exact Hu | exact (PackageSetFibred.tailFibre_subset _ _ _ HuR)].
      Qed.

    End Lookup.
  End Reduction.

End Virtual.
