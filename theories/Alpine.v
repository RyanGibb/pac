From Stdlib Require Import MSets OrdersEx Bool List.
From PackageCalculus Require Import Prelude Core Versions PackageFormula.

Create HintDb cmp_alp.
Create Rewrite HintDb cmp_alp.

(* apk's ~ (component-prefix) and >< (build identity) constraints are not
   expressible through V.compare; they arrive as opaque predicates and only
   ever build version sets, so no laws are demanded of them. *)
Module Type ApkVerMatch (V : UsualOrderedType).
  Parameter prefix : V.t -> V.t -> bool.
  Parameter hash : V.t -> V.t -> bool.
End ApkVerMatch.

Module Alpine (N V : UsualOrderedType) (PM : ApkVerMatch V).
  Module C := Core N V.
  Module Pkg := C.Pkg.
  Module PkgSet := C.PkgSet.
  Module NEqb := UOTEqb N.
  Module PkgEqb := UOTEqb Pkg.

  Inductive Constr : Type :=
  | CAny
  | COp (op : CmpOp) (c : V.t)
  | CPrefix (c : V.t)
  | CGtPrefix (c : V.t)
  | CLtPrefix (c : V.t)
  | CHash (c : V.t).

  Definition constrMatch (ct : Constr) (v : V.t) : bool :=
    match ct with
    | CAny => true
    | COp op c => cmpOpEvalBy V.compare op v c
    | CPrefix c => PM.prefix v c
    | CGtPrefix c => orb (cmpOpEvalBy V.compare OpGt v c) (PM.prefix v c)
    | CLtPrefix c => orb (cmpOpEvalBy V.compare OpLt v c) (PM.prefix v c)
    | CHash c => PM.hash v c
    end.

  Definition isAny (ct : Constr) : bool :=
    match ct with CAny => true | _ => false end.

  Module VF := UOTCompareFacts V.
  Module OV := PairUOT OpOT V.
  Module OVF := UOTCompareFacts OV.
  #[local] Hint Rewrite OVF.compare_eq_iff VF.compare_eq_iff : cmp_alp.
  #[local] Hint Extern 1 => cmp_by OVF.compare_antisym : cmp_alp.
  #[local] Hint Extern 1 => cmp_by VF.compare_antisym : cmp_alp.
  #[local] Hint Extern 1 => cmp_by OVF.compare_lt_trans : cmp_alp.
  #[local] Hint Extern 1 => cmp_by VF.compare_lt_trans : cmp_alp.
  Module ConstrComp <: ComparableType.
    Definition t := Constr.
    Definition rank (ct : Constr) : nat :=
      match ct with
      | CAny => 0 | COp _ _ => 1 | CPrefix _ => 2
      | CGtPrefix _ => 3 | CLtPrefix _ => 4 | CHash _ => 5
      end.
    Definition compare (x y : t) : comparison :=
      match Nat.compare (rank x) (rank y) with
      | Eq =>
          match x, y with
          | COp o1 c1, COp o2 c2 => OV.compare (o1, c1) (o2, c2)
          | CPrefix c1, CPrefix c2 => V.compare c1 c2
          | CGtPrefix c1, CGtPrefix c2 => V.compare c1 c2
          | CLtPrefix c1, CLtPrefix c2 => V.compare c1 c2
          | CHash c1, CHash c2 => V.compare c1 c2
          | _, _ => Eq
          end
      | c => c
      end.
    Lemma compare_eq_iff : forall x y, compare x y = Eq <-> x = y.
    Proof. cmp_eq_iff cmp_alp. Qed.
    Lemma compare_antisym : forall x y, compare y x = CompOpp (compare x y).
    Proof. cmp_antisym cmp_alp. Qed.
    Lemma compare_lt_trans : forall x y z,
        compare x y = Lt -> compare y z = Lt -> compare x z = Lt.
    Proof. cmp_lt_trans cmp_alp. Qed.
  End ConstrComp.
  Module ConstrOT := UOTFromCompare ConstrComp.

  Module Atom := PairUOT N ConstrOT.
  Module AtomF := UOTCompareFacts Atom.

  Inductive Dep : Type :=
  | DPos (a : Atom.t)
  | DNeg (a : Atom.t).

  Module DepComp <: ComparableType.
    Definition t := Dep.
    Definition rank (d : Dep) : nat :=
      match d with DPos _ => 0 | DNeg _ => 1 end.
    Definition compare (x y : t) : comparison :=
      match Nat.compare (rank x) (rank y) with
      | Eq =>
          match x, y with
          | DPos a1, DPos a2 => Atom.compare a1 a2
          | DNeg a1, DNeg a2 => Atom.compare a1 a2
          | _, _ => Eq
          end
      | c => c
      end.
    #[local] Hint Rewrite AtomF.compare_eq_iff : cmp_alp.
    #[local] Hint Extern 1 => cmp_by AtomF.compare_antisym : cmp_alp.
    #[local] Hint Extern 1 => cmp_by AtomF.compare_lt_trans : cmp_alp.
    Lemma compare_eq_iff : forall x y, compare x y = Eq <-> x = y.
    Proof. cmp_eq_iff cmp_alp. Qed.
    Lemma compare_antisym : forall x y, compare y x = CompOpp (compare x y).
    Proof. cmp_antisym cmp_alp. Qed.
    Lemma compare_lt_trans : forall x y z,
        compare x y = Lt -> compare y z = Lt -> compare x z = Lt.
    Proof. cmp_lt_trans cmp_alp. Qed.
  End DepComp.
  Module DepOT := UOTFromCompare DepComp.

  Module DepElt := PairUOT Pkg DepOT.
  Module Deps := FSetUOT DepElt.

  Inductive PTag : Type :=
  | PVer (pv : V.t)
  | PVirt.

  Module PTagComp <: ComparableType.
    Definition t := PTag.
    Definition compare (x y : t) : comparison :=
      match x, y with
      | PVer v1, PVer v2 => V.compare v1 v2
      | PVer _, PVirt => Lt
      | PVirt, PVer _ => Gt
      | PVirt, PVirt => Eq
      end.
    Lemma compare_eq_iff : forall x y, compare x y = Eq <-> x = y.
    Proof. cmp_eq_iff cmp_alp. Qed.
    Lemma compare_antisym : forall x y, compare y x = CompOpp (compare x y).
    Proof. cmp_antisym cmp_alp. Qed.
    Lemma compare_lt_trans : forall x y z,
        compare x y = Lt -> compare y z = Lt -> compare x z = Lt.
    Proof. cmp_lt_trans cmp_alp. Qed.
  End PTagComp.
  Module PTagOT := UOTFromCompare PTagComp.

  Module Provided := PairUOT N PTagOT.
  Module ProvElt := PairUOT Pkg Provided.
  Module Prov := FSetUOT ProvElt.

  Module CondSet := FSetUOT Atom.
  Module TrigElt := PairUOT Pkg CondSet.AsUOT.
  Module Trig := FSetUOT TrigElt.

  Module WSet := FSetUOT DepOT.

  Module PrioElt := PairUOT Pkg Nat_as_OT.
  Module Prio := FSetUOT PrioElt.
  Module ReplElt := PairUOT Pkg N.
  Module Repl := FSetUOT ReplElt.

  (* provider_priority and replaces steer apk's solver preference and
     file ownership; neither constrains which sets are resolutions. *)
  Record Inst : Type :=
    { inst_repo : PkgSet.t
    ; inst_deps : Deps.t
    ; inst_prov : Prov.t
    ; inst_trig : Trig.t
    ; inst_world : WSet.t
    ; inst_prio : Prio.t
    ; inst_repl : Repl.t }.

  (* A versioned provide is an alias: it satisfies constrained atoms at
     the provided version and claims the name.  An unversioned provide
     satisfies only bare atoms and claims nothing. *)
  Definition MatchPos (I : Inst) (S : PkgSet.t)
      (n : N.t) (ct : Constr) : Prop :=
    (exists v, PkgSet.In (n, v) S /\ constrMatch ct v = true) \/
    (exists q pv, Prov.In (q, (n, PVer pv)) (inst_prov I) /\
       PkgSet.In q S /\ constrMatch ct pv = true) \/
    (isAny ct = true /\
     exists q, Prov.In (q, (n, PVirt)) (inst_prov I) /\ PkgSet.In q S).

  Definition MatchDep (I : Inst) (S : PkgSet.t) (d : Dep) : Prop :=
    match d with
    | DPos (n, ct) => MatchPos I S n ct
    | DNeg (n, ct) => ~ MatchPos I S n ct
    end.

  (* Real packages and versioned providers both claim their name; claim
     uniqueness subsumes per-name version uniqueness. *)
  Definition Claims (I : Inst) (n : N.t) (p : Pkg.t) : Prop :=
    fst p = n \/ exists pv, Prov.In (p, (n, PVer pv)) (inst_prov I).

  Record IsResolution (I : Inst) (S : PkgSet.t) : Prop :=
    { res_subset : PkgSet.Subset S (inst_repo I)
    ; res_world : forall d, WSet.In d (inst_world I) -> MatchDep I S d
    ; res_dep :
        forall p d, PkgSet.In p S -> Deps.In (p, d) (inst_deps I) ->
        MatchDep I S d
    ; res_claim_unique :
        forall n p q, PkgSet.In p S -> PkgSet.In q S ->
        Claims I n p -> Claims I n q -> p = q
    (* install_if obliges the name, not the declaring version: apk is
       satisfied by any installed claimant of the package's name. *)
    ; res_trig :
        forall p conds, Trig.In (p, conds) (inst_trig I) ->
        (forall n ct, CondSet.In (n, ct) conds -> MatchPos I S n ct) ->
        MatchPos I S (fst p) CAny }.

  Module Reduction.
    Module NF := UOTCompareFacts N.
    Module PV := PairUOT Pkg V.
    Module PVF := UOTCompareFacts PV.
    #[local] Hint Rewrite NF.compare_eq_iff PVF.compare_eq_iff : cmp_alp.
    #[local] Hint Extern 1 => cmp_by NF.compare_antisym : cmp_alp.
    #[local] Hint Extern 1 => cmp_by PVF.compare_antisym : cmp_alp.
    #[local] Hint Extern 1 => cmp_by NF.compare_lt_trans : cmp_alp.
    #[local] Hint Extern 1 => cmp_by PVF.compare_lt_trans : cmp_alp.

    Module Name.
      Inductive name : Type :=
      | Root
      | Orig (n : N.t).
      Definition t := name.

      Definition compare (x y : t) : comparison :=
        match x, y with
        | Root, Root => Eq
        | Root, Orig _ => Lt
        | Orig _, Root => Gt
        | Orig n1, Orig n2 => N.compare n1 n2
        end.
      Lemma compare_eq_iff : forall x y, compare x y = Eq <-> x = y.
      Proof. cmp_eq_iff cmp_alp. Qed.
      Lemma compare_antisym : forall x y,
          compare y x = CompOpp (compare x y).
      Proof. cmp_antisym cmp_alp. Qed.
      Lemma compare_lt_trans : forall x y z,
          compare x y = Lt -> compare y z = Lt -> compare x z = Lt.
      Proof. cmp_lt_trans cmp_alp. Qed.
    End Name.
    Module NameOT := UOTFromCompare Name.

    (* An alias version's identity is its provider, so two providers
       aliasing the same name at the same version stay distinct target
       versions and claim conflicts surface as core version uniqueness. *)
    Module Version.
      Inductive version : Type :=
      | RootV
      | Orig (v : V.t)
      | Prov (p : Pkg.t) (pv : V.t).
      Definition t := version.

      Definition rank (w : t) : nat :=
        match w with RootV => 0 | Orig _ => 1 | Prov _ _ => 2 end.
      Definition compare (x y : t) : comparison :=
        match Nat.compare (rank x) (rank y) with
        | Eq =>
            match x, y with
            | Orig v1, Orig v2 => V.compare v1 v2
            | Prov p1 v1, Prov p2 v2 => PV.compare (p1, v1) (p2, v2)
            | _, _ => Eq
            end
        | c => c
        end.
      Lemma compare_eq_iff : forall x y, compare x y = Eq <-> x = y.
      Proof. cmp_eq_iff cmp_alp. Qed.
      Lemma compare_antisym : forall x y,
          compare y x = CompOpp (compare x y).
      Proof. cmp_antisym cmp_alp. Qed.
      Lemma compare_lt_trans : forall x y z,
          compare x y = Lt -> compare y z = Lt -> compare x z = Lt.
      Proof. cmp_lt_trans cmp_alp. Qed.
    End Version.
    Module VersionOT := UOTFromCompare Version.

    Module PF := PackageFormula NameOT VersionOT.

    Module DepsFibred := FibredRel Pkg DepOT DepElt Deps.
    Module ProvFibred := FibredLabelledRel Pkg N PTagOT ProvElt Prov.

    Module SOpw := SetOps Pkg VersionOT PkgSet PF.VSet.
    Module SOrw := SetOps ProvElt VersionOT Prov PF.VSet.
    Definition constrVers (I : Inst) (n : N.t) (ct : Constr) : PF.VSet.t :=
      PF.VSet.union
        (SOpw.filterMap
           (fun p =>
              if andb (NEqb.eqb (fst p) n) (constrMatch ct (snd p))
              then Some (Version.Orig (snd p)) else None)
           (inst_repo I))
        (SOrw.filterMap
           (fun '(q, (m, tg)) =>
              match tg with
              | PVer pv =>
                  if andb (NEqb.eqb m n)
                       (andb (PkgSet.mem q (inst_repo I))
                          (constrMatch ct pv))
                  then Some (Version.Prov q pv) else None
              | PVirt => None
              end)
           (inst_prov I)).

    Definition versions (I : Inst) (n : N.t) : PF.VSet.t :=
      constrVers I n CAny.

    Module SOrp := SetOps ProvElt Pkg Prov PkgSet.
    Definition uprovSet (I : Inst) (n : N.t) : PkgSet.t :=
      SOrp.filterMap
        (fun '(q, (m, tg)) =>
           match tg with
           | PVirt =>
               if andb (NEqb.eqb m n) (PkgSet.mem q (inst_repo I))
               then Some q else None
           | PVer _ => None
           end)
        (inst_prov I).

    Definition uprovL (I : Inst) (n : N.t) : list Pkg.t :=
      PkgSet.elements (uprovSet I n).

    Definition encPos (I : Inst) (n : N.t) (ct : Constr) : PF.Formula :=
      let base := PF.FDep (Name.Orig n) (constrVers I n ct) in
      if isAny ct
      then
        fold_right
          (fun q f =>
             PF.FDisj
               (PF.FDep (Name.Orig (fst q))
                  (PF.VSet.singleton (Version.Orig (snd q)))) f)
          base (uprovL I n)
      else base.

    Definition encDep (I : Inst) (d : Dep) : PF.Formula :=
      match d with
      | DPos (n, ct) => encPos I n ct
      | DNeg (n, ct) => PF.FNeg (encPos I n ct)
      end.

    Definition trigForm (I : Inst) (p : Pkg.t) (conds : CondSet.t) :
        PF.Formula :=
      fold_right
        (fun a f => PF.FDisj (PF.FNeg (encPos I (fst a) (snd a))) f)
        (encPos I (fst p) CAny) (CondSet.elements conds).

    Definition rootPkg : PF.Pkg.t := (Name.Root, Version.RootV).

    Module FSet := FSetUOT PF.FOT.
    Module SOdf := SetOps DepElt PF.FOT Deps FSet.
    Module SOrf := SetOps ProvElt PF.FOT Prov FSet.
    Module SOtf := SetOps TrigElt PF.FOT Trig FSet.
    Module SOwf := SetOps DepOT PF.FOT WSet FSet.
    Definition dependees (I : Inst) (q : PF.Pkg.t) : FSet.t :=
      match q with
      | (Name.Root, Version.RootV) =>
          FSet.union (SOwf.map (encDep I) (inst_world I))
            (SOtf.map (fun '(p, conds) => trigForm I p conds)
               (inst_trig I))
      | (Name.Orig n, Version.Orig v) =>
          FSet.union
            (SOdf.map (fun '(_, d) => encDep I d)
               (DepsFibred.tailFibre (inst_deps I) (n, v)))
            (SOrf.filterMap
               (fun '(_, (m, tg)) =>
                  match tg with
                  | PVer pv =>
                      Some (PF.FDep (Name.Orig m)
                              (PF.VSet.singleton (Version.Prov (n, v) pv)))
                  | PVirt => None
                  end)
               (ProvFibred.tailFibre (inst_prov I) (n, v)))
      | (Name.Orig _, Version.Prov q0 _) =>
          FSet.singleton
            (PF.FDep (Name.Orig (fst q0))
               (PF.VSet.singleton (Version.Orig (snd q0))))
      | _ => FSet.empty
      end.

    Module SOpp := SetOps Pkg PF.Pkg PkgSet PF.PkgSet.
    Module SOrq := SetOps ProvElt PF.Pkg Prov PF.PkgSet.
    Definition embedPkg (p : Pkg.t) : PF.Pkg.t :=
      (Name.Orig (fst p), Version.Orig (snd p)).

    Definition provPkgs (I : Inst) (S : PkgSet.t) : PF.PkgSet.t :=
      SOrq.filterMap
        (fun '(q, (m, tg)) =>
           match tg with
           | PVer pv =>
               if PkgSet.mem q S
               then Some (Name.Orig m, Version.Prov q pv) else None
           | PVirt => None
           end)
        (inst_prov I).

    Definition transR (I : Inst) : PF.PkgSet.t :=
      PF.PkgSet.add rootPkg
        (PF.PkgSet.union (SOpp.map embedPkg (inst_repo I))
           (provPkgs I (inst_repo I))).

    Module SOqd := SetOps PF.Pkg PF.DepElt PF.PkgSet PF.DepRel.
    Module SOfd := SetOps PF.FOT PF.DepElt FSet PF.DepRel.
    Definition depEdges (q : PF.Pkg.t) (fs : FSet.t) : PF.DepRel.t :=
      SOfd.map (fun f => (q, f)) fs.

    Definition transD (I : Inst) : PF.DepRel.t :=
      SOqd.unionMap (fun q => depEdges q (dependees I q)) (transR I).

    Definition tryInvPkg (q : PF.Pkg.t) : option Pkg.t :=
      match q with
      | (Name.Orig n, Version.Orig v) => Some (n, v)
      | _ => None
      end.
    Module SOqp := SetOps PF.Pkg Pkg PF.PkgSet PkgSet.
    Definition alpineResolution (S' : PF.PkgSet.t) : PkgSet.t :=
      SOqp.filterMap tryInvPkg S'.

    Definition transS (I : Inst) (S : PkgSet.t) : PF.PkgSet.t :=
      PF.PkgSet.add rootPkg
        (PF.PkgSet.union (SOpp.map embedPkg S) (provPkgs I S)).

    Lemma tryInvPkg_embed : forall p, tryInvPkg (embedPkg p) = Some p.
    Proof. intros [n v]; reflexivity. Qed.

    Lemma tryInvPkg_some : forall q p, tryInvPkg q = Some p -> embedPkg p = q.
    Proof.
      intros [[|n] [|v|q0 pv]] p H; try discriminate.
      injection H as <-; reflexivity.
    Qed.

    Lemma embedPkg_injective : forall p q, embedPkg p = embedPkg q -> p = q.
    Proof. exact (SOqp.emb_injective tryInvPkg embedPkg tryInvPkg_embed). Qed.

    Lemma mem_alpineResolution : forall S' p,
        PkgSet.In p (alpineResolution S') <->
        PF.PkgSet.In (embedPkg p) S'.
    Proof.
      exact (SOqp.mem_filterMap_inv tryInvPkg embedPkg
               tryInvPkg_embed tryInvPkg_some).
    Qed.

    Lemma mem_constrVers : forall I n ct w,
        PF.VSet.In w (constrVers I n ct) <->
        (exists v, PkgSet.In (n, v) (inst_repo I) /\
           constrMatch ct v = true /\ w = Version.Orig v) \/
        (exists q pv, Prov.In (q, (n, PVer pv)) (inst_prov I) /\
           PkgSet.In q (inst_repo I) /\ constrMatch ct pv = true /\
           w = Version.Prov q pv).
    Proof.
      intros I n ct w; unfold constrVers.
      rewrite PF.VSet.union_spec, SOpw.mem_filterMap, SOrw.mem_filterMap.
      split.
      - intros [[[m v] [Hm Hf]] | [[q [m tg]] [Hm Hf]]].
        + cbn in Hf.
          destruct (NEqb.eqb m n) eqn:En; [| discriminate].
          apply NEqb.eqb_true_iff in En; subst m.
          destruct (constrMatch ct v) eqn:Ec; [| discriminate].
          injection Hf as <-; left; eauto.
        + cbn in Hf; destruct tg as [pv |]; [| discriminate].
          destruct (NEqb.eqb m n) eqn:En; [| discriminate].
          apply NEqb.eqb_true_iff in En; subst m.
          destruct (PkgSet.mem q (inst_repo I)) eqn:Eq; [| discriminate].
          destruct (constrMatch ct pv) eqn:Ec; [| discriminate].
          injection Hf as <-; right.
          exists q, pv; repeat split; try assumption.
          apply PkgSet.mem_spec; assumption.
      - intros [[v [Hv [Hc ->]]] | [q [pv [Hr [Hq [Hc ->]]]]]].
        + left; exists (n, v); split; [exact Hv | cbn].
          rewrite (proj2 (NEqb.eqb_true_iff n n) eq_refl), Hc; reflexivity.
        + right; exists (q, (n, PVer pv)); split; [exact Hr | cbn].
          rewrite (proj2 (NEqb.eqb_true_iff n n) eq_refl), Hc.
          rewrite (proj2 (PkgSet.mem_spec _ _) Hq); reflexivity.
    Qed.

    Lemma mem_uprovSet : forall I n q,
        PkgSet.In q (uprovSet I n) <->
        Prov.In (q, (n, PVirt)) (inst_prov I) /\
        PkgSet.In q (inst_repo I).
    Proof.
      intros I n q; unfold uprovSet; rewrite SOrp.mem_filterMap.
      split.
      - intros [[q0 [m tg]] [Hm Hf]]; cbn in Hf.
        destruct tg as [|]; [discriminate |].
        destruct (NEqb.eqb m n) eqn:En; [| discriminate].
        apply NEqb.eqb_true_iff in En; subst m.
        destruct (PkgSet.mem q0 (inst_repo I)) eqn:Eq; [| discriminate].
        injection Hf as <-.
        split; [exact Hm | apply PkgSet.mem_spec; assumption].
      - intros [Hr Hq]; exists (q, (n, PVirt)); split; [exact Hr | cbn].
        rewrite (proj2 (NEqb.eqb_true_iff n n) eq_refl).
        rewrite (proj2 (PkgSet.mem_spec _ _) Hq); reflexivity.
    Qed.

    Lemma mem_provPkgs : forall I S y,
        PF.PkgSet.In y (provPkgs I S) <->
        exists q m pv, Prov.In (q, (m, PVer pv)) (inst_prov I) /\
          PkgSet.In q S /\ y = (Name.Orig m, Version.Prov q pv).
    Proof.
      intros I S y; unfold provPkgs; rewrite SOrq.mem_filterMap.
      split.
      - intros [[q [m tg]] [Hm Hf]]; cbn in Hf.
        destruct tg as [pv |]; [| discriminate].
        destruct (PkgSet.mem q S) eqn:Eq; [| discriminate].
        injection Hf as <-.
        exists q, m, pv; repeat split; try assumption.
        apply PkgSet.mem_spec; assumption.
      - intros [q [m [pv [Hr [Hq ->]]]]].
        exists (q, (m, PVer pv)); split; [exact Hr | cbn].
        rewrite (proj2 (PkgSet.mem_spec _ _) Hq); reflexivity.
    Qed.

    Lemma mem_transR : forall I y,
        PF.PkgSet.In y (transR I) <->
        y = rootPkg \/
        (exists p, PkgSet.In p (inst_repo I) /\ y = embedPkg p) \/
        (exists q m pv, Prov.In (q, (m, PVer pv)) (inst_prov I) /\
           PkgSet.In q (inst_repo I) /\
           y = (Name.Orig m, Version.Prov q pv)).
    Proof.
      intros I y; unfold transR.
      rewrite PF.PkgSet.add_spec, PF.PkgSet.union_spec, SOpp.mem_map,
        mem_provPkgs.
      firstorder.
    Qed.

    Lemma mem_transS : forall I S y,
        PF.PkgSet.In y (transS I S) <->
        y = rootPkg \/
        (exists p, PkgSet.In p S /\ y = embedPkg p) \/
        (exists q m pv, Prov.In (q, (m, PVer pv)) (inst_prov I) /\
           PkgSet.In q S /\ y = (Name.Orig m, Version.Prov q pv)).
    Proof.
      intros I S y; unfold transS.
      rewrite PF.PkgSet.add_spec, PF.PkgSet.union_spec, SOpp.mem_map,
        mem_provPkgs.
      firstorder.
    Qed.

    Lemma mem_transD : forall I y f,
        PF.DepRel.In (y, f) (transD I) <->
        PF.PkgSet.In y (transR I) /\ FSet.In f (dependees I y).
    Proof.
      intros I y f; unfold transD; rewrite SOqd.mem_unionMap.
      split.
      - intros [q [Hq Hf]]; unfold depEdges in Hf.
        apply SOfd.mem_map in Hf; destruct Hf as [g [Hg He]].
        injection He as <- <-; split; assumption.
      - intros [Hy Hf]; exists y; split; [exact Hy |].
        unfold depEdges; apply SOfd.mem_map; exists f; split;
          [exact Hf | reflexivity].
    Qed.

    Lemma in_elements_pkg : forall s q,
        List.In q (PkgSet.elements s) <-> PkgSet.In q s.
    Proof.
      intros s q; rewrite <- (PkgSet.elements_spec1 s q).
      rewrite InA_alt; split.
      - intro H; exists q; split; reflexivity + assumption.
      - intros [y [-> Hy]]; exact Hy.
    Qed.

    Lemma in_elements_cond : forall s a,
        List.In a (CondSet.elements s) <-> CondSet.In a s.
    Proof.
      intros s a; rewrite <- (CondSet.elements_spec1 s a).
      rewrite InA_alt; split.
      - intro H; exists a; split; reflexivity + assumption.
      - intros [y [-> Hy]]; exact Hy.
    Qed.

    Lemma satisfies_disjFold : forall S' l (base : PF.Formula),
        PF.Satisfies S'
          (fold_right
             (fun q f =>
                PF.FDisj
                  (PF.FDep (Name.Orig (fst q))
                     (PF.VSet.singleton (Version.Orig (snd q)))) f)
             base l) <->
        PF.Satisfies S' base \/
        (exists q, List.In q l /\ PF.PkgSet.In (embedPkg q) S').
    Proof.
      intros S' l base; induction l as [| q l IH]; cbn.
      - firstorder.
      - rewrite IH; split.
        + intros [[w [Hw Hm]] | H].
          * apply PF.VSet.singleton_spec in Hw; subst w.
            right; exists q; auto.
          * destruct H as [H | [q0 [Hq0 Hm]]]; [left; exact H |].
            right; exists q0; auto.
        + intros [H | [q0 [[<- | Hq0] Hm]]].
          * right; left; exact H.
          * left; exists (Version.Orig (snd q)); split;
              [apply PF.VSet.singleton_spec; reflexivity | exact Hm].
          * right; right; exists q0; auto.
    Qed.

    Lemma satisfies_encPos : forall I S' n ct,
        PF.Satisfies S' (encPos I n ct) <->
        (exists w, PF.VSet.In w (constrVers I n ct) /\
           PF.PkgSet.In (Name.Orig n, w) S') \/
        (isAny ct = true /\
         exists q, PkgSet.In q (uprovSet I n) /\
           PF.PkgSet.In (embedPkg q) S').
    Proof.
      intros I S' n ct; unfold encPos.
      destruct (isAny ct) eqn:Ea.
      - rewrite satisfies_disjFold; cbn.
        unfold uprovL; split.
        + intros [[w [Hw Hm]] | [q [Hq Hm]]]; [left; eauto |].
          apply in_elements_pkg in Hq; right; split; [reflexivity |].
          eauto.
        + intros [[w [Hw Hm]] | [_ [q [Hq Hm]]]]; [left; eauto |].
          right; exists q; split; [| exact Hm].
          apply in_elements_pkg; exact Hq.
      - cbn; split.
        + intros [w [Hw Hm]]; left; eauto.
        + intros [[w [Hw Hm]] | [Hany _]]; [eauto | congruence].
    Qed.

    Lemma satisfies_negFold : forall I S' l (base : PF.Formula),
        PF.Satisfies S'
          (fold_right
             (fun a f =>
                PF.FDisj (PF.FNeg (encPos I (fst a) (snd a))) f)
             base l) <->
        (exists a, List.In a l /\
           ~ PF.Satisfies S' (encPos I (fst a) (snd a))) \/
        PF.Satisfies S' base.
    Proof.
      intros I S' l base; induction l as [| a l IH]; cbn.
      - firstorder.
      - rewrite IH; split.
        + intros [Hn | [[a0 [Ha0 Hn]] | Hb]].
          * left; exists a; auto.
          * left; exists a0; auto.
          * right; exact Hb.
        + intros [[a0 [[<- | Ha0] Hn]] | Hb].
          * left; exact Hn.
          * right; left; exists a0; auto.
          * right; right; exact Hb.
    Qed.

    Lemma satisfies_trigForm : forall I S' p conds,
        PF.Satisfies S' (trigForm I p conds) <->
        (exists a, CondSet.In a conds /\
           ~ PF.Satisfies S' (encPos I (fst a) (snd a))) \/
        PF.Satisfies S' (encPos I (fst p) CAny).
    Proof.
      intros I S' p conds; unfold trigForm.
      rewrite satisfies_negFold.
      split; intros [[a [Ha Hn]] | Hb];
        try (right; exact Hb); left; exists a;
        (split; [| exact Hn]); apply in_elements_cond; exact Ha.
    Qed.

    Lemma embed_transR : forall I p,
        PF.PkgSet.In (embedPkg p) (transR I) ->
        PkgSet.In p (inst_repo I).
    Proof.
      intros I p H; apply mem_transR in H.
      destruct p as [n v].
      destruct H as [H | [[p0 [Hp0 He]] | [q [m [pv [_ [_ He]]]]]]].
      - discriminate H.
      - apply embedPkg_injective in He; subst p0; exact Hp0.
      - injection He as _ He; discriminate He.
    Qed.

    Lemma root_transR : forall I, PF.PkgSet.In rootPkg (transR I).
    Proof.
      intro I; unfold transR; apply PF.PkgSet.add_spec; left; reflexivity.
    Qed.

    Lemma prov_selected : forall I S' m q pv,
        PF.IsResolution (transR I) (transD I) rootPkg S' ->
        PF.PkgSet.In (Name.Orig m, Version.Prov q pv) S' ->
        Prov.In (q, (m, PVer pv)) (inst_prov I) /\
        PF.PkgSet.In (embedPkg q) S'.
    Proof.
      intros I S' m q pv [Hsub Hroot Hclo Huniq] Hm.
      assert (Ht := Hsub _ Hm); apply mem_transR in Ht.
      destruct Ht as [Ht | [[p0 [_ He]] | [q0 [m0 [pv0 [Hrow [_ He]]]]]]].
      - discriminate Ht.
      - destruct p0; discriminate He.
      - injection He as He1 He2 He3; subst m0 q0 pv0.
        split; [exact Hrow |].
        assert (Hf : FSet.In
                       (PF.FDep (Name.Orig (fst q))
                          (PF.VSet.singleton (Version.Orig (snd q))))
                       (dependees I (Name.Orig m, Version.Prov q pv))).
        { cbn [dependees]; apply FSet.singleton_spec; reflexivity. }
        assert (Hd : PF.DepRel.In
                       ((Name.Orig m, Version.Prov q pv),
                        PF.FDep (Name.Orig (fst q))
                          (PF.VSet.singleton (Version.Orig (snd q))))
                       (transD I)).
        { apply mem_transD; split; [apply Hsub; exact Hm | exact Hf]. }
        assert (Hs := Hclo _ Hm _ Hd).
        destruct Hs as [w [Hw HwS]].
        apply PF.VSet.singleton_spec in Hw; subst w.
        destruct q as [nq vq]; exact HwS.
    Qed.

    Lemma reg_edge : forall I S' p m pv,
        PF.IsResolution (transR I) (transD I) rootPkg S' ->
        PF.PkgSet.In (embedPkg p) S' ->
        Prov.In (p, (m, PVer pv)) (inst_prov I) ->
        PF.PkgSet.In (Name.Orig m, Version.Prov p pv) S'.
    Proof.
      intros I S' [n v] m pv [Hsub Hroot Hclo Huniq] HpS Hrow.
      assert (Hf : FSet.In
                     (PF.FDep (Name.Orig m)
                        (PF.VSet.singleton (Version.Prov (n, v) pv)))
                     (dependees I (embedPkg (n, v)))).
      { cbn [dependees embedPkg fst snd]; apply FSet.union_spec; right.
        apply SOrf.mem_filterMap.
        exists ((n, v), (m, PVer pv)); split; [| reflexivity].
        apply ProvFibred.mem_tailFibre; split; [exact Hrow | reflexivity]. }
      assert (Hd : PF.DepRel.In
                     (embedPkg (n, v),
                      PF.FDep (Name.Orig m)
                        (PF.VSet.singleton (Version.Prov (n, v) pv)))
                     (transD I)).
      { apply mem_transD; split; [apply Hsub; exact HpS | exact Hf]. }
      assert (Hs := Hclo _ HpS _ Hd).
      destruct Hs as [w [Hw HwS]].
      apply PF.VSet.singleton_spec in Hw; subst w; exact HwS.
    Qed.

    Lemma match_decode : forall I S' n ct,
        PF.IsResolution (transR I) (transD I) rootPkg S' ->
        (PF.Satisfies S' (encPos I n ct) <->
         MatchPos I (alpineResolution S') n ct).
    Proof.
      intros I S' n ct Hres.
      assert (Hsub := PF.res_subset _ _ _ _ Hres).
      rewrite satisfies_encPos; split.
      - intros [[w [Hw Hm]] | [Hany [q [Hq Hm]]]].
        + apply mem_constrVers in Hw.
          destruct Hw as
            [[v [Hrep [Hc ->]]] | [q [pv [Hrow [Hrep [Hc ->]]]]]].
          * left; exists v; split; [| exact Hc].
            apply mem_alpineResolution; exact Hm.
          * right; left; exists q, pv.
            destruct (prov_selected _ _ _ _ _ Hres Hm) as [_ HqS'].
            repeat split; try assumption.
            apply mem_alpineResolution; exact HqS'.
        + right; right; split; [exact Hany |].
          apply mem_uprovSet in Hq; destruct Hq as [Hrow _].
          exists q; split; [exact Hrow |].
          apply mem_alpineResolution; exact Hm.
      - intros [[v [HvS Hc]] |
                [[q [pv [Hrow [HqS Hc]]]] | [Hany [q [Hrow HqS]]]]].
        + apply mem_alpineResolution in HvS.
          left; exists (Version.Orig v); split; [| exact HvS].
          apply mem_constrVers; left; exists v.
          repeat split; try assumption.
          exact (embed_transR _ _ (Hsub _ HvS)).
        + apply mem_alpineResolution in HqS.
          left; exists (Version.Prov q pv); split.
          * apply mem_constrVers; right; exists q, pv.
            repeat split; try assumption.
            exact (embed_transR _ _ (Hsub _ HqS)).
          * exact (reg_edge _ _ _ _ _ Hres HqS Hrow).
        + apply mem_alpineResolution in HqS.
          right; split; [exact Hany |].
          exists q; split; [| exact HqS].
          apply mem_uprovSet; split; [exact Hrow |].
          exact (embed_transR _ _ (Hsub _ HqS)).
    Qed.

    Theorem alpine_soundness : forall I S',
        PF.IsResolution (transR I) (transD I) rootPkg S' ->
        IsResolution I (alpineResolution S').
    Proof.
      intros I S' Hres.
      assert (Hres' := Hres); destruct Hres' as [Hsub Hroot Hclo Huniq].
      constructor.
      - intros p Hp; apply mem_alpineResolution in Hp.
        exact (embed_transR _ _ (Hsub _ Hp)).
      - intros d Hd.
        assert (Hf : FSet.In (encDep I d) (dependees I rootPkg)).
        { cbn [dependees rootPkg]; apply FSet.union_spec; left.
          apply SOwf.mem_map; exists d; split; [exact Hd | reflexivity]. }
        assert (Hrow : PF.DepRel.In (rootPkg, encDep I d) (transD I)).
        { apply mem_transD; split; [apply root_transR | exact Hf]. }
        assert (Hs := Hclo _ Hroot _ Hrow).
        destruct d as [[m ct] | [m ct]]; cbn [MatchDep].
        + exact (proj1 (match_decode _ _ _ _ Hres) Hs).
        + intro HM; cbn [encDep] in Hs.
          exact (Hs (proj2 (match_decode _ _ _ _ Hres) HM)).
      - intros p d Hp Hrow0; apply mem_alpineResolution in Hp.
        destruct p as [np vp].
        assert (Hf : FSet.In (encDep I d)
                       (dependees I (embedPkg (np, vp)))).
        { cbn [dependees embedPkg fst snd]; apply FSet.union_spec; left.
          apply SOdf.mem_map; exists ((np, vp), d); split; [| reflexivity].
          apply DepsFibred.mem_tailFibre; split; [exact Hrow0 | reflexivity]. }
        assert (Hrow : PF.DepRel.In (embedPkg (np, vp), encDep I d)
                         (transD I)).
        { apply mem_transD; split; [apply Hsub; exact Hp | exact Hf]. }
        assert (Hs := Hclo _ Hp _ Hrow).
        destruct d as [[m ct] | [m ct]]; cbn [MatchDep].
        + exact (proj1 (match_decode _ _ _ _ Hres) Hs).
        + intro HM; cbn [encDep] in Hs.
          exact (Hs (proj2 (match_decode _ _ _ _ Hres) HM)).
      - intros m p q HpS HqS Hp Hq.
        apply mem_alpineResolution in HpS, HqS.
        assert (Hwp : exists w,
                   PF.PkgSet.In (Name.Orig m, w) S' /\
                   ((exists v, p = (m, v) /\ w = Version.Orig v) \/
                    (exists pv, w = Version.Prov p pv))).
        { destruct Hp as [Hp | [pv Hrowp]].
          - destruct p as [np vp]; cbn in Hp; subst np.
            exists (Version.Orig vp); split; [exact HpS |].
            left; exists vp; split; reflexivity.
          - exists (Version.Prov p pv); split.
            + exact (reg_edge _ _ _ _ _ Hres HpS Hrowp).
            + right; exists pv; reflexivity. }
        assert (Hwq : exists w,
                   PF.PkgSet.In (Name.Orig m, w) S' /\
                   ((exists v, q = (m, v) /\ w = Version.Orig v) \/
                    (exists pv, w = Version.Prov q pv))).
        { destruct Hq as [Hq | [pv Hrowq]].
          - destruct q as [nq vq]; cbn in Hq; subst nq.
            exists (Version.Orig vq); split; [exact HqS |].
            left; exists vq; split; reflexivity.
          - exists (Version.Prov q pv); split.
            + exact (reg_edge _ _ _ _ _ Hres HqS Hrowq).
            + right; exists pv; reflexivity. }
        destruct Hwp as [wp [HwpS Hshp]], Hwq as [wq [HwqS Hshq]].
        assert (Hew : wp = wq) by exact (Huniq _ _ _ HwpS HwqS).
        subst wq.
        destruct Hshp as [[vp [-> ->]] | [pv ->]],
            Hshq as [[vq [-> He]] | [pv' He]];
          try discriminate He.
        + injection He as <-; reflexivity.
        + injection He as <- _; reflexivity.
      - intros p conds Hrow0 Hc.
        assert (Hf : FSet.In (trigForm I p conds) (dependees I rootPkg)).
        { cbn [dependees rootPkg]; apply FSet.union_spec; right.
          apply SOtf.mem_map; exists (p, conds); split;
            [exact Hrow0 | reflexivity]. }
        assert (Hrow : PF.DepRel.In (rootPkg, trigForm I p conds)
                         (transD I)).
        { apply mem_transD; split; [apply root_transR | exact Hf]. }
        assert (Hs := Hclo _ Hroot _ Hrow).
        apply satisfies_trigForm in Hs.
        destruct Hs as [[a [Ha Hn]] | Hb].
        + exfalso; apply Hn.
          destruct a as [m ct].
          exact (proj2 (match_decode _ _ _ _ Hres) (Hc _ _ Ha)).
        + exact (proj1 (match_decode _ _ _ _ Hres) Hb).
    Qed.

    (* A package aliasing one name at two versions, or aliasing its own
       name, would put two target versions of that name in the witness
       from a single source claimant; apk metadata declares neither. *)
    Definition WfAlias (I : Inst) : Prop :=
      (forall q n pv pv',
          Prov.In (q, (n, PVer pv)) (inst_prov I) ->
          Prov.In (q, (n, PVer pv')) (inst_prov I) -> pv = pv') /\
      (forall n v pv, ~ Prov.In ((n, v), (n, PVer pv)) (inst_prov I)).

    Lemma match_transS : forall I S n ct,
        PkgSet.Subset S (inst_repo I) ->
        (PF.Satisfies (transS I S) (encPos I n ct) <->
         MatchPos I S n ct).
    Proof.
      intros I S n ct Hsub.
      rewrite satisfies_encPos; split.
      - intros [[w [Hw Hm]] | [Hany [q [Hq Hm]]]].
        + apply mem_constrVers in Hw.
          destruct Hw as
            [[v [_ [Hc ->]]] | [q [pv [Hrow [_ [Hc ->]]]]]].
          * apply mem_transS in Hm.
            destruct Hm as
              [Hm | [[p0 [Hp0 He]] | [q0 [m0 [pv0 [_ [_ He]]]]]]].
            -- discriminate Hm.
            -- destruct p0 as [n0 v0]; injection He as <- <-.
               left; exists v; split; assumption.
            -- injection He as _ He; discriminate He.
          * apply mem_transS in Hm.
            destruct Hm as
              [Hm | [[p0 [_ He]] | [q0 [m0 [pv0 [Hrow0 [Hq0 He]]]]]]].
            -- discriminate Hm.
            -- destruct p0; discriminate He.
            -- injection He as He1 He2 He3; subst m0 q0 pv0.
               right; left; exists q, pv; repeat split; assumption.
        + apply mem_uprovSet in Hq; destruct Hq as [Hrow _].
          apply mem_transS in Hm.
          destruct Hm as
            [Hm | [[p0 [Hp0 He]] | [q0 [m0 [pv0 [_ [_ He]]]]]]].
          * destruct q; discriminate Hm.
          * apply embedPkg_injective in He; subst p0.
            right; right; split; [exact Hany | eauto].
          * destruct q; injection He as _ He; discriminate He.
      - intros [[v [HvS Hc]] |
                [[q [pv [Hrow [HqS Hc]]]] | [Hany [q [Hrow HqS]]]]].
        + left; exists (Version.Orig v); split.
          * apply mem_constrVers; left; exists v.
            repeat split; try assumption.
            exact (Hsub _ HvS).
          * apply mem_transS; right; left; exists (n, v); split;
              [exact HvS | reflexivity].
        + left; exists (Version.Prov q pv); split.
          * apply mem_constrVers; right; exists q, pv.
            repeat split; try assumption.
            exact (Hsub _ HqS).
          * apply mem_transS; right; right; eauto 7.
        + right; split; [exact Hany |].
          exists q; split.
          * apply mem_uprovSet; split; [exact Hrow | exact (Hsub _ HqS)].
          * apply mem_transS; right; left; exists q; split;
              [exact HqS | reflexivity].
    Qed.

    Theorem alpine_completeness : forall I S,
        WfAlias I -> IsResolution I S ->
        PF.IsResolution (transR I) (transD I) rootPkg (transS I S).
    Proof.
      intros I S [Wf1 Wf2] Hres.
      destruct Hres as [Hsub Hw Hd Hcu Ht].
      assert (Hiff := fun n ct => match_transS I S n ct Hsub).
      constructor.
      - intros y Hy; apply mem_transS in Hy; apply mem_transR.
        destruct Hy as [-> | [[p [Hp ->]] | [q [m [pv [Hr [Hq ->]]]]]]].
        + left; reflexivity.
        + right; left; exists p; split; [exact (Hsub _ Hp) | reflexivity].
        + right; right; exists q, m, pv.
          repeat split; try assumption.
          exact (Hsub _ Hq).
      - apply mem_transS; left; reflexivity.
      - intros y Hy f Hrow.
        apply mem_transD in Hrow; destruct Hrow as [HyR Hf].
        apply mem_transS in Hy.
        destruct Hy as [-> | [[p [Hp ->]] | [q [m [pv [Hr [Hq ->]]]]]]].
        + cbn [dependees rootPkg] in Hf.
          apply FSet.union_spec in Hf; destruct Hf as [Hf | Hf].
          * apply SOwf.mem_map in Hf; destruct Hf as [d [Hd0 ->]].
            assert (Hmd := Hw _ Hd0).
            destruct d as [[m ct] | [m ct]]; cbn [MatchDep] in Hmd;
              cbn [encDep].
            -- apply Hiff; exact Hmd.
            -- cbn [PF.Satisfies]; intro Hs; apply Hmd.
               apply Hiff; exact Hs.
          * apply SOtf.mem_map in Hf; destruct Hf as [[p conds] [Ht0 ->]].
            apply satisfies_trigForm.
            destruct (CondSet.exists_
                        (fun a => negb (PF.satisfiesb (transS I S)
                                          (encPos I (fst a) (snd a))))
                        conds) eqn:Ee.
            -- apply CondSet.exists_spec' in Ee.
               destruct Ee as [a [Ha Hb]].
               apply Bool.negb_true_iff in Hb.
               left; exists a; split; [exact Ha |].
               intro Hs; apply PF.satisfiesb_iff in Hs; congruence.
            -- right; apply Hiff, (Ht p conds Ht0).
               intros m ct Hc.
               assert (Hbt : PF.satisfiesb (transS I S)
                               (encPos I m ct) = true).
               { destruct (PF.satisfiesb (transS I S) (encPos I m ct))
                   eqn:Eb; [reflexivity |].
                 exfalso.
                 assert (He : CondSet.exists_
                                (fun a => negb (PF.satisfiesb (transS I S)
                                                  (encPos I (fst a)
                                                     (snd a))))
                                conds = true).
                 { apply CondSet.exists_spec'; exists (m, ct); split;
                     [exact Hc | cbn; rewrite Eb; reflexivity]. }
                 congruence. }
               apply Hiff; apply PF.satisfiesb_iff; exact Hbt.
        + destruct p as [n0 v0].
          cbn [dependees embedPkg fst snd] in Hf.
          apply FSet.union_spec in Hf; destruct Hf as [Hf | Hf].
          * apply SOdf.mem_map in Hf; destruct Hf as [[p' d] [Hin ->]].
            apply DepsFibred.mem_tailFibre in Hin.
            destruct Hin as [Hin ->].
            assert (Hmd := Hd _ _ Hp Hin).
            destruct d as [[m ct] | [m ct]]; cbn [MatchDep] in Hmd;
              cbn [encDep].
            -- apply Hiff; exact Hmd.
            -- cbn [PF.Satisfies]; intro Hs; apply Hmd.
               apply Hiff; exact Hs.
          * apply SOrf.mem_filterMap in Hf.
            destruct Hf as [[p' [m tg]] [Hin Hval]].
            apply ProvFibred.mem_tailFibre in Hin.
            destruct Hin as [Hin ->].
            destruct tg as [pv |]; [| discriminate].
            injection Hval as <-.
            cbn [PF.Satisfies].
            exists (Version.Prov (n0, v0) pv); split.
            -- apply PF.VSet.singleton_spec; reflexivity.
            -- apply mem_transS; right; right.
               exists (n0, v0), m, pv; repeat split; assumption.
        + cbn [dependees] in Hf.
          apply FSet.singleton_spec in Hf; subst f.
          cbn [PF.Satisfies].
          exists (Version.Orig (snd q)); split.
          * apply PF.VSet.singleton_spec; reflexivity.
          * apply mem_transS; right; left; exists q.
            split; [exact Hq |].
            destruct q; reflexivity.
      - intros m w w' H1 H2.
        apply mem_transS in H1, H2.
        destruct m as [| n].
        + destruct H1 as
            [H1 | [[p1 [_ He1]] | [q1 [m1 [pv1 [_ [_ He1]]]]]]];
            [| destruct p1; discriminate He1 | discriminate He1].
          destruct H2 as
            [H2 | [[p2 [_ He2]] | [q2 [m2 [pv2 [_ [_ He2]]]]]]];
            [| destruct p2; discriminate He2 | discriminate He2].
          injection H1 as ->; injection H2 as ->; reflexivity.
        + assert (Hs1 : (exists v, PkgSet.In (n, v) S /\
                           w = Version.Orig v) \/
                        (exists q pv,
                            Prov.In (q, (n, PVer pv)) (inst_prov I) /\
                            PkgSet.In q S /\ w = Version.Prov q pv)).
          { destruct H1 as
              [H1 | [[p1 [Hp1 He1]] | [q1 [m1 [pv1 [Hr1 [Hq1 He1]]]]]]].
            - discriminate H1.
            - destruct p1 as [n1 v1]; injection He1 as <- ->.
              left; exists v1; split; [exact Hp1 | reflexivity].
            - injection He1 as <- ->.
              right; exists q1, pv1; repeat split; assumption. }
          assert (Hs2 : (exists v, PkgSet.In (n, v) S /\
                           w' = Version.Orig v) \/
                        (exists q pv,
                            Prov.In (q, (n, PVer pv)) (inst_prov I) /\
                            PkgSet.In q S /\ w' = Version.Prov q pv)).
          { destruct H2 as
              [H2 | [[p2 [Hp2 He2]] | [q2 [m2 [pv2 [Hr2 [Hq2 He2]]]]]]].
            - discriminate H2.
            - destruct p2 as [n2 v2]; injection He2 as <- ->.
              left; exists v2; split; [exact Hp2 | reflexivity].
            - injection He2 as <- ->.
              right; exists q2, pv2; repeat split; assumption. }
          destruct Hs1 as [[v1 [Hv1 ->]] | [q1 [pv1 [Hr1 [Hq1 ->]]]]],
              Hs2 as [[v2 [Hv2 ->]] | [q2 [pv2 [Hr2 [Hq2 ->]]]]].
          * f_equal.
            assert (He : (n, v1) = (n, v2)).
            { apply (Hcu n (n, v1) (n, v2) Hv1 Hv2);
                left; reflexivity. }
            injection He as He; exact He.
          * exfalso.
            assert (He : (n, v1) = q2).
            { apply (Hcu n (n, v1) q2 Hv1 Hq2);
                [left; reflexivity | right; exists pv2; exact Hr2]. }
            subst q2; exact (Wf2 _ _ _ Hr2).
          * exfalso.
            assert (He : q1 = (n, v2)).
            { apply (Hcu n q1 (n, v2) Hq1 Hv2);
                [right; exists pv1; exact Hr1 | left; reflexivity]. }
            subst q1; exact (Wf2 _ _ _ Hr1).
          * assert (He : q1 = q2).
            { apply (Hcu n q1 q2 Hq1 Hq2);
                [right; exists pv1; exact Hr1
                | right; exists pv2; exact Hr2]. }
            subst q2.
            rewrite (Wf1 _ _ _ _ Hr1 Hr2); reflexivity.
    Qed.

    Module Lookup.
      Lemma or_iff : forall A B C D : Prop,
          (A <-> C) -> (B <-> D) -> (A \/ B <-> C \/ D).
      Proof. tauto. Qed.

      Module NSet := FSetUOT N.
      Module SOdn := SetOps DepElt N Deps NSet.
      Definition depName (d : Dep) : N.t :=
        match d with DPos (n, _) => n | DNeg (n, _) => n end.

      Definition atomNames (I : Inst) (p : Pkg.t) : NSet.t :=
        SOdn.map (fun '(_, d) => depName d)
          (DepsFibred.tailFibre (inst_deps I) p).

      Definition provTouchb (I : Inst) (ns : NSet.t) (q : Pkg.t) : bool :=
        Prov.exists_
          (fun '(q', (m, _)) => andb (PkgEqb.eqb q' q) (NSet.mem m ns))
          (inst_prov I).

      Module PkgPre := Preimage Pkg PkgSet.
      (* A dependee query reads the repository at the mentioned names and
         at their providers, which need not bear those names. *)
      Definition repoSlice (I : Inst) (ns : NSet.t) : PkgSet.t :=
        PkgPre.preimage (fun p => p)
          (fun q => orb (NSet.mem (fst q) ns) (provTouchb I ns q))
          (inst_repo I).

      Module ProvPre := Preimage ProvElt Prov.
      Definition provSlice (I : Inst) (ns : NSet.t) : Prov.t :=
        ProvPre.preimage (fun '(_, (m, _)) => m)
          (fun m => NSet.mem m ns) (inst_prov I).

      Lemma mem_repoSlice : forall I ns q,
          PkgSet.In q (repoSlice I ns) <->
          PkgSet.In q (inst_repo I) /\
          (NSet.In (fst q) ns \/
           exists m tg, Prov.In (q, (m, tg)) (inst_prov I) /\
             NSet.In m ns).
      Proof.
        intros I ns q; unfold repoSlice.
        rewrite PkgPre.mem_preimage, Bool.orb_true_iff.
        apply and_iff_compat_l.
        rewrite NSet.mem_spec; apply or_iff_compat_l.
        unfold provTouchb; rewrite Prov.exists_spec'.
        split.
        - intros [[q' [m tg]] [Hr Hb]]; cbn in Hb.
          apply Bool.andb_true_iff in Hb; destruct Hb as [Hq Hm].
          apply PkgEqb.eqb_true_iff in Hq; subst q'.
          apply NSet.mem_spec in Hm; eauto.
        - intros [m [tg [Hr Hm]]]; exists (q, (m, tg)); split;
            [exact Hr | cbn].
          rewrite (proj2 (PkgEqb.eqb_true_iff q q) eq_refl).
          rewrite (proj2 (NSet.mem_spec _ _) Hm); reflexivity.
      Qed.

      Lemma mem_provSlice : forall I ns e,
          Prov.In e (provSlice I ns) <->
          Prov.In e (inst_prov I) /\ NSet.In (fst (snd e)) ns.
      Proof.
        intros I ns [q [m tg]]; unfold provSlice.
        rewrite ProvPre.mem_preimage, NSet.mem_spec; cbn.
        reflexivity.
      Qed.

      Lemma encPos_agree : forall I I' n ct,
          constrVers I' n ct = constrVers I n ct ->
          uprovSet I' n = uprovSet I n ->
          encPos I' n ct = encPos I n ct.
      Proof.
        intros I I' n ct Hc Hu; unfold encPos, uprovL.
        rewrite Hc, Hu; reflexivity.
      Qed.

      (* Any instance whose repository and provides agree with I at the
         names in ns answers every constraint at those names alike. *)
      Definition sliceInst (I : Inst) (ns : NSet.t) (deps : Deps.t)
          (ownProv : Prov.t) (trig : Trig.t) (world : WSet.t) : Inst :=
        {| inst_repo := repoSlice I ns
         ; inst_deps := deps
         ; inst_prov := Prov.union ownProv (provSlice I ns)
         ; inst_trig := trig
         ; inst_world := world
         ; inst_prio := Prio.empty
         ; inst_repl := Repl.empty |}.

      Lemma constrVers_slice : forall I ns deps ownProv trig world n ct,
          NSet.In n ns ->
          Prov.Subset ownProv (inst_prov I) ->
          constrVers (sliceInst I ns deps ownProv trig world) n ct =
          constrVers I n ct.
      Proof.
        intros I ns deps ownProv trig world n ct Hn Hown.
        apply PF.VSet.ext; intro w.
        rewrite !mem_constrVers; cbn [sliceInst inst_repo inst_prov].
        split.
        - intros [[v [Hrep [Hc ->]]] | [q [pv [Hrow [Hrep [Hc ->]]]]]].
          + apply mem_repoSlice in Hrep; destruct Hrep as [Hrep _].
            left; eauto.
          + apply Prov.union_spec in Hrow.
            assert (Hrow' : Prov.In (q, (n, PVer pv)) (inst_prov I)).
            { destruct Hrow as [Hrow | Hrow]; [exact (Hown _ Hrow) |].
              apply mem_provSlice in Hrow; exact (proj1 Hrow). }
            apply mem_repoSlice in Hrep; destruct Hrep as [Hrep _].
            right; eauto 8.
        - intros [[v [Hrep [Hc ->]]] | [q [pv [Hrow [Hrep [Hc ->]]]]]].
          + left; exists v; repeat split; try assumption.
            apply mem_repoSlice; split; [exact Hrep |].
            left; exact Hn.
          + right; exists q, pv; repeat split; try assumption.
            * apply Prov.union_spec; right.
              apply mem_provSlice; split; [exact Hrow | exact Hn].
            * apply mem_repoSlice; split; [exact Hrep |].
              right; exists n, (PVer pv); split; assumption.
      Qed.

      Lemma uprovSet_slice : forall I ns deps ownProv trig world n,
          NSet.In n ns ->
          Prov.Subset ownProv (inst_prov I) ->
          uprovSet (sliceInst I ns deps ownProv trig world) n =
          uprovSet I n.
      Proof.
        intros I ns deps ownProv trig world n Hn Hown.
        apply PkgSet.ext; intro q.
        rewrite !mem_uprovSet; cbn [sliceInst inst_repo inst_prov].
        split.
        - intros [Hrow Hrep].
          apply Prov.union_spec in Hrow.
          assert (Hrow' : Prov.In (q, (n, PVirt)) (inst_prov I)).
          { destruct Hrow as [Hrow | Hrow]; [exact (Hown _ Hrow) |].
            apply mem_provSlice in Hrow; exact (proj1 Hrow). }
          apply mem_repoSlice in Hrep; destruct Hrep as [Hrep _].
          split; assumption.
        - intros [Hrow Hrep]; split.
          + apply Prov.union_spec; right.
            apply mem_provSlice; split; [exact Hrow | exact Hn].
          + apply mem_repoSlice; split; [exact Hrep |].
            right; exists n, PVirt; split; assumption.
      Qed.

      (* Alias link rows read nothing from the instance. *)
      Theorem dependees_lookupProv : forall I m q pv,
          dependees I (Name.Orig m, Version.Prov q pv) =
          FSet.singleton
            (PF.FDep (Name.Orig (fst q))
               (PF.VSet.singleton (Version.Orig (snd q)))).
      Proof. reflexivity. Qed.

      Definition nameSlice (I : Inst) (n : N.t) : Inst :=
        sliceInst I (NSet.singleton n) Deps.empty Prov.empty
          Trig.empty WSet.empty.

      Theorem versions_lookupName : forall I n,
          versions (nameSlice I n) n = versions I n.
      Proof.
        intros I n; unfold versions, nameSlice.
        apply constrVers_slice.
        - apply NSet.singleton_spec; reflexivity.
        - intros e He; destruct (Prov.empty_spec He).
      Qed.

      Definition pkgSlice (I : Inst) (p : Pkg.t) : Inst :=
        sliceInst I (atomNames I p)
          (DepsFibred.tailFibre (inst_deps I) p)
          (ProvFibred.tailFibre (inst_prov I) p)
          Trig.empty WSet.empty.

      Theorem dependees_lookupOrig : forall I n v,
          dependees (pkgSlice I (n, v)) (embedPkg (n, v)) =
          dependees I (embedPkg (n, v)).
      Proof.
        intros I n v.
        apply FSet.ext; intro f.
        cbn [dependees embedPkg fst snd pkgSlice sliceInst
             inst_deps inst_prov].
        rewrite !FSet.union_spec, !SOdf.mem_map, !SOrf.mem_filterMap.
        apply or_iff.
        - split.
          + intros [[p' d] [Hin ->]].
            apply DepsFibred.mem_tailFibre in Hin.
            destruct Hin as [Hin ->].
            exists ((n, v), d); split; [exact Hin |].
            assert (Hns : NSet.In (depName d) (atomNames I (n, v))).
            { apply SOdn.mem_map; exists ((n, v), d); split;
                [exact Hin | reflexivity]. }
            destruct d as [[m ct] | [m ct]]; cbn [encDep depName] in *;
              [| f_equal];
              (apply encPos_agree;
               [ apply constrVers_slice;
                 [exact Hns | apply ProvFibred.tailFibre_subset]
               | apply uprovSet_slice;
                 [exact Hns | apply ProvFibred.tailFibre_subset] ]).
          + intros [[p' d] [Hin ->]].
            apply DepsFibred.mem_tailFibre in Hin.
            destruct Hin as [Hin ->].
            assert (Hfib : Deps.In ((n, v), d)
                             (DepsFibred.tailFibre (inst_deps I) (n, v))).
            { apply DepsFibred.mem_tailFibre; split;
                [exact Hin | reflexivity]. }
            assert (Hns : NSet.In (depName d) (atomNames I (n, v))).
            { apply SOdn.mem_map; exists ((n, v), d); split;
                [exact Hfib | reflexivity]. }
            exists ((n, v), d); split.
            { apply DepsFibred.mem_tailFibre; split;
                [exact Hfib | reflexivity]. }
            destruct d as [[m ct] | [m ct]]; cbn [encDep depName] in *;
              [| f_equal]; symmetry;
              (apply encPos_agree;
               [ apply constrVers_slice;
                 [exact Hns | apply ProvFibred.tailFibre_subset]
               | apply uprovSet_slice;
                 [exact Hns | apply ProvFibred.tailFibre_subset] ]).
        - split.
          + intros [[p' [m tg]] [Hin Hv]].
            apply ProvFibred.mem_tailFibre in Hin.
            destruct Hin as [Hin ->].
            apply Prov.union_spec in Hin.
            assert (Hin' : Prov.In ((n, v), (m, tg)) (inst_prov I)).
            { destruct Hin as [Hin | Hin].
              - apply ProvFibred.mem_tailFibre in Hin;
                  exact (proj1 Hin).
              - apply mem_provSlice in Hin; exact (proj1 Hin). }
            exists ((n, v), (m, tg)); split; [| exact Hv].
            apply ProvFibred.mem_tailFibre; split;
              [exact Hin' | reflexivity].
          + intros [[p' [m tg]] [Hin Hv]].
            apply ProvFibred.mem_tailFibre in Hin.
            destruct Hin as [Hin ->].
            exists ((n, v), (m, tg)); split; [| exact Hv].
            apply ProvFibred.mem_tailFibre; split; [| reflexivity].
            apply Prov.union_spec; left.
            apply ProvFibred.mem_tailFibre; split;
              [exact Hin | reflexivity].
      Qed.

      Module SOwn := SetOps DepOT N WSet NSet.
      Module SOan := SetOps Atom N CondSet NSet.
      Module SOtn := SetOps TrigElt N Trig NSet.

      Definition condNames (conds : CondSet.t) : NSet.t :=
        SOan.map fst conds.

      (* The root's dependees read the world set at its dependency names
         and each trigger row at its own name and its condition names. *)
      Definition rootNames (I : Inst) : NSet.t :=
        NSet.union (SOwn.map depName (inst_world I))
          (SOtn.unionMap
             (fun '(p, conds) => NSet.add (fst p) (condNames conds))
             (inst_trig I)).

      Lemma world_rootNames : forall I d,
          WSet.In d (inst_world I) -> NSet.In (depName d) (rootNames I).
      Proof.
        intros I d Hd; unfold rootNames; apply NSet.union_spec; left.
        apply SOwn.mem_map; exists d; split; [exact Hd | reflexivity].
      Qed.

      Lemma trigSelf_rootNames : forall I p conds,
          Trig.In (p, conds) (inst_trig I) ->
          NSet.In (fst p) (rootNames I).
      Proof.
        intros I p conds Ht; unfold rootNames; apply NSet.union_spec; right.
        apply SOtn.mem_unionMap; exists (p, conds); split; [exact Ht |].
        cbv beta iota; apply NSet.add_spec; left; reflexivity.
      Qed.

      Lemma trigCond_rootNames : forall I p conds a,
          Trig.In (p, conds) (inst_trig I) -> CondSet.In a conds ->
          NSet.In (fst a) (rootNames I).
      Proof.
        intros I p conds a Ht Ha; unfold rootNames.
        apply NSet.union_spec; right.
        apply SOtn.mem_unionMap; exists (p, conds); split; [exact Ht |].
        cbv beta iota; apply NSet.add_spec; right.
        unfold condNames; apply SOan.mem_map; exists a; split;
          [exact Ha | reflexivity].
      Qed.

      Lemma encPos_slice : forall I ns deps ownProv trig world
              (n : N.t) (ct : Constr),
          NSet.In n ns ->
          Prov.Subset ownProv (inst_prov I) ->
          encPos (sliceInst I ns deps ownProv trig world) n ct =
          encPos I n ct.
      Proof.
        intros I ns deps ownProv trig world n ct Hn Hown.
        apply encPos_agree.
        - apply constrVers_slice; assumption.
        - apply uprovSet_slice; assumption.
      Qed.

      Lemma encDep_slice : forall I ns deps ownProv trig world d,
          NSet.In (depName d) ns ->
          Prov.Subset ownProv (inst_prov I) ->
          encDep (sliceInst I ns deps ownProv trig world) d = encDep I d.
      Proof.
        intros I ns deps ownProv trig world [[m ct] | [m ct]] Hn Hown;
          cbn [encDep depName] in *; [| f_equal];
          apply encPos_slice; assumption.
      Qed.

      (* The condition fold is a congruence in encPos: only the atoms the
         set lists are read, so agreement there transports the formula. *)
      Lemma negFold_agree : forall I I' l base,
          (forall a, List.In a l ->
             encPos I' (fst a) (snd a) = encPos I (fst a) (snd a)) ->
          fold_right
            (fun a f => PF.FDisj (PF.FNeg (encPos I' (fst a) (snd a))) f)
            base l =
          fold_right
            (fun a f => PF.FDisj (PF.FNeg (encPos I (fst a) (snd a))) f)
            base l.
      Proof.
        intros I I' l base H; induction l as [| a l IH]; cbn.
        - reflexivity.
        - rewrite (H a (or_introl eq_refl)), IH; [reflexivity |].
          intros b Hb; apply H; right; exact Hb.
      Qed.

      Lemma trigForm_slice : forall I ns deps ownProv trig world
              (p : Pkg.t) (conds : CondSet.t),
          NSet.In (fst p) ns ->
          (forall a : Atom.t, CondSet.In a conds -> NSet.In (fst a) ns) ->
          Prov.Subset ownProv (inst_prov I) ->
          trigForm (sliceInst I ns deps ownProv trig world) p conds =
          trigForm I p conds.
      Proof.
        intros I ns deps ownProv trig world p conds Hp Hc Hown.
        unfold trigForm.
        rewrite (encPos_slice I ns deps ownProv trig world (fst p) CAny
                   Hp Hown).
        apply negFold_agree; intros a Ha.
        apply in_elements_cond in Ha.
        apply encPos_slice; [exact (Hc _ Ha) | exact Hown].
      Qed.

      Definition rootSlice (I : Inst) : Inst :=
        sliceInst I (rootNames I) Deps.empty Prov.empty
          (inst_trig I) (inst_world I).

      Lemma rootSlice_world : forall I,
          inst_world (rootSlice I) = inst_world I.
      Proof. reflexivity. Qed.

      Lemma rootSlice_trig : forall I,
          inst_trig (rootSlice I) = inst_trig I.
      Proof. reflexivity. Qed.

      Theorem dependees_lookupRoot : forall I,
          dependees (rootSlice I) rootPkg = dependees I rootPkg.
      Proof.
        intro I.
        assert (Hown : Prov.Subset Prov.empty (inst_prov I)).
        { intros e He; destruct (Prov.empty_spec He). }
        cbn [dependees rootPkg].
        rewrite rootSlice_world, rootSlice_trig.
        f_equal.
        - apply FSet.ext; intro f; rewrite !SOwf.mem_map.
          split; intros [d [Hd ->]]; exists d; split; try exact Hd;
            [| symmetry]; unfold rootSlice;
            apply encDep_slice;
            [ exact (world_rootNames I d Hd) | exact Hown
            | exact (world_rootNames I d Hd) | exact Hown ].
        - apply FSet.ext; intro f; rewrite !SOtf.mem_map.
          split; intros [[p conds] [Ht Hf]]; exists (p, conds);
            split; try exact Ht; cbv beta iota in Hf |- *; subst f;
            [| symmetry]; unfold rootSlice;
            apply trigForm_slice; try exact Hown;
            [ exact (trigSelf_rootNames I p conds Ht)
            | intros a Ha; exact (trigCond_rootNames I p conds a Ht Ha)
            | exact (trigSelf_rootNames I p conds Ht)
            | intros a Ha; exact (trigCond_rootNames I p conds a Ht Ha) ].
      Qed.
    End Lookup.
  End Reduction.
End Alpine.
