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

  Module CondSet := FSetUOT DepOT.
  Module InstallIfElt := PairUOT Pkg CondSet.AsUOT.
  Module InstallIf := FSetUOT InstallIfElt.

  Module WSet := FSetUOT DepOT.

  Module PrioElt := PairUOT Pkg Nat_as_OT.
  Module Prio := FSetUOT PrioElt.
  Module ReplElt := PairUOT Pkg N.
  Module Repl := FSetUOT ReplElt.

  (* replaces steers file ownership and constrains nothing here.
     provider_priority steers apk's preference among providers by its
     value, and constrains resolutions only by whether it is non-zero:
     see AutoSelectable. *)
  Record Inst : Type :=
    { inst_repo : PkgSet.t
    ; inst_deps : Deps.t
    ; inst_prov : Prov.t
    ; inst_installIf : InstallIf.t
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

  Definition HasPriority (I : Inst) (q : Pkg.t) : Prop :=
    exists k, Prio.In (q, k) (inst_prio I) /\ k <> 0.

  (* apk-package(5): a provides without a version is selected
     automatically only for a provider_priority, "otherwise user is
     expected to manually select one of the concrete package names in
     world". *)
  Definition AutoSelectable (I : Inst) (q : Pkg.t) : Prop :=
    HasPriority I q \/ exists ct, WSet.In (DPos (fst q, ct)) (inst_world I).

  Definition MatchReq (I : Inst) (S : PkgSet.t)
      (n : N.t) (ct : Constr) : Prop :=
    (exists v, PkgSet.In (n, v) S /\ constrMatch ct v = true) \/
    (exists q pv, Prov.In (q, (n, PVer pv)) (inst_prov I) /\
       PkgSet.In q S /\ constrMatch ct pv = true) \/
    (isAny ct = true /\
     exists q, Prov.In (q, (n, PVirt)) (inst_prov I) /\ PkgSet.In q S /\
       AutoSelectable I q).

  Definition MatchDep (I : Inst) (S : PkgSet.t) (d : Dep) : Prop :=
    match d with
    | DPos (n, ct) => MatchReq I S n ct
    | DNeg (n, ct) => ~ MatchPos I S n ct
    end.

  (* apk tests an install_if condition against whichever package holds
     its name, selectable or not, so both signs read MatchPos. *)
  Definition MatchCond (I : Inst) (S : PkgSet.t) (c : Dep) : Prop :=
    match c with
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
    ; res_installIf :
        forall p conds, InstallIf.In (p, conds) (inst_installIf I) ->
        (forall c, CondSet.In c conds -> MatchCond I S c) ->
        MatchPos I S (fst p) CAny }.

  (* Only a positive condition can be designated: a rule is carried by a
     package satisfying its designated condition, and absence is
     satisfied by no package. *)
  Module Type Designation.
    Parameter designation : CondSet.t -> option Atom.t.
    Parameter designation_spec : forall conds : CondSet.t,
        (exists a, CondSet.In (DPos a) conds) ->
        exists a, designation conds = Some a /\ CondSet.In (DPos a) conds.
  End Designation.

  Module LeastDesignation <: Designation.
    Fixpoint firstPos (l : list Dep) : option Atom.t :=
      match l with
      | nil => None
      | DPos a :: _ => Some a
      | DNeg _ :: l' => firstPos l'
      end.

    Lemma firstPos_spec : forall l,
        (exists a, List.In (DPos a) l) ->
        exists a, firstPos l = Some a /\ List.In (DPos a) l.
    Proof.
      induction l as [| d l IH]; intros [a Ha]; [destruct Ha |].
      destruct d as [b | b]; cbn [firstPos].
      - exists b; split; [reflexivity | left; reflexivity].
      - destruct Ha as [He | Ha]; [discriminate He |].
        destruct (IH (ex_intro _ a Ha)) as [a' [E H]].
        exists a'; split; [exact E | right; exact H].
    Qed.

    Definition designation (conds : CondSet.t) : option Atom.t :=
      firstPos (CondSet.elements conds).

    Lemma in_elements : forall s d,
        List.In d (CondSet.elements s) <-> CondSet.In d s.
    Proof.
      intros s d; rewrite <- (CondSet.elements_spec1 s d).
      rewrite InA_alt; split.
      - intro H; exists d; split; reflexivity + assumption.
      - intros [y [-> Hy]]; exact Hy.
    Qed.

    Lemma designation_spec : forall conds : CondSet.t,
        (exists a, CondSet.In (DPos a) conds) ->
        exists a, designation conds = Some a /\ CondSet.In (DPos a) conds.
    Proof.
      intros conds [a Ha]; unfold designation.
      destruct (firstPos_spec (CondSet.elements conds)
                  (ex_intro _ a (proj2 (in_elements _ _) Ha)))
        as [a' [E H]].
      exists a'; split; [exact E | apply in_elements; exact H].
    Qed.
  End LeastDesignation.

  Module Reduct (D : Designation).
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

    Definition hasPriorityb (I : Inst) (q : Pkg.t) : bool :=
      Prio.exists_
        (fun '(q', k) => andb (PkgEqb.eqb q' q) (negb (Nat.eqb k 0)))
        (inst_prio I).

    Definition worldNamesb (I : Inst) (m : N.t) : bool :=
      WSet.exists_
        (fun d => match d with
                  | DPos (m', _) => NEqb.eqb m' m
                  | DNeg _ => false
                  end)
        (inst_world I).

    Definition selectableb (I : Inst) (q : Pkg.t) : bool :=
      orb (hasPriorityb I q) (worldNamesb I (fst q)).

    Definition encReq (I : Inst) (n : N.t) (ct : Constr) : PF.Formula :=
      let base := PF.FDep (Name.Orig n) (constrVers I n ct) in
      if isAny ct
      then
        fold_right
          (fun q f =>
             PF.FDisj
               (PF.FDep (Name.Orig (fst q))
                  (PF.VSet.singleton (Version.Orig (snd q)))) f)
          base (List.filter (selectableb I) (uprovL I n))
      else base.

    Definition encDep (I : Inst) (d : Dep) : PF.Formula :=
      match d with
      | DPos (n, ct) => encReq I n ct
      | DNeg (n, ct) => PF.FNeg (encPos I n ct)
      end.

    Definition attachAt (I : Inst) (p : Pkg.t) (a : Atom.t) : bool :=
      orb (andb (NEqb.eqb (fst p) (fst a)) (constrMatch (snd a) (snd p)))
        (Prov.exists_
           (fun '(q, (m, tg)) =>
              andb (PkgEqb.eqb q p)
                (andb (NEqb.eqb m (fst a))
                   (match tg with
                    | PVer pv => constrMatch (snd a) pv
                    | PVirt => isAny (snd a)
                    end)))
           (inst_prov I)).

    Definition condRest (conds : CondSet.t) : CondSet.t :=
      match D.designation conds with
      | Some a => CondSet.remove (DPos a) conds
      | None => conds
      end.

    Definition attachDesignation (I : Inst) (p : Pkg.t)
        (conds : CondSet.t) : bool :=
      match D.designation conds with
      | Some a => attachAt I p a
      | None => false
      end.

    Definition installIfFibre (I : Inst) (p : Pkg.t) : InstallIf.t :=
      InstallIf.filter (fun '(_, conds) => attachDesignation I p conds)
        (inst_installIf I).

    (* installIfForm negates every condition, so a negated one is
       negated twice; the package-formula encoder cancels the pair, and
       the alternative it leaves is the atom being present. *)
    Definition encCond (I : Inst) (c : Dep) : PF.Formula :=
      match c with
      | DPos (n, ct) => encPos I n ct
      | DNeg (n, ct) => PF.FNeg (encPos I n ct)
      end.

    Definition installIfForm (I : Inst) (z : Pkg.t) (conds : CondSet.t) :
        PF.Formula :=
      fold_right
        (fun c f => PF.FDisj (PF.FNeg (encCond I c)) f)
        (encPos I (fst z) CAny) (CondSet.elements (condRest conds)).

    Definition rootPkg : PF.Pkg.t := (Name.Root, Version.RootV).

    Module FSet := FSetUOT PF.FOT.
    Module SOdf := SetOps DepElt PF.FOT Deps FSet.
    Module SOrf := SetOps ProvElt PF.FOT Prov FSet.
    Module SOtf := SetOps InstallIfElt PF.FOT InstallIf FSet.
    Module SOwf := SetOps DepOT PF.FOT WSet FSet.
    Definition dependees (I : Inst) (q : PF.Pkg.t) : FSet.t :=
      match q with
      | (Name.Root, Version.RootV) => SOwf.map (encDep I) (inst_world I)
      | (Name.Orig n, Version.Orig v) =>
          FSet.union
            (SOdf.map (fun '(_, d) => encDep I d)
               (DepsFibred.tailFibre (inst_deps I) (n, v)))
            (FSet.union
               (SOrf.filterMap
                  (fun '(_, (m, tg)) =>
                     match tg with
                     | PVer pv =>
                         Some (PF.FDep (Name.Orig m)
                                 (PF.VSet.singleton
                                    (Version.Prov (n, v) pv)))
                     | PVirt => None
                     end)
                  (ProvFibred.tailFibre (inst_prov I) (n, v)))
               (SOtf.map (fun '(z, conds) => installIfForm I z conds)
                  (installIfFibre I (n, v))))
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

    Lemma attachAt_spec : forall I p a,
        attachAt I p a = true <->
        (fst p = fst a /\ constrMatch (snd a) (snd p) = true) \/
        (exists pv, Prov.In (p, (fst a, PVer pv)) (inst_prov I) /\
           constrMatch (snd a) pv = true) \/
        (isAny (snd a) = true /\
         Prov.In (p, (fst a, PVirt)) (inst_prov I)).
    Proof.
      intros I p a; unfold attachAt.
      rewrite Bool.orb_true_iff, Bool.andb_true_iff, NEqb.eqb_true_iff.
      rewrite Prov.exists_spec'.
      apply or_iff_compat_l.
      split.
      - intros [[q [m tg]] [Hr Hb]]; cbn in Hb.
        apply Bool.andb_true_iff in Hb; destruct Hb as [Hq Hb].
        apply PkgEqb.eqb_true_iff in Hq; subst q.
        apply Bool.andb_true_iff in Hb; destruct Hb as [Hm Hb].
        apply NEqb.eqb_true_iff in Hm; subst m.
        destruct tg as [pv |]; [left; eauto | right; eauto].
      - intros [[pv [Hr Hc]] | [Hany Hr]].
        + exists (p, (fst a, PVer pv)); split; [exact Hr | cbn].
          rewrite (proj2 (PkgEqb.eqb_true_iff p p) eq_refl).
          rewrite (proj2 (NEqb.eqb_true_iff (fst a) (fst a)) eq_refl).
          rewrite Hc; reflexivity.
        + exists (p, (fst a, PVirt)); split; [exact Hr | cbn].
          rewrite (proj2 (PkgEqb.eqb_true_iff p p) eq_refl).
          rewrite (proj2 (NEqb.eqb_true_iff (fst a) (fst a)) eq_refl).
          rewrite Hany; reflexivity.
    Qed.

    Lemma matchPos_attachAt : forall I S n ct,
        MatchPos I S n ct <->
        exists p, PkgSet.In p S /\ attachAt I p (n, ct) = true.
    Proof.
      intros I S n ct; unfold MatchPos; split.
      - intros [[v [Hv Hc]] |
                [[q [pv [Hr [Hq Hc]]]] | [Hany [q [Hr Hq]]]]].
        + exists (n, v); split; [exact Hv |].
          apply attachAt_spec; left; split; [reflexivity | exact Hc].
        + exists q; split; [exact Hq |].
          apply attachAt_spec; right; left; exists pv; split; assumption.
        + exists q; split; [exact Hq |].
          apply attachAt_spec; right; right; split; assumption.
      - intros [p [Hp Ha]]; apply attachAt_spec in Ha; cbn in Ha.
        destruct Ha as [[Hn Hc] | [[pv [Hr Hc]] | [Hany Hr]]].
        + left; exists (snd p); split; [| exact Hc].
          destruct p as [np vp]; cbn in Hn |- *; subst np; exact Hp.
        + right; left; exists p, pv; repeat split; assumption.
        + right; right; split; [exact Hany | exists p; split; assumption].
    Qed.

    Lemma mem_installIfFibre : forall I p z conds,
        InstallIf.In (z, conds) (installIfFibre I p) <->
        InstallIf.In (z, conds) (inst_installIf I) /\
        attachDesignation I p conds = true.
    Proof.
      intros I p z conds; unfold installIfFibre.
      rewrite InstallIf.filter_spec'; reflexivity.
    Qed.

    Lemma condRest_subset : forall conds a,
        CondSet.In a (condRest conds) -> CondSet.In a conds.
    Proof.
      intros conds a; unfold condRest.
      destruct (D.designation conds) as [b |]; [| exact (fun H => H)].
      intro H; apply CondSet.remove_spec in H; exact (proj1 H).
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

    Lemma in_elements_cond : forall s c,
        List.In c (CondSet.elements s) <-> CondSet.In c s.
    Proof. exact LeastDesignation.in_elements. Qed.

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

    Lemma satisfies_encReq : forall I S' n ct,
        PF.Satisfies S' (encReq I n ct) <->
        (exists w, PF.VSet.In w (constrVers I n ct) /\
           PF.PkgSet.In (Name.Orig n, w) S') \/
        (isAny ct = true /\
         exists q, PkgSet.In q (uprovSet I n) /\ selectableb I q = true /\
           PF.PkgSet.In (embedPkg q) S').
    Proof.
      intros I S' n ct; unfold encReq; cbv zeta.
      destruct (isAny ct) eqn:Ea.
      - rewrite satisfies_disjFold; cbn [PF.Satisfies].
        apply or_iff_compat_l; split.
        + intros [q [Hq Hm]]; apply filter_In in Hq; destruct Hq as [Hq Hs].
          split; [reflexivity |]; exists q.
          split; [apply in_elements_pkg; exact Hq | split; assumption].
        + intros [_ [q [Hq [Hs Hm]]]]; exists q; split; [| exact Hm].
          apply filter_In; split; [apply in_elements_pkg; exact Hq | exact Hs].
      - cbn [PF.Satisfies]; split; [intro H; left; exact H |].
        intros [H | [Hany _]]; [exact H | discriminate Hany].
    Qed.

    Lemma hasPriorityb_spec : forall I q,
        hasPriorityb I q = true <-> HasPriority I q.
    Proof.
      intros I q; unfold hasPriorityb, HasPriority; rewrite Prio.exists_spec'.
      split.
      - intros [[q' k] [Hin Hb]]; cbn in Hb.
        apply Bool.andb_true_iff in Hb; destruct Hb as [Hq Hk].
        apply PkgEqb.eqb_true_iff in Hq; subst q'.
        exists k; split; [exact Hin |].
        intro Hk0; subst k; discriminate Hk.
      - intros [k [Hin Hk]]; exists (q, k); split; [exact Hin | cbn].
        rewrite (proj2 (PkgEqb.eqb_true_iff q q) eq_refl).
        destruct k; [contradiction | reflexivity].
    Qed.

    Lemma selectableb_spec : forall I q,
        selectableb I q = true <-> AutoSelectable I q.
    Proof.
      intros I q; unfold selectableb, AutoSelectable.
      rewrite Bool.orb_true_iff, hasPriorityb_spec.
      apply or_iff_compat_l.
      unfold worldNamesb; rewrite WSet.exists_spec'; split.
      - intros [[[m ct] | [m ct]] [Hd Hb]]; cbn in Hb; [| discriminate].
        apply NEqb.eqb_true_iff in Hb; subst m; exists ct; exact Hd.
      - intros [ct Hd]; exists (DPos (fst q, ct)); split; [exact Hd | cbn].
        apply NEqb.eqb_true_iff; reflexivity.
    Qed.

    Lemma satisfies_negFold : forall I S' l (base : PF.Formula),
        PF.Satisfies S'
          (fold_right
             (fun c f => PF.FDisj (PF.FNeg (encCond I c)) f)
             base l) <->
        (exists c, List.In c l /\ ~ PF.Satisfies S' (encCond I c)) \/
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

    Lemma satisfies_installIfForm : forall I S' z conds,
        PF.Satisfies S' (installIfForm I z conds) <->
        (exists c, CondSet.In c (condRest conds) /\
           ~ PF.Satisfies S' (encCond I c)) \/
        PF.Satisfies S' (encPos I (fst z) CAny).
    Proof.
      intros I S' z conds; unfold installIfForm.
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
      destruct Ht as [Ht | [[p0 [_ He]] | [q0 [m0 [pv0 [Hprov [_ He]]]]]]].
      - discriminate Ht.
      - destruct p0; discriminate He.
      - injection He as He1 He2 He3; subst m0 q0 pv0.
        split; [exact Hprov |].
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
      intros I S' [n v] m pv [Hsub Hroot Hclo Huniq] HpS Hprov.
      assert (Hf : FSet.In
                     (PF.FDep (Name.Orig m)
                        (PF.VSet.singleton (Version.Prov (n, v) pv)))
                     (dependees I (embedPkg (n, v)))).
      { cbn [dependees embedPkg fst snd]; apply FSet.union_spec; right.
        apply FSet.union_spec; left.
        apply SOrf.mem_filterMap.
        exists ((n, v), (m, PVer pv)); split; [| reflexivity].
        apply ProvFibred.mem_tailFibre; split; [exact Hprov | reflexivity]. }
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
            [[v [Hrep [Hc ->]]] | [q [pv [Hprov [Hrep [Hc ->]]]]]].
          * left; exists v; split; [| exact Hc].
            apply mem_alpineResolution; exact Hm.
          * right; left; exists q, pv.
            destruct (prov_selected _ _ _ _ _ Hres Hm) as [_ HqS'].
            repeat split; try assumption.
            apply mem_alpineResolution; exact HqS'.
        + right; right; split; [exact Hany |].
          apply mem_uprovSet in Hq; destruct Hq as [Hprov _].
          exists q; split; [exact Hprov |].
          apply mem_alpineResolution; exact Hm.
      - intros [[v [HvS Hc]] |
                [[q [pv [Hprov [HqS Hc]]]] | [Hany [q [Hprov HqS]]]]].
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
          * exact (reg_edge _ _ _ _ _ Hres HqS Hprov).
        + apply mem_alpineResolution in HqS.
          right; split; [exact Hany |].
          exists q; split; [| exact HqS].
          apply mem_uprovSet; split; [exact Hprov |].
          exact (embed_transR _ _ (Hsub _ HqS)).
    Qed.

    Lemma base_decode : forall I S' n ct,
        PF.IsResolution (transR I) (transD I) rootPkg S' ->
        ((exists w, PF.VSet.In w (constrVers I n ct) /\
            PF.PkgSet.In (Name.Orig n, w) S') <->
         (exists v, PkgSet.In (n, v) (alpineResolution S') /\
            constrMatch ct v = true) \/
         (exists q pv, Prov.In (q, (n, PVer pv)) (inst_prov I) /\
            PkgSet.In q (alpineResolution S') /\ constrMatch ct pv = true)).
    Proof.
      intros I S' n ct Hres.
      assert (Hsub := PF.res_subset _ _ _ _ Hres).
      split.
      - intros [w [Hw Hm]].
        apply mem_constrVers in Hw.
        destruct Hw as
          [[v [Hrep [Hc ->]]] | [q [pv [Hprov [Hrep [Hc ->]]]]]].
        + left; exists v; split; [| exact Hc].
          apply mem_alpineResolution; exact Hm.
        + right; exists q, pv.
          destruct (prov_selected _ _ _ _ _ Hres Hm) as [_ HqS'].
          repeat split; try assumption.
          apply mem_alpineResolution; exact HqS'.
      - intros [[v [HvS Hc]] | [q [pv [Hprov [HqS Hc]]]]].
        + apply mem_alpineResolution in HvS.
          exists (Version.Orig v); split; [| exact HvS].
          apply mem_constrVers; left; exists v.
          repeat split; try assumption.
          exact (embed_transR _ _ (Hsub _ HvS)).
        + apply mem_alpineResolution in HqS.
          exists (Version.Prov q pv); split.
          * apply mem_constrVers; right; exists q, pv.
            repeat split; try assumption.
            exact (embed_transR _ _ (Hsub _ HqS)).
          * exact (reg_edge _ _ _ _ _ Hres HqS Hprov).
    Qed.

    Lemma match_req_decode : forall I S' n ct,
        PF.IsResolution (transR I) (transD I) rootPkg S' ->
        (PF.Satisfies S' (encReq I n ct) <->
         MatchReq I (alpineResolution S') n ct).
    Proof.
      intros I S' n ct Hres.
      assert (Hsub := PF.res_subset _ _ _ _ Hres).
      rewrite satisfies_encReq, (base_decode I S' n ct Hres).
      unfold MatchReq; rewrite or_assoc.
      apply or_iff_compat_l, or_iff_compat_l, and_iff_compat_l; split.
      - intros [q [Hq [Hs Hm]]]; apply mem_uprovSet in Hq.
        exists q; split; [exact (proj1 Hq) |].
        split; [apply mem_alpineResolution; exact Hm |].
        apply selectableb_spec; exact Hs.
      - intros [q [Hp [HqS Ha]]]; exists q.
        apply mem_alpineResolution in HqS.
        split; [apply mem_uprovSet; split;
                [exact Hp | exact (embed_transR _ _ (Hsub _ HqS))] |].
        split; [apply selectableb_spec; exact Ha | exact HqS].
    Qed.

    Lemma cond_decode : forall I S' c,
        PF.IsResolution (transR I) (transD I) rootPkg S' ->
        (PF.Satisfies S' (encCond I c) <->
         MatchCond I (alpineResolution S') c).
    Proof.
      intros I S' [[n ct] | [n ct]] Hres;
        cbn [encCond MatchCond PF.Satisfies];
        rewrite (match_decode I S' n ct Hres); reflexivity.
    Qed.

    (* A rule with no positive condition has nothing to designate, so the
       obligation res_installIf states of it would have nothing to carry
       it.  apk never fires such a rule: its changeset reaches a rule only
       from an installed package bearing or providing a condition's name,
       and for a negated condition that package falsifies it. *)
    Definition WfInstallIf (I : Inst) : Prop :=
      forall z conds, InstallIf.In (z, conds) (inst_installIf I) ->
      exists a, CondSet.In (DPos a) conds.

    Theorem alpine_soundness : forall I S',
        WfInstallIf I ->
        PF.IsResolution (transR I) (transD I) rootPkg S' ->
        IsResolution I (alpineResolution S').
    Proof.
      intros I S' Hwf Hres.
      assert (Hres' := Hres); destruct Hres' as [Hsub Hroot Hclo Huniq].
      constructor.
      - intros p Hp; apply mem_alpineResolution in Hp.
        exact (embed_transR _ _ (Hsub _ Hp)).
      - intros d Hd.
        assert (Hf : FSet.In (encDep I d) (dependees I rootPkg)).
        { cbn [dependees rootPkg].
          apply SOwf.mem_map; exists d; split; [exact Hd | reflexivity]. }
        assert (Hdep : PF.DepRel.In (rootPkg, encDep I d) (transD I)).
        { apply mem_transD; split; [apply root_transR | exact Hf]. }
        assert (Hs := Hclo _ Hroot _ Hdep).
        destruct d as [[m ct] | [m ct]]; cbn [MatchDep].
        + exact (proj1 (match_req_decode _ _ _ _ Hres) Hs).
        + intro HM; cbn [encDep] in Hs.
          exact (Hs (proj2 (match_decode _ _ _ _ Hres) HM)).
      - intros p d Hp Hdep0; apply mem_alpineResolution in Hp.
        destruct p as [np vp].
        assert (Hf : FSet.In (encDep I d)
                       (dependees I (embedPkg (np, vp)))).
        { cbn [dependees embedPkg fst snd]; apply FSet.union_spec; left.
          apply SOdf.mem_map; exists ((np, vp), d); split; [| reflexivity].
          apply DepsFibred.mem_tailFibre; split; [exact Hdep0 | reflexivity]. }
        assert (Hdep : PF.DepRel.In (embedPkg (np, vp), encDep I d)
                         (transD I)).
        { apply mem_transD; split; [apply Hsub; exact Hp | exact Hf]. }
        assert (Hs := Hclo _ Hp _ Hdep).
        destruct d as [[m ct] | [m ct]]; cbn [MatchDep].
        + exact (proj1 (match_req_decode _ _ _ _ Hres) Hs).
        + intro HM; cbn [encDep] in Hs.
          exact (Hs (proj2 (match_decode _ _ _ _ Hres) HM)).
      - intros m p q HpS HqS Hp Hq.
        apply mem_alpineResolution in HpS, HqS.
        assert (Hwp : exists w,
                   PF.PkgSet.In (Name.Orig m, w) S' /\
                   ((exists v, p = (m, v) /\ w = Version.Orig v) \/
                    (exists pv, w = Version.Prov p pv))).
        { destruct Hp as [Hp | [pv Hprovp]].
          - destruct p as [np vp]; cbn in Hp; subst np.
            exists (Version.Orig vp); split; [exact HpS |].
            left; exists vp; split; reflexivity.
          - exists (Version.Prov p pv); split.
            + exact (reg_edge _ _ _ _ _ Hres HpS Hprovp).
            + right; exists pv; reflexivity. }
        assert (Hwq : exists w,
                   PF.PkgSet.In (Name.Orig m, w) S' /\
                   ((exists v, q = (m, v) /\ w = Version.Orig v) \/
                    (exists pv, w = Version.Prov q pv))).
        { destruct Hq as [Hq | [pv Hprovq]].
          - destruct q as [nq vq]; cbn in Hq; subst nq.
            exists (Version.Orig vq); split; [exact HqS |].
            left; exists vq; split; reflexivity.
          - exists (Version.Prov q pv); split.
            + exact (reg_edge _ _ _ _ _ Hres HqS Hprovq).
            + right; exists pv; reflexivity. }
        destruct Hwp as [wp [HwpS Hshp]], Hwq as [wq [HwqS Hshq]].
        assert (Hew : wp = wq) by exact (Huniq _ _ _ HwpS HwqS).
        subst wq.
        destruct Hshp as [[vp [-> ->]] | [pv ->]],
            Hshq as [[vq [-> He]] | [pv' He]];
          try discriminate He.
        + injection He as <-; reflexivity.
        + injection He as <- _; reflexivity.
      - intros z conds Hrule Hc.
        destruct (D.designation_spec conds (Hwf _ _ Hrule))
          as [[na cta] [Hdes Hin]].
        assert (HM := Hc _ Hin); cbn [MatchCond] in HM.
        apply (matchPos_attachAt I (alpineResolution S') na cta) in HM.
        destruct HM as [p [HpS Hatt]].
        apply mem_alpineResolution in HpS.
        assert (Hfib : InstallIf.In (z, conds) (installIfFibre I p)).
        { apply mem_installIfFibre; split; [exact Hrule |].
          unfold attachDesignation; rewrite Hdes; exact Hatt. }
        assert (Hf : FSet.In (installIfForm I z conds)
                       (dependees I (embedPkg p))).
        { destruct p as [np vp]; cbn [dependees embedPkg fst snd].
          apply FSet.union_spec; right; apply FSet.union_spec; right.
          apply SOtf.mem_map; exists (z, conds); split;
            [exact Hfib | reflexivity]. }
        assert (Hdep : PF.DepRel.In (embedPkg p, installIfForm I z conds)
                         (transD I)).
        { apply mem_transD; split; [apply Hsub; exact HpS | exact Hf]. }
        assert (Hs := Hclo _ HpS _ Hdep).
        apply satisfies_installIfForm in Hs.
        destruct Hs as [[c [Hcr Hn]] | Hb].
        + exfalso; apply Hn.
          apply (proj2 (cond_decode _ _ _ Hres)).
          exact (Hc _ (condRest_subset _ _ Hcr)).
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
            [[v [_ [Hc ->]]] | [q [pv [Hprov [_ [Hc ->]]]]]].
          * apply mem_transS in Hm.
            destruct Hm as
              [Hm | [[p0 [Hp0 He]] | [q0 [m0 [pv0 [_ [_ He]]]]]]].
            -- discriminate Hm.
            -- destruct p0 as [n0 v0]; injection He as <- <-.
               left; exists v; split; assumption.
            -- injection He as _ He; discriminate He.
          * apply mem_transS in Hm.
            destruct Hm as
              [Hm | [[p0 [_ He]] | [q0 [m0 [pv0 [Hprov0 [Hq0 He]]]]]]].
            -- discriminate Hm.
            -- destruct p0; discriminate He.
            -- injection He as He1 He2 He3; subst m0 q0 pv0.
               right; left; exists q, pv; repeat split; assumption.
        + apply mem_uprovSet in Hq; destruct Hq as [Hprov _].
          apply mem_transS in Hm.
          destruct Hm as
            [Hm | [[p0 [Hp0 He]] | [q0 [m0 [pv0 [_ [_ He]]]]]]].
          * destruct q; discriminate Hm.
          * apply embedPkg_injective in He; subst p0.
            right; right; split; [exact Hany | eauto].
          * destruct q; injection He as _ He; discriminate He.
      - intros [[v [HvS Hc]] |
                [[q [pv [Hprov [HqS Hc]]]] | [Hany [q [Hprov HqS]]]]].
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
          * apply mem_uprovSet; split; [exact Hprov | exact (Hsub _ HqS)].
          * apply mem_transS; right; left; exists q; split;
              [exact HqS | reflexivity].
    Qed.

    Lemma base_transS : forall I S n ct,
        PkgSet.Subset S (inst_repo I) ->
        ((exists w, PF.VSet.In w (constrVers I n ct) /\
            PF.PkgSet.In (Name.Orig n, w) (transS I S)) <->
         (exists v, PkgSet.In (n, v) S /\ constrMatch ct v = true) \/
         (exists q pv, Prov.In (q, (n, PVer pv)) (inst_prov I) /\
            PkgSet.In q S /\ constrMatch ct pv = true)).
    Proof.
      intros I S n ct Hsub; split.
      - intros [w [Hw Hm]].
        apply mem_constrVers in Hw.
        destruct Hw as
          [[v [_ [Hc ->]]] | [q [pv [Hprov [_ [Hc ->]]]]]].
        + apply mem_transS in Hm.
          destruct Hm as
            [Hm | [[p0 [Hp0 He]] | [q0 [m0 [pv0 [_ [_ He]]]]]]].
          * discriminate Hm.
          * destruct p0 as [n0 v0]; injection He as <- <-.
            left; exists v; split; assumption.
          * injection He as _ He; discriminate He.
        + apply mem_transS in Hm.
          destruct Hm as
            [Hm | [[p0 [_ He]] | [q0 [m0 [pv0 [Hprov0 [Hq0 He]]]]]]].
          * discriminate Hm.
          * destruct p0; discriminate He.
          * injection He as He1 He2 He3; subst m0 q0 pv0.
            right; exists q, pv; repeat split; assumption.
      - intros [[v [HvS Hc]] | [q [pv [Hprov [HqS Hc]]]]].
        + exists (Version.Orig v); split.
          * apply mem_constrVers; left; exists v.
            repeat split; try assumption.
            exact (Hsub _ HvS).
          * apply mem_transS; right; left; exists (n, v); split;
              [exact HvS | reflexivity].
        + exists (Version.Prov q pv); split.
          * apply mem_constrVers; right; exists q, pv.
            repeat split; try assumption.
            exact (Hsub _ HqS).
          * apply mem_transS; right; right; eauto 7.
    Qed.

    Lemma match_req_transS : forall I S n ct,
        PkgSet.Subset S (inst_repo I) ->
        (PF.Satisfies (transS I S) (encReq I n ct) <->
         MatchReq I S n ct).
    Proof.
      intros I S n ct Hsub.
      rewrite satisfies_encReq, (base_transS I S n ct Hsub).
      unfold MatchReq; rewrite or_assoc.
      apply or_iff_compat_l, or_iff_compat_l, and_iff_compat_l; split.
      - intros [q [Hq [Hs Hm]]]; apply mem_uprovSet in Hq.
        exists q; split; [exact (proj1 Hq) |].
        split; [| apply selectableb_spec; exact Hs].
        apply mem_transS in Hm.
        destruct Hm as [Hm | [[p0 [Hp0 He]] | [q0 [m0 [pv0 [_ [_ He]]]]]]].
        + destruct q; discriminate Hm.
        + apply embedPkg_injective in He; subst p0; exact Hp0.
        + destruct q; injection He as _ He; discriminate He.
      - intros [q [Hp [HqS Ha]]]; exists q.
        split; [apply mem_uprovSet; split; [exact Hp | exact (Hsub _ HqS)] |].
        split; [apply selectableb_spec; exact Ha |].
        apply mem_transS; right; left; exists q; split;
          [exact HqS | reflexivity].
    Qed.

    Theorem alpine_completeness : forall I S,
        WfAlias I -> IsResolution I S ->
        PF.IsResolution (transR I) (transD I) rootPkg (transS I S).
    Proof.
      intros I S [Wf1 Wf2] Hres.
      destruct Hres as [Hsub Hw Hd Hcu Ht].
      assert (Hiff := fun n ct => match_transS I S n ct Hsub).
      assert (Hreq := fun n ct => match_req_transS I S n ct Hsub).
      assert (Hcond : forall c, PF.Satisfies (transS I S) (encCond I c) <->
                                MatchCond I S c).
      { intros [[n ct] | [n ct]]; cbn [encCond MatchCond PF.Satisfies];
          rewrite (Hiff n ct); reflexivity. }
      constructor.
      - intros y Hy; apply mem_transS in Hy; apply mem_transR.
        destruct Hy as [-> | [[p [Hp ->]] | [q [m [pv [Hr [Hq ->]]]]]]].
        + left; reflexivity.
        + right; left; exists p; split; [exact (Hsub _ Hp) | reflexivity].
        + right; right; exists q, m, pv.
          repeat split; try assumption.
          exact (Hsub _ Hq).
      - apply mem_transS; left; reflexivity.
      - intros y Hy f Hdep.
        apply mem_transD in Hdep; destruct Hdep as [HyR Hf].
        apply mem_transS in Hy.
        destruct Hy as [-> | [[p [Hp ->]] | [q [m [pv [Hr [Hq ->]]]]]]].
        + cbn [dependees rootPkg] in Hf.
          apply SOwf.mem_map in Hf; destruct Hf as [d [Hd0 ->]].
          assert (Hmd := Hw _ Hd0).
          destruct d as [[m ct] | [m ct]]; cbn [MatchDep] in Hmd;
            cbn [encDep].
          * apply Hreq; exact Hmd.
          * cbn [PF.Satisfies]; intro Hs; apply Hmd.
            apply Hiff; exact Hs.
        + destruct p as [n0 v0].
          cbn [dependees embedPkg fst snd] in Hf.
          apply FSet.union_spec in Hf; destruct Hf as [Hf | Hf];
            [| apply FSet.union_spec in Hf; destruct Hf as [Hf | Hf]].
          * apply SOdf.mem_map in Hf; destruct Hf as [[p' d] [Hin ->]].
            apply DepsFibred.mem_tailFibre in Hin.
            destruct Hin as [Hin ->].
            assert (Hmd := Hd _ _ Hp Hin).
            destruct d as [[m ct] | [m ct]]; cbn [MatchDep] in Hmd;
              cbn [encDep].
            -- apply Hreq; exact Hmd.
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
          * apply SOtf.mem_map in Hf; destruct Hf as [[z conds] [Hfib ->]].
            apply mem_installIfFibre in Hfib.
            destruct Hfib as [Ht0 Hatt]; unfold attachDesignation in Hatt.
            destruct (D.designation conds) as [a |] eqn:Edes; [| discriminate].
            apply satisfies_installIfForm.
            destruct (CondSet.exists_
                        (fun b => negb (PF.satisfiesb (transS I S)
                                          (encCond I b)))
                        (condRest conds)) eqn:Ee.
            -- apply CondSet.exists_spec' in Ee.
               destruct Ee as [b [Hb Hnb]].
               apply Bool.negb_true_iff in Hnb.
               left; exists b; split; [exact Hb |].
               intro Hs; apply PF.satisfiesb_iff in Hs; congruence.
            -- right; apply Hiff, (Ht z conds Ht0).
               intros c Hc.
               destruct (DepOT.eq_dec c (DPos a)) as [He | Hne].
               ++ subst c; destruct a as [ma cta]; cbn [MatchCond].
                  apply matchPos_attachAt; exists (n0, v0).
                  split; [exact Hp | exact Hatt].
               ++ assert (Hr : CondSet.In c (condRest conds)).
                  { unfold condRest; rewrite Edes.
                    apply CondSet.remove_spec; split;
                      [exact Hc | exact Hne]. }
                  assert (Hbt : PF.satisfiesb (transS I S)
                                  (encCond I c) = true).
                  { destruct (PF.satisfiesb (transS I S) (encCond I c))
                      eqn:Eb; [reflexivity |].
                    exfalso.
                    assert (Hex : CondSet.exists_
                                    (fun b =>
                                       negb (PF.satisfiesb (transS I S)
                                               (encCond I b)))
                                    (condRest conds) = true).
                    { apply CondSet.exists_spec'; exists c; split;
                        [exact Hr | cbn; rewrite Eb; reflexivity]. }
                    congruence. }
                  apply Hcond; apply PF.satisfiesb_iff; exact Hbt.
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

    (* A resolution is S alone, and the witness adds only the root and the
       alias versions S's members provide, both functions of S. *)
    Theorem alpineResolution_transS : forall I S,
        alpineResolution (transS I S) = S.
    Proof.
      intros I S; apply PkgSet.ext; intros [n v].
      rewrite mem_alpineResolution, mem_transS; unfold embedPkg, rootPkg;
        cbn [fst snd].
      split.
      - intros [E | [[q [Hq E]] | [q [m [pv [_ [_ E]]]]]]];
          try discriminate E.
        destruct q as [qn qv]; injection E as -> ->; exact Hq.
      - intro Hp; right; left; exists (n, v); split; [exact Hp | reflexivity].
    Qed.

    Theorem alpineResolution_coreResolution : forall I S,
        alpineResolution
          (PF.Reduction.packageFormulaResolution
             (PF.Reduction.coreResolution (transS I S) (transR I) (transD I)))
        = S.
    Proof.
      intros I S; rewrite PF.Reduction.packageFormulaResolution_coreResolution.
      apply alpineResolution_transS.
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
      (* A dependee lookup reads the repository at the mentioned names and
         at their providers, which need not bear those names. *)
      Definition repoPreimage (I : Inst) (ns : NSet.t) : PkgSet.t :=
        PkgPre.preimage (fun p => p)
          (fun q => orb (NSet.mem (fst q) ns) (provTouchb I ns q))
          (inst_repo I).

      Module ProvPre := Preimage ProvElt Prov.
      Definition provPreimage (I : Inst) (ns : NSet.t) : Prov.t :=
        ProvPre.preimage (fun '(_, (m, _)) => m)
          (fun m => NSet.mem m ns) (inst_prov I).

      Lemma mem_repoPreimage : forall I ns q,
          PkgSet.In q (repoPreimage I ns) <->
          PkgSet.In q (inst_repo I) /\
          (NSet.In (fst q) ns \/
           exists m tg, Prov.In (q, (m, tg)) (inst_prov I) /\
             NSet.In m ns).
      Proof.
        intros I ns q; unfold repoPreimage.
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

      Lemma mem_provPreimage : forall I ns e,
          Prov.In e (provPreimage I ns) <->
          Prov.In e (inst_prov I) /\ NSet.In (fst (snd e)) ns.
      Proof.
        intros I ns [q [m tg]]; unfold provPreimage.
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

      Definition prioOf (I : Inst) (qs : PkgSet.t) : Prio.t :=
        Prio.filter (fun '(q, _) => PkgSet.mem q qs) (inst_prio I).

      Lemma mem_prioOf : forall I qs q k,
          Prio.In (q, k) (prioOf I qs) <->
          Prio.In (q, k) (inst_prio I) /\ PkgSet.In q qs.
      Proof.
        intros I qs q k; unfold prioOf; rewrite Prio.filter_spec'.
        cbn; rewrite PkgSet.mem_spec; reflexivity.
      Qed.

      (* Any instance whose repository and provides agree with I at the
         names in ns answers every constraint at those names alike. *)
      Definition subInst (I : Inst) (ns : NSet.t) (deps : Deps.t)
          (ownProv : Prov.t) (installIf : InstallIf.t) (world : WSet.t)
        : Inst :=
        {| inst_repo := repoPreimage I ns
         ; inst_deps := deps
         ; inst_prov := Prov.union ownProv (provPreimage I ns)
         ; inst_installIf := installIf
         ; inst_world := world
         ; inst_prio := prioOf I (repoPreimage I ns)
         ; inst_repl := Repl.empty |}.

      Lemma constrVers_subInst : forall I ns deps ownProv installIf world n ct,
          NSet.In n ns ->
          Prov.Subset ownProv (inst_prov I) ->
          constrVers (subInst I ns deps ownProv installIf world) n ct =
          constrVers I n ct.
      Proof.
        intros I ns deps ownProv installIf world n ct Hn Hown.
        apply PF.VSet.ext; intro w.
        rewrite !mem_constrVers; cbn [subInst inst_repo inst_prov].
        split.
        - intros [[v [Hrep [Hc ->]]] | [q [pv [Hprov [Hrep [Hc ->]]]]]].
          + apply mem_repoPreimage in Hrep; destruct Hrep as [Hrep _].
            left; eauto.
          + apply Prov.union_spec in Hprov.
            assert (Hprov' : Prov.In (q, (n, PVer pv)) (inst_prov I)).
            { destruct Hprov as [Hprov | Hprov]; [exact (Hown _ Hprov) |].
              apply mem_provPreimage in Hprov; exact (proj1 Hprov). }
            apply mem_repoPreimage in Hrep; destruct Hrep as [Hrep _].
            right; eauto 8.
        - intros [[v [Hrep [Hc ->]]] | [q [pv [Hprov [Hrep [Hc ->]]]]]].
          + left; exists v; repeat split; try assumption.
            apply mem_repoPreimage; split; [exact Hrep |].
            left; exact Hn.
          + right; exists q, pv; repeat split; try assumption.
            * apply Prov.union_spec; right.
              apply mem_provPreimage; split; [exact Hprov | exact Hn].
            * apply mem_repoPreimage; split; [exact Hrep |].
              right; exists n, (PVer pv); split; assumption.
      Qed.

      Lemma uprovSet_subInst : forall I ns deps ownProv installIf world n,
          NSet.In n ns ->
          Prov.Subset ownProv (inst_prov I) ->
          uprovSet (subInst I ns deps ownProv installIf world) n =
          uprovSet I n.
      Proof.
        intros I ns deps ownProv installIf world n Hn Hown.
        apply PkgSet.ext; intro q.
        rewrite !mem_uprovSet; cbn [subInst inst_repo inst_prov].
        split.
        - intros [Hprov Hrep].
          apply Prov.union_spec in Hprov.
          assert (Hprov' : Prov.In (q, (n, PVirt)) (inst_prov I)).
          { destruct Hprov as [Hprov | Hprov]; [exact (Hown _ Hprov) |].
            apply mem_provPreimage in Hprov; exact (proj1 Hprov). }
          apply mem_repoPreimage in Hrep; destruct Hrep as [Hrep _].
          split; assumption.
        - intros [Hprov Hrep]; split.
          + apply Prov.union_spec; right.
            apply mem_provPreimage; split; [exact Hprov | exact Hn].
          + apply mem_repoPreimage; split; [exact Hrep |].
            right; exists n, PVirt; split; assumption.
      Qed.

      (* Alias link dependencies read nothing from the instance. *)
      Theorem dependees_lookupProv : forall I m q pv,
          dependees I (Name.Orig m, Version.Prov q pv) =
          FSet.singleton
            (PF.FDep (Name.Orig (fst q))
               (PF.VSet.singleton (Version.Orig (snd q)))).
      Proof. reflexivity. Qed.

      Definition nameSubInst (I : Inst) (n : N.t) : Inst :=
        subInst I (NSet.singleton n) Deps.empty Prov.empty
          InstallIf.empty WSet.empty.

      Theorem versions_lookupName : forall I n,
          versions (nameSubInst I n) n = versions I n.
      Proof.
        intros I n; unfold versions, nameSubInst.
        apply constrVers_subInst.
        - apply NSet.singleton_spec; reflexivity.
        - intros e He; destruct (Prov.empty_spec He).
      Qed.

      Module SOwn := SetOps DepOT N WSet NSet.
      Module SOan := SetOps DepOT N CondSet NSet.
      Module SOtn := SetOps InstallIfElt N InstallIf NSet.

      Definition condNames (conds : CondSet.t) : NSet.t :=
        SOan.map depName conds.

      Lemma encPos_subInst : forall I ns deps ownProv installIf world
              (n : N.t) (ct : Constr),
          NSet.In n ns ->
          Prov.Subset ownProv (inst_prov I) ->
          encPos (subInst I ns deps ownProv installIf world) n ct =
          encPos I n ct.
      Proof.
        intros I ns deps ownProv installIf world n ct Hn Hown.
        apply encPos_agree.
        - apply constrVers_subInst; assumption.
        - apply uprovSet_subInst; assumption.
      Qed.

      Lemma selectableb_subInst : forall I ns deps ownProv installIf q,
          PkgSet.In q (repoPreimage I ns) ->
          selectableb (subInst I ns deps ownProv installIf (inst_world I)) q =
          selectableb I q.
      Proof.
        intros I ns deps ownProv installIf q Hq.
        unfold selectableb, hasPriorityb, worldNamesb.
        cbn [subInst inst_prio inst_world]; f_equal.
        apply Prio.exists_restrict.
        - intros [q' k] H; apply mem_prioOf in H; exact (proj1 H).
        - intros [q' k] Hin Hb; cbn in Hb.
          apply Bool.andb_true_iff in Hb; destruct Hb as [Hq' _].
          apply PkgEqb.eqb_true_iff in Hq'; subst q'.
          apply mem_prioOf; split; assumption.
      Qed.

      Lemma encReq_subInst : forall I ns deps ownProv installIf
              (n : N.t) (ct : Constr),
          NSet.In n ns ->
          Prov.Subset ownProv (inst_prov I) ->
          encReq (subInst I ns deps ownProv installIf (inst_world I)) n ct =
          encReq I n ct.
      Proof.
        intros I ns deps ownProv installIf n ct Hn Hown.
        unfold encReq, uprovL; cbv zeta.
        rewrite (constrVers_subInst I ns deps ownProv installIf
                   (inst_world I) n ct Hn Hown).
        rewrite (uprovSet_subInst I ns deps ownProv installIf
                   (inst_world I) n Hn Hown).
        destruct (isAny ct); [| reflexivity].
        f_equal; apply filter_ext_in; intros q Hq.
        apply selectableb_subInst.
        apply in_elements_pkg, mem_uprovSet in Hq; destruct Hq as [Hp Hr].
        apply mem_repoPreimage; split; [exact Hr |].
        right; exists n, PVirt; split; assumption.
      Qed.

      Lemma encDep_subInst : forall I ns deps ownProv installIf d,
          NSet.In (depName d) ns ->
          Prov.Subset ownProv (inst_prov I) ->
          encDep (subInst I ns deps ownProv installIf (inst_world I)) d =
          encDep I d.
      Proof.
        intros I ns deps ownProv installIf [[m ct] | [m ct]] Hn Hown;
          cbn [encDep depName] in *; [| f_equal].
        - apply encReq_subInst; assumption.
        - apply encPos_subInst; assumption.
      Qed.

      Lemma encCond_subInst : forall I ns deps ownProv installIf world c,
          NSet.In (depName c) ns ->
          Prov.Subset ownProv (inst_prov I) ->
          encCond (subInst I ns deps ownProv installIf world) c =
          encCond I c.
      Proof.
        intros I ns deps ownProv installIf world [[m ct] | [m ct]] Hn Hown;
          cbn [encCond depName] in *; [| f_equal];
          apply encPos_subInst; assumption.
      Qed.

      (* The condition fold is a congruence in encCond: only the atoms the
         set lists are read, so agreement there transports the formula. *)
      Lemma negFold_agree : forall I I' l base,
          (forall c, List.In c l -> encCond I' c = encCond I c) ->
          fold_right
            (fun c f => PF.FDisj (PF.FNeg (encCond I' c)) f) base l =
          fold_right
            (fun c f => PF.FDisj (PF.FNeg (encCond I c)) f) base l.
      Proof.
        intros I I' l base H; induction l as [| c l IH]; cbn.
        - reflexivity.
        - rewrite (H c (or_introl eq_refl)), IH; [reflexivity |].
          intros b Hb; apply H; right; exact Hb.
      Qed.

      Lemma installIfForm_subInst : forall I ns deps ownProv installIf world
              (z : Pkg.t) (conds : CondSet.t),
          NSet.In (fst z) ns ->
          (forall c : Dep,
              CondSet.In c (condRest conds) -> NSet.In (depName c) ns) ->
          Prov.Subset ownProv (inst_prov I) ->
          installIfForm (subInst I ns deps ownProv installIf world) z conds =
          installIfForm I z conds.
      Proof.
        intros I ns deps ownProv installIf world z conds Hz Hc Hown.
        unfold installIfForm.
        rewrite (encPos_subInst I ns deps ownProv installIf world (fst z) CAny
                   Hz Hown).
        apply negFold_agree; intros c Hcl.
        apply in_elements_cond in Hcl.
        apply encCond_subInst; [exact (Hc _ Hcl) | exact Hown].
      Qed.

      Lemma subInst_installIf : forall I ns deps ownProv installIf world,
          inst_installIf (subInst I ns deps ownProv installIf world) =
          installIf.
      Proof. reflexivity. Qed.

      (* Attachment reads the package itself and the provides entries it
         is the tail of, so a sub-instance keeping that fibre answers
         alike. *)
      Lemma attachAt_subInst : forall I ns deps ownProv installIf world p a,
          Prov.Subset ownProv (inst_prov I) ->
          (forall m tg, Prov.In (p, (m, tg)) (inst_prov I) ->
             Prov.In (p, (m, tg)) ownProv) ->
          attachAt (subInst I ns deps ownProv installIf world) p a =
          attachAt I p a.
      Proof.
        intros I ns deps ownProv installIf world p a Hown Hcov.
        unfold attachAt; cbn [subInst inst_prov];
          f_equal; try reflexivity.
        apply Prov.exists_restrict.
        - intros e He; apply Prov.union_spec in He.
          destruct He as [He | He]; [exact (Hown _ He) |].
          apply mem_provPreimage in He; exact (proj1 He).
        - intros [q [m tg]] He Hb; cbn in Hb.
          apply Bool.andb_true_iff in Hb; destruct Hb as [Hq _].
          apply PkgEqb.eqb_true_iff in Hq; subst q.
          apply Prov.union_spec; left; exact (Hcov _ _ He).
      Qed.

      Lemma attachDesignation_subInst :
        forall I ns deps ownProv installIf world p conds,
          Prov.Subset ownProv (inst_prov I) ->
          (forall m tg, Prov.In (p, (m, tg)) (inst_prov I) ->
             Prov.In (p, (m, tg)) ownProv) ->
          attachDesignation (subInst I ns deps ownProv installIf world) p
            conds = attachDesignation I p conds.
      Proof.
        intros I ns deps ownProv installIf world p conds Hown Hcov.
        unfold attachDesignation; destruct (D.designation conds) as [a |];
          [apply attachAt_subInst; assumption | reflexivity].
      Qed.

      Lemma installIfFibre_subInst : forall I ns deps ownProv world p,
          Prov.Subset ownProv (inst_prov I) ->
          (forall m tg, Prov.In (p, (m, tg)) (inst_prov I) ->
             Prov.In (p, (m, tg)) ownProv) ->
          installIfFibre
            (subInst I ns deps ownProv (installIfFibre I p) world) p =
          installIfFibre I p.
      Proof.
        intros I ns deps ownProv world p Hown Hcov.
        apply InstallIf.ext; intros [z conds].
        rewrite (mem_installIfFibre I p z conds).
        rewrite (mem_installIfFibre
                   (subInst I ns deps ownProv (installIfFibre I p) world)
                   p z conds).
        rewrite subInst_installIf.
        rewrite (attachDesignation_subInst I ns deps ownProv
                   (installIfFibre I p) world p conds Hown Hcov).
        rewrite (mem_installIfFibre I p z conds).
        tauto.
      Qed.

      (* A package's dependee lookup reads its own dependency names and,
         per install-if rule it carries, the rule's declaring name and the
         names of the conditions it did not designate. *)
      Definition pkgNames (I : Inst) (p : Pkg.t) : NSet.t :=
        NSet.union (atomNames I p)
          (SOtn.unionMap
             (fun '(z, conds) =>
                NSet.add (fst z) (condNames (condRest conds)))
             (installIfFibre I p)).

      Lemma dep_pkgNames : forall I p d,
          Deps.In (p, d) (DepsFibred.tailFibre (inst_deps I) p) ->
          NSet.In (depName d) (pkgNames I p).
      Proof.
        intros I p d H; unfold pkgNames; apply NSet.union_spec; left.
        unfold atomNames; apply SOdn.mem_map; exists (p, d); split;
          [exact H | reflexivity].
      Qed.

      Lemma selfName_pkgNames : forall I p z conds,
          InstallIf.In (z, conds) (installIfFibre I p) ->
          NSet.In (fst z) (pkgNames I p).
      Proof.
        intros I p z conds H; unfold pkgNames; apply NSet.union_spec; right.
        apply SOtn.mem_unionMap; exists (z, conds); split; [exact H |].
        cbv beta iota; apply NSet.add_spec; left; reflexivity.
      Qed.

      Lemma condName_pkgNames : forall I p z conds a,
          InstallIf.In (z, conds) (installIfFibre I p) ->
          CondSet.In a (condRest conds) ->
          NSet.In (depName a) (pkgNames I p).
      Proof.
        intros I p z conds a Ht Ha; unfold pkgNames.
        apply NSet.union_spec; right.
        apply SOtn.mem_unionMap; exists (z, conds); split; [exact Ht |].
        cbv beta iota; apply NSet.add_spec; right.
        unfold condNames; apply SOan.mem_map; exists a; split;
          [exact Ha | reflexivity].
      Qed.

      Definition pkgSubInst (I : Inst) (p : Pkg.t) : Inst :=
        subInst I (pkgNames I p)
          (DepsFibred.tailFibre (inst_deps I) p)
          (ProvFibred.tailFibre (inst_prov I) p)
          (installIfFibre I p) (inst_world I).

      Theorem dependees_lookupOrig : forall I n v,
          dependees (pkgSubInst I (n, v)) (embedPkg (n, v)) =
          dependees I (embedPkg (n, v)).
      Proof.
        intros I n v.
        assert (Hown : Prov.Subset
                         (ProvFibred.tailFibre (inst_prov I) (n, v))
                         (inst_prov I))
          by apply ProvFibred.tailFibre_subset.
        assert (Hcov : forall m tg,
                   Prov.In ((n, v), (m, tg)) (inst_prov I) ->
                   Prov.In ((n, v), (m, tg))
                     (ProvFibred.tailFibre (inst_prov I) (n, v))).
        { intros m tg H; apply ProvFibred.mem_tailFibre; split;
            [exact H | reflexivity]. }
        assert (Hfib : installIfFibre (pkgSubInst I (n, v)) (n, v) =
                         installIfFibre I (n, v)).
        { unfold pkgSubInst; apply installIfFibre_subInst; assumption. }
        apply FSet.ext; intro f.
        cbn [dependees embedPkg fst snd].
        rewrite Hfib.
        cbn [pkgSubInst subInst inst_deps inst_prov].
        rewrite !FSet.union_spec, !SOdf.mem_map, !SOrf.mem_filterMap,
          !SOtf.mem_map.
        apply or_iff; [| apply or_iff].
        - split.
          + intros [[p' d] [Hin ->]].
            apply DepsFibred.mem_tailFibre in Hin.
            destruct Hin as [Hin ->].
            exists ((n, v), d); split; [exact Hin |].
            cbv beta iota; apply encDep_subInst;
              [exact (dep_pkgNames I (n, v) d Hin) | exact Hown].
          + intros [[p' d] [Hin ->]].
            apply DepsFibred.mem_tailFibre in Hin.
            destruct Hin as [Hin ->].
            assert (Hfb : Deps.In ((n, v), d)
                            (DepsFibred.tailFibre (inst_deps I) (n, v))).
            { apply DepsFibred.mem_tailFibre; split;
                [exact Hin | reflexivity]. }
            exists ((n, v), d); split.
            { apply DepsFibred.mem_tailFibre; split;
                [exact Hfb | reflexivity]. }
            cbv beta iota; symmetry; apply encDep_subInst;
              [exact (dep_pkgNames I (n, v) d Hfb) | exact Hown].
        - split.
          + intros [[p' [m tg]] [Hin Hv]].
            apply ProvFibred.mem_tailFibre in Hin.
            destruct Hin as [Hin ->].
            apply Prov.union_spec in Hin.
            assert (Hin' : Prov.In ((n, v), (m, tg)) (inst_prov I)).
            { destruct Hin as [Hin | Hin].
              - apply ProvFibred.mem_tailFibre in Hin;
                  exact (proj1 Hin).
              - apply mem_provPreimage in Hin; exact (proj1 Hin). }
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
        - split.
          + intros [[z conds] [Hin ->]].
            exists (z, conds); split; [exact Hin |].
            cbv beta iota; apply installIfForm_subInst;
              [ exact (selfName_pkgNames I (n, v) z conds Hin)
              | intros a Ha;
                exact (condName_pkgNames I (n, v) z conds a Hin Ha)
              | exact Hown ].
          + intros [[z conds] [Hin ->]].
            exists (z, conds); split; [exact Hin |].
            cbv beta iota; symmetry; apply installIfForm_subInst;
              [ exact (selfName_pkgNames I (n, v) z conds Hin)
              | intros a Ha;
                exact (condName_pkgNames I (n, v) z conds a Hin Ha)
              | exact Hown ].
      Qed.

      (* The root's dependees read the world set at its dependency names
         alone: every install-if rule is carried by a package. *)
      Definition rootNames (I : Inst) : NSet.t :=
        SOwn.map depName (inst_world I).

      Lemma world_rootNames : forall I d,
          WSet.In d (inst_world I) -> NSet.In (depName d) (rootNames I).
      Proof.
        intros I d Hd; unfold rootNames.
        apply SOwn.mem_map; exists d; split; [exact Hd | reflexivity].
      Qed.

      Definition rootSubInst (I : Inst) : Inst :=
        subInst I (rootNames I) Deps.empty Prov.empty
          InstallIf.empty (inst_world I).

      Lemma rootSubInst_world : forall I,
          inst_world (rootSubInst I) = inst_world I.
      Proof. reflexivity. Qed.

      Theorem dependees_lookupRoot : forall I,
          dependees (rootSubInst I) rootPkg = dependees I rootPkg.
      Proof.
        intro I.
        assert (Hown : Prov.Subset Prov.empty (inst_prov I)).
        { intros e He; destruct (Prov.empty_spec He). }
        cbn [dependees rootPkg]; rewrite rootSubInst_world.
        apply FSet.ext; intro f; rewrite !SOwf.mem_map.
        split; intros [d [Hd ->]]; exists d; split; try exact Hd;
          [| symmetry]; unfold rootSubInst;
          apply encDep_subInst;
          [ exact (world_rootNames I d Hd) | exact Hown
          | exact (world_rootNames I d Hd) | exact Hown ].
      Qed.

      Lemma versions_transR : forall I m,
          PF.C.versions (transR I) (Name.Orig m) = versions I m.
      Proof.
        intros I m; apply PF.VSet.ext; intro w.
        rewrite PF.C.mem_versions, mem_transR; unfold versions.
        rewrite mem_constrVers; unfold rootPkg.
        split.
        - intros [E | [[[n v] [Hp E]] | [q [m' [pv [Hprov [Hq E]]]]]]].
          + discriminate E.
          + unfold embedPkg in E; cbn [fst snd] in E; injection E as -> ->.
            left; exists v; split; [exact Hp | split; reflexivity].
          + injection E as -> ->.
            right; exists q, pv; split; [exact Hprov |].
            split; [exact Hq | split; reflexivity].
        - intros [[v [Hv [_ ->]]] | [q [pv [Hprov [Hq [_ ->]]]]]].
          + right; left; exists (m, v); split; [exact Hv | reflexivity].
          + right; right; exists q, m, pv; split; [exact Hprov |].
            split; [exact Hq | reflexivity].
      Qed.

      Lemma versions_transR_root : forall I,
          PF.C.versions (transR I) Name.Root = PF.VSet.singleton Version.RootV.
      Proof.
        intro I; apply PF.VSet.ext; intro w.
        rewrite PF.C.mem_versions, mem_transR, PF.VSet.singleton_spec.
        unfold rootPkg; split.
        - intros [E | [[[n v] [_ E]] | [q [m [pv [_ [_ E]]]]]]];
            unfold embedPkg in E; try discriminate E.
          injection E as ->; reflexivity.
        - intros ->; left; reflexivity.
      Qed.

      Lemma transD_tailFibre : forall I q,
          PF.PkgSet.In q (transR I) ->
          PF.Reduction.Lookup.DepRelFibred.tailFibre (transD I) q =
          depEdges q (dependees I q).
      Proof.
        intros I q Hq; apply PF.DepRel.ext; intros [q' f].
        rewrite PF.Reduction.Lookup.DepRelFibred.mem_tailFibre, mem_transD.
        unfold depEdges; rewrite SOfd.mem_map.
        split.
        - intros [[_ Hf] ->]; exists f; split; [exact Hf | reflexivity].
        - intros [f0 [Hf0 E]]; injection E as -> ->.
          split; [split; [exact Hq | exact Hf0] | reflexivity].
      Qed.

      (* The core lookups a driver answers: a package's formulas from its
         own sub-instance, pushed through the package-formula reduction
         under an oracle agreeing with versions.  That sub-instance cannot
         serve as the oracle: a negated requirement or positive install-if
         condition with no constraint negates each bare provider q at q's
         own name, whose complement ranges over every version at that
         name, alias versions included, while repoPreimage keeps only the
         packages at or providing the names the package mentions -- q
         itself, and not the rest of q's name.  The versions lookup at q's
         name does hold them. *)
      Lemma dependees_core : forall I Vq q,
          PF.PkgSet.In q (transR I) ->
          Vq Name.Root = PF.VSet.singleton Version.RootV ->
          (forall m, Vq (Name.Orig m) = versions I m) ->
          PF.Reduction.T.dependees
            (PF.Reduction.reduceDeps (transR I) (transD I))
            (PF.Reduction.Name.Orig (fst q),
             PF.Reduction.Version.Orig (snd q)) =
          PF.Reduction.T.dependees
            (PF.Reduction.reduceDepsBy Vq (depEdges q (dependees I q)))
            (PF.Reduction.Name.Orig (fst q),
             PF.Reduction.Version.Orig (snd q)).
      Proof.
        intros I Vq [tn tv] Hq HR HO; cbn [fst snd].
        rewrite (PF.Reduction.Lookup.dependees_lookupOrigBy _ _ Vq)
          by (intros [| m] _;
              [rewrite HR, versions_transR_root | rewrite HO, versions_transR];
              reflexivity).
        rewrite (transD_tailFibre I (tn, tv) Hq); reflexivity.
      Qed.

      Theorem dependees_lookupOrigCore : forall I Vq n v,
          PkgSet.In (n, v) (inst_repo I) ->
          Vq Name.Root = PF.VSet.singleton Version.RootV ->
          (forall m, Vq (Name.Orig m) = versions I m) ->
          PF.Reduction.T.dependees
            (PF.Reduction.reduceDeps (transR I) (transD I))
            (PF.Reduction.embedPkg (embedPkg (n, v))) =
          PF.Reduction.T.dependees
            (PF.Reduction.reduceDepsBy Vq
               (depEdges (embedPkg (n, v))
                  (dependees (pkgSubInst I (n, v)) (embedPkg (n, v)))))
            (PF.Reduction.embedPkg (embedPkg (n, v))).
      Proof.
        intros I Vq n v Hnv HR HO; rewrite dependees_lookupOrig.
        apply (dependees_core I Vq (embedPkg (n, v))); [| exact HR | exact HO].
        apply mem_transR; right; left; exists (n, v); split;
          [exact Hnv | reflexivity].
      Qed.

      Theorem dependees_lookupRootCore : forall I Vq,
          Vq Name.Root = PF.VSet.singleton Version.RootV ->
          (forall m, Vq (Name.Orig m) = versions I m) ->
          PF.Reduction.T.dependees
            (PF.Reduction.reduceDeps (transR I) (transD I))
            (PF.Reduction.embedPkg rootPkg) =
          PF.Reduction.T.dependees
            (PF.Reduction.reduceDepsBy Vq
               (depEdges rootPkg (dependees (rootSubInst I) rootPkg)))
            (PF.Reduction.embedPkg rootPkg).
      Proof.
        intros I Vq HR HO; rewrite dependees_lookupRoot.
        exact (dependees_core I Vq rootPkg (root_transR I) HR HO).
      Qed.

      Theorem dependees_lookupProvCore : forall I I' Vq m q pv,
          Prov.In (q, (m, PVer pv)) (inst_prov I) ->
          PkgSet.In q (inst_repo I) ->
          Vq Name.Root = PF.VSet.singleton Version.RootV ->
          (forall m, Vq (Name.Orig m) = versions I m) ->
          PF.Reduction.T.dependees
            (PF.Reduction.reduceDeps (transR I) (transD I))
            (PF.Reduction.embedPkg (Name.Orig m, Version.Prov q pv)) =
          PF.Reduction.T.dependees
            (PF.Reduction.reduceDepsBy Vq
               (depEdges (Name.Orig m, Version.Prov q pv)
                  (dependees I' (Name.Orig m, Version.Prov q pv))))
            (PF.Reduction.embedPkg (Name.Orig m, Version.Prov q pv)).
      Proof.
        intros I I' Vq m q pv Hprov Hq HR HO.
        rewrite (dependees_lookupProv I' m q pv),
          <- (dependees_lookupProv I m q pv).
        apply (dependees_core I Vq (Name.Orig m, Version.Prov q pv));
          [| exact HR | exact HO].
        apply mem_transR; right; right; exists q, m, pv.
        split; [exact Hprov | split; [exact Hq | reflexivity]].
      Qed.

      (* A disjunct's edges are recorded when its owner is reduced.  An
         install-if rule's conditions are negated as alternatives of its
         disjunct, so this is where the bare providers' complements of its
         positive ones are taken. *)
      Theorem dependees_lookupDisjunctCore : forall I I' Vq q fs i,
          PF.PkgSet.In q (transR I) ->
          dependees I' q = dependees I q ->
          Vq Name.Root = PF.VSet.singleton Version.RootV ->
          (forall m, Vq (Name.Orig m) = versions I m) ->
          PF.Reduction.T.PkgSet.In (PF.Reduction.Name.Disjunct fs, i)
            (PF.Reduction.reduceReal (PF.PkgSet.singleton q)
               (depEdges q (dependees I' q))) ->
          PF.Reduction.T.dependees
            (PF.Reduction.reduceDeps (transR I) (transD I))
            (PF.Reduction.Name.Disjunct fs, i) =
          PF.Reduction.T.dependees
            (PF.Reduction.reduceDepsBy Vq (depEdges q (dependees I' q)))
            (PF.Reduction.Name.Disjunct fs, i).
      Proof.
        intros I I' Vq q fs i Hq HI HR HO Hin; rewrite HI in Hin |- *.
        assert (Hsub : PF.DepRel.Subset (depEdges q (dependees I q))
                         (transD I)).
        { rewrite <- (transD_tailFibre I q Hq).
          apply PF.Reduction.Lookup.DepRelFibred.tailFibre_subset. }
        apply (PF.Reduction.Lookup.dependees_lookupDisjunctBy
                 _ _ _ _ _ _ _ Hsub Hin).
        intros p f [| m] _ _;
          [rewrite HR, versions_transR_root | rewrite HO, versions_transR];
          reflexivity.
      Qed.

      Lemma versions_core : forall I tn,
          (exists w, PF.PkgSet.In (tn, w) (transR I)) \/
          (exists s h,
              PF.Reduction.T.DepRel.In (s, (PF.Reduction.Name.Orig tn, h))
                (PF.Reduction.reduceDeps (transR I) (transD I))) ->
          PF.Reduction.T.versions
            (PF.Reduction.reduceReal (transR I) (transD I))
            (PF.Reduction.Name.Orig tn) =
          PF.Reduction.T.VSet.add PF.Reduction.Version.Bot
            (PF.Reduction.embedVS (PF.C.versions (transR I) tn)).
      Proof.
        intros I tn Hreach.
        destruct Hreach as [[w Hw] | Hreach];
          [rewrite (PF.Reduction.Lookup.versions_lookupOrig _ _ (tn, w) tn Hw
                      (or_intror eq_refl))
          | rewrite (PF.Reduction.Lookup.versions_lookupOrig _ _ rootPkg tn
                       (root_transR I) (or_introl Hreach))];
          do 2 f_equal; apply PF.C.versions_ext; intro v;
          rewrite PF.Reduction.Lookup.PkgFibred.mem_tailFibre; tauto.
      Qed.

      Theorem versions_lookupNameCore : forall I n,
          (exists v, PkgSet.In (n, v) (inst_repo I)) \/
          (exists s h,
              PF.Reduction.T.DepRel.In
                (s, (PF.Reduction.Name.Orig (Name.Orig n), h))
                (PF.Reduction.reduceDeps (transR I) (transD I))) ->
          PF.Reduction.T.versions
            (PF.Reduction.reduceReal (transR I) (transD I))
            (PF.Reduction.Name.Orig (Name.Orig n)) =
          PF.Reduction.T.VSet.add PF.Reduction.Version.Bot
            (PF.Reduction.embedVS (versions (nameSubInst I n) n)).
      Proof.
        intros I n H; rewrite versions_lookupName, <- versions_transR.
        apply versions_core.
        destruct H as [[v Hv] | H];
          [left; exists (Version.Orig v) | right; exact H].
        apply mem_transR; right; left; exists (n, v); split;
          [exact Hv | reflexivity].
      Qed.

      (* As every original name, the root has ⊥ in the core, which a driver
         may leave out: PF.Reduction.Lookup.root_not_absent. *)
      Theorem versions_lookupRootCore : forall I,
          PF.Reduction.T.versions
            (PF.Reduction.reduceReal (transR I) (transD I))
            (PF.Reduction.Name.Orig Name.Root) =
          PF.Reduction.T.VSet.add PF.Reduction.Version.Bot
            (PF.Reduction.embedVS (PF.VSet.singleton Version.RootV)).
      Proof.
        intro I; rewrite <- (versions_transR_root I); apply versions_core.
        left; exists Version.RootV; exact (root_transR I).
      Qed.
    End Lookup.
  End Reduct.

  Module Reduction := Reduct LeastDesignation.
End Alpine.
