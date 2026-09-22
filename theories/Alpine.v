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
    ; inst_repl : Repl.t
    (* the packages Supported is demanded of: a frontend's choice *)
    ; inst_supp : PkgSet.t }.

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

  Definition HasRequirer (I : Inst) (S : PkgSet.t) (m : N.t) : Prop :=
    (exists ct, WSet.In (DPos (m, ct)) (inst_world I)) \/
    (exists r ct, PkgSet.In r S /\ Deps.In (r, DPos (m, ct)) (inst_deps I)).

  (* apk's is_provider_auto_selectable, read over the final set, and
     widened to a package selected for another reason: apk assigns it every
     name it provides, so it satisfies a dependency there all the same. *)
  Definition AutoSelectable (I : Inst) (S : PkgSet.t) (q : Pkg.t) : Prop :=
    HasPriority I q \/
    HasRequirer I S (fst q) \/
    (exists m pv, Prov.In (q, (m, PVer pv)) (inst_prov I) /\
       HasRequirer I S m) \/
    (exists conds, InstallIf.In (q, conds) (inst_installIf I) /\
       forall n ct, CondSet.In (n, ct) conds -> MatchPos I S n ct).

  Definition MatchReq (I : Inst) (S : PkgSet.t)
      (n : N.t) (ct : Constr) : Prop :=
    (exists v, PkgSet.In (n, v) S /\ constrMatch ct v = true) \/
    (exists q pv, Prov.In (q, (n, PVer pv)) (inst_prov I) /\
       PkgSet.In q S /\ constrMatch ct pv = true) \/
    (isAny ct = true /\
     exists q, Prov.In (q, (n, PVirt)) (inst_prov I) /\ PkgSet.In q S /\
       AutoSelectable I S q).

  (* A package satisfies the atom itself: by name and version, by a
     versioned provides, or by a bare one apk may select it through. *)
  Definition Offers (I : Inst) (p : Pkg.t) (a : Atom.t) : Prop :=
    (fst p = fst a /\ constrMatch (snd a) (snd p) = true) \/
    (exists pv, Prov.In (p, (fst a, PVer pv)) (inst_prov I) /\
       constrMatch (snd a) pv = true) \/
    (isAny (snd a) = true /\ Prov.In (p, (fst a, PVirt)) (inst_prov I) /\
     HasPriority I p).

  (* apk keeps a package only while something leads to it: the world, a
     dependency of a package it keeps, or the package's own install_if.
     Read over the final set this admits packages that only lead to each
     other. *)
  Definition Supported (I : Inst) (S : PkgSet.t) (p : Pkg.t) : Prop :=
    (exists a, WSet.In (DPos a) (inst_world I) /\ Offers I p a) \/
    (exists r a, PkgSet.In r S /\ Deps.In (r, DPos a) (inst_deps I) /\
       Offers I p a) \/
    (exists conds, InstallIf.In (p, conds) (inst_installIf I) /\
       forall n ct, CondSet.In (n, ct) conds -> MatchPos I S n ct).

  Definition MatchDep (I : Inst) (S : PkgSet.t) (d : Dep) : Prop :=
    match d with
    | DPos (n, ct) => MatchReq I S n ct
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
        (forall n ct, CondSet.In (n, ct) conds -> MatchPos I S n ct) ->
        MatchPos I S (fst p) CAny
    ; res_support :
        forall p, PkgSet.In p S -> PkgSet.In p (inst_supp I) ->
        Supported I S p }.

  Module Type Designation.
    Parameter designation : CondSet.t -> option Atom.t.
    Parameter designation_spec : forall conds : CondSet.t,
        ~ CondSet.Empty conds ->
        exists a, designation conds = Some a /\ CondSet.In a conds.
  End Designation.

  Module LeastDesignation <: Designation.
    Definition designation (conds : CondSet.t) : option Atom.t :=
      CondSet.choose conds.
    Lemma designation_spec : forall conds : CondSet.t,
        ~ CondSet.Empty conds ->
        exists a, designation conds = Some a /\ CondSet.In a conds.
    Proof.
      intros conds Hne; unfold designation.
      destruct (CondSet.choose conds) as [a |] eqn:Ec.
      - exists a; split; [reflexivity | exact (CondSet.choose_spec1 Ec)].
      - destruct (Hne (CondSet.choose_spec2 Ec)).
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

    Module NSet := FSetUOT N.

    Definition provForm (q : Pkg.t) : PF.Formula :=
      PF.FDep (Name.Orig (fst q)) (PF.VSet.singleton (Version.Orig (snd q))).

    Definition hasPriorityb (I : Inst) (q : Pkg.t) : bool :=
      Prio.exists_
        (fun '(q', k) => andb (PkgEqb.eqb q' q) (negb (Nat.eqb k 0)))
        (inst_prio I).

    Module SOrn := SetOps ProvElt N Prov NSet.
    Definition ownNames (I : Inst) (q : Pkg.t) : NSet.t :=
      NSet.add (fst q)
        (SOrn.filterMap
           (fun '(q', (m, tg)) =>
              match tg with
              | PVer _ => if PkgEqb.eqb q' q then Some m else None
              | PVirt => None
              end)
           (inst_prov I)).

    Definition reqName (ms : NSet.t) (d : Dep) : bool :=
      match d with DPos (m, _) => NSet.mem m ms | DNeg _ => false end.

    Definition rootRequiresb (I : Inst) (ms : NSet.t) : bool :=
      WSet.exists_ (reqName ms) (inst_world I).

    Module SOdp := SetOps DepElt Pkg Deps PkgSet.
    Definition requirerSet (I : Inst) (ms : NSet.t) : PkgSet.t :=
      SOdp.filterMap (fun '(r, d) => if reqName ms d then Some r else None)
        (inst_deps I).

    Definition ownRules (I : Inst) (q : Pkg.t) : InstallIf.t :=
      InstallIf.filter (fun '(z, _) => PkgEqb.eqb z q) (inst_installIf I).

    (* The provider is the last conjunct of each of its alternatives, which
       is where a driver finds it. *)
    Definition condsForm (I : Inst) (q : Pkg.t) (conds : CondSet.t) :
        PF.Formula :=
      fold_right (fun a f => PF.FConj (encPos I (fst a) (snd a)) f)
        (provForm q) (CondSet.elements conds).

    Definition selectableAlts (I : Inst) (q : Pkg.t) : list PF.Formula :=
      let ms := ownNames I q in
      if orb (hasPriorityb I q) (rootRequiresb I ms) then provForm q :: nil
      else
        map (fun r => PF.FConj (provForm r) (provForm q))
          (PkgSet.elements (requirerSet I ms)) ++
        map (fun '(_, conds) => condsForm I q conds)
          (InstallIf.elements (ownRules I q)).

    Definition encReq (I : Inst) (n : N.t) (ct : Constr) : PF.Formula :=
      let base := PF.FDep (Name.Orig n) (constrVers I n ct) in
      if isAny ct
      then fold_right PF.FDisj base (flat_map (selectableAlts I) (uprovL I n))
      else base.

    Definition offersb (I : Inst) (p : Pkg.t) (a : Atom.t) : bool :=
      orb (andb (NEqb.eqb (fst p) (fst a)) (constrMatch (snd a) (snd p)))
        (Prov.exists_
           (fun '(q, (m, tg)) =>
              andb (PkgEqb.eqb q p)
                (andb (NEqb.eqb m (fst a))
                   (match tg with
                    | PVer pv => constrMatch (snd a) pv
                    | PVirt => andb (isAny (snd a)) (hasPriorityb I p)
                    end)))
           (inst_prov I)).

    Definition offersDep (I : Inst) (p : Pkg.t) (d : Dep) : bool :=
      match d with DPos a => offersb I p a | DNeg _ => false end.

    Definition rootSupportsb (I : Inst) (p : Pkg.t) : bool :=
      WSet.exists_ (offersDep I p) (inst_world I).

    Definition supporterSet (I : Inst) (p : Pkg.t) : PkgSet.t :=
      SOdp.filterMap
        (fun '(r, d) => if offersDep I p d then Some r else None)
        (inst_deps I).

    Definition condsConj (I : Inst) (conds : CondSet.t) :
        option PF.Formula :=
      match CondSet.elements conds with
      | nil => None
      | a :: l =>
          Some (fold_right (fun b f => PF.FConj (encPos I (fst b) (snd b)) f)
                  (encPos I (fst a) (snd a)) l)
      end.

    Definition supportAlts (I : Inst) (p : Pkg.t) : list PF.Formula :=
      map provForm (PkgSet.elements (supporterSet I p)) ++
      flat_map
        (fun '(_, conds) =>
           match condsConj I conds with Some f => f :: nil | None => nil end)
        (InstallIf.elements (ownRules I p)).

    Definition vacuousRuleb (I : Inst) (p : Pkg.t) : bool :=
      InstallIf.exists_ (fun '(_, conds) => CondSet.is_empty conds)
        (ownRules I p).

    (* None where the instance alone supports the package; an empty
       version set where nothing can. *)
    Definition supportForm (I : Inst) (p : Pkg.t) : option PF.Formula :=
      if orb (negb (PkgSet.mem p (inst_supp I)))
           (orb (rootSupportsb I p) (vacuousRuleb I p)) then None
      else
        match supportAlts I p with
        | nil => Some (PF.FDep (Name.Orig (fst p)) PF.VSet.empty)
        | g :: l => Some (fold_right PF.FDisj g l)
        end.

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
      | Some a => CondSet.remove a conds
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

    Definition installIfForm (I : Inst) (z : Pkg.t) (conds : CondSet.t) :
        PF.Formula :=
      fold_right
        (fun a f => PF.FDisj (PF.FNeg (encPos I (fst a) (snd a))) f)
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
               (FSet.union
                  (SOtf.map (fun '(z, conds) => installIfForm I z conds)
                     (installIfFibre I (n, v)))
                  (match supportForm I (n, v) with
                   | Some f => FSet.singleton f
                   | None => FSet.empty
                   end)))
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

    Lemma satisfies_installIfForm : forall I S' z conds,
        PF.Satisfies S' (installIfForm I z conds) <->
        (exists a, CondSet.In a (condRest conds) /\
           ~ PF.Satisfies S' (encPos I (fst a) (snd a))) \/
        PF.Satisfies S' (encPos I (fst z) CAny).
    Proof.
      intros I S' z conds; unfold installIfForm.
      rewrite satisfies_negFold.
      split; intros [[a [Ha Hn]] | Hb];
        try (right; exact Hb); left; exists a;
        (split; [| exact Hn]); apply in_elements_cond; exact Ha.
    Qed.

    Lemma in_elements_iif : forall s x,
        List.In x (InstallIf.elements s) <-> InstallIf.In x s.
    Proof.
      intros s x; rewrite <- (InstallIf.elements_spec1 s x).
      rewrite InA_alt; split.
      - intro H; exists x; split; reflexivity + assumption.
      - intros [y [-> Hy]]; exact Hy.
    Qed.

    Lemma satisfies_provForm : forall S' q,
        PF.Satisfies S' (provForm q) <-> PF.PkgSet.In (embedPkg q) S'.
    Proof.
      intros S' [n v]; unfold provForm, embedPkg; cbn [PF.Satisfies fst snd].
      split.
      - intros [w [Hw Hm]]; apply PF.VSet.singleton_spec in Hw; subst w.
        exact Hm.
      - intro H; exists (Version.Orig v); split;
          [apply PF.VSet.singleton_spec; reflexivity | exact H].
    Qed.

    Lemma hasPriorityb_spec : forall I q, hasPriorityb I q = true <-> HasPriority I q.
    Proof.
      intros I q; unfold hasPriorityb, HasPriority; rewrite Prio.exists_spec'; split.
      - intros [[q' k] [Hin Hb]]; cbn in Hb.
        apply Bool.andb_true_iff in Hb; destruct Hb as [Hq Hk].
        apply PkgEqb.eqb_true_iff in Hq; subst q'.
        exists k; split; [exact Hin |].
        intro Hk0; subst k; discriminate Hk.
      - intros [k [Hin Hk]]; exists (q, k); split; [exact Hin | cbn].
        rewrite (proj2 (PkgEqb.eqb_true_iff q q) eq_refl).
        destruct k; [contradiction | reflexivity].
    Qed.

    Lemma mem_ownNames : forall I q m,
        NSet.In m (ownNames I q) <->
        m = fst q \/ exists pv, Prov.In (q, (m, PVer pv)) (inst_prov I).
    Proof.
      intros I q m; unfold ownNames.
      rewrite NSet.add_spec, SOrn.mem_filterMap.
      apply or_iff_compat_l; split.
      - intros [[q' [m' tg]] [Hin Hf]]; cbn in Hf.
        destruct tg as [pv |]; [| discriminate].
        destruct (PkgEqb.eqb q' q) eqn:Eq; [| discriminate].
        apply PkgEqb.eqb_true_iff in Eq; subst q'.
        injection Hf as <-; exists pv; exact Hin.
      - intros [pv Hin]; exists (q, (m, PVer pv)); split; [exact Hin | cbn].
        rewrite (proj2 (PkgEqb.eqb_true_iff q q) eq_refl); reflexivity.
    Qed.

    Lemma reqName_spec : forall ms d,
        reqName ms d = true <->
        exists m ct, d = DPos (m, ct) /\ NSet.In m ms.
    Proof.
      intros ms [[m ct] | [m ct]]; cbn [reqName].
      - rewrite NSet.mem_spec; split.
        + intro H; exists m, ct; split; [reflexivity | exact H].
        + intros [m' [ct' [He H]]]; injection He as <- <-; exact H.
      - split; [discriminate | intros [m' [ct' [He _]]]; discriminate He].
    Qed.

    Lemma rootRequiresb_spec : forall I ms,
        rootRequiresb I ms = true <->
        exists m ct, WSet.In (DPos (m, ct)) (inst_world I) /\ NSet.In m ms.
    Proof.
      intros I ms; unfold rootRequiresb; rewrite WSet.exists_spec'; split.
      - intros [d [Hd Hr]]; apply reqName_spec in Hr.
        destruct Hr as [m [ct [-> Hm]]]; exists m, ct; split; assumption.
      - intros [m [ct [Hd Hm]]]; exists (DPos (m, ct)); split; [exact Hd |].
        apply reqName_spec; exists m, ct; split; [reflexivity | exact Hm].
    Qed.

    Lemma mem_requirerSet : forall I ms r,
        PkgSet.In r (requirerSet I ms) <->
        exists m ct, Deps.In (r, DPos (m, ct)) (inst_deps I) /\ NSet.In m ms.
    Proof.
      intros I ms r; unfold requirerSet; rewrite SOdp.mem_filterMap; split.
      - intros [[r' d] [Hin Hf]]; cbn in Hf.
        destruct (reqName ms d) eqn:Er; [| discriminate].
        injection Hf as <-.
        apply reqName_spec in Er; destruct Er as [m [ct [-> Hm]]].
        exists m, ct; split; assumption.
      - intros [m [ct [Hin Hm]]]; exists (r, DPos (m, ct)); split;
          [exact Hin | cbn].
        rewrite (proj2 (NSet.mem_spec _ _) Hm); reflexivity.
    Qed.

    Lemma mem_ownRules : forall I q z conds,
        InstallIf.In (z, conds) (ownRules I q) <->
        InstallIf.In (z, conds) (inst_installIf I) /\ z = q.
    Proof.
      intros I q z conds; unfold ownRules; rewrite InstallIf.filter_spec'.
      cbn; rewrite PkgEqb.eqb_true_iff; reflexivity.
    Qed.

    Lemma satisfies_conjFold : forall I S' l (base : PF.Formula),
        PF.Satisfies S'
          (fold_right (fun a f => PF.FConj (encPos I (fst a) (snd a)) f)
             base l) <->
        (forall a, List.In a l ->
           PF.Satisfies S' (encPos I (fst a) (snd a))) /\
        PF.Satisfies S' base.
    Proof.
      intros I S' l base; induction l as [| a l IH]; cbn [fold_right].
      - split; [intro H; split; [intros _ [] | exact H] |].
        intros [_ H]; exact H.
      - cbn [PF.Satisfies]; rewrite IH; split.
        + intros [Ha [Hl Hb]]; split; [| exact Hb].
          intros a0 [<- | Ha0]; [exact Ha | exact (Hl _ Ha0)].
        + intros [Hl Hb]; split; [apply Hl; left; reflexivity |].
          split; [intros a0 Ha0; apply Hl; right; exact Ha0 | exact Hb].
    Qed.

    Lemma satisfies_condsForm : forall I S' q conds,
        PF.Satisfies S' (condsForm I q conds) <->
        (forall a, CondSet.In a conds ->
           PF.Satisfies S' (encPos I (fst a) (snd a))) /\
        PF.PkgSet.In (embedPkg q) S'.
    Proof.
      intros I S' q conds; unfold condsForm.
      rewrite satisfies_conjFold, satisfies_provForm.
      split; intros [Hl Hb]; split; try exact Hb; intros a Ha; apply Hl;
        apply in_elements_cond; exact Ha.
    Qed.

    Lemma satisfies_disjList : forall S' l (base : PF.Formula),
        PF.Satisfies S' (fold_right PF.FDisj base l) <->
        PF.Satisfies S' base \/ exists g, List.In g l /\ PF.Satisfies S' g.
    Proof.
      intros S' l base; induction l as [| g l IH]; cbn [fold_right].
      - split; [intro H; left; exact H |].
        intros [H | [g [[] _]]]; exact H.
      - cbn [PF.Satisfies]; rewrite IH; split.
        + intros [Hg | [Hb | [g0 [Hg0 Hs]]]].
          * right; exists g; split; [left; reflexivity | exact Hg].
          * left; exact Hb.
          * right; exists g0; split; [right; exact Hg0 | exact Hs].
        + intros [Hb | [g0 [[<- | Hg0] Hs]]].
          * right; left; exact Hb.
          * left; exact Hs.
          * right; right; exists g0; split; assumption.
    Qed.

    Lemma satisfies_encReq : forall I S' n ct,
        PF.Satisfies S' (encReq I n ct) <->
        (exists w, PF.VSet.In w (constrVers I n ct) /\
           PF.PkgSet.In (Name.Orig n, w) S') \/
        (isAny ct = true /\
         exists q, PkgSet.In q (uprovSet I n) /\
           exists g, List.In g (selectableAlts I q) /\ PF.Satisfies S' g).
    Proof.
      intros I S' n ct; unfold encReq; cbv zeta.
      destruct (isAny ct) eqn:Ea.
      - rewrite satisfies_disjList; cbn [PF.Satisfies].
        apply or_iff_compat_l; split.
        + intros [g [Hg Hs]]; apply in_flat_map in Hg.
          destruct Hg as [q [Hq Hg]].
          split; [reflexivity |]; exists q; split;
            [apply in_elements_pkg; exact Hq |].
          exists g; split; assumption.
        + intros [_ [q [Hq [g [Hg Hs]]]]]; exists g; split; [| exact Hs].
          apply in_flat_map; exists q; split;
            [apply in_elements_pkg; exact Hq | exact Hg].
      - cbn [PF.Satisfies]; split.
        + intro H; left; exact H.
        + intros [H | [Hany _]]; [exact H | discriminate Hany].
    Qed.

    Lemma autoSelectable_ownNames : forall I S q,
        AutoSelectable I S q <->
        HasPriority I q \/
        (exists m, NSet.In m (ownNames I q) /\ HasRequirer I S m) \/
        (exists conds, InstallIf.In (q, conds) (inst_installIf I) /\
           forall n ct, CondSet.In (n, ct) conds -> MatchPos I S n ct).
    Proof.
      intros I S q; unfold AutoSelectable; apply or_iff_compat_l; split.
      - intros [H | [[m [pv [Hp H]]] | H]].
        + left; exists (fst q); split; [| exact H].
          apply mem_ownNames; left; reflexivity.
        + left; exists m; split; [| exact H].
          apply mem_ownNames; right; exists pv; exact Hp.
        + right; exact H.
      - intros [[m [Hm H]] | H].
        + apply mem_ownNames in Hm; destruct Hm as [-> | [pv Hp]];
            [left; exact H | right; left; exists m, pv; split; assumption].
        + right; right; exact H.
    Qed.

    (* Stated against any pair of sets agreeing on packages and on
       MatchPos, so that soundness and completeness share it. *)
    Lemma selectableAlts_spec : forall I S' S q,
        (forall p, PF.PkgSet.In (embedPkg p) S' <-> PkgSet.In p S) ->
        (forall n ct, PF.Satisfies S' (encPos I n ct) <-> MatchPos I S n ct) ->
        ((exists g, List.In g (selectableAlts I q) /\ PF.Satisfies S' g) <->
         PkgSet.In q S /\ AutoSelectable I S q).
    Proof.
      intros I S' S q Hemb Hpos.
      rewrite autoSelectable_ownNames.
      unfold selectableAlts; cbv zeta.
      destruct (hasPriorityb I q) eqn:Ek; cbn [orb].
      - split.
        + intros [g [[<- | []] Hs]]; split;
            [apply Hemb, satisfies_provForm; exact Hs |].
          left; apply hasPriorityb_spec; exact Ek.
        + intros [Hq _]; exists (provForm q); split; [left; reflexivity |].
          apply satisfies_provForm, Hemb; exact Hq.
      - destruct (rootRequiresb I (ownNames I q)) eqn:Er.
        + split.
          * intros [g [[<- | []] Hs]]; split;
              [apply Hemb, satisfies_provForm; exact Hs |].
            apply rootRequiresb_spec in Er.
            destruct Er as [m [ct [Hw Hm]]].
            right; left; exists m; split; [exact Hm |].
            left; exists ct; exact Hw.
          * intros [Hq _]; exists (provForm q); split; [left; reflexivity |].
            apply satisfies_provForm, Hemb; exact Hq.
        + split.
          * intros [g [Hg Hs]]; apply in_app_iff in Hg.
            destruct Hg as [Hg | Hg]; apply in_map_iff in Hg.
            -- destruct Hg as [r [<- Hr]].
               cbn [PF.Satisfies] in Hs; destruct Hs as [Hsr Hsq].
               apply satisfies_provForm, Hemb in Hsr.
               apply satisfies_provForm, Hemb in Hsq.
               split; [exact Hsq |].
               apply in_elements_pkg, mem_requirerSet in Hr.
               destruct Hr as [m [ct [Hd Hm]]].
               right; left; exists m; split; [exact Hm |].
               right; exists r, ct; split; assumption.
            -- destruct Hg as [[z conds] [<- Hz]]; cbv beta iota in Hs.
               apply in_elements_iif, mem_ownRules in Hz.
               destruct Hz as [Hz ->].
               apply satisfies_condsForm in Hs; destruct Hs as [Hc Hq].
               split; [apply Hemb; exact Hq |].
               right; right; exists conds; split; [exact Hz |].
               intros m ct Hmc; apply Hpos; exact (Hc (m, ct) Hmc).
          * intros [Hq [Hk | [[m [Hm [[ct Hw] | [r [ct [Hr Hd]]]]]] |
                               [conds [Hz Hc]]]]].
            -- apply hasPriorityb_spec in Hk; congruence.
            -- exfalso.
               assert (Ht : rootRequiresb I (ownNames I q) = true)
                 by (apply rootRequiresb_spec; exists m, ct; split; assumption).
               congruence.
            -- exists (PF.FConj (provForm r) (provForm q)); split.
               ++ apply in_app_iff; left; apply in_map_iff.
                  exists r; split; [reflexivity |].
                  apply in_elements_pkg, mem_requirerSet.
                  exists m, ct; split; assumption.
               ++ cbn [PF.Satisfies]; split;
                    apply satisfies_provForm, Hemb; assumption.
            -- exists (condsForm I q conds); split.
               ++ apply in_app_iff; right; apply in_map_iff.
                  exists (q, conds); split; [reflexivity |].
                  apply in_elements_iif, mem_ownRules; split;
                    [exact Hz | reflexivity].
               ++ apply satisfies_condsForm; split;
                    [| apply Hemb; exact Hq].
                  intros [m ct] Ha; apply Hpos; exact (Hc m ct Ha).
    Qed.

    Lemma offersb_spec : forall I p a,
        offersb I p a = true <-> Offers I p a.
    Proof.
      intros I p a; unfold offersb, Offers.
      rewrite Bool.orb_true_iff, Bool.andb_true_iff, NEqb.eqb_true_iff.
      rewrite Prov.exists_spec'.
      apply or_iff_compat_l.
      split.
      - intros [[q [m tg]] [Hr Hb]]; cbn in Hb.
        apply Bool.andb_true_iff in Hb; destruct Hb as [Hq Hb].
        apply PkgEqb.eqb_true_iff in Hq; subst q.
        apply Bool.andb_true_iff in Hb; destruct Hb as [Hm Hb].
        apply NEqb.eqb_true_iff in Hm; subst m.
        destruct tg as [pv |]; [left; eauto |].
        apply Bool.andb_true_iff in Hb; destruct Hb as [Ha Hk].
        right; split; [exact Ha |]; split; [exact Hr |].
        apply hasPriorityb_spec; exact Hk.
      - intros [[pv [Hr Hc]] | [Hany [Hr Hk]]].
        + exists (p, (fst a, PVer pv)); split; [exact Hr | cbn].
          rewrite (proj2 (PkgEqb.eqb_true_iff p p) eq_refl).
          rewrite (proj2 (NEqb.eqb_true_iff (fst a) (fst a)) eq_refl).
          rewrite Hc; reflexivity.
        + exists (p, (fst a, PVirt)); split; [exact Hr | cbn].
          rewrite (proj2 (PkgEqb.eqb_true_iff p p) eq_refl).
          rewrite (proj2 (NEqb.eqb_true_iff (fst a) (fst a)) eq_refl).
          rewrite Hany, (proj2 (hasPriorityb_spec I p) Hk); reflexivity.
    Qed.

    Lemma offersDep_spec : forall I p d,
        offersDep I p d = true <-> exists a, d = DPos a /\ Offers I p a.
    Proof.
      intros I p [a | a]; cbn [offersDep].
      - rewrite offersb_spec; split.
        + intro H; exists a; split; [reflexivity | exact H].
        + intros [a' [He H]]; injection He as <-; exact H.
      - split; [discriminate | intros [a' [He _]]; discriminate He].
    Qed.

    Lemma rootSupportsb_spec : forall I p,
        rootSupportsb I p = true <->
        exists a, WSet.In (DPos a) (inst_world I) /\ Offers I p a.
    Proof.
      intros I p; unfold rootSupportsb; rewrite WSet.exists_spec'; split.
      - intros [d [Hd Ho]]; apply offersDep_spec in Ho.
        destruct Ho as [a [-> Ho]]; exists a; split; assumption.
      - intros [a [Hd Ho]]; exists (DPos a); split; [exact Hd |].
        apply offersDep_spec; exists a; split; [reflexivity | exact Ho].
    Qed.

    Lemma mem_supporterSet : forall I p r,
        PkgSet.In r (supporterSet I p) <->
        exists a, Deps.In (r, DPos a) (inst_deps I) /\ Offers I p a.
    Proof.
      intros I p r; unfold supporterSet; rewrite SOdp.mem_filterMap; split.
      - intros [[r' d] [Hin Hf]]; cbn in Hf.
        destruct (offersDep I p d) eqn:Eo; [| discriminate].
        injection Hf as <-.
        apply offersDep_spec in Eo; destruct Eo as [a [-> Ho]].
        exists a; split; assumption.
      - intros [a [Hin Ho]]; exists (r, DPos a); split; [exact Hin | cbn].
        rewrite (proj2 (offersb_spec I p a) Ho); reflexivity.
    Qed.

    Lemma vacuousRuleb_spec : forall I p,
        vacuousRuleb I p = true <->
        exists conds, InstallIf.In (p, conds) (inst_installIf I) /\
          CondSet.Empty conds.
    Proof.
      intros I p; unfold vacuousRuleb; rewrite InstallIf.exists_spec'; split.
      - intros [[z conds] [Hin He]]; apply mem_ownRules in Hin.
        destruct Hin as [Hin ->]; exists conds; split; [exact Hin |].
        cbn in He; apply CondSet.is_empty_spec; exact He.
      - intros [conds [Hin He]]; exists (p, conds); split.
        + apply mem_ownRules; split; [exact Hin | reflexivity].
        + cbn; apply CondSet.is_empty_spec; exact He.
    Qed.

    Lemma condsConj_some : forall I S' conds f,
        condsConj I conds = Some f ->
        (PF.Satisfies S' f <->
         forall a, CondSet.In a conds ->
           PF.Satisfies S' (encPos I (fst a) (snd a))).
    Proof.
      intros I S' conds f; unfold condsConj.
      destruct (CondSet.elements conds) as [| a l] eqn:El; [discriminate |].
      intro Hf; injection Hf as <-.
      rewrite satisfies_conjFold; split.
      - intros [Hl Ha] b Hb; apply in_elements_cond in Hb; rewrite El in Hb.
        destruct Hb as [<- | Hb]; [exact Ha | exact (Hl _ Hb)].
      - intro H; split.
        + intros b Hb; apply H, in_elements_cond; rewrite El; right; exact Hb.
        + apply H, in_elements_cond; rewrite El; left; reflexivity.
    Qed.

    Lemma condsConj_none : forall I conds,
        condsConj I conds = None -> CondSet.Empty conds.
    Proof.
      intros I conds; unfold condsConj.
      destruct (CondSet.elements conds) as [| a l] eqn:El; [| discriminate].
      intros _ a Ha; apply in_elements_cond in Ha; rewrite El in Ha.
      destruct Ha.
    Qed.

    Lemma satisfies_disjCons : forall S' g l,
        PF.Satisfies S' (fold_right PF.FDisj g l) <->
        exists h, List.In h (g :: l) /\ PF.Satisfies S' h.
    Proof.
      intros S' g l; rewrite satisfies_disjList; split.
      - intros [H | [h [Hh H]]].
        + exists g; split; [left; reflexivity | exact H].
        + exists h; split; [right; exact Hh | exact H].
      - intros [h [[<- | Hh] H]]; [left; exact H | right; exists h; auto].
    Qed.

    Definition SupportHolds (S' : PF.PkgSet.t) (I : Inst) (p : Pkg.t) : Prop :=
      match supportForm I p with
      | Some f => PF.Satisfies S' f
      | None => True
      end.

    Lemma supportForm_spec : forall I S' S p,
        (forall q, PF.PkgSet.In (embedPkg q) S' <-> PkgSet.In q S) ->
        (forall n ct, PF.Satisfies S' (encPos I n ct) <-> MatchPos I S n ct) ->
        (SupportHolds S' I p <->
         (PkgSet.In p (inst_supp I) -> Supported I S p)).
    Proof.
      intros I S' S p Hemb Hpos; unfold SupportHolds, supportForm.
      assert (Halts : forall h, List.In h (supportAlts I p) ->
                 PF.Satisfies S' h -> Supported I S p).
      { intros h Hh Hs; unfold supportAlts in Hh.
        apply in_app_iff in Hh; destruct Hh as [Hh | Hh].
        - apply in_map_iff in Hh; destruct Hh as [r [<- Hr]].
          apply in_elements_pkg, mem_supporterSet in Hr.
          destruct Hr as [a [Hd Ho]].
          apply satisfies_provForm, Hemb in Hs.
          right; left; exists r, a; repeat split; assumption.
        - apply in_flat_map in Hh; destruct Hh as [[z conds] [Hz Hh]].
          apply in_elements_iif, mem_ownRules in Hz; destruct Hz as [Hz ->].
          destruct (condsConj I conds) as [f |] eqn:Ec; [| destruct Hh].
          destruct Hh as [<- | []].
          rewrite (condsConj_some I S' conds f Ec) in Hs.
          right; right; exists conds; split; [exact Hz |].
          intros n ct Hc; apply Hpos; exact (Hs (n, ct) Hc). }
      destruct (PkgSet.mem p (inst_supp I)) eqn:Em; cbn [negb orb].
      2: { split; [intros _ Hm | intros _; exact Logic.I].
           apply PkgSet.mem_spec in Hm; congruence. }
      assert (Hm : PkgSet.In p (inst_supp I)) by (apply PkgSet.mem_spec; exact Em).
      destruct (rootSupportsb I p) eqn:Er; cbn [orb].
      - split; [intros _ _ | intros _; exact Logic.I].
        apply rootSupportsb_spec in Er; left; exact Er.
      - destruct (vacuousRuleb I p) eqn:Ev.
        + split; [intros _ _ | intros _; exact Logic.I].
          apply vacuousRuleb_spec in Ev; destruct Ev as [conds [Hin He]].
          right; right; exists conds; split; [exact Hin |].
          intros n ct Hc; destruct (He _ Hc).
        + assert (Hback : Supported I S p ->
                    exists h, List.In h (supportAlts I p) /\ PF.Satisfies S' h).
          { intros [Hw | [[r [a [Hr [Hd Ho]]]] | [conds [Hin Hc]]]].
            - apply rootSupportsb_spec in Hw; congruence.
            - exists (provForm r); split.
              + unfold supportAlts; apply in_app_iff; left.
                apply in_map_iff; exists r; split; [reflexivity |].
                apply in_elements_pkg, mem_supporterSet.
                exists a; split; assumption.
              + apply satisfies_provForm, Hemb; exact Hr.
            - destruct (condsConj I conds) as [f |] eqn:Ec.
              + exists f; split.
                * unfold supportAlts; apply in_app_iff; right.
                  apply in_flat_map; exists (p, conds); split.
                  -- apply in_elements_iif, mem_ownRules; split;
                       [exact Hin | reflexivity].
                  -- cbv beta iota; rewrite Ec; left; reflexivity.
                * apply (condsConj_some I S' conds f Ec).
                  intros [n ct] Ha; apply Hpos; exact (Hc n ct Ha).
              + exfalso.
                assert (Hv : vacuousRuleb I p = true).
                { apply vacuousRuleb_spec; exists conds; split;
                    [exact Hin | exact (condsConj_none I conds Ec)]. }
                congruence. }
          destruct (supportAlts I p) as [| g l] eqn:Ea.
          * split; [cbn [PF.Satisfies]; intros [w [Hw _]];
                    destruct (PF.VSet.empty_spec Hw) |].
            intro Hs; destruct (Hback (Hs Hm)) as [h [[] _]].
          * rewrite satisfies_disjCons; split.
            -- intros [h [Hh Hs]] _; exact (Halts h Hh Hs).
            -- intro Hs; exact (Hback (Hs Hm)).
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
      assert (Hsel := fun q =>
                selectableAlts_spec I S' (alpineResolution S') q
                  (fun p => iff_sym (mem_alpineResolution S' p))
                  (fun n ct => match_decode I S' n ct Hres)).
      rewrite satisfies_encReq, (base_decode I S' n ct Hres).
      unfold MatchReq; rewrite or_assoc.
      apply or_iff_compat_l, or_iff_compat_l, and_iff_compat_l; split.
      - intros [q [Hq Hg]]; apply Hsel in Hg; destruct Hg as [HqS Ha].
        apply mem_uprovSet in Hq.
        exists q; split; [exact (proj1 Hq) | split; assumption].
      - intros [q [Hp [HqS Ha]]]; exists q; split.
        + apply mem_uprovSet; split; [exact Hp |].
          apply mem_alpineResolution in HqS.
          exact (embed_transR _ _ (Hsub _ HqS)).
        + apply Hsel; split; assumption.
    Qed.

    (* An install-if rule with no conditions has no atom to designate, so
       the obligation res_installIf states unconditionally would have
       nothing to carry it. *)
    Definition WfInstallIf (I : Inst) : Prop :=
      forall z conds, InstallIf.In (z, conds) (inst_installIf I) ->
      ~ CondSet.Empty conds.

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
        assert (HM := Hc _ _ Hin).
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
          apply FSet.union_spec; left.
          apply SOtf.mem_map; exists (z, conds); split;
            [exact Hfib | reflexivity]. }
        assert (Hdep : PF.DepRel.In (embedPkg p, installIfForm I z conds)
                         (transD I)).
        { apply mem_transD; split; [apply Hsub; exact HpS | exact Hf]. }
        assert (Hs := Hclo _ HpS _ Hdep).
        apply satisfies_installIfForm in Hs.
        destruct Hs as [[a [Ha Hn]] | Hb].
        + exfalso; apply Hn.
          destruct a as [m ct].
          apply (proj2 (match_decode _ _ _ _ Hres)).
          exact (Hc _ _ (condRest_subset _ _ Ha)).
        + exact (proj1 (match_decode _ _ _ _ Hres) Hb).
      - intros p Hp Hm; apply mem_alpineResolution in Hp.
        refine (proj1 (supportForm_spec I S' (alpineResolution S') p
                 (fun q => iff_sym (mem_alpineResolution S' q))
                 (fun n ct => match_decode I S' n ct Hres)) _ Hm).
        unfold SupportHolds.
        destruct (supportForm I p) as [f |] eqn:Ef; [| exact Logic.I].
        apply (Hclo _ Hp); apply mem_transD; split; [apply Hsub; exact Hp |].
        destruct p as [np vp]; cbn [dependees embedPkg fst snd].
        apply FSet.union_spec; right; apply FSet.union_spec; right.
        apply FSet.union_spec; right; rewrite Ef.
        apply FSet.singleton_spec; reflexivity.
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

    Lemma embed_transS : forall I S p,
        PF.PkgSet.In (embedPkg p) (transS I S) <-> PkgSet.In p S.
    Proof.
      intros I S p; rewrite mem_transS; split.
      - intros [H | [[p0 [Hp0 He]] | [q [m [pv [_ [_ He]]]]]]].
        + destruct p; discriminate H.
        + apply embedPkg_injective in He; subst p0; exact Hp0.
        + destruct p; injection He as _ He; discriminate He.
      - intro H; right; left; exists p; split; [exact H | reflexivity].
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
      assert (Hsel := fun q =>
                selectableAlts_spec I (transS I S) S q
                  (embed_transS I S)
                  (fun n ct => match_transS I S n ct Hsub)).
      rewrite satisfies_encReq, (base_transS I S n ct Hsub).
      unfold MatchReq; rewrite or_assoc.
      apply or_iff_compat_l, or_iff_compat_l, and_iff_compat_l; split.
      - intros [q [Hq Hg]]; apply Hsel in Hg; destruct Hg as [HqS Ha].
        apply mem_uprovSet in Hq.
        exists q; split; [exact (proj1 Hq) | split; assumption].
      - intros [q [Hp [HqS Ha]]]; exists q; split.
        + apply mem_uprovSet; split; [exact Hp | exact (Hsub _ HqS)].
        + apply Hsel; split; assumption.
    Qed.

    Theorem alpine_completeness : forall I S,
        WfAlias I -> IsResolution I S ->
        PF.IsResolution (transR I) (transD I) rootPkg (transS I S).
    Proof.
      intros I S [Wf1 Wf2] Hres.
      destruct Hres as [Hsub Hw Hd Hcu Ht Hsp].
      assert (Hiff := fun n ct => match_transS I S n ct Hsub).
      assert (Hreq := fun n ct => match_req_transS I S n ct Hsub).
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
          * apply FSet.union_spec in Hf; destruct Hf as [Hf | Hf].
            2: { destruct (supportForm I (n0, v0)) as [g |] eqn:Eg;
                   [| destruct (FSet.empty_spec Hf)].
                 apply FSet.singleton_spec in Hf; subst f.
                 assert (Hs := proj2 (supportForm_spec I (transS I S) S
                                        (n0, v0) (embed_transS I S) Hiff)
                                 (Hsp _ Hp)).
                 unfold SupportHolds in Hs; rewrite Eg in Hs; exact Hs. }
            apply SOtf.mem_map in Hf; destruct Hf as [[z conds] [Hfib ->]].
            apply mem_installIfFibre in Hfib.
            destruct Hfib as [Ht0 Hatt]; unfold attachDesignation in Hatt.
            destruct (D.designation conds) as [a |] eqn:Edes; [| discriminate].
            apply satisfies_installIfForm.
            destruct (CondSet.exists_
                        (fun b => negb (PF.satisfiesb (transS I S)
                                          (encPos I (fst b) (snd b))))
                        (condRest conds)) eqn:Ee.
            -- apply CondSet.exists_spec' in Ee.
               destruct Ee as [b [Hb Hnb]].
               apply Bool.negb_true_iff in Hnb.
               left; exists b; split; [exact Hb |].
               intro Hs; apply PF.satisfiesb_iff in Hs; congruence.
            -- right; apply Hiff, (Ht z conds Ht0).
               intros m ct Hc.
               destruct (Atom.eq_dec (m, ct) a) as [He | Hne].
               ++ apply matchPos_attachAt; exists (n0, v0).
                  split; [exact Hp | destruct He; exact Hatt].
               ++ assert (Hr : CondSet.In (m, ct) (condRest conds)).
                  { unfold condRest; rewrite Edes.
                    apply CondSet.remove_spec; split;
                      [exact Hc | exact Hne]. }
                  assert (Hbt : PF.satisfiesb (transS I S)
                                  (encPos I m ct) = true).
                  { destruct (PF.satisfiesb (transS I S) (encPos I m ct))
                      eqn:Eb; [reflexivity |].
                    exfalso.
                    assert (Hex : CondSet.exists_
                                    (fun b =>
                                       negb (PF.satisfiesb (transS I S)
                                               (encPos I (fst b) (snd b))))
                                    (condRest conds) = true).
                    { apply CondSet.exists_spec'; exists (m, ct); split;
                        [exact Hr | cbn; rewrite Eb; reflexivity]. }
                    congruence. }
                  apply Hiff; apply PF.satisfiesb_iff; exact Hbt.
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

      (* Any instance whose repository and provides agree with I at the
         names in ns answers every constraint at those names alike. *)
      Definition subInst (I : Inst) (ns : NSet.t) (deps : Deps.t)
          (ownProv : Prov.t) (installIf : InstallIf.t) (world : WSet.t)
          (prio : Prio.t) : Inst :=
        {| inst_repo := repoPreimage I ns
         ; inst_deps := deps
         ; inst_prov := Prov.union ownProv (provPreimage I ns)
         ; inst_installIf := installIf
         ; inst_world := world
         ; inst_prio := prio
         ; inst_repl := Repl.empty
         ; inst_supp := inst_supp I |}.

      Lemma constrVers_subInst : forall I ns deps ownProv installIf world prio n ct,
          NSet.In n ns ->
          Prov.Subset ownProv (inst_prov I) ->
          constrVers (subInst I ns deps ownProv installIf world prio) n ct =
          constrVers I n ct.
      Proof.
        intros I ns deps ownProv installIf world prio n ct Hn Hown.
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

      Lemma uprovSet_subInst : forall I ns deps ownProv installIf world prio n,
          NSet.In n ns ->
          Prov.Subset ownProv (inst_prov I) ->
          uprovSet (subInst I ns deps ownProv installIf world prio) n =
          uprovSet I n.
      Proof.
        intros I ns deps ownProv installIf world prio n Hn Hown.
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
          InstallIf.empty WSet.empty Prio.empty.

      Theorem versions_lookupName : forall I n,
          versions (nameSubInst I n) n = versions I n.
      Proof.
        intros I n; unfold versions, nameSubInst.
        apply constrVers_subInst.
        - apply NSet.singleton_spec; reflexivity.
        - intros e He; destruct (Prov.empty_spec He).
      Qed.

      Module SOwn := SetOps DepOT N WSet NSet.
      Module SOan := SetOps Atom N CondSet NSet.
      Module SOtn := SetOps InstallIfElt N InstallIf NSet.

      Definition condNames (conds : CondSet.t) : NSet.t :=
        SOan.map fst conds.

      Lemma encPos_subInst : forall I ns deps ownProv installIf world prio
              (n : N.t) (ct : Constr),
          NSet.In n ns ->
          Prov.Subset ownProv (inst_prov I) ->
          encPos (subInst I ns deps ownProv installIf world prio) n ct =
          encPos I n ct.
      Proof.
        intros I ns deps ownProv installIf world prio n ct Hn Hown.
        apply encPos_agree.
        - apply constrVers_subInst; assumption.
        - apply uprovSet_subInst; assumption.
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

      Lemma installIfForm_subInst : forall I ns deps ownProv installIf world prio
              (z : Pkg.t) (conds : CondSet.t),
          NSet.In (fst z) ns ->
          (forall a : Atom.t,
              CondSet.In a (condRest conds) -> NSet.In (fst a) ns) ->
          Prov.Subset ownProv (inst_prov I) ->
          installIfForm (subInst I ns deps ownProv installIf world prio) z conds =
          installIfForm I z conds.
      Proof.
        intros I ns deps ownProv installIf world prio z conds Hz Hc Hown.
        unfold installIfForm.
        rewrite (encPos_subInst I ns deps ownProv installIf world prio (fst z) CAny
                   Hz Hown).
        apply negFold_agree; intros a Ha.
        apply in_elements_cond in Ha.
        apply encPos_subInst; [exact (Hc _ Ha) | exact Hown].
      Qed.

      Lemma subInst_installIf : forall I ns deps ownProv installIf world prio,
          inst_installIf (subInst I ns deps ownProv installIf world prio) =
          installIf.
      Proof. reflexivity. Qed.

      (* Attachment reads the package itself and the provides entries it
         is the tail of, so a sub-instance keeping that fibre answers
         alike. *)
      Lemma attachAt_subInst : forall I ns deps ownProv installIf world prio p a,
          Prov.Subset ownProv (inst_prov I) ->
          (forall m tg, Prov.In (p, (m, tg)) (inst_prov I) ->
             Prov.In (p, (m, tg)) ownProv) ->
          attachAt (subInst I ns deps ownProv installIf world prio) p a =
          attachAt I p a.
      Proof.
        intros I ns deps ownProv installIf world prio p a Hown Hcov.
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
        forall I ns deps ownProv installIf world prio p conds,
          Prov.Subset ownProv (inst_prov I) ->
          (forall m tg, Prov.In (p, (m, tg)) (inst_prov I) ->
             Prov.In (p, (m, tg)) ownProv) ->
          attachDesignation (subInst I ns deps ownProv installIf world prio) p
            conds = attachDesignation I p conds.
      Proof.
        intros I ns deps ownProv installIf world prio p conds Hown Hcov.
        unfold attachDesignation; destruct (D.designation conds) as [a |];
          [apply attachAt_subInst; assumption | reflexivity].
      Qed.

      Lemma installIfFibre_subInst :
        forall I ns deps ownProv installIf world prio p,
          Prov.Subset ownProv (inst_prov I) ->
          (forall m tg, Prov.In (p, (m, tg)) (inst_prov I) ->
             Prov.In (p, (m, tg)) ownProv) ->
          InstallIf.Subset (installIfFibre I p) installIf ->
          InstallIf.Subset installIf (inst_installIf I) ->
          installIfFibre (subInst I ns deps ownProv installIf world prio) p =
          installIfFibre I p.
      Proof.
        intros I ns deps ownProv installIf world prio p Hown Hcov Hfib Hsub.
        apply InstallIf.ext; intros [z conds].
        rewrite (mem_installIfFibre
                   (subInst I ns deps ownProv installIf world prio)
                   p z conds).
        rewrite subInst_installIf.
        rewrite (attachDesignation_subInst I ns deps ownProv
                   installIf world prio p conds Hown Hcov).
        rewrite (mem_installIfFibre I p z conds).
        split.
        - intros [Hin Ha]; split; [exact (Hsub _ Hin) | exact Ha].
        - intros [Hin Ha]; split; [| exact Ha].
          apply Hfib, mem_installIfFibre; split; assumption.
      Qed.

      Definition anyName (d : Dep) : option N.t :=
        match d with
        | DPos (m, ct) => if isAny ct then Some m else None
        | DNeg _ => None
        end.

      Definition anyNames (I : Inst) (p : Pkg.t) : NSet.t :=
        SOdn.filterMap (fun '(_, d) => anyName d)
          (DepsFibred.tailFibre (inst_deps I) p).

      Definition rootAnyNames (I : Inst) : NSet.t :=
        SOwn.filterMap anyName (inst_world I).

      Definition bareProviders (I : Inst) (ns : NSet.t) : PkgSet.t :=
        SOrp.filterMap
          (fun '(q, (m, tg)) =>
             match tg with
             | PVirt => if NSet.mem m ns then Some q else None
             | PVer _ => None
             end)
          (inst_prov I).

      Definition noPriority (I : Inst) (ns : NSet.t) : PkgSet.t :=
        PkgSet.filter (fun q => negb (hasPriorityb I q)) (bareProviders I ns).

      Module SOpn := SetOps Pkg N PkgSet NSet.
      Definition ownNamesOf (I : Inst) (qs : PkgSet.t) : NSet.t :=
        SOpn.unionMap (ownNames I) qs.

      Definition depsOn (I : Inst) (ms : NSet.t) : Deps.t :=
        Deps.filter (fun '(_, d) => reqName ms d) (inst_deps I).

      Definition worldOn (I : Inst) (ms : NSet.t) : WSet.t :=
        WSet.filter (reqName ms) (inst_world I).

      Definition provOf (I : Inst) (qs : PkgSet.t) : Prov.t :=
        Prov.filter (fun '(q, _) => PkgSet.mem q qs) (inst_prov I).

      Definition rulesOf (I : Inst) (qs : PkgSet.t) : InstallIf.t :=
        InstallIf.filter (fun '(z, _) => PkgSet.mem z qs) (inst_installIf I).

      Definition prioOf (I : Inst) (qs : PkgSet.t) : Prio.t :=
        Prio.filter (fun '(q, _) => PkgSet.mem q qs) (inst_prio I).

      Definition ruleCondNames (rs : InstallIf.t) : NSet.t :=
        SOtn.unionMap (fun '(_, conds) => condNames conds) rs.

      Lemma mem_anyNames : forall I p m,
          NSet.In m (anyNames I p) <->
          exists ct, Deps.In (p, DPos (m, ct)) (inst_deps I) /\
            isAny ct = true.
      Proof.
        intros I p m; unfold anyNames; rewrite SOdn.mem_filterMap; split.
        - intros [[p' d] [Hin Hf]].
          apply DepsFibred.mem_tailFibre in Hin; destruct Hin as [Hin ->].
          destruct d as [[m' ct] | [m' ct]]; cbn in Hf; [| discriminate].
          destruct (isAny ct) eqn:Ea; [| discriminate].
          injection Hf as <-; exists ct; split; assumption.
        - intros [ct [Hin Ha]]; exists (p, DPos (m, ct)); split.
          + apply DepsFibred.mem_tailFibre; split; [exact Hin | reflexivity].
          + cbn; rewrite Ha; reflexivity.
      Qed.

      Lemma mem_rootAnyNames : forall I m,
          NSet.In m (rootAnyNames I) <->
          exists ct, WSet.In (DPos (m, ct)) (inst_world I) /\
            isAny ct = true.
      Proof.
        intros I m; unfold rootAnyNames; rewrite SOwn.mem_filterMap; split.
        - intros [d [Hin Hf]].
          destruct d as [[m' ct] | [m' ct]]; cbn in Hf; [| discriminate].
          destruct (isAny ct) eqn:Ea; [| discriminate].
          injection Hf as <-; exists ct; split; assumption.
        - intros [ct [Hin Ha]]; exists (DPos (m, ct)); split;
            [exact Hin | cbn; rewrite Ha; reflexivity].
      Qed.

      Lemma mem_bareProviders : forall I ns q,
          PkgSet.In q (bareProviders I ns) <->
          exists m, Prov.In (q, (m, PVirt)) (inst_prov I) /\ NSet.In m ns.
      Proof.
        intros I ns q; unfold bareProviders; rewrite SOrp.mem_filterMap.
        split.
        - intros [[q' [m tg]] [Hin Hf]]; cbn in Hf.
          destruct tg as [pv |]; [discriminate |].
          destruct (NSet.mem m ns) eqn:Em; [| discriminate].
          injection Hf as <-; apply NSet.mem_spec in Em.
          exists m; split; assumption.
        - intros [m [Hin Hm]]; exists (q, (m, PVirt)); split;
            [exact Hin | cbn].
          rewrite (proj2 (NSet.mem_spec _ _) Hm); reflexivity.
      Qed.

      Lemma mem_noPriority : forall I ns q,
          PkgSet.In q (noPriority I ns) <->
          PkgSet.In q (bareProviders I ns) /\ hasPriorityb I q = false.
      Proof.
        intros I ns q; unfold noPriority; rewrite PkgSet.filter_spec'.
        rewrite Bool.negb_true_iff; reflexivity.
      Qed.

      Lemma ownNames_ownNamesOf : forall I qs q,
          PkgSet.In q qs -> NSet.Subset (ownNames I q) (ownNamesOf I qs).
      Proof.
        intros I qs q Hq m Hm; unfold ownNamesOf; apply SOpn.mem_unionMap.
        exists q; split; assumption.
      Qed.

      Lemma mem_depsOn : forall I ms r d,
          Deps.In (r, d) (depsOn I ms) <->
          Deps.In (r, d) (inst_deps I) /\ reqName ms d = true.
      Proof.
        intros I ms r d; unfold depsOn; rewrite Deps.filter_spec'.
        reflexivity.
      Qed.

      Lemma mem_worldOn : forall I ms d,
          WSet.In d (worldOn I ms) <->
          WSet.In d (inst_world I) /\ reqName ms d = true.
      Proof.
        intros I ms d; unfold worldOn; rewrite WSet.filter_spec'.
        reflexivity.
      Qed.

      Lemma mem_provOf : forall I qs q x,
          Prov.In (q, x) (provOf I qs) <->
          Prov.In (q, x) (inst_prov I) /\ PkgSet.In q qs.
      Proof.
        intros I qs q x; unfold provOf; rewrite Prov.filter_spec'.
        cbn; rewrite PkgSet.mem_spec; reflexivity.
      Qed.

      Lemma mem_rulesOf : forall I qs z conds,
          InstallIf.In (z, conds) (rulesOf I qs) <->
          InstallIf.In (z, conds) (inst_installIf I) /\ PkgSet.In z qs.
      Proof.
        intros I qs z conds; unfold rulesOf; rewrite InstallIf.filter_spec'.
        cbn; rewrite PkgSet.mem_spec; reflexivity.
      Qed.

      Lemma mem_prioOf : forall I qs q k,
          Prio.In (q, k) (prioOf I qs) <->
          Prio.In (q, k) (inst_prio I) /\ PkgSet.In q qs.
      Proof.
        intros I qs q k; unfold prioOf; rewrite Prio.filter_spec'.
        cbn; rewrite PkgSet.mem_spec; reflexivity.
      Qed.

      Lemma depsOn_subset : forall I ms,
          Deps.Subset (depsOn I ms) (inst_deps I).
      Proof.
        intros I ms [r d] H; apply mem_depsOn in H; exact (proj1 H).
      Qed.

      Lemma worldOn_subset : forall I ms,
          WSet.Subset (worldOn I ms) (inst_world I).
      Proof.
        intros I ms d H; apply mem_worldOn in H; exact (proj1 H).
      Qed.

      Lemma provOf_subset : forall I qs,
          Prov.Subset (provOf I qs) (inst_prov I).
      Proof.
        intros I qs [q x] H; apply mem_provOf in H; exact (proj1 H).
      Qed.

      Lemma rulesOf_subset : forall I qs,
          InstallIf.Subset (rulesOf I qs) (inst_installIf I).
      Proof.
        intros I qs [z conds] H; apply mem_rulesOf in H; exact (proj1 H).
      Qed.

      Lemma prioOf_subset : forall I qs,
          Prio.Subset (prioOf I qs) (inst_prio I).
      Proof.
        intros I qs [q k] H; apply mem_prioOf in H; exact (proj1 H).
      Qed.

      Lemma condName_ruleCondNames : forall rs z conds a,
          InstallIf.In (z, conds) rs -> CondSet.In a conds ->
          NSet.In (fst a) (ruleCondNames rs).
      Proof.
        intros rs z conds a Hr Ha; unfold ruleCondNames.
        apply SOtn.mem_unionMap; exists (z, conds); split; [exact Hr |].
        cbv beta iota; unfold condNames; apply SOan.mem_map.
        exists a; split; [exact Ha | reflexivity].
      Qed.

      Lemma reqName_mono : forall ms ms' d,
          NSet.Subset ms ms' -> reqName ms d = true -> reqName ms' d = true.
      Proof.
        intros ms ms' d Hs Hr; apply reqName_spec in Hr.
        destruct Hr as [m [ct [-> Hm]]]; apply reqName_spec.
        exists m, ct; split; [reflexivity | exact (Hs _ Hm)].
      Qed.

      Lemma hasPriorityb_subInst : forall I ns deps ownProv installIf world prio q,
          Prio.Subset prio (inst_prio I) ->
          (forall k, Prio.In (q, k) (inst_prio I) -> Prio.In (q, k) prio) ->
          hasPriorityb (subInst I ns deps ownProv installIf world prio) q =
          hasPriorityb I q.
      Proof.
        intros I ns deps ownProv installIf world prio q Hsub Hcov.
        unfold hasPriorityb; cbn [subInst inst_prio].
        apply Prio.exists_restrict; [exact Hsub |].
        intros [q' k] Hin Hb; cbn in Hb.
        apply Bool.andb_true_iff in Hb; destruct Hb as [Hq _].
        apply PkgEqb.eqb_true_iff in Hq; subst q'; exact (Hcov _ Hin).
      Qed.

      Lemma ownNames_subInst : forall I ns deps ownProv installIf world prio q,
          Prov.Subset ownProv (inst_prov I) ->
          (forall m tg, Prov.In (q, (m, tg)) (inst_prov I) ->
             Prov.In (q, (m, tg)) ownProv) ->
          ownNames (subInst I ns deps ownProv installIf world prio) q =
          ownNames I q.
      Proof.
        intros I ns deps ownProv installIf world prio q Hown Hcov.
        apply NSet.ext; intro m; rewrite !mem_ownNames.
        cbn [subInst inst_prov].
        apply or_iff_compat_l; split; intros [pv Hp]; exists pv.
        - apply Prov.union_spec in Hp; destruct Hp as [Hp | Hp];
            [exact (Hown _ Hp) |].
          apply mem_provPreimage in Hp; exact (proj1 Hp).
        - apply Prov.union_spec; left; exact (Hcov _ _ Hp).
      Qed.

      Lemma rootRequiresb_subInst :
        forall I ns deps ownProv installIf world prio ms,
          WSet.Subset world (inst_world I) ->
          (forall d, WSet.In d (inst_world I) -> reqName ms d = true ->
             WSet.In d world) ->
          rootRequiresb (subInst I ns deps ownProv installIf world prio) ms =
          rootRequiresb I ms.
      Proof.
        intros I ns deps ownProv installIf world prio ms Hsub Hcov.
        unfold rootRequiresb; cbn [subInst inst_world].
        apply WSet.exists_restrict; assumption.
      Qed.

      Lemma requirerSet_subInst :
        forall I ns deps ownProv installIf world prio ms,
          Deps.Subset deps (inst_deps I) ->
          (forall e, Deps.In e (inst_deps I) -> reqName ms (snd e) = true ->
             Deps.In e deps) ->
          requirerSet (subInst I ns deps ownProv installIf world prio) ms =
          requirerSet I ms.
      Proof.
        intros I ns deps ownProv installIf world prio ms Hsub Hcov.
        apply PkgSet.ext; intro r; unfold requirerSet.
        cbn [subInst inst_deps].
        apply SOdp.filterMap_restrict; [exact Hsub |].
        intros [r' d] Hin Hf; cbn in Hf.
        destruct (reqName ms d) eqn:E; [| discriminate].
        exact (Hcov _ Hin E).
      Qed.

      Lemma ownRules_subInst : forall I ns deps ownProv installIf world prio q,
          InstallIf.Subset installIf (inst_installIf I) ->
          (forall conds, InstallIf.In (q, conds) (inst_installIf I) ->
             InstallIf.In (q, conds) installIf) ->
          ownRules (subInst I ns deps ownProv installIf world prio) q =
          ownRules I q.
      Proof.
        intros I ns deps ownProv installIf world prio q Hsub Hcov.
        apply InstallIf.ext; intros [z conds].
        rewrite !mem_ownRules; cbn [subInst inst_installIf]; split.
        - intros [H ->]; split; [exact (Hsub _ H) | reflexivity].
        - intros [H ->]; split; [exact (Hcov _ H) | reflexivity].
      Qed.

      Lemma condsForm_agree : forall I I' q conds,
          (forall a, CondSet.In a conds ->
             encPos I' (fst a) (snd a) = encPos I (fst a) (snd a)) ->
          condsForm I' q conds = condsForm I q conds.
      Proof.
        intros I I' q conds H; unfold condsForm.
        assert (Hl : forall l,
                   (forall a, List.In a l ->
                      encPos I' (fst a) (snd a) = encPos I (fst a) (snd a)) ->
                   fold_right
                     (fun a f => PF.FConj (encPos I' (fst a) (snd a)) f)
                     (provForm q) l =
                   fold_right
                     (fun a f => PF.FConj (encPos I (fst a) (snd a)) f)
                     (provForm q) l).
        { induction l as [| a l IH]; intro Ha; cbn [fold_right];
            [reflexivity |].
          rewrite (Ha a (or_introl eq_refl)), IH; [reflexivity |].
          intros b Hb; apply Ha; right; exact Hb. }
        apply Hl; intros a Ha; apply H, in_elements_cond, Ha.
      Qed.

      Lemma selectableAlts_agree : forall I I' q,
          hasPriorityb I' q = hasPriorityb I q ->
          (hasPriorityb I q = false ->
           ownNames I' q = ownNames I q /\
           rootRequiresb I' (ownNames I q) = rootRequiresb I (ownNames I q) /\
           (rootRequiresb I (ownNames I q) = false ->
            requirerSet I' (ownNames I q) = requirerSet I (ownNames I q) /\
            ownRules I' q = ownRules I q /\
            (forall z conds a, InstallIf.In (z, conds) (ownRules I q) ->
               CondSet.In a conds ->
               encPos I' (fst a) (snd a) = encPos I (fst a) (snd a)))) ->
          selectableAlts I' q = selectableAlts I q.
      Proof.
        intros I I' q Hk Hrest; unfold selectableAlts; cbv zeta; rewrite Hk.
        destruct (hasPriorityb I q) eqn:Ek; [reflexivity |].
        destruct (Hrest eq_refl) as [Hn [Hr Hrest']].
        rewrite Hn, Hr; cbn [orb].
        destruct (rootRequiresb I (ownNames I q)) eqn:Er; [reflexivity |].
        destruct (Hrest' eq_refl) as [Hs [Ho Hc]].
        rewrite Hs, Ho; f_equal.
        apply map_ext_in; intros [z conds] Hz; cbv beta iota.
        apply condsForm_agree; intros a Ha.
        apply (Hc z conds a); [apply in_elements_iif; exact Hz | exact Ha].
      Qed.

      Lemma encReq_agree : forall I I' n ct,
          constrVers I' n ct = constrVers I n ct ->
          uprovSet I' n = uprovSet I n ->
          (isAny ct = true -> forall q, PkgSet.In q (uprovSet I n) ->
             selectableAlts I' q = selectableAlts I q) ->
          encReq I' n ct = encReq I n ct.
      Proof.
        intros I I' n ct Hc Hu Hg; unfold encReq, uprovL; cbv zeta.
        rewrite Hc, Hu.
        destruct (isAny ct) eqn:Ea; [| reflexivity].
        assert (H : forall l,
                   (forall q, List.In q l -> selectableAlts I' q = selectableAlts I q) ->
                   flat_map (selectableAlts I') l = flat_map (selectableAlts I) l).
        { induction l as [| q l IH]; intro Hl; cbn [flat_map];
            [reflexivity |].
          rewrite (Hl q (or_introl eq_refl)), IH; [reflexivity |].
          intros q0 Hq0; apply Hl; right; exact Hq0. }
        rewrite H; [reflexivity |].
        intros q Hq; apply (Hg eq_refl), in_elements_pkg, Hq.
      Qed.

      Lemma selectableAlts_subInst :
        forall I ns deps ownProv installIf world prio q,
          Prov.Subset ownProv (inst_prov I) ->
          Deps.Subset deps (inst_deps I) ->
          InstallIf.Subset installIf (inst_installIf I) ->
          WSet.Subset world (inst_world I) ->
          Prio.Subset prio (inst_prio I) ->
          (forall k, Prio.In (q, k) (inst_prio I) -> Prio.In (q, k) prio) ->
          (hasPriorityb I q = false ->
           (forall m tg, Prov.In (q, (m, tg)) (inst_prov I) ->
              Prov.In (q, (m, tg)) ownProv) /\
           (forall d, WSet.In d (inst_world I) ->
              reqName (ownNames I q) d = true -> WSet.In d world) /\
           (forall e, Deps.In e (inst_deps I) ->
              reqName (ownNames I q) (snd e) = true -> Deps.In e deps) /\
           (forall conds, InstallIf.In (q, conds) (inst_installIf I) ->
              InstallIf.In (q, conds) installIf) /\
           (forall conds a, InstallIf.In (q, conds) (inst_installIf I) ->
              CondSet.In a conds -> NSet.In (fst a) ns)) ->
          selectableAlts (subInst I ns deps ownProv installIf world prio) q =
          selectableAlts I q.
      Proof.
        intros I ns deps ownProv installIf world prio q
          Ho Hd Hi Hw Hp Cp Hrest.
        apply selectableAlts_agree.
        - apply hasPriorityb_subInst; assumption.
        - intro Ek; destruct (Hrest Ek) as [Ct [Cw [Cd [Ci Cn]]]].
          split; [apply ownNames_subInst; assumption |].
          split; [apply rootRequiresb_subInst; assumption |].
          intros _; split; [apply requirerSet_subInst; assumption |].
          split; [apply ownRules_subInst; assumption |].
          intros z conds a Hz Ha; apply mem_ownRules in Hz.
          destruct Hz as [Hz ->].
          apply encPos_subInst; [exact (Cn _ _ Hz Ha) | exact Ho].
      Qed.

      Theorem selectableAlts_lookup :
        forall I ns deps ownProv installIf world prio ns0 m q,
          Prov.Subset ownProv (inst_prov I) ->
          Deps.Subset deps (inst_deps I) ->
          InstallIf.Subset installIf (inst_installIf I) ->
          WSet.Subset world (inst_world I) ->
          Prio.Subset prio (inst_prio I) ->
          Prov.Subset (provOf I (noPriority I ns0)) ownProv ->
          Deps.Subset (depsOn I (ownNamesOf I (noPriority I ns0))) deps ->
          InstallIf.Subset (rulesOf I (noPriority I ns0)) installIf ->
          WSet.Subset (worldOn I (ownNamesOf I (noPriority I ns0))) world ->
          Prio.Subset (prioOf I (bareProviders I ns0)) prio ->
          NSet.Subset (ruleCondNames (rulesOf I (noPriority I ns0))) ns ->
          NSet.In m ns0 -> PkgSet.In q (uprovSet I m) ->
          selectableAlts (subInst I ns deps ownProv installIf world prio) q =
          selectableAlts I q.
      Proof.
        intros I ns deps ownProv installIf world prio ns0 m q
          Ho Hd Hi Hw Hp Co Cd Ci Cw Cp Cn Hm Hq.
        apply mem_uprovSet in Hq; destruct Hq as [Hq _].
        assert (Hv : PkgSet.In q (bareProviders I ns0))
          by (apply mem_bareProviders; exists m; split; assumption).
        apply selectableAlts_subInst; try assumption.
        - intros k Hk; apply Cp, mem_prioOf; split; assumption.
        - intro Ek.
          assert (Hg : PkgSet.In q (noPriority I ns0))
            by (apply mem_noPriority; split; assumption).
          assert (Hms := ownNames_ownNamesOf I (noPriority I ns0) q Hg).
          split; [| split; [| split; [| split]]].
          + intros m' tg H; apply Co, mem_provOf; split; assumption.
          + intros d Hd' Hr; apply Cw, mem_worldOn; split;
              [exact Hd' | exact (reqName_mono _ _ d Hms Hr)].
          + intros [r d] Hd' Hr; apply Cd, mem_depsOn; split;
              [exact Hd' | exact (reqName_mono _ _ d Hms Hr)].
          + intros conds H; apply Ci, mem_rulesOf; split; assumption.
          + intros conds a H Ha; apply Cn.
            apply (condName_ruleCondNames _ q conds a); [| exact Ha].
            apply mem_rulesOf; split; assumption.
      Qed.

      Lemma encDep_subInst : forall I ns deps ownProv installIf world prio d,
          NSet.In (depName d) ns ->
          Prov.Subset ownProv (inst_prov I) ->
          (forall m ct, d = DPos (m, ct) -> isAny ct = true ->
             forall q, PkgSet.In q (uprovSet I m) ->
             selectableAlts (subInst I ns deps ownProv installIf world prio) q =
             selectableAlts I q) ->
          encDep (subInst I ns deps ownProv installIf world prio) d =
          encDep I d.
      Proof.
        intros I ns deps ownProv installIf world prio [[m ct] | [m ct]]
          Hn Hown Hg; cbn [encDep depName] in Hn |- *.
        - apply encReq_agree.
          + apply constrVers_subInst; assumption.
          + apply uprovSet_subInst; assumption.
          + exact (Hg m ct eq_refl).
        - f_equal; apply encPos_subInst; assumption.
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
          NSet.In (fst a) (pkgNames I p).
      Proof.
        intros I p z conds a Ht Ha; unfold pkgNames.
        apply NSet.union_spec; right.
        apply SOtn.mem_unionMap; exists (z, conds); split; [exact Ht |].
        cbv beta iota; apply NSet.add_spec; right.
        unfold condNames; apply SOan.mem_map; exists a; split;
          [exact Ha | reflexivity].
      Qed.

      Definition offeredNames (I : Inst) (p : Pkg.t) : NSet.t :=
        NSet.add (fst p)
          (SOrn.filterMap
             (fun '(q, (m, _)) => if PkgEqb.eqb q p then Some m else None)
             (inst_prov I)).

      Definition supportNames (I : Inst) (p : Pkg.t) : NSet.t :=
        if PkgSet.mem p (inst_supp I) then offeredNames I p else NSet.empty.

      Lemma offers_offeredNames : forall I p a,
          Offers I p a -> NSet.In (fst a) (offeredNames I p).
      Proof.
        intros I p a Ho; unfold offeredNames; apply NSet.add_spec.
        destruct Ho as [[He _] | [[pv [Hr _]] | [_ [Hr _]]]];
          [left; symmetry; exact He | right | right];
          apply SOrn.mem_filterMap;
          [exists (p, (fst a, PVer pv)) | exists (p, (fst a, PVirt))];
          (split; [assumption | cbn]);
          rewrite (proj2 (PkgEqb.eqb_true_iff p p) eq_refl); reflexivity.
      Qed.

      Lemma depsOn_mono : forall I ms ms',
          NSet.Subset ms ms' -> Deps.Subset (depsOn I ms) (depsOn I ms').
      Proof.
        intros I ms ms' Hs [r d] H; apply mem_depsOn in H.
        apply mem_depsOn; split; [exact (proj1 H) |].
        exact (reqName_mono _ _ d Hs (proj2 H)).
      Qed.

      Lemma rulesOf_mono : forall I qs qs',
          PkgSet.Subset qs qs' ->
          InstallIf.Subset (rulesOf I qs) (rulesOf I qs').
      Proof.
        intros I qs qs' Hs [z conds] H; apply mem_rulesOf in H.
        apply mem_rulesOf; split; [exact (proj1 H) | exact (Hs _ (proj2 H))].
      Qed.

      Lemma prioOf_mono : forall I qs qs',
          PkgSet.Subset qs qs' -> Prio.Subset (prioOf I qs) (prioOf I qs').
      Proof.
        intros I qs qs' Hs [q k] H; apply mem_prioOf in H.
        apply mem_prioOf; split; [exact (proj1 H) | exact (Hs _ (proj2 H))].
      Qed.

      Lemma ruleCondNames_mono : forall rs rs',
          InstallIf.Subset rs rs' ->
          NSet.Subset (ruleCondNames rs) (ruleCondNames rs').
      Proof.
        intros rs rs' Hs m H; unfold ruleCondNames in *.
        apply SOtn.mem_unionMap in H; destruct H as [x [Hx Hm]].
        apply SOtn.mem_unionMap; exists x; split; [exact (Hs _ Hx) | exact Hm].
      Qed.

      Lemma offersb_subInst :
        forall I ns deps ownProv installIf world prio p a,
          Prov.Subset ownProv (inst_prov I) ->
          (forall m tg, Prov.In (p, (m, tg)) (inst_prov I) ->
             Prov.In (p, (m, tg)) ownProv) ->
          Prio.Subset prio (inst_prio I) ->
          (forall k, Prio.In (p, k) (inst_prio I) -> Prio.In (p, k) prio) ->
          offersb (subInst I ns deps ownProv installIf world prio) p a =
          offersb I p a.
      Proof.
        intros I ns deps ownProv installIf world prio p a Hown Hcov Hp Cp.
        unfold offersb.
        rewrite (hasPriorityb_subInst I ns deps ownProv installIf world prio p
                   Hp Cp).
        f_equal; cbn [subInst inst_prov].
        apply Prov.exists_restrict.
        - intros e He; apply Prov.union_spec in He.
          destruct He as [He | He]; [exact (Hown _ He) |].
          apply mem_provPreimage in He; exact (proj1 He).
        - intros [q [m tg]] He Hb; cbn in Hb.
          apply Bool.andb_true_iff in Hb; destruct Hb as [Hq _].
          apply PkgEqb.eqb_true_iff in Hq; subst q.
          apply Prov.union_spec; left; exact (Hcov _ _ He).
      Qed.

      Lemma condsConj_agree : forall I I' conds,
          (forall a, CondSet.In a conds ->
             encPos I' (fst a) (snd a) = encPos I (fst a) (snd a)) ->
          condsConj I' conds = condsConj I conds.
      Proof.
        intros I I' conds H; unfold condsConj.
        destruct (CondSet.elements conds) as [| a l] eqn:El; [reflexivity |].
        assert (Hl : forall b, List.In b (a :: l) ->
                   encPos I' (fst b) (snd b) = encPos I (fst b) (snd b)).
        { intros b Hb; apply H, in_elements_cond; rewrite El; exact Hb. }
        f_equal; rewrite (Hl a (or_introl eq_refl)).
        assert (Hf : forall l' base,
                   (forall b, List.In b l' ->
                      encPos I' (fst b) (snd b) = encPos I (fst b) (snd b)) ->
                   fold_right
                     (fun b f => PF.FConj (encPos I' (fst b) (snd b)) f) base l' =
                   fold_right
                     (fun b f => PF.FConj (encPos I (fst b) (snd b)) f) base l').
        { induction l' as [| b l' IH]; intros base Hb; cbn [fold_right];
            [reflexivity |].
          rewrite (Hb b (or_introl eq_refl)), IH; [reflexivity |].
          intros c Hc; apply Hb; right; exact Hc. }
        apply Hf; intros b Hb; apply Hl; right; exact Hb.
      Qed.

      Lemma supportForm_agree : forall I I' p,
          inst_supp I' = inst_supp I ->
          rootSupportsb I' p = rootSupportsb I p ->
          (PkgSet.In p (inst_supp I) -> supporterSet I' p = supporterSet I p) ->
          ownRules I' p = ownRules I p ->
          (forall z conds a, InstallIf.In (z, conds) (ownRules I p) ->
             CondSet.In a conds ->
             encPos I' (fst a) (snd a) = encPos I (fst a) (snd a)) ->
          supportForm I' p = supportForm I p.
      Proof.
        intros I I' p Hq Hr Hs Ho Hc.
        unfold supportForm, vacuousRuleb, supportAlts.
        rewrite Hq, Hr, Ho.
        destruct (PkgSet.mem p (inst_supp I)) eqn:Em; cbn [negb orb];
          [| reflexivity].
        rewrite (Hs (proj1 (PkgSet.mem_spec _ _) Em)).
        assert (Hl : forall l,
                   (forall x, List.In x l -> InstallIf.In x (ownRules I p)) ->
                   flat_map
                     (fun '(_, conds) =>
                        match condsConj I' conds with
                        | Some f => f :: nil | None => nil end) l =
                   flat_map
                     (fun '(_, conds) =>
                        match condsConj I conds with
                        | Some f => f :: nil | None => nil end) l).
        { induction l as [| [z conds] l IH]; intro Hin; cbn [flat_map];
            [reflexivity |].
          rewrite (condsConj_agree I I' conds).
          - rewrite IH; [reflexivity |].
            intros x Hx; apply Hin; right; exact Hx.
          - intros a Ha; exact (Hc z conds a (Hin _ (or_introl eq_refl)) Ha). }
        rewrite Hl; [reflexivity |].
        intros x Hx; apply in_elements_iif; exact Hx.
      Qed.

      Lemma supportForm_subInst :
        forall I ns deps ownProv installIf world prio p,
          Prov.Subset ownProv (inst_prov I) ->
          (forall m tg, Prov.In (p, (m, tg)) (inst_prov I) ->
             Prov.In (p, (m, tg)) ownProv) ->
          Deps.Subset deps (inst_deps I) ->
          (PkgSet.In p (inst_supp I) ->
           Deps.Subset (depsOn I (offeredNames I p)) deps) ->
          InstallIf.Subset installIf (inst_installIf I) ->
          InstallIf.Subset (rulesOf I (PkgSet.singleton p)) installIf ->
          (forall d, WSet.In d world <-> WSet.In d (inst_world I)) ->
          Prio.Subset prio (inst_prio I) ->
          (forall k, Prio.In (p, k) (inst_prio I) -> Prio.In (p, k) prio) ->
          NSet.Subset (ruleCondNames (rulesOf I (PkgSet.singleton p))) ns ->
          supportForm (subInst I ns deps ownProv installIf world prio) p =
          supportForm I p.
      Proof.
        intros I ns deps ownProv installIf world prio p
          Ho Hcov Hd Cd Hi Ci Hw Hp Cp Cn.
        assert (Hoff : forall a,
                   Offers (subInst I ns deps ownProv installIf world prio) p a <->
                   Offers I p a).
        { intro a; rewrite <- !offersb_spec.
          rewrite (offersb_subInst I ns deps ownProv installIf world prio p a
                     Ho Hcov Hp Cp).
          reflexivity. }
        apply supportForm_agree; [reflexivity | | | |].
        - apply Bool.eq_iff_eq_true; rewrite !rootSupportsb_spec.
          cbn [subInst inst_world]; split; intros [a [Ha Hb]]; exists a;
            (split; [apply Hw; exact Ha + exact (proj2 (Hw _) Ha) |]);
            apply Hoff; exact Hb.
        - intro Hin; specialize (Cd Hin).
          apply PkgSet.ext; intro r; rewrite !mem_supporterSet.
          cbn [subInst inst_deps]; split; intros [a [Ha Hb]]; exists a.
          + split; [exact (Hd _ Ha) | apply Hoff; exact Hb].
          + split; [| apply Hoff; exact Hb].
            apply Cd, mem_depsOn; split; [exact Ha |].
            apply reqName_spec; exists (fst a), (snd a).
            split; [destruct a; reflexivity |].
            apply (offers_offeredNames I p a Hb).
        - apply ownRules_subInst; [exact Hi |].
          intros conds H; apply Ci, mem_rulesOf; split;
            [exact H | apply PkgSet.singleton_spec; reflexivity].
        - intros z conds a Hz Ha; apply mem_ownRules in Hz.
          destruct Hz as [Hz ->].
          apply encPos_subInst; [| exact Ho].
          apply Cn, (condName_ruleCondNames _ p conds a); [| exact Ha].
          apply mem_rulesOf; split;
            [exact Hz | apply PkgSet.singleton_spec; reflexivity].
      Qed.

      Definition pkgSubInst (I : Inst) (p : Pkg.t) : Inst :=
        subInst I
          (NSet.union (pkgNames I p)
             (ruleCondNames
                (rulesOf I (PkgSet.add p (noPriority I (anyNames I p))))))
          (Deps.union (DepsFibred.tailFibre (inst_deps I) p)
             (depsOn I (NSet.union (supportNames I p)
                          (ownNamesOf I (noPriority I (anyNames I p))))))
          (Prov.union (ProvFibred.tailFibre (inst_prov I) p)
             (provOf I (noPriority I (anyNames I p))))
          (InstallIf.union (installIfFibre I p)
             (rulesOf I (PkgSet.add p (noPriority I (anyNames I p)))))
          (inst_world I)
          (prioOf I (PkgSet.add p (bareProviders I (anyNames I p)))).

      Lemma tailFibre_union_own : forall D E p,
          Deps.Subset E D ->
          DepsFibred.tailFibre (Deps.union (DepsFibred.tailFibre D p) E) p =
          DepsFibred.tailFibre D p.
      Proof.
        intros D E p HE; apply Deps.ext; intros [p' d].
        rewrite !DepsFibred.mem_tailFibre, Deps.union_spec,
          DepsFibred.mem_tailFibre.
        split.
        - intros [[[H _] | H] Hp]; split; try exact Hp;
            [exact H | exact (HE _ H)].
        - intros [H Hp]; split; [left; split; assumption | exact Hp].
      Qed.

      Theorem dependees_lookupOrig : forall I n v,
          dependees (pkgSubInst I (n, v)) (embedPkg (n, v)) =
          dependees I (embedPkg (n, v)).
      Proof.
        intros I n v.
        assert (Hown : Prov.Subset
                         (Prov.union (ProvFibred.tailFibre (inst_prov I) (n, v))
                            (provOf I (noPriority I (anyNames I (n, v)))))
                         (inst_prov I)).
        { intros e He; apply Prov.union_spec in He; destruct He as [He | He];
            [exact (ProvFibred.tailFibre_subset _ _ _ He) |
             exact (provOf_subset _ _ _ He)]. }
        assert (Hcov : forall m tg,
                   Prov.In ((n, v), (m, tg)) (inst_prov I) ->
                   Prov.In ((n, v), (m, tg))
                     (Prov.union (ProvFibred.tailFibre (inst_prov I) (n, v))
                        (provOf I (noPriority I (anyNames I (n, v)))))).
        { intros m tg H; apply Prov.union_spec; left.
          apply ProvFibred.mem_tailFibre; split; [exact H | reflexivity]. }
        assert (Hdeps : Deps.Subset
                          (Deps.union (DepsFibred.tailFibre (inst_deps I) (n, v))
                             (depsOn I (NSet.union (supportNames I (n, v))
                                (ownNamesOf I
                                   (noPriority I (anyNames I (n, v)))))))
                          (inst_deps I)).
        { intros e He; apply Deps.union_spec in He; destruct He as [He | He];
            [exact (DepsFibred.tailFibre_subset _ _ _ He) |
             exact (depsOn_subset _ _ _ He)]. }
        assert (Hrules : InstallIf.Subset
                           (InstallIf.union (installIfFibre I (n, v))
                              (rulesOf I (PkgSet.add (n, v)
                                 (noPriority I (anyNames I (n, v))))))
                           (inst_installIf I)).
        { intros [z conds] He; apply InstallIf.union_spec in He.
          destruct He as [He | He];
            [apply mem_installIfFibre in He; exact (proj1 He) |
             exact (rulesOf_subset _ _ _ He)]. }
        assert (Hfib : installIfFibre (pkgSubInst I (n, v)) (n, v) =
                         installIfFibre I (n, v)).
        { unfold pkgSubInst; apply installIfFibre_subInst;
            try assumption.
          intros e He; apply InstallIf.union_spec; left; exact He. }
        assert (Hsel : forall m ct, Deps.In ((n, v), DPos (m, ct)) (inst_deps I) ->
                   isAny ct = true -> forall q, PkgSet.In q (uprovSet I m) ->
                   selectableAlts (pkgSubInst I (n, v)) q = selectableAlts I q).
        { intros m ct Hd Ha q Hq; unfold pkgSubInst.
          apply (selectableAlts_lookup I _ _ _ _ _ _ (anyNames I (n, v)) m q);
            try assumption.
          - intros d Hd'; exact Hd'.
          - exact (prioOf_subset _ _).
          - intros e He; apply Prov.union_spec; right; exact He.
          - intros e He; apply Deps.union_spec; right.
            apply (depsOn_mono I _ _ (fun x Hx => proj2 (NSet.union_spec _ _ _)
                                                   (or_intror Hx))).
            exact He.
          - intros e He; apply InstallIf.union_spec; right.
            apply (rulesOf_mono I _ _ (fun x Hx => proj2 (PkgSet.add_spec _ _ _)
                                                    (or_intror Hx))).
            exact He.
          - exact (worldOn_subset _ _).
          - apply prioOf_mono; intros x Hx; apply PkgSet.add_spec; right;
              exact Hx.
          - intros a Ha'; apply NSet.union_spec; right.
            apply (ruleCondNames_mono _ _
                     (rulesOf_mono I _ _ (fun x Hx => proj2 (PkgSet.add_spec _ _ _)
                                                       (or_intror Hx)))).
            exact Ha'.
          - apply mem_anyNames; exists ct; split; assumption. }
        assert (Hsup : supportForm (pkgSubInst I (n, v)) (n, v) =
                         supportForm I (n, v)).
        { unfold pkgSubInst; apply supportForm_subInst; try assumption.
          - intros Hin e He; apply Deps.union_spec; right.
            apply (depsOn_mono I (offeredNames I (n, v))).
            + intros x Hx; apply NSet.union_spec; left.
              unfold supportNames; rewrite (proj2 (PkgSet.mem_spec _ _) Hin).
              exact Hx.
            + exact He.
          - intros e He; apply InstallIf.union_spec; right.
            apply (rulesOf_mono I _ _ (fun x Hx =>
                     proj2 (PkgSet.add_spec _ _ _)
                       (or_introl (proj1 (PkgSet.singleton_spec _ _) Hx)))).
            exact He.
          - intro d; reflexivity.
          - exact (prioOf_subset _ _).
          - intros k Hk; apply mem_prioOf; split; [exact Hk |].
            apply PkgSet.add_spec; left; reflexivity.
          - intros a Ha'; apply NSet.union_spec; right.
            apply (ruleCondNames_mono _ _
                     (rulesOf_mono I _ _ (fun x Hx =>
                        proj2 (PkgSet.add_spec _ _ _)
                          (or_introl (proj1 (PkgSet.singleton_spec _ _) Hx))))).
            exact Ha'. }
        apply FSet.ext; intro f.
        cbn [dependees embedPkg fst snd].
        rewrite Hfib, Hsup.
        cbn [pkgSubInst subInst inst_deps inst_prov].
        rewrite (tailFibre_union_own (inst_deps I) _ (n, v)
                   (depsOn_subset _ _)).
        rewrite !FSet.union_spec, !SOdf.mem_map, !SOrf.mem_filterMap,
          !SOtf.mem_map.
        apply or_iff; [| apply or_iff; [| apply or_iff; [| apply iff_refl]]].
        - split; intros [[p' d] [Hin ->]]; exists (p', d); split;
            try exact Hin; cbv beta iota;
            apply DepsFibred.mem_tailFibre in Hin; destruct Hin as [Hin ->];
            [| symmetry]; apply encDep_subInst.
          1, 4: apply NSet.union_spec; left; apply dep_pkgNames;
                apply DepsFibred.mem_tailFibre; split;
                [exact Hin | reflexivity].
          1, 3: exact Hown.
          1, 2: intros m ct -> Ha q Hq; exact (Hsel m ct Hin Ha q Hq).
        - split.
          + intros [[p' [m tg]] [Hin Hv]].
            apply ProvFibred.mem_tailFibre in Hin.
            destruct Hin as [Hin ->].
            exists ((n, v), (m, tg)); split; [| exact Hv].
            apply ProvFibred.mem_tailFibre; split; [| reflexivity].
            apply Prov.union_spec in Hin; destruct Hin as [Hin | Hin];
              [exact (Hown _ Hin) |].
            apply mem_provPreimage in Hin; exact (proj1 Hin).
          + intros [[p' [m tg]] [Hin Hv]].
            apply ProvFibred.mem_tailFibre in Hin.
            destruct Hin as [Hin ->].
            exists ((n, v), (m, tg)); split; [| exact Hv].
            apply ProvFibred.mem_tailFibre; split; [| reflexivity].
            apply Prov.union_spec; left; exact (Hcov _ _ Hin).
        - split.
          + intros [[z conds] [Hin ->]].
            exists (z, conds); split; [exact Hin |].
            cbv beta iota; apply installIfForm_subInst;
              [ apply NSet.union_spec; left;
                exact (selfName_pkgNames I (n, v) z conds Hin)
              | intros a Ha; apply NSet.union_spec; left;
                exact (condName_pkgNames I (n, v) z conds a Hin Ha)
              | exact Hown ].
          + intros [[z conds] [Hin ->]].
            exists (z, conds); split; [exact Hin |].
            cbv beta iota; symmetry; apply installIfForm_subInst;
              [ apply NSet.union_spec; left;
                exact (selfName_pkgNames I (n, v) z conds Hin)
              | intros a Ha; apply NSet.union_spec; left;
                exact (condName_pkgNames I (n, v) z conds a Hin Ha)
              | exact Hown ].
      Qed.

      (* The root carries no install-if rule: the ones its dependees read
         belong to providers of its bare atoms. *)
      Definition rootNames (I : Inst) : NSet.t :=
        SOwn.map depName (inst_world I).

      Lemma world_rootNames : forall I d,
          WSet.In d (inst_world I) -> NSet.In (depName d) (rootNames I).
      Proof.
        intros I d Hd; unfold rootNames.
        apply SOwn.mem_map; exists d; split; [exact Hd | reflexivity].
      Qed.

      Definition rootSubInst (I : Inst) : Inst :=
        subInst I
          (NSet.union (rootNames I)
             (ruleCondNames (rulesOf I (noPriority I (rootAnyNames I)))))
          (depsOn I (ownNamesOf I (noPriority I (rootAnyNames I))))
          (provOf I (noPriority I (rootAnyNames I)))
          (rulesOf I (noPriority I (rootAnyNames I)))
          (inst_world I)
          (prioOf I (bareProviders I (rootAnyNames I))).

      Lemma rootSubInst_world : forall I,
          inst_world (rootSubInst I) = inst_world I.
      Proof. reflexivity. Qed.

      Theorem dependees_lookupRoot : forall I,
          dependees (rootSubInst I) rootPkg = dependees I rootPkg.
      Proof.
        intro I.
        assert (Heq : forall d, WSet.In d (inst_world I) ->
                   encDep (rootSubInst I) d = encDep I d).
        { intros d Hd; unfold rootSubInst; apply encDep_subInst.
          - apply NSet.union_spec; left; exact (world_rootNames I d Hd).
          - exact (provOf_subset _ _).
          - intros m ct -> Ha q Hq.
            apply (selectableAlts_lookup I _ _ _ _ _ _ (rootAnyNames I) m q);
              try exact Hq.
            + exact (provOf_subset _ _).
            + exact (depsOn_subset _ _).
            + exact (rulesOf_subset _ _).
            + intros e He; exact He.
            + exact (prioOf_subset _ _).
            + intros e He; exact He.
            + intros e He; exact He.
            + intros e He; exact He.
            + exact (worldOn_subset _ _).
            + intros e He; exact He.
            + intros a Ha'; apply NSet.union_spec; right; exact Ha'.
            + apply mem_rootAnyNames; exists ct; split; assumption. }
        cbn [dependees rootPkg]; rewrite rootSubInst_world.
        apply FSet.ext; intro f; rewrite !SOwf.mem_map.
        split; intros [d [Hd ->]]; exists d; split; try exact Hd;
          [| symmetry]; exact (Heq d Hd).
      Qed.
    End Lookup.
  End Reduct.

  Module Reduction := Reduct LeastDesignation.
End Alpine.
