From Stdlib Require Import MSets OrdersEx Bool List.
From PackageCalculus Require Import Prelude Core VersionFormula PackageFormula.

Create HintDb cmp_alp.
Create Rewrite HintDb cmp_alp.

(* apk's ~ (component-prefix) and >< (build identity) constraints are not
   expressible through V.compare; they arrive as opaque predicates and only
   ever build version sets, so no laws are demanded of them. *)
Module Type ApkVersionMatch (V : UsualOrderedType).
  Parameter prefix : V.t -> V.t -> bool.
  Parameter hash : V.t -> V.t -> bool.
End ApkVersionMatch.

Module Alpine (N V : UsualOrderedType) (ApkVersionMatch : ApkVersionMatch V).
  Module Source := Core N V.
  Module Package := Source.Package.
  Module PackageSet := Source.PackageSet.
  Module NEqb := UOTEqb N.
  Module PackageEqb := UOTEqb Package.

  Inductive Constr : Type :=
  | CAny
  | COp (op : CmpOp) (c : V.t)
  | CPrefix (c : V.t)
  | CGtPrefix (c : V.t)
  | CLtPrefix (c : V.t)
  | CHash (c : V.t).

  Definition constrMatch (zeta : Constr) (v : V.t) : bool :=
    match zeta with
    | CAny => true
    | COp op c => cmpOpEvalBy V.compare op v c
    | CPrefix c => ApkVersionMatch.prefix v c
    | CGtPrefix c =>
        orb (cmpOpEvalBy V.compare OpGt v c) (ApkVersionMatch.prefix v c)
    | CLtPrefix c =>
        orb (cmpOpEvalBy V.compare OpLt v c) (ApkVersionMatch.prefix v c)
    | CHash c => ApkVersionMatch.hash v c
    end.

  Definition bareMatch (zeta : Constr) : bool :=
    match zeta with
    | CAny => true
    | COp op _ => match op with OpLt | OpLe | OpNe => true | _ => false end
    | CLtPrefix _ => true
    | CPrefix _ | CGtPrefix _ | CHash _ => false
    end.

  Module VFacts := UOTCompareFacts V.
  Module ComparisonConstraint := PairUOT ComparisonOperatorOT V.
  Module ComparisonConstraintFacts := UOTCompareFacts ComparisonConstraint.
  #[local] Hint Rewrite ComparisonConstraintFacts.compare_eq_iff
    VFacts.compare_eq_iff : cmp_alp.
  #[local] Hint Extern 1 =>
    cmp_by ComparisonConstraintFacts.compare_antisym : cmp_alp.
  #[local] Hint Extern 1 => cmp_by VFacts.compare_antisym : cmp_alp.
  #[local] Hint Extern 1 =>
    cmp_by ComparisonConstraintFacts.compare_lt_trans : cmp_alp.
  #[local] Hint Extern 1 => cmp_by VFacts.compare_lt_trans : cmp_alp.
  Module ConstraintComp <: ComparableType.
    Definition t := Constr.
    Definition rank (zeta : Constr) : nat :=
      match zeta with
      | CAny => 0 | COp _ _ => 1 | CPrefix _ => 2
      | CGtPrefix _ => 3 | CLtPrefix _ => 4 | CHash _ => 5
      end.
    Definition compare (x y : t) : comparison :=
      match Nat.compare (rank x) (rank y) with
      | Eq =>
          match x, y with
          | COp o1 c1, COp o2 c2 =>
              ComparisonConstraint.compare (o1, c1) (o2, c2)
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
  End ConstraintComp.
  Module ConstraintOT := UOTFromCompare ConstraintComp.

  Module Atom := PairUOT N ConstraintOT.
  Module AtomFacts := UOTCompareFacts Atom.

  Inductive Dep : Type :=
  | DPos (a : Atom.t)
  | DNeg (a : Atom.t).

  Module DependencyAtomComp <: ComparableType.
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
    #[local] Hint Rewrite AtomFacts.compare_eq_iff : cmp_alp.
    #[local] Hint Extern 1 => cmp_by AtomFacts.compare_antisym : cmp_alp.
    #[local] Hint Extern 1 => cmp_by AtomFacts.compare_lt_trans : cmp_alp.
    Lemma compare_eq_iff : forall x y, compare x y = Eq <-> x = y.
    Proof. cmp_eq_iff cmp_alp. Qed.
    Lemma compare_antisym : forall x y, compare y x = CompOpp (compare x y).
    Proof. cmp_antisym cmp_alp. Qed.
    Lemma compare_lt_trans : forall x y z,
        compare x y = Lt -> compare y z = Lt -> compare x z = Lt.
    Proof. cmp_lt_trans cmp_alp. Qed.
  End DependencyAtomComp.
  Module DependencyAtomOT := UOTFromCompare DependencyAtomComp.

  Module DependencyElt := PairUOT Package DependencyAtomOT.
  Module DependencyRel := FSetUOT DependencyElt.

  Inductive PTag : Type :=
  | PVer (u : V.t)
  | PBare.

  Module ProvidedVersionComp <: ComparableType.
    Definition t := PTag.
    Definition compare (x y : t) : comparison :=
      match x, y with
      | PVer v1, PVer v2 => V.compare v1 v2
      | PVer _, PBare => Lt
      | PBare, PVer _ => Gt
      | PBare, PBare => Eq
      end.
    Lemma compare_eq_iff : forall x y, compare x y = Eq <-> x = y.
    Proof. cmp_eq_iff cmp_alp. Qed.
    Lemma compare_antisym : forall x y, compare y x = CompOpp (compare x y).
    Proof. cmp_antisym cmp_alp. Qed.
    Lemma compare_lt_trans : forall x y z,
        compare x y = Lt -> compare y z = Lt -> compare x z = Lt.
    Proof. cmp_lt_trans cmp_alp. Qed.
  End ProvidedVersionComp.
  Module ProvidedVersionOT := UOTFromCompare ProvidedVersionComp.

  Module Provided := PairUOT N ProvidedVersionOT.
  Module ProvidesElt := PairUOT Package Provided.
  Module ProvidesRel := FSetUOT ProvidesElt.

  Module ConditionSet := FSetUOT DependencyAtomOT.
  Module InstallIfRuleElt := PairUOT Package ConditionSet.AsUOT.
  Module InstallIfRuleRel := FSetUOT InstallIfRuleElt.

  Module WorldSet := FSetUOT DependencyAtomOT.

  Module PriorityElt := PairUOT Package Nat_as_OT.
  Module PriorityRel := FSetUOT PriorityElt.

  Record Inst : Type :=
    { inst_real : PackageSet.t
    ; inst_deps : DependencyRel.t
    ; inst_prov : ProvidesRel.t
    ; inst_installIf : InstallIfRuleRel.t
    ; inst_world : WorldSet.t
    ; inst_prio : PriorityRel.t }.

  Definition Match (I : Inst) (S : PackageSet.t)
      (n : N.t) (zeta : Constr) : Prop :=
    (exists u, PackageSet.In (n, u) S /\ constrMatch zeta u = true) \/
    (exists q u, ProvidesRel.In (q, (n, PVer u)) (inst_prov I) /\
       PackageSet.In q S /\ constrMatch zeta u = true) \/
    (bareMatch zeta = true /\
     exists q, ProvidesRel.In (q, (n, PBare)) (inst_prov I) /\
       PackageSet.In q S).

  Definition HasPriority (I : Inst) (q : Package.t) : Prop :=
    exists prio, PriorityRel.In (q, prio) (inst_prio I) /\ prio <> 0.

  Definition Selectable (I : Inst) '(((m, u) as q) : Package.t) : Prop :=
    HasPriority I q \/ exists zeta, WorldSet.In (DPos (m, zeta)) (inst_world I).

  Definition Req (I : Inst) (S : PackageSet.t)
      (n : N.t) (zeta : Constr) : Prop :=
    (exists u, PackageSet.In (n, u) S /\ constrMatch zeta u = true) \/
    (exists q u, ProvidesRel.In (q, (n, PVer u)) (inst_prov I) /\
       PackageSet.In q S /\ constrMatch zeta u = true) \/
    (bareMatch zeta = true /\
     exists q, ProvidesRel.In (q, (n, PBare)) (inst_prov I) /\
       PackageSet.In q S /\
       Selectable I q).

  Definition MatchDep (I : Inst) (S : PackageSet.t) (d : Dep) : Prop :=
    match d with
    | DPos (n, zeta) => Req I S n zeta
    | DNeg (n, zeta) => ~ Match I S n zeta
    end.

  Definition MatchCond (I : Inst) (S : PackageSet.t) (a : Dep) : Prop :=
    match a with
    | DPos (n, zeta) => Match I S n zeta
    | DNeg (n, zeta) => ~ Match I S n zeta
    end.

  Definition Claims (I : Inst) (n : N.t) (p : Package.t) : Prop :=
    fst p = n \/ exists u, ProvidesRel.In (p, (n, PVer u)) (inst_prov I).

  Record IsResolution (I : Inst) (S : PackageSet.t) : Prop :=
    { res_subset : PackageSet.Subset S (inst_real I)
    ; res_world : forall d, WorldSet.In d (inst_world I) -> MatchDep I S d
    ; res_dep_closure :
        forall p d, PackageSet.In p S ->
          DependencyRel.In (p, d) (inst_deps I) ->
        MatchDep I S d
    ; res_claim_unique :
        forall n p q, PackageSet.In p S -> PackageSet.In q S ->
        Claims I n p -> Claims I n q -> p = q
    ; res_install_if :
        forall n v B, InstallIfRuleRel.In ((n, v), B) (inst_installIf I) ->
        (forall a, ConditionSet.In a B -> MatchCond I S a) ->
        Match I S n CAny }.

  Module Type Designation.
    Parameter designation : ConditionSet.t -> option Atom.t.
    Parameter designation_spec : forall B : ConditionSet.t,
        (exists a, ConditionSet.In (DPos a) B) ->
        exists a, designation B = Some a /\ ConditionSet.In (DPos a) B.
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

    Definition designation (B : ConditionSet.t) : option Atom.t :=
      firstPos (ConditionSet.elements B).

    Lemma in_elements : forall s d,
        List.In d (ConditionSet.elements s) <-> ConditionSet.In d s.
    Proof.
      intros s d; rewrite <- (ConditionSet.elements_spec1 s d).
      rewrite InA_alt; split.
      - intro H; exists d; split; reflexivity + assumption.
      - intros [y [-> Hy]]; exact Hy.
    Qed.

    Lemma designation_spec : forall B : ConditionSet.t,
        (exists a, ConditionSet.In (DPos a) B) ->
        exists a, designation B = Some a /\ ConditionSet.In (DPos a) B.
    Proof.
      intros B [a Ha]; unfold designation.
      destruct (firstPos_spec (ConditionSet.elements B)
                  (ex_intro _ a (proj2 (in_elements _ _) Ha)))
        as [a' [E H]].
      exists a'; split; [exact E | apply in_elements; exact H].
    Qed.
  End LeastDesignation.

  Module ReductionUnder (Designation : Designation).
    Module NFacts := UOTCompareFacts N.
    Module ProvidesVersion := PairUOT Package V.
    Module ProvidesVersionFacts := UOTCompareFacts ProvidesVersion.
    #[local] Hint Rewrite NFacts.compare_eq_iff
      ProvidesVersionFacts.compare_eq_iff : cmp_alp.
    #[local] Hint Extern 1 => cmp_by NFacts.compare_antisym : cmp_alp.
    #[local] Hint Extern 1 =>
      cmp_by ProvidesVersionFacts.compare_antisym : cmp_alp.
    #[local] Hint Extern 1 => cmp_by NFacts.compare_lt_trans : cmp_alp.
    #[local] Hint Extern 1 =>
      cmp_by ProvidesVersionFacts.compare_lt_trans : cmp_alp.

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

    Module Version.
      Inductive version : Type :=
      | UnitV
      | Orig (v : V.t)
      | Prov (p : Package.t) (u : V.t).
      Definition t := version.

      Definition rank (w : t) : nat :=
        match w with UnitV => 0 | Orig _ => 1 | Prov _ _ => 2 end.
      Definition compare (x y : t) : comparison :=
        match Nat.compare (rank x) (rank y) with
        | Eq =>
            match x, y with
            | Orig v1, Orig v2 => V.compare v1 v2
            | Prov p1 v1, Prov p2 v2 =>
                ProvidesVersion.compare (p1, v1) (p2, v2)
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

    Module PackageFormula := PackageFormula NameOT VersionOT.

    Module DependencyRelFibred :=
      FibredRel Package DependencyAtomOT DependencyElt DependencyRel.
    Module ProvidesRelFibred :=
      FibredLabelledRel Package N ProvidedVersionOT ProvidesElt ProvidesRel.

    Module SOpw := SetOps Package VersionOT PackageSet PackageFormula.VSet.
    Module SOrw := SetOps ProvidesElt VersionOT ProvidesRel PackageFormula.VSet.
    Definition versionsAt (I : Inst) (n : N.t) (zeta : Constr) :
        PackageFormula.VSet.t :=
      PackageFormula.VSet.union
        (SOpw.filterMap
           (fun p =>
              if andb (NEqb.eqb (fst p) n) (constrMatch zeta (snd p))
              then Some (Version.Orig (snd p)) else None)
           (inst_real I))
        (SOrw.filterMap
           (fun '(q, (m, tg)) =>
              match tg with
              | PVer u =>
                  if andb (NEqb.eqb m n)
                       (andb (PackageSet.mem q (inst_real I))
                          (constrMatch zeta u))
                  then Some (Version.Prov q u) else None
              | PBare => None
              end)
           (inst_prov I)).

    Definition versions (I : Inst) (n : N.t) : PackageFormula.VSet.t :=
      versionsAt I n CAny.

    Module SOrp := SetOps ProvidesElt Package ProvidesRel PackageSet.
    Definition bareProvSet (I : Inst) (n : N.t) : PackageSet.t :=
      SOrp.filterMap
        (fun '(q, (m, tg)) =>
           match tg with
           | PBare =>
               if andb (NEqb.eqb m n) (PackageSet.mem q (inst_real I))
               then Some q else None
           | PVer _ => None
           end)
        (inst_prov I).

    Definition bareProvL (I : Inst) (n : N.t) : list Package.t :=
      PackageSet.elements (bareProvSet I n).

    Definition encPos (I : Inst) (n : N.t) (zeta : Constr) :
        PackageFormula.Formula :=
      let base := PackageFormula.FAtom (Name.Orig n) (versionsAt I n zeta) in
      if bareMatch zeta
      then
        fold_right
          (fun q f =>
             PackageFormula.FDisj
               (PackageFormula.FAtom (Name.Orig (fst q))
                  (PackageFormula.VSet.singleton (Version.Orig (snd q)))) f)
          base (bareProvL I n)
      else base.

    Definition hasPriorityb (I : Inst) (q : Package.t) : bool :=
      PriorityRel.exists_
        (fun '(q', k) => andb (PackageEqb.eqb q' q) (negb (Nat.eqb k 0)))
        (inst_prio I).

    Definition worldNamesb (I : Inst) (m : N.t) : bool :=
      WorldSet.exists_
        (fun d => match d with
                  | DPos (m', _) => NEqb.eqb m' m
                  | DNeg _ => false
                  end)
        (inst_world I).

    Definition selectableb (I : Inst) (q : Package.t) : bool :=
      orb (hasPriorityb I q) (worldNamesb I (fst q)).

    Definition encReq (I : Inst) (n : N.t) (zeta : Constr) :
        PackageFormula.Formula :=
      let base := PackageFormula.FAtom (Name.Orig n) (versionsAt I n zeta) in
      if bareMatch zeta
      then
        fold_right
          (fun q f =>
             PackageFormula.FDisj
               (PackageFormula.FAtom (Name.Orig (fst q))
                  (PackageFormula.VSet.singleton (Version.Orig (snd q)))) f)
          base (List.filter (selectableb I) (bareProvL I n))
      else base.

    Definition encDep (I : Inst) (d : Dep) : PackageFormula.Formula :=
      match d with
      | DPos (n, zeta) => encReq I n zeta
      | DNeg (n, zeta) => PackageFormula.FNeg (encPos I n zeta)
      end.

    Definition attachAt (I : Inst) (p : Package.t) (a : Atom.t) : bool :=
      orb (andb (NEqb.eqb (fst p) (fst a)) (constrMatch (snd a) (snd p)))
        (ProvidesRel.exists_
           (fun '(q, (m, tg)) =>
              andb (PackageEqb.eqb q p)
                (andb (NEqb.eqb m (fst a))
                   (match tg with
                    | PVer u => constrMatch (snd a) u
                    | PBare => bareMatch (snd a)
                    end)))
           (inst_prov I)).

    Definition condRest (B : ConditionSet.t) : ConditionSet.t :=
      match Designation.designation B with
      | Some a => ConditionSet.remove (DPos a) B
      | None => B
      end.

    Definition attachDesignation (I : Inst) (p : Package.t)
        (B : ConditionSet.t) : bool :=
      match Designation.designation B with
      | Some a => attachAt I p a
      | None => false
      end.

    Definition installIfFibre (I : Inst) (p : Package.t) : InstallIfRuleRel.t :=
      InstallIfRuleRel.filter (fun '(_, B) => attachDesignation I p B)
        (inst_installIf I).

    Definition encCond (I : Inst) (a : Dep) : PackageFormula.Formula :=
      match a with
      | DPos (n, zeta) => encPos I n zeta
      | DNeg (n, zeta) => PackageFormula.FNeg (encPos I n zeta)
      end.

    Definition installIfForm (I : Inst) (p : Package.t) (B : ConditionSet.t) :
        PackageFormula.Formula :=
      fold_right
        (fun a psi =>
          PackageFormula.FDisj (PackageFormula.FNeg (encCond I a)) psi)
        (encPos I (fst p) CAny) (ConditionSet.elements (condRest B)).

    Definition rootPkg : PackageFormula.Package.t := (Name.Root, Version.UnitV).

    Module PackageFormulaSet := PackageFormula.PackageFormulaSet.
    Module SOdf :=
      SetOps DependencyElt PackageFormula.PackageFormulaOT DependencyRel
      PackageFormulaSet.
    Module SOrf :=
      SetOps ProvidesElt PackageFormula.PackageFormulaOT ProvidesRel
      PackageFormulaSet.
    Module SOtf :=
      SetOps InstallIfRuleElt PackageFormula.PackageFormulaOT InstallIfRuleRel
      PackageFormulaSet.
    Module SOwf :=
      SetOps DependencyAtomOT PackageFormula.PackageFormulaOT WorldSet
      PackageFormulaSet.
    Definition dependees (I : Inst) (q : PackageFormula.Package.t) :
        PackageFormulaSet.t :=
      match q with
      | (Name.Root, Version.UnitV) => SOwf.map (encDep I) (inst_world I)
      | (Name.Orig n, Version.Orig v) =>
          PackageFormulaSet.union
            (SOdf.map (fun '(_, d) => encDep I d)
               (DependencyRelFibred.tailFibre (inst_deps I) (n, v)))
            (PackageFormulaSet.union
               (SOrf.filterMap
                  (fun '(_, (m, tg)) =>
                     match tg with
                     | PVer u =>
                         Some (PackageFormula.FAtom (Name.Orig m)
                                 (PackageFormula.VSet.singleton
                                    (Version.Prov (n, v) u)))
                     | PBare => None
                     end)
                  (ProvidesRelFibred.tailFibre (inst_prov I) (n, v)))
               (SOtf.map (fun '(p, B) => installIfForm I p B)
                  (installIfFibre I (n, v))))
      | (Name.Orig _, Version.Prov q0 _) =>
          PackageFormulaSet.singleton
            (PackageFormula.FAtom (Name.Orig (fst q0))
               (PackageFormula.VSet.singleton (Version.Orig (snd q0))))
      | _ => PackageFormulaSet.empty
      end.

    Module SOpp :=
      SetOps Package PackageFormula.Package PackageSet
      PackageFormula.PackageSet.
    Module SOrq :=
      SetOps ProvidesElt PackageFormula.Package ProvidesRel
      PackageFormula.PackageSet.
    Definition embedPkg (p : Package.t) : PackageFormula.Package.t :=
      (Name.Orig (fst p), Version.Orig (snd p)).

    Definition provPkgs (I : Inst) (S : PackageSet.t) :
        PackageFormula.PackageSet.t :=
      SOrq.filterMap
        (fun '(q, (m, tg)) =>
           match tg with
           | PVer u =>
               if PackageSet.mem q S
               then Some (Name.Orig m, Version.Prov q u) else None
           | PBare => None
           end)
        (inst_prov I).

    Definition reduceReal (I : Inst) : PackageFormula.PackageSet.t :=
      PackageFormula.PackageSet.add rootPkg
        (PackageFormula.PackageSet.union (SOpp.map embedPkg (inst_real I))
           (provPkgs I (inst_real I))).

    Module SOqd :=
      SetOps PackageFormula.Package PackageFormula.DependencyElt
      PackageFormula.PackageSet PackageFormula.DependencyRel.

    Definition reduceDeps (I : Inst) : PackageFormula.DependencyRel.t :=
      SOqd.unionMap (fun q => PackageFormula.depEdges q (dependees I q))
        (reduceReal I).

    Definition tryInvPkg (q : PackageFormula.Package.t) : option Package.t :=
      match q with
      | (Name.Orig n, Version.Orig v) => Some (n, v)
      | _ => None
      end.
    Module SOqp :=
      SetOps PackageFormula.Package Package
      PackageFormula.PackageSet PackageSet.
    Definition alpineResolution (S' : PackageFormula.PackageSet.t) :
        PackageSet.t :=
      SOqp.filterMap tryInvPkg S'.

    Definition coreResolution (I : Inst) (S : PackageSet.t) :
        PackageFormula.PackageSet.t :=
      PackageFormula.PackageSet.add rootPkg
        (PackageFormula.PackageSet.union (SOpp.map embedPkg S) (provPkgs I S)).

    Lemma tryInvPkg_embed : forall p, tryInvPkg (embedPkg p) = Some p.
    Proof. intros [n v]; reflexivity. Qed.

    Lemma tryInvPkg_some : forall q p, tryInvPkg q = Some p -> embedPkg p = q.
    Proof.
      intros [[|n] [|v|q0 u]] p H; try discriminate.
      injection H as <-; reflexivity.
    Qed.

    Lemma mem_alpineResolution : forall S' p,
        PackageSet.In p (alpineResolution S') <->
        PackageFormula.PackageSet.In (embedPkg p) S'.
    Proof.
      exact (SOqp.mem_filterMap_inv tryInvPkg embedPkg
               tryInvPkg_embed tryInvPkg_some).
    Qed.

    Lemma mem_versionsAt : forall I n zeta w,
        PackageFormula.VSet.In w (versionsAt I n zeta) <->
        (exists v, PackageSet.In (n, v) (inst_real I) /\
           constrMatch zeta v = true /\ w = Version.Orig v) \/
        (exists q u, ProvidesRel.In (q, (n, PVer u)) (inst_prov I) /\
           PackageSet.In q (inst_real I) /\ constrMatch zeta u = true /\
           w = Version.Prov q u).
    Proof.
      intros I n zeta w; unfold versionsAt.
      rewrite PackageFormula.VSet.union_spec, SOpw.mem_filterMap_if,
        SOrw.mem_filterMap.
      split.
      - intros [[[m v] [Hm [Hb ->]]] | [[q [m tg]] [Hm Hf]]].
        + cbn [fst snd] in Hb.
          rewrite Bool.andb_true_iff, NEqb.eqb_true_iff in Hb.
          destruct Hb as [-> Hc]; left; eauto.
        + cbn in Hf; destruct tg as [u |]; [| discriminate].
          rewrite if_some_iff, !Bool.andb_true_iff, NEqb.eqb_true_iff,
            PackageSet.mem_spec in Hf.
          destruct Hf as [[-> [Hq Hc]] <-]; right; exists q, u; auto.
      - intros [[v [Hv [Hc ->]]] | [q [u [Hr [Hq [Hc ->]]]]]].
        + left; exists (n, v); cbn [fst snd].
          rewrite Bool.andb_true_iff, NEqb.eqb_true_iff; auto.
        + right; exists (q, (n, PVer u)); split; [exact Hr | cbn].
          apply if_some_iff; rewrite !Bool.andb_true_iff, NEqb.eqb_true_iff,
            PackageSet.mem_spec; auto.
    Qed.

    Lemma mem_bareProvSet : forall I n q,
        PackageSet.In q (bareProvSet I n) <->
        ProvidesRel.In (q, (n, PBare)) (inst_prov I) /\
        PackageSet.In q (inst_real I).
    Proof.
      intros I n q; unfold bareProvSet; rewrite SOrp.mem_filterMap.
      split.
      - intros [[q0 [m tg]] [Hm Hf]]; cbn in Hf.
        destruct tg as [|]; [discriminate |].
        rewrite if_some_iff, Bool.andb_true_iff, NEqb.eqb_true_iff,
          PackageSet.mem_spec in Hf.
        destruct Hf as [[-> Hq] <-]; auto.
      - intros [Hr Hq]; exists (q, (n, PBare)); split; [exact Hr | cbn].
        apply if_some_iff; rewrite Bool.andb_true_iff, NEqb.eqb_true_iff,
          PackageSet.mem_spec; auto.
    Qed.

    Lemma mem_provPkgs : forall I S p,
        PackageFormula.PackageSet.In p (provPkgs I S) <->
        exists q m u, ProvidesRel.In (q, (m, PVer u)) (inst_prov I) /\
          PackageSet.In q S /\ p = (Name.Orig m, Version.Prov q u).
    Proof.
      intros I S p; unfold provPkgs; rewrite SOrq.mem_filterMap.
      split.
      - intros [[q [m tg]] [Hm Hf]]; cbn in Hf.
        destruct tg as [u |]; [| discriminate].
        rewrite if_some_iff, PackageSet.mem_spec in Hf; destruct Hf as [Hq <-].
        exists q, m, u; auto.
      - intros [q [m [u [Hr [Hq ->]]]]].
        exists (q, (m, PVer u)); split; [exact Hr | cbn].
        apply if_some_iff; rewrite PackageSet.mem_spec; auto.
    Qed.

    Lemma attachAt_spec : forall I p a,
        attachAt I p a = true <->
        (fst p = fst a /\ constrMatch (snd a) (snd p) = true) \/
        (exists u, ProvidesRel.In (p, (fst a, PVer u)) (inst_prov I) /\
           constrMatch (snd a) u = true) \/
        (bareMatch (snd a) = true /\
         ProvidesRel.In (p, (fst a, PBare)) (inst_prov I)).
    Proof.
      intros I p a; unfold attachAt.
      rewrite Bool.orb_true_iff, Bool.andb_true_iff, NEqb.eqb_true_iff.
      rewrite ProvidesRel.exists_spec'.
      apply or_iff_compat_l.
      split.
      - intros [[q [m tg]] [Hr Hb]]; cbn in Hb.
        apply Bool.andb_true_iff in Hb; destruct Hb as [Hq Hb].
        apply PackageEqb.eqb_true_iff in Hq; subst q.
        apply Bool.andb_true_iff in Hb; destruct Hb as [Hm Hb].
        apply NEqb.eqb_true_iff in Hm; subst m.
        destruct tg as [u |]; [left; eauto | right; eauto].
      - intros [[u [Hr Hc]] | [Hany Hr]].
        + exists (p, (fst a, PVer u)); split; [exact Hr | cbn].
          rewrite (proj2 (PackageEqb.eqb_true_iff p p) eq_refl).
          rewrite (proj2 (NEqb.eqb_true_iff (fst a) (fst a)) eq_refl).
          rewrite Hc; reflexivity.
        + exists (p, (fst a, PBare)); split; [exact Hr | cbn].
          rewrite (proj2 (PackageEqb.eqb_true_iff p p) eq_refl).
          rewrite (proj2 (NEqb.eqb_true_iff (fst a) (fst a)) eq_refl).
          rewrite Hany; reflexivity.
    Qed.

    Lemma match_attachAt : forall I S n zeta,
        Match I S n zeta <->
        exists p, PackageSet.In p S /\ attachAt I p (n, zeta) = true.
    Proof.
      intros I S n zeta; unfold Match; split.
      - intros [[v [Hv Hc]] |
                [[q [u [Hr [Hq Hc]]]] | [Hany [q [Hr Hq]]]]].
        + exists (n, v); split; [exact Hv |].
          apply attachAt_spec; left; split; [reflexivity | exact Hc].
        + exists q; split; [exact Hq |].
          apply attachAt_spec; right; left; exists u; split; assumption.
        + exists q; split; [exact Hq |].
          apply attachAt_spec; right; right; split; assumption.
      - intros [p [Hp Ha]]; apply attachAt_spec in Ha; cbn in Ha.
        destruct Ha as [[Hn Hc] | [[u [Hr Hc]] | [Hany Hr]]].
        + left; exists (snd p); split; [| exact Hc].
          destruct p as [np vp]; cbn in Hn |- *; subst np; exact Hp.
        + right; left; exists p, u; repeat split; assumption.
        + right; right; split; [exact Hany | exists p; split; assumption].
    Qed.

    Lemma mem_installIfFibre : forall I q p B,
        InstallIfRuleRel.In (p, B) (installIfFibre I q) <->
        InstallIfRuleRel.In (p, B) (inst_installIf I) /\
        attachDesignation I q B = true.
    Proof.
      intros I q p B; unfold installIfFibre.
      rewrite InstallIfRuleRel.filter_spec'; reflexivity.
    Qed.

    Lemma condRest_subset : forall B a,
        ConditionSet.In a (condRest B) -> ConditionSet.In a B.
    Proof.
      intros B a; unfold condRest.
      destruct (Designation.designation B) as [b |]; [| exact (fun H => H)].
      intro H; apply ConditionSet.remove_spec in H; exact (proj1 H).
    Qed.

    Lemma mem_coreResolution : forall I S p',
        PackageFormula.PackageSet.In p' (coreResolution I S) <->
        p' = rootPkg \/
        (exists p, PackageSet.In p S /\ p' = embedPkg p) \/
        (exists q m u, ProvidesRel.In (q, (m, PVer u)) (inst_prov I) /\
           PackageSet.In q S /\ p' = (Name.Orig m, Version.Prov q u)).
    Proof.
      intros I S p'; unfold coreResolution.
      rewrite PackageFormula.PackageSet.add_spec,
        PackageFormula.PackageSet.union_spec, SOpp.mem_map,
        mem_provPkgs.
      reflexivity.
    Qed.

    Lemma reduceReal_coreResolution : forall I,
        reduceReal I = coreResolution I (inst_real I).
    Proof. reflexivity. Qed.

    Lemma mem_reduceReal : forall I p',
        PackageFormula.PackageSet.In p' (reduceReal I) <->
        p' = rootPkg \/
        (exists p, PackageSet.In p (inst_real I) /\ p' = embedPkg p) \/
        (exists q m u, ProvidesRel.In (q, (m, PVer u)) (inst_prov I) /\
           PackageSet.In q (inst_real I) /\
           p' = (Name.Orig m, Version.Prov q u)).
    Proof.
      intros I p'; rewrite reduceReal_coreResolution; apply mem_coreResolution.
    Qed.

    (* Each of the core's names draws its versions from one branch of
       coreResolution, so the callers name the branch they mean rather than
       its position. *)
    Lemma coreResolution_at_root : forall I S v,
        PackageFormula.PackageSet.In (Name.Root, v) (coreResolution I S) -> v =
          Version.UnitV.
    Proof.
      intros I S v H; apply mem_coreResolution in H.
      unfold embedPkg, rootPkg in H.
      destruct H as [E | [[p [_ E]] | [q [m [u [_ [_ E]]]]]]];
        [injection E as ->; reflexivity | discriminate E | discriminate E].
    Qed.

    Lemma coreResolution_at_orig : forall I S n w,
        PackageFormula.PackageSet.In (Name.Orig n, w) (coreResolution I S) ->
        (exists v, PackageSet.In (n, v) S /\ w = Version.Orig v) \/
        (exists q u, ProvidesRel.In (q, (n, PVer u)) (inst_prov I) /\
           PackageSet.In q S /\ w = Version.Prov q u).
    Proof.
      intros I S n w H; apply mem_coreResolution in H.
      unfold embedPkg, rootPkg in H.
      destruct H as [E | [[[n' v] [Hp E]] | [q [m [u [Hr [Hq E]]]]]]];
        [discriminate E | left; exists v | right; exists q, u];
        cbn [fst snd] in E; injection E as <- ->; auto.
    Qed.

    Lemma coreResolution_embed : forall I S p,
        PackageFormula.PackageSet.In (embedPkg p) (coreResolution I S) <->
          PackageSet.In p S.
    Proof.
      intros I S [n v]; split.
      - intro H; apply coreResolution_at_orig in H.
        destruct H as [[v' [Hp E]] | [q [u [_ [_ E]]]]];
          [injection E as <-; exact Hp | discriminate E].
      - intro Hp; apply mem_coreResolution; right; left; exists (n, v); auto.
    Qed.

    Lemma coreResolution_prov : forall I S m q u,
        PackageFormula.PackageSet.In (Name.Orig m, Version.Prov q u)
          (coreResolution I S) <->
        ProvidesRel.In (q, (m, PVer u)) (inst_prov I) /\ PackageSet.In q S.
    Proof.
      intros I S m q u; split.
      - intro H; apply coreResolution_at_orig in H.
        destruct H as [[v [_ E]] | [q' [u' [Hr [Hq E]]]]];
          [discriminate E | injection E as <- <-; auto].
      - intros [Hr Hq]; apply mem_coreResolution; right; right.
        exists q, m, u; auto.
    Qed.

    Lemma mem_reduceDeps : forall I p psi,
        PackageFormula.DependencyRel.In (p, psi) (reduceDeps I) <->
        PackageFormula.PackageSet.In p (reduceReal I) /\
          PackageFormulaSet.In psi (dependees I p).
    Proof.
      intros I p psi; unfold reduceDeps; rewrite SOqd.mem_unionMap.
      split.
      - intros [q [Hq Hf]]; unfold PackageFormula.depEdges in Hf.
        apply PackageFormula.SOfd.mem_map in Hf; mem_destruct; auto.
      - intros [Hy Hf]; exists p; split; [exact Hy |].
        unfold PackageFormula.depEdges; apply PackageFormula.SOfd.mem_map;
          exists psi; split;
          [exact Hf | reflexivity].
    Qed.

    Lemma satisfies_disjFold : forall S' l (base : PackageFormula.Formula),
        PackageFormula.Satisfies S'
          (fold_right
             (fun q f =>
                PackageFormula.FDisj
                  (PackageFormula.FAtom (Name.Orig (fst q))
                     (PackageFormula.VSet.singleton (Version.Orig (snd q)))) f)
             base l) <->
        PackageFormula.Satisfies S' base \/
        (exists q, List.In q l /\ PackageFormula.PackageSet.In (embedPkg q) S').
    Proof.
      intros S' l base; induction l as [| q l IH]; cbn.
      - split; [intro H; left; exact H | intros [H | [q [[] _]]]; exact H].
      - rewrite IH; split.
        + intros [[w [Hw Hm]] | H].
          * apply PackageFormula.VSet.singleton_spec in Hw; subst w.
            right; exists q; auto.
          * destruct H as [H | [q0 [Hq0 Hm]]]; [left; exact H |].
            right; exists q0; auto.
        + intros [H | [q0 [[<- | Hq0] Hm]]].
          * right; left; exact H.
          * left; exists (Version.Orig (snd q)); split;
              [apply PackageFormula.VSet.singleton_spec;
                reflexivity | exact Hm].
          * right; right; exists q0; auto.
    Qed.

    Lemma satisfies_encPos : forall I S' n zeta,
        PackageFormula.Satisfies S' (encPos I n zeta) <->
        (exists v, PackageFormula.VSet.In v (versionsAt I n zeta) /\
           PackageFormula.PackageSet.In (Name.Orig n, v) S') \/
        (bareMatch zeta = true /\
         exists q, PackageSet.In q (bareProvSet I n) /\
           PackageFormula.PackageSet.In (embedPkg q) S').
    Proof.
      intros I S' n zeta; unfold encPos.
      destruct (bareMatch zeta) eqn:Ea.
      - rewrite satisfies_disjFold; cbn.
        unfold bareProvL; split.
        + intros [[w [Hw Hm]] | [q [Hq Hm]]]; [left; eauto |].
          apply SOpp.elements_in in Hq; right; split; [reflexivity |].
          eauto.
        + intros [[w [Hw Hm]] | [_ [q [Hq Hm]]]]; [left; eauto |].
          right; exists q; split; [| exact Hm].
          apply SOpp.elements_in; exact Hq.
      - cbn; split.
        + intros [w [Hw Hm]]; left; eauto.
        + intros [[w [Hw Hm]] | [Hany _]]; [eauto | congruence].
    Qed.

    Lemma satisfies_encReq : forall I S' n zeta,
        PackageFormula.Satisfies S' (encReq I n zeta) <->
        (exists v, PackageFormula.VSet.In v (versionsAt I n zeta) /\
           PackageFormula.PackageSet.In (Name.Orig n, v) S') \/
        (bareMatch zeta = true /\
         exists q, PackageSet.In q (bareProvSet I n) /\
           selectableb I q = true /\
           PackageFormula.PackageSet.In (embedPkg q) S').
    Proof.
      intros I S' n zeta; unfold encReq; cbv zeta.
      destruct (bareMatch zeta) eqn:Ea.
      - rewrite satisfies_disjFold; cbn [PackageFormula.Satisfies].
        apply or_iff_compat_l; split.
        + intros [q [Hq Hm]]; apply filter_In in Hq; destruct Hq as [Hq Hs].
          split; [reflexivity |]; exists q.
          split; [apply SOpp.elements_in; exact Hq | split; assumption].
        + intros [_ [q [Hq [Hs Hm]]]]; exists q; split; [| exact Hm].
          apply filter_In; split; [apply SOpp.elements_in; exact Hq | exact Hs].
      - cbn [PackageFormula.Satisfies]; split; [intro H; left; exact H |].
        intros [H | [Hany _]]; [exact H | discriminate Hany].
    Qed.

    Lemma hasPriorityb_spec : forall I q,
        hasPriorityb I q = true <-> HasPriority I q.
    Proof.
      intros I q; unfold hasPriorityb, HasPriority;
        rewrite PriorityRel.exists_spec'.
      split.
      - intros [[q' k] [Hin Hb]]; cbn in Hb.
        apply Bool.andb_true_iff in Hb; destruct Hb as [Hq Hk].
        apply PackageEqb.eqb_true_iff in Hq; subst q'.
        exists k; split; [exact Hin |].
        intro Hk0; subst k; discriminate Hk.
      - intros [k [Hin Hk]]; exists (q, k); split; [exact Hin | cbn].
        rewrite (proj2 (PackageEqb.eqb_true_iff q q) eq_refl).
        destruct k; [contradiction | reflexivity].
    Qed.

    Lemma selectableb_spec : forall I q,
        selectableb I q = true <-> Selectable I q.
    Proof.
      intros I [m u]; unfold selectableb, Selectable.
      rewrite Bool.orb_true_iff, hasPriorityb_spec.
      apply or_iff_compat_l.
      unfold worldNamesb; rewrite WorldSet.exists_spec'; split.
      - intros [[[m' zeta] | [m' zeta]] [Hd Hb]]; cbn in Hb; [| discriminate].
        apply NEqb.eqb_true_iff in Hb; subst m'; exists zeta; exact Hd.
      - intros [zeta Hd]; exists (DPos (m, zeta)); split; [exact Hd | cbn].
        apply NEqb.eqb_true_iff; reflexivity.
    Qed.

    Lemma satisfies_negFold : forall I S' l (base : PackageFormula.Formula),
        PackageFormula.Satisfies S'
          (fold_right
             (fun c f => PackageFormula.FDisj
               (PackageFormula.FNeg (encCond I c)) f)
             base l) <->
        (exists c, List.In c l /\
          ~ PackageFormula.Satisfies S' (encCond I c)) \/
        PackageFormula.Satisfies S' base.
    Proof.
      intros I S' l base; induction l as [| a l IH]; cbn.
      - split; [intro H; right; exact H | intros [[c [[] _]] | H]; exact H].
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

    Lemma satisfies_installIfForm : forall I S' n v B,
        PackageFormula.Satisfies S' (installIfForm I (n, v) B) <->
        (exists a, ConditionSet.In a (condRest B) /\
           ~ PackageFormula.Satisfies S' (encCond I a)) \/
        PackageFormula.Satisfies S' (encPos I n CAny).
    Proof.
      intros I S' n v B; unfold installIfForm.
      rewrite satisfies_negFold.
      split; intros [[a [Ha Hn]] | Hb];
        try (right; exact Hb); left; exists a;
        (split; [| exact Hn]); apply LeastDesignation.in_elements; exact Ha.
    Qed.

    Lemma embed_reduceReal : forall I p,
        PackageFormula.PackageSet.In (embedPkg p) (reduceReal I) ->
        PackageSet.In p (inst_real I).
    Proof.
      intros I p H.
      rewrite reduceReal_coreResolution, coreResolution_embed in H; exact H.
    Qed.

    Lemma root_reduceReal : forall I,
        PackageFormula.PackageSet.In rootPkg (reduceReal I).
    Proof.
      intro I; unfold reduceReal; apply PackageFormula.PackageSet.add_spec;
        left; reflexivity.
    Qed.

    Lemma prov_selected : forall I S' m q u,
        PackageFormula.IsResolution (reduceReal I) (reduceDeps I) rootPkg S' ->
        PackageFormula.PackageSet.In (Name.Orig m, Version.Prov q u) S' ->
        ProvidesRel.In (q, (m, PVer u)) (inst_prov I) /\
        PackageFormula.PackageSet.In (embedPkg q) S'.
    Proof.
      intros I S' m q u [Hsub Hroot Hclo Huniq] Hm.
      assert (Ht := Hsub _ Hm).
      rewrite reduceReal_coreResolution, coreResolution_prov in Ht.
      split; [exact (proj1 Ht) |].
      assert (Hf : PackageFormulaSet.In
                     (PackageFormula.FAtom (Name.Orig (fst q))
                        (PackageFormula.VSet.singleton (Version.Orig (snd q))))
                     (dependees I (Name.Orig m, Version.Prov q u))).
      { cbn [dependees]; apply PackageFormulaSet.singleton_spec; reflexivity. }
      assert (Hd : PackageFormula.DependencyRel.In
                     ((Name.Orig m, Version.Prov q u),
                      PackageFormula.FAtom (Name.Orig (fst q))
                        (PackageFormula.VSet.singleton (Version.Orig (snd q))))
                     (reduceDeps I)).
      { apply mem_reduceDeps; split; [apply Hsub; exact Hm | exact Hf]. }
      assert (Hs := Hclo _ Hm _ Hd).
      destruct Hs as [w [Hw HwS]].
      apply PackageFormula.VSet.singleton_spec in Hw; subst w.
      destruct q as [nq vq]; exact HwS.
    Qed.

    Lemma reg_edge : forall I S' p m u,
        PackageFormula.IsResolution (reduceReal I) (reduceDeps I) rootPkg S' ->
        PackageFormula.PackageSet.In (embedPkg p) S' ->
        ProvidesRel.In (p, (m, PVer u)) (inst_prov I) ->
        PackageFormula.PackageSet.In (Name.Orig m, Version.Prov p u) S'.
    Proof.
      intros I S' [n v] m u [Hsub Hroot Hclo Huniq] HpS Hprov.
      assert (Hf : PackageFormulaSet.In
                     (PackageFormula.FAtom (Name.Orig m)
                        (PackageFormula.VSet.singleton (Version.Prov (n, v) u)))
                     (dependees I (embedPkg (n, v)))).
      { cbn [dependees embedPkg fst snd];
          apply PackageFormulaSet.union_spec; right.
        apply PackageFormulaSet.union_spec; left.
        apply SOrf.mem_filterMap.
        exists ((n, v), (m, PVer u)); split; [| reflexivity].
        apply ProvidesRelFibred.mem_tailFibre; split;
          [exact Hprov | reflexivity]. }
      assert (Hd : PackageFormula.DependencyRel.In
                     (embedPkg (n, v),
                      PackageFormula.FAtom (Name.Orig m)
                        (PackageFormula.VSet.singleton (Version.Prov (n, v) u)))
                     (reduceDeps I)).
      { apply mem_reduceDeps; split; [apply Hsub; exact HpS | exact Hf]. }
      assert (Hs := Hclo _ HpS _ Hd).
      destruct Hs as [w [Hw HwS]].
      apply PackageFormula.VSet.singleton_spec in Hw; subst w; exact HwS.
    Qed.

    Lemma base_decode : forall I S' n zeta,
        PackageFormula.IsResolution (reduceReal I) (reduceDeps I) rootPkg S' ->
        ((exists w, PackageFormula.VSet.In w (versionsAt I n zeta) /\
            PackageFormula.PackageSet.In (Name.Orig n, w) S') <->
         (exists v, PackageSet.In (n, v) (alpineResolution S') /\
            constrMatch zeta v = true) \/
         (exists q u, ProvidesRel.In (q, (n, PVer u)) (inst_prov I) /\
            PackageSet.In q (alpineResolution S') /\
              constrMatch zeta u = true)).
    Proof.
      intros I S' n zeta Hres.
      assert (Hsub := PackageFormula.res_subset _ _ _ _ Hres).
      split.
      - intros [w [Hw Hm]].
        apply mem_versionsAt in Hw.
        destruct Hw as
          [[v [Hrep [Hc ->]]] | [q [u [Hprov [Hrep [Hc ->]]]]]].
        + left; exists v; split; [| exact Hc].
          apply mem_alpineResolution; exact Hm.
        + right; exists q, u.
          destruct (prov_selected _ _ _ _ _ Hres Hm) as [_ HqS'].
          repeat split; try assumption.
          apply mem_alpineResolution; exact HqS'.
      - intros [[v [HvS Hc]] | [q [u [Hprov [HqS Hc]]]]].
        + apply mem_alpineResolution in HvS.
          exists (Version.Orig v); split; [| exact HvS].
          apply mem_versionsAt; left; exists v.
          repeat split; try assumption.
          exact (embed_reduceReal _ _ (Hsub _ HvS)).
        + apply mem_alpineResolution in HqS.
          exists (Version.Prov q u); split.
          * apply mem_versionsAt; right; exists q, u.
            repeat split; try assumption.
            exact (embed_reduceReal _ _ (Hsub _ HqS)).
          * exact (reg_edge _ _ _ _ _ Hres HqS Hprov).
    Qed.

    Lemma match_decode : forall I S' n zeta,
        PackageFormula.IsResolution (reduceReal I) (reduceDeps I) rootPkg S' ->
        (PackageFormula.Satisfies S' (encPos I n zeta) <->
         Match I (alpineResolution S') n zeta).
    Proof.
      intros I S' n zeta Hres.
      assert (Hsub := PackageFormula.res_subset _ _ _ _ Hres).
      rewrite satisfies_encPos, (base_decode I S' n zeta Hres).
      unfold Match; rewrite or_assoc.
      apply or_iff_compat_l, or_iff_compat_l, and_iff_compat_l; split.
      - intros [q [Hq Hm]]; apply mem_bareProvSet in Hq.
        exists q; split; [exact (proj1 Hq) |].
        apply mem_alpineResolution; exact Hm.
      - intros [q [Hp HqS]]; exists q.
        apply mem_alpineResolution in HqS; split; [| exact HqS].
        apply mem_bareProvSet; split;
          [exact Hp | exact (embed_reduceReal _ _ (Hsub _ HqS))].
    Qed.

    Lemma req_decode : forall I S' n zeta,
        PackageFormula.IsResolution (reduceReal I) (reduceDeps I) rootPkg S' ->
        (PackageFormula.Satisfies S' (encReq I n zeta) <->
         Req I (alpineResolution S') n zeta).
    Proof.
      intros I S' n zeta Hres.
      assert (Hsub := PackageFormula.res_subset _ _ _ _ Hres).
      rewrite satisfies_encReq, (base_decode I S' n zeta Hres).
      unfold Req; rewrite or_assoc.
      apply or_iff_compat_l, or_iff_compat_l, and_iff_compat_l; split.
      - intros [q [Hq [Hs Hm]]]; apply mem_bareProvSet in Hq.
        exists q; split; [exact (proj1 Hq) |].
        split; [apply mem_alpineResolution; exact Hm |].
        apply selectableb_spec; exact Hs.
      - intros [q [Hp [HqS Ha]]]; exists q.
        apply mem_alpineResolution in HqS.
        split; [apply mem_bareProvSet; split;
                [exact Hp | exact (embed_reduceReal _ _ (Hsub _ HqS))] |].
        split; [apply selectableb_spec; exact Ha | exact HqS].
    Qed.

    Lemma cond_decode : forall I S' a,
        PackageFormula.IsResolution (reduceReal I) (reduceDeps I) rootPkg S' ->
        (PackageFormula.Satisfies S' (encCond I a) <->
         MatchCond I (alpineResolution S') a).
    Proof.
      intros I S' [[n zeta] | [n zeta]] Hres;
        cbn [encCond MatchCond PackageFormula.Satisfies];
        rewrite (match_decode I S' n zeta Hres); reflexivity.
    Qed.

    Definition WfInstallIf (I : Inst) : Prop :=
      forall p B, InstallIfRuleRel.In (p, B) (inst_installIf I) ->
      exists a, ConditionSet.In (DPos a) B.

    Theorem alpine_soundness : forall I S,
        WfInstallIf I ->
        PackageFormula.IsResolution (reduceReal I) (reduceDeps I) rootPkg S ->
        IsResolution I (alpineResolution S).
    Proof.
      intros I S Hwf Hres.
      assert (Hres' := Hres); destruct Hres' as [Hsub Hroot Hclo Huniq].
      constructor.
      - intros p Hp; apply mem_alpineResolution in Hp.
        exact (embed_reduceReal _ _ (Hsub _ Hp)).
      - intros d Hd.
        assert (Hf : PackageFormulaSet.In (encDep I d) (dependees I rootPkg)).
        { cbn [dependees rootPkg].
          apply SOwf.mem_map; exists d; split; [exact Hd | reflexivity]. }
        assert (Hdep :
          PackageFormula.DependencyRel.In (rootPkg, encDep I d) (reduceDeps I)).
        { apply mem_reduceDeps; split; [apply root_reduceReal | exact Hf]. }
        assert (Hs := Hclo _ Hroot _ Hdep).
        destruct d as [[m zeta] | [m zeta]]; cbn [MatchDep].
        + exact (proj1 (req_decode _ _ _ _ Hres) Hs).
        + intro HM; cbn [encDep] in Hs.
          exact (Hs (proj2 (match_decode _ _ _ _ Hres) HM)).
      - intros p d Hp Hdep0; apply mem_alpineResolution in Hp.
        destruct p as [np vp].
        assert (Hf : PackageFormulaSet.In (encDep I d)
                       (dependees I (embedPkg (np, vp)))).
        { cbn [dependees embedPkg fst snd];
            apply PackageFormulaSet.union_spec; left.
          apply SOdf.mem_map; exists ((np, vp), d); split; [| reflexivity].
          apply DependencyRelFibred.mem_tailFibre; split;
            [exact Hdep0 | reflexivity]. }
        assert (Hdep :
          PackageFormula.DependencyRel.In (embedPkg (np, vp), encDep I d)
                         (reduceDeps I)).
        { apply mem_reduceDeps; split; [apply Hsub; exact Hp | exact Hf]. }
        assert (Hs := Hclo _ Hp _ Hdep).
        destruct d as [[m zeta] | [m zeta]]; cbn [MatchDep].
        + exact (proj1 (req_decode _ _ _ _ Hres) Hs).
        + intro HM; cbn [encDep] in Hs.
          exact (Hs (proj2 (match_decode _ _ _ _ Hres) HM)).
      - intros m p q HpS HqS Hp Hq.
        apply mem_alpineResolution in HpS, HqS.
        assert (Hwp : exists w,
                   PackageFormula.PackageSet.In (Name.Orig m, w) S /\
                   ((exists v, p = (m, v) /\ w = Version.Orig v) \/
                    (exists u, w = Version.Prov p u))).
        { destruct Hp as [Hp | [u Hprovp]].
          - destruct p as [np vp]; cbn in Hp; subst np.
            exists (Version.Orig vp); split; [exact HpS |].
            left; exists vp; split; reflexivity.
          - exists (Version.Prov p u); split.
            + exact (reg_edge _ _ _ _ _ Hres HpS Hprovp).
            + right; exists u; reflexivity. }
        assert (Hwq : exists w,
                   PackageFormula.PackageSet.In (Name.Orig m, w) S /\
                   ((exists v, q = (m, v) /\ w = Version.Orig v) \/
                    (exists u, w = Version.Prov q u))).
        { destruct Hq as [Hq | [u Hprovq]].
          - destruct q as [nq vq]; cbn in Hq; subst nq.
            exists (Version.Orig vq); split; [exact HqS |].
            left; exists vq; split; reflexivity.
          - exists (Version.Prov q u); split.
            + exact (reg_edge _ _ _ _ _ Hres HqS Hprovq).
            + right; exists u; reflexivity. }
        destruct Hwp as [wp [HwpS Hshp]], Hwq as [wq [HwqS Hshq]].
        assert (Hew : wp = wq) by exact (Huniq _ _ _ HwpS HwqS).
        subst wq.
        destruct Hshp as [[vp [-> ->]] | [u ->]],
            Hshq as [[vq [-> He]] | [u' He]];
          try discriminate He.
        + injection He as <-; reflexivity.
        + injection He as <- _; reflexivity.
      - intros zn zv B Hrule Hc; set (z := (zn, zv)) in *.
        destruct (Designation.designation_spec B (Hwf _ _ Hrule))
          as [[na cta] [Hdes Hin]].
        assert (HM := Hc _ Hin); cbn [MatchCond] in HM.
        apply (match_attachAt I (alpineResolution S) na cta) in HM.
        destruct HM as [p [HpS Hatt]].
        apply mem_alpineResolution in HpS.
        assert (Hfib : InstallIfRuleRel.In (z, B) (installIfFibre I p)).
        { apply mem_installIfFibre; split; [exact Hrule |].
          unfold attachDesignation; rewrite Hdes; exact Hatt. }
        assert (Hf : PackageFormulaSet.In (installIfForm I z B)
                       (dependees I (embedPkg p))).
        { destruct p as [np vp]; cbn [dependees embedPkg fst snd].
          apply PackageFormulaSet.union_spec; right;
            apply PackageFormulaSet.union_spec; right.
          apply SOtf.mem_map; exists (z, B); split;
            [exact Hfib | reflexivity]. }
        assert (Hdep :
          PackageFormula.DependencyRel.In (embedPkg p, installIfForm I z B)
                         (reduceDeps I)).
        { apply mem_reduceDeps; split; [apply Hsub; exact HpS | exact Hf]. }
        assert (Hs := Hclo _ HpS _ Hdep).
        apply satisfies_installIfForm in Hs.
        destruct Hs as [[c [Hcr Hn]] | Hb].
        + exfalso; apply Hn.
          apply (proj2 (cond_decode _ _ _ Hres)).
          exact (Hc _ (condRest_subset _ _ Hcr)).
        + exact (proj1 (match_decode _ _ _ _ Hres) Hb).
    Qed.

    Definition WfProvides (I : Inst) : Prop :=
      (forall q n u u',
          ProvidesRel.In (q, (n, PVer u)) (inst_prov I) ->
          ProvidesRel.In (q, (n, PVer u')) (inst_prov I) -> u = u') /\
      (forall n v u, ~ ProvidesRel.In ((n, v), (n, PVer u)) (inst_prov I)).

    Lemma base_coreResolution : forall I S n zeta,
        PackageSet.Subset S (inst_real I) ->
        ((exists w, PackageFormula.VSet.In w (versionsAt I n zeta) /\
            PackageFormula.PackageSet.In (Name.Orig n, w)
              (coreResolution I S)) <->
         (exists v, PackageSet.In (n, v) S /\ constrMatch zeta v = true) \/
         (exists q u, ProvidesRel.In (q, (n, PVer u)) (inst_prov I) /\
            PackageSet.In q S /\ constrMatch zeta u = true)).
    Proof.
      intros I S n zeta Hsub; split.
      - intros [w [Hw Hm]]; apply mem_versionsAt in Hw.
        destruct Hw as [[v [_ [Hc ->]]] | [q [u [_ [_ [Hc ->]]]]]].
        + apply (coreResolution_embed I S (n, v)) in Hm; left; eauto.
        + apply coreResolution_prov in Hm; destruct Hm as [Hprov Hq].
          right; exists q, u; auto.
      - intros [[v [HvS Hc]] | [q [u [Hprov [HqS Hc]]]]].
        + exists (Version.Orig v); split.
          * apply mem_versionsAt; left; exists v.
            repeat split; try assumption.
            exact (Hsub _ HvS).
          * exact (proj2 (coreResolution_embed I S (n, v)) HvS).
        + exists (Version.Prov q u); split.
          * apply mem_versionsAt; right; exists q, u.
            repeat split; try assumption.
            exact (Hsub _ HqS).
          * apply coreResolution_prov; split; assumption.
    Qed.

    Lemma match_coreResolution : forall I S n zeta,
        PackageSet.Subset S (inst_real I) ->
        (PackageFormula.Satisfies (coreResolution I S) (encPos I n zeta) <->
         Match I S n zeta).
    Proof.
      intros I S n zeta Hsub.
      rewrite satisfies_encPos, (base_coreResolution I S n zeta Hsub).
      unfold Match; rewrite or_assoc.
      apply or_iff_compat_l, or_iff_compat_l, and_iff_compat_l; split.
      - intros [q [Hq Hm]]; apply mem_bareProvSet in Hq.
        apply coreResolution_embed in Hm; exists q; split; [exact (proj1 Hq) |].
        exact Hm.
      - intros [q [Hp HqS]]; exists q; split;
          [apply mem_bareProvSet; split; [exact Hp | exact (Hsub _ HqS)]
          | apply coreResolution_embed; exact HqS].
    Qed.

    Lemma req_coreResolution : forall I S n zeta,
        PackageSet.Subset S (inst_real I) ->
        (PackageFormula.Satisfies (coreResolution I S) (encReq I n zeta) <->
         Req I S n zeta).
    Proof.
      intros I S n zeta Hsub.
      rewrite satisfies_encReq, (base_coreResolution I S n zeta Hsub).
      unfold Req; rewrite or_assoc.
      apply or_iff_compat_l, or_iff_compat_l, and_iff_compat_l; split.
      - intros [q [Hq [Hs Hm]]]; apply mem_bareProvSet in Hq.
        apply coreResolution_embed in Hm; exists q; split; [exact (proj1 Hq) |].
        split; [exact Hm | apply selectableb_spec; exact Hs].
      - intros [q [Hp [HqS Ha]]]; exists q.
        split;
          [apply mem_bareProvSet; split; [exact Hp | exact (Hsub _ HqS)] |].
        split; [apply selectableb_spec; exact Ha |].
        apply coreResolution_embed; exact HqS.
    Qed.

    Theorem alpine_completeness : forall I S,
        WfProvides I -> IsResolution I S ->
        PackageFormula.IsResolution (reduceReal I) (reduceDeps I) rootPkg
          (coreResolution I S).
    Proof.
      intros I S [Wf1 Wf2] Hres.
      destruct Hres as [Hsub Hw Hd Hcu Ht].
      assert (Hiff := fun n zeta => match_coreResolution I S n zeta Hsub).
      assert (Hreq := fun n zeta => req_coreResolution I S n zeta Hsub).
      assert (Hcond : forall c,
                 PackageFormula.Satisfies (coreResolution I S) (encCond I c) <->
                                MatchCond I S c).
      { intros [[n zeta] | [n zeta]];
          cbn [encCond MatchCond PackageFormula.Satisfies];
          rewrite (Hiff n zeta); reflexivity. }
      constructor.
      - intros [[| n] w] Hy.
        + apply coreResolution_at_root in Hy; subst w; apply root_reduceReal.
        + rewrite reduceReal_coreResolution; apply coreResolution_at_orig in Hy.
          destruct Hy as [[v [Hv ->]] | [q [u [Hr [Hq ->]]]]].
          * exact (proj2 (coreResolution_embed I _ (n, v)) (Hsub _ Hv)).
          * apply coreResolution_prov; split; [exact Hr | exact (Hsub _ Hq)].
      - apply mem_coreResolution; left; reflexivity.
      - intros p' Hp' f Hdep.
        apply mem_reduceDeps in Hdep; destruct Hdep as [HyR Hf].
        apply mem_coreResolution in Hp'.
        destruct Hp' as [-> | [[p [Hp ->]] | [q [m [u [Hr [Hq ->]]]]]]].
        + cbn [dependees rootPkg] in Hf.
          apply SOwf.mem_map in Hf; destruct Hf as [d [Hd0 ->]].
          assert (Hmd := Hw _ Hd0).
          destruct d as [[m zeta] | [m zeta]]; cbn [MatchDep] in Hmd;
            cbn [encDep].
          * apply Hreq; exact Hmd.
          * cbn [PackageFormula.Satisfies]; intro Hs; apply Hmd.
            apply Hiff; exact Hs.
        + destruct p as [n0 v0].
          cbn [dependees embedPkg fst snd] in Hf.
          apply PackageFormulaSet.union_spec in Hf; destruct Hf as [Hf | Hf];
            [| apply PackageFormulaSet.union_spec in Hf;
              destruct Hf as [Hf | Hf]].
          * apply SOdf.mem_map in Hf; destruct Hf as [[p' d] [Hin ->]].
            apply DependencyRelFibred.mem_tailFibre in Hin.
            destruct Hin as [Hin ->].
            assert (Hmd := Hd _ _ Hp Hin).
            destruct d as [[m zeta] | [m zeta]]; cbn [MatchDep] in Hmd;
              cbn [encDep].
            -- apply Hreq; exact Hmd.
            -- cbn [PackageFormula.Satisfies]; intro Hs; apply Hmd.
               apply Hiff; exact Hs.
          * apply SOrf.mem_filterMap in Hf.
            destruct Hf as [[p' [m tg]] [Hin Hval]].
            apply ProvidesRelFibred.mem_tailFibre in Hin.
            destruct Hin as [Hin ->].
            destruct tg as [u |]; [| discriminate].
            injection Hval as <-.
            cbn [PackageFormula.Satisfies].
            exists (Version.Prov (n0, v0) u); split.
            -- apply PackageFormula.VSet.singleton_spec; reflexivity.
            -- apply coreResolution_prov; split; assumption.
          * apply SOtf.mem_map in Hf; destruct Hf as [[[zn zv] B] [Hfib ->]].
            apply mem_installIfFibre in Hfib.
            destruct Hfib as [Ht0 Hatt]; unfold attachDesignation in Hatt.
            destruct (Designation.designation B) as [a |] eqn:Edes;
              [| discriminate].
            apply satisfies_installIfForm.
            destruct (ConditionSet.exists_
                        (fun b => negb
                          (PackageFormula.satisfiesb (coreResolution I S)
                                          (encCond I b)))
                        (condRest B)) eqn:Ee.
            -- apply ConditionSet.exists_spec' in Ee.
               destruct Ee as [b [Hb Hnb]].
               apply Bool.negb_true_iff in Hnb.
               left; exists b; split; [exact Hb |].
               intro Hs; apply PackageFormula.satisfiesb_iff in Hs; congruence.
            -- right; apply Hiff, (Ht zn zv B Ht0).
               intros c Hc.
               destruct (DependencyAtomOT.eq_dec c (DPos a)) as [He | Hne].
               ++ subst c; destruct a as [ma cta]; cbn [MatchCond].
                  apply match_attachAt; exists (n0, v0).
                  split; [exact Hp | exact Hatt].
               ++ assert (Hr : ConditionSet.In c (condRest B)).
                  { unfold condRest; rewrite Edes.
                    apply ConditionSet.remove_spec; split;
                      [exact Hc | exact Hne]. }
                  assert (Hbt : PackageFormula.satisfiesb (coreResolution I S)
                                  (encCond I c) = true).
                  { destruct (PackageFormula.satisfiesb (coreResolution I S)
                      (encCond I c))
                      eqn:Eb; [reflexivity |].
                    exfalso.
                    assert (Hex : ConditionSet.exists_
                                    (fun b =>
                                       negb (PackageFormula.satisfiesb
                                         (coreResolution I S)
                                               (encCond I b)))
                                    (condRest B) = true).
                    { apply ConditionSet.exists_spec'; exists c; split;
                        [exact Hr | cbn; rewrite Eb; reflexivity]. }
                    congruence. }
                  apply Hcond; apply PackageFormula.satisfiesb_iff; exact Hbt.
        + cbn [dependees] in Hf.
          apply PackageFormulaSet.singleton_spec in Hf; subst f.
          cbn [PackageFormula.Satisfies].
          exists (Version.Orig (snd q)); split.
          * apply PackageFormula.VSet.singleton_spec; reflexivity.
          * exact (proj2 (coreResolution_embed I S q) Hq).
      - intros m w w' H1 H2.
        destruct m as [| n].
        + apply coreResolution_at_root in H1, H2; congruence.
        + apply coreResolution_at_orig in H1, H2.
          destruct H1 as [[v1 [Hv1 ->]] | [q1 [u1 [Hr1 [Hq1 ->]]]]],
              H2 as [[v2 [Hv2 ->]] | [q2 [u2 [Hr2 [Hq2 ->]]]]].
          * f_equal.
            assert (He : (n, v1) = (n, v2)).
            { apply (Hcu n (n, v1) (n, v2) Hv1 Hv2);
                left; reflexivity. }
            injection He as He; exact He.
          * exfalso.
            assert (He : (n, v1) = q2).
            { apply (Hcu n (n, v1) q2 Hv1 Hq2);
                [left; reflexivity | right; exists u2; exact Hr2]. }
            subst q2; exact (Wf2 _ _ _ Hr2).
          * exfalso.
            assert (He : q1 = (n, v2)).
            { apply (Hcu n q1 (n, v2) Hq1 Hv2);
                [right; exists u1; exact Hr1 | left; reflexivity]. }
            subst q1; exact (Wf2 _ _ _ Hr1).
          * assert (He : q1 = q2).
            { apply (Hcu n q1 q2 Hq1 Hq2);
                [right; exists u1; exact Hr1
                | right; exists u2; exact Hr2]. }
            subst q2.
            rewrite (Wf1 _ _ _ _ Hr1 Hr2); reflexivity.
    Qed.

    Module Lookup.
      Lemma or_iff : forall A B C D : Prop,
          (A <-> C) -> (B <-> D) -> (A \/ B <-> C \/ D).
      Proof. tauto. Qed.

      Module NSet := FSetUOT N.
      Module SOdn := SetOps DependencyElt N DependencyRel NSet.
      Definition depName (d : Dep) : N.t :=
        match d with DPos (n, _) => n | DNeg (n, _) => n end.

      Definition atomNames (I : Inst) (p : Package.t) : NSet.t :=
        SOdn.map (fun '(_, d) => depName d)
          (DependencyRelFibred.tailFibre (inst_deps I) p).

      Definition provTouchb (I : Inst) (ns : NSet.t) (q : Package.t) : bool :=
        ProvidesRel.exists_
          (fun '(q', (m, _)) => andb (PackageEqb.eqb q' q) (NSet.mem m ns))
          (inst_prov I).

      Module PackageSetPreimage := Preimage Package PackageSet.
      Definition repoPreimage (I : Inst) (ns : NSet.t) : PackageSet.t :=
        PackageSetPreimage.preimage (fun p => p)
          (fun q => orb (NSet.mem (fst q) ns) (provTouchb I ns q))
          (inst_real I).

      Module ProvidesRelPreimage := Preimage ProvidesElt ProvidesRel.
      Definition provPreimage (I : Inst) (ns : NSet.t) : ProvidesRel.t :=
        ProvidesRelPreimage.preimage (fun '(_, (m, _)) => m)
          (fun m => NSet.mem m ns) (inst_prov I).

      Lemma mem_repoPreimage : forall I ns q,
          PackageSet.In q (repoPreimage I ns) <->
          PackageSet.In q (inst_real I) /\
          (NSet.In (fst q) ns \/
           exists m tg, ProvidesRel.In (q, (m, tg)) (inst_prov I) /\
             NSet.In m ns).
      Proof.
        intros I ns q; unfold repoPreimage.
        rewrite PackageSetPreimage.mem_preimage, Bool.orb_true_iff.
        apply and_iff_compat_l.
        rewrite NSet.mem_spec; apply or_iff_compat_l.
        unfold provTouchb; rewrite ProvidesRel.exists_spec'.
        split.
        - intros [[q' [m tg]] [Hr Hb]]; cbn in Hb.
          apply Bool.andb_true_iff in Hb; destruct Hb as [Hq Hm].
          apply PackageEqb.eqb_true_iff in Hq; subst q'.
          apply NSet.mem_spec in Hm; eauto.
        - intros [m [tg [Hr Hm]]]; exists (q, (m, tg)); split;
            [exact Hr | cbn].
          rewrite (proj2 (PackageEqb.eqb_true_iff q q) eq_refl).
          rewrite (proj2 (NSet.mem_spec _ _) Hm); reflexivity.
      Qed.

      Lemma mem_provPreimage : forall I ns e,
          ProvidesRel.In e (provPreimage I ns) <->
          ProvidesRel.In e (inst_prov I) /\ NSet.In (fst (snd e)) ns.
      Proof.
        intros I ns [q [m tg]]; unfold provPreimage.
        rewrite ProvidesRelPreimage.mem_preimage, NSet.mem_spec; cbn.
        reflexivity.
      Qed.

      Lemma encPos_agree : forall I I' n zeta,
          versionsAt I' n zeta = versionsAt I n zeta ->
          bareProvSet I' n = bareProvSet I n ->
          encPos I' n zeta = encPos I n zeta.
      Proof.
        intros I I' n zeta Hc Hu; unfold encPos, bareProvL.
        rewrite Hc, Hu; reflexivity.
      Qed.

      Definition prioOf (I : Inst) (qs : PackageSet.t) : PriorityRel.t :=
        PriorityRel.filter (fun '(q, _) => PackageSet.mem q qs) (inst_prio I).

      Lemma mem_prioOf : forall I qs q prio,
          PriorityRel.In (q, prio) (prioOf I qs) <->
          PriorityRel.In (q, prio) (inst_prio I) /\ PackageSet.In q qs.
      Proof.
        intros I qs q prio; unfold prioOf; rewrite PriorityRel.filter_spec'.
        cbn; rewrite PackageSet.mem_spec; reflexivity.
      Qed.

      Definition subInst (I : Inst) (ns : NSet.t) (deps : DependencyRel.t)
          (ownProv : ProvidesRel.t) (installIf : InstallIfRuleRel.t)
            (world : WorldSet.t)
        : Inst :=
        {| inst_real := repoPreimage I ns
         ; inst_deps := deps
         ; inst_prov := ProvidesRel.union ownProv (provPreimage I ns)
         ; inst_installIf := installIf
         ; inst_world := world
         ; inst_prio := prioOf I (repoPreimage I ns) |}.

      Lemma versionsAt_subInst :
        forall I ns deps ownProv installIf world n zeta,
          NSet.In n ns ->
          ProvidesRel.Subset ownProv (inst_prov I) ->
          versionsAt (subInst I ns deps ownProv installIf world) n zeta =
          versionsAt I n zeta.
      Proof.
        intros I ns deps ownProv installIf world n zeta Hn Hown.
        apply PackageFormula.VSet.ext; intro w.
        rewrite !mem_versionsAt; cbn [subInst inst_real inst_prov].
        split.
        - intros [[v [Hrep [Hc ->]]] | [q [u [Hprov [Hrep [Hc ->]]]]]].
          + apply mem_repoPreimage in Hrep; destruct Hrep as [Hrep _].
            left; eauto.
          + apply ProvidesRel.union_spec in Hprov.
            assert (Hprov' : ProvidesRel.In (q, (n, PVer u)) (inst_prov I)).
            { destruct Hprov as [Hprov | Hprov]; [exact (Hown _ Hprov) |].
              apply mem_provPreimage in Hprov; exact (proj1 Hprov). }
            apply mem_repoPreimage in Hrep; destruct Hrep as [Hrep _].
            right; exists q, u; auto.
        - intros [[v [Hrep [Hc ->]]] | [q [u [Hprov [Hrep [Hc ->]]]]]].
          + left; exists v; repeat split; try assumption.
            apply mem_repoPreimage; split; [exact Hrep |].
            left; exact Hn.
          + right; exists q, u; repeat split; try assumption.
            * apply ProvidesRel.union_spec; right.
              apply mem_provPreimage; split; [exact Hprov | exact Hn].
            * apply mem_repoPreimage; split; [exact Hrep |].
              right; exists n, (PVer u); split; assumption.
      Qed.

      Lemma bareProvSet_subInst : forall I ns deps ownProv installIf world n,
          NSet.In n ns ->
          ProvidesRel.Subset ownProv (inst_prov I) ->
          bareProvSet (subInst I ns deps ownProv installIf world) n =
          bareProvSet I n.
      Proof.
        intros I ns deps ownProv installIf world n Hn Hown.
        apply PackageSet.ext; intro q.
        rewrite !mem_bareProvSet; cbn [subInst inst_real inst_prov].
        split.
        - intros [Hprov Hrep].
          apply ProvidesRel.union_spec in Hprov.
          assert (Hprov' : ProvidesRel.In (q, (n, PBare)) (inst_prov I)).
          { destruct Hprov as [Hprov | Hprov]; [exact (Hown _ Hprov) |].
            apply mem_provPreimage in Hprov; exact (proj1 Hprov). }
          apply mem_repoPreimage in Hrep; destruct Hrep as [Hrep _].
          split; assumption.
        - intros [Hprov Hrep]; split.
          + apply ProvidesRel.union_spec; right.
            apply mem_provPreimage; split; [exact Hprov | exact Hn].
          + apply mem_repoPreimage; split; [exact Hrep |].
            right; exists n, PBare; split; assumption.
      Qed.

      Theorem dependees_lookupProv : forall I m n v u,
          dependees I (Name.Orig m, Version.Prov (n, v) u) =
          PackageFormulaSet.singleton
            (PackageFormula.FAtom (Name.Orig n)
              (PackageFormula.VSet.singleton (Version.Orig v))).
      Proof. reflexivity. Qed.

      Definition nameSubInst (I : Inst) (n : N.t) : Inst :=
        subInst I (NSet.singleton n) DependencyRel.empty ProvidesRel.empty
          InstallIfRuleRel.empty WorldSet.empty.

      Theorem versions_lookupOrig : forall I n,
          versions I n = versions (nameSubInst I n) n.
      Proof.
        intros I n; symmetry; unfold versions, nameSubInst.
        apply versionsAt_subInst.
        - apply NSet.singleton_spec; reflexivity.
        - intros e He; destruct (ProvidesRel.empty_spec He).
      Qed.

      Module SOwn := SetOps DependencyAtomOT N WorldSet NSet.
      Module SOan := SetOps DependencyAtomOT N ConditionSet NSet.
      Module SOtn := SetOps InstallIfRuleElt N InstallIfRuleRel NSet.

      Definition condNames (B : ConditionSet.t) : NSet.t :=
        SOan.map depName B.

      Lemma encPos_subInst : forall I ns deps ownProv installIf world
              (n : N.t) (zeta : Constr),
          NSet.In n ns ->
          ProvidesRel.Subset ownProv (inst_prov I) ->
          encPos (subInst I ns deps ownProv installIf world) n zeta =
          encPos I n zeta.
      Proof.
        intros I ns deps ownProv installIf world n zeta Hn Hown.
        apply encPos_agree.
        - apply versionsAt_subInst; assumption.
        - apply bareProvSet_subInst; assumption.
      Qed.

      Lemma selectableb_subInst : forall I ns deps ownProv installIf q,
          PackageSet.In q (repoPreimage I ns) ->
          selectableb (subInst I ns deps ownProv installIf (inst_world I)) q =
          selectableb I q.
      Proof.
        intros I ns deps ownProv installIf q Hq.
        unfold selectableb, hasPriorityb, worldNamesb.
        cbn [subInst inst_prio inst_world]; f_equal.
        apply PriorityRel.exists_restrict.
        - intros [q' k] H; apply mem_prioOf in H; exact (proj1 H).
        - intros [q' k] Hin Hb; cbn in Hb.
          apply Bool.andb_true_iff in Hb; destruct Hb as [Hq' _].
          apply PackageEqb.eqb_true_iff in Hq'; subst q'.
          apply mem_prioOf; split; assumption.
      Qed.

      Lemma encReq_subInst : forall I ns deps ownProv installIf
              (n : N.t) (zeta : Constr),
          NSet.In n ns ->
          ProvidesRel.Subset ownProv (inst_prov I) ->
          encReq (subInst I ns deps ownProv installIf (inst_world I)) n zeta =
          encReq I n zeta.
      Proof.
        intros I ns deps ownProv installIf n zeta Hn Hown.
        unfold encReq, bareProvL; cbv zeta.
        rewrite (versionsAt_subInst I ns deps ownProv installIf
                   (inst_world I) n zeta Hn Hown).
        rewrite (bareProvSet_subInst I ns deps ownProv installIf
                   (inst_world I) n Hn Hown).
        destruct (bareMatch zeta); [| reflexivity].
        f_equal; apply filter_ext_in; intros q Hq.
        apply selectableb_subInst.
        apply SOpp.elements_in, mem_bareProvSet in Hq;
          destruct Hq as [Hp Hr].
        apply mem_repoPreimage; split; [exact Hr |].
        right; exists n, PBare; split; assumption.
      Qed.

      Lemma encDep_subInst : forall I ns deps ownProv installIf d,
          NSet.In (depName d) ns ->
          ProvidesRel.Subset ownProv (inst_prov I) ->
          encDep (subInst I ns deps ownProv installIf (inst_world I)) d =
          encDep I d.
      Proof.
        intros I ns deps ownProv installIf [[m zeta] | [m zeta]] Hn Hown;
          cbn [encDep depName] in *; [| f_equal].
        - apply encReq_subInst; assumption.
        - apply encPos_subInst; assumption.
      Qed.

      Lemma encCond_subInst : forall I ns deps ownProv installIf world a,
          NSet.In (depName a) ns ->
          ProvidesRel.Subset ownProv (inst_prov I) ->
          encCond (subInst I ns deps ownProv installIf world) a =
          encCond I a.
      Proof.
        intros I ns deps ownProv installIf world [[m zeta] | [m zeta]] Hn Hown;
          cbn [encCond depName] in *; [| f_equal];
          apply encPos_subInst; assumption.
      Qed.

      Lemma negFold_agree : forall I I' l base,
          (forall c, List.In c l -> encCond I' c = encCond I c) ->
          fold_right
            (fun c f => PackageFormula.FDisj
              (PackageFormula.FNeg (encCond I' c)) f) base l =
          fold_right
            (fun c f => PackageFormula.FDisj
              (PackageFormula.FNeg (encCond I c)) f) base l.
      Proof.
        intros I I' l base H; induction l as [| c l IH]; cbn.
        - reflexivity.
        - rewrite (H c (or_introl eq_refl)), IH; [reflexivity |].
          intros b Hb; apply H; right; exact Hb.
      Qed.

      Lemma installIfForm_subInst : forall I ns deps ownProv installIf world
              (p : Package.t) (B : ConditionSet.t),
          NSet.In (fst p) ns ->
          (forall a : Dep,
              ConditionSet.In a (condRest B) -> NSet.In (depName a) ns) ->
          ProvidesRel.Subset ownProv (inst_prov I) ->
          installIfForm (subInst I ns deps ownProv installIf world) p B =
          installIfForm I p B.
      Proof.
        intros I ns deps ownProv installIf world p B Hz Hc Hown.
        unfold installIfForm.
        rewrite (encPos_subInst I ns deps ownProv installIf world (fst p) CAny
                   Hz Hown).
        apply negFold_agree; intros a Hcl.
        apply LeastDesignation.in_elements in Hcl.
        apply encCond_subInst; [exact (Hc _ Hcl) | exact Hown].
      Qed.

      Lemma subInst_installIf : forall I ns deps ownProv installIf world,
          inst_installIf (subInst I ns deps ownProv installIf world) =
          installIf.
      Proof. reflexivity. Qed.

      Lemma attachAt_subInst : forall I ns deps ownProv installIf world p a,
          ProvidesRel.Subset ownProv (inst_prov I) ->
          (forall m tg, ProvidesRel.In (p, (m, tg)) (inst_prov I) ->
             ProvidesRel.In (p, (m, tg)) ownProv) ->
          attachAt (subInst I ns deps ownProv installIf world) p a =
          attachAt I p a.
      Proof.
        intros I ns deps ownProv installIf world p a Hown Hcov.
        unfold attachAt; cbn [subInst inst_prov];
          f_equal; try reflexivity.
        apply ProvidesRel.exists_restrict.
        - intros e He; apply ProvidesRel.union_spec in He.
          destruct He as [He | He]; [exact (Hown _ He) |].
          apply mem_provPreimage in He; exact (proj1 He).
        - intros [q [m tg]] He Hb; cbn in Hb.
          apply Bool.andb_true_iff in Hb; destruct Hb as [Hq _].
          apply PackageEqb.eqb_true_iff in Hq; subst q.
          apply ProvidesRel.union_spec; left; exact (Hcov _ _ He).
      Qed.

      Lemma attachDesignation_subInst :
        forall I ns deps ownProv installIf world p B,
          ProvidesRel.Subset ownProv (inst_prov I) ->
          (forall m tg, ProvidesRel.In (p, (m, tg)) (inst_prov I) ->
             ProvidesRel.In (p, (m, tg)) ownProv) ->
          attachDesignation (subInst I ns deps ownProv installIf world) p
            B = attachDesignation I p B.
      Proof.
        intros I ns deps ownProv installIf world p B Hown Hcov.
        unfold attachDesignation; destruct (Designation.designation B) as [a |];
          [apply attachAt_subInst; assumption | reflexivity].
      Qed.

      Lemma installIfFibre_subInst : forall I ns deps ownProv world p,
          ProvidesRel.Subset ownProv (inst_prov I) ->
          (forall m tg, ProvidesRel.In (p, (m, tg)) (inst_prov I) ->
             ProvidesRel.In (p, (m, tg)) ownProv) ->
          installIfFibre
            (subInst I ns deps ownProv (installIfFibre I p) world) p =
          installIfFibre I p.
      Proof.
        intros I ns deps ownProv world p Hown Hcov.
        apply InstallIfRuleRel.ext; intros [z B].
        rewrite (mem_installIfFibre I p z B).
        rewrite (mem_installIfFibre
                   (subInst I ns deps ownProv (installIfFibre I p) world)
                   p z B).
        rewrite subInst_installIf.
        rewrite (attachDesignation_subInst I ns deps ownProv
                   (installIfFibre I p) world p B Hown Hcov).
        rewrite (mem_installIfFibre I p z B).
        tauto.
      Qed.

      Definition pkgNames (I : Inst) (p : Package.t) : NSet.t :=
        NSet.union (atomNames I p)
          (SOtn.unionMap
             (fun '(z, B) =>
                NSet.add (fst z) (condNames (condRest B)))
             (installIfFibre I p)).

      Lemma dep_pkgNames : forall I p d,
          DependencyRel.In (p, d)
            (DependencyRelFibred.tailFibre (inst_deps I) p) ->
          NSet.In (depName d) (pkgNames I p).
      Proof.
        intros I p d H; unfold pkgNames; apply NSet.union_spec; left.
        unfold atomNames; apply SOdn.mem_map; exists (p, d); split;
          [exact H | reflexivity].
      Qed.

      Lemma selfName_pkgNames : forall I q p B,
          InstallIfRuleRel.In (p, B) (installIfFibre I q) ->
          NSet.In (fst p) (pkgNames I q).
      Proof.
        intros I q p B H; unfold pkgNames; apply NSet.union_spec; right.
        apply SOtn.mem_unionMap; exists (p, B); split; [exact H |].
        cbv beta iota; apply NSet.add_spec; left; reflexivity.
      Qed.

      Lemma condName_pkgNames : forall I q p B a,
          InstallIfRuleRel.In (p, B) (installIfFibre I q) ->
          ConditionSet.In a (condRest B) ->
          NSet.In (depName a) (pkgNames I q).
      Proof.
        intros I q p B a Ht Ha; unfold pkgNames.
        apply NSet.union_spec; right.
        apply SOtn.mem_unionMap; exists (p, B); split; [exact Ht |].
        cbv beta iota; apply NSet.add_spec; right.
        unfold condNames; apply SOan.mem_map; exists a; split;
          [exact Ha | reflexivity].
      Qed.

      Definition pkgSubInst (I : Inst) (p : Package.t) : Inst :=
        subInst I (pkgNames I p)
          (DependencyRelFibred.tailFibre (inst_deps I) p)
          (ProvidesRelFibred.tailFibre (inst_prov I) p)
          (installIfFibre I p) (inst_world I).

      Theorem dependees_lookupOrig : forall I n v,
          dependees I (embedPkg (n, v)) =
          dependees (pkgSubInst I (n, v)) (embedPkg (n, v)).
      Proof.
        intros I n v; symmetry.
        assert (Hown : ProvidesRel.Subset
                         (ProvidesRelFibred.tailFibre (inst_prov I) (n, v))
                         (inst_prov I))
          by apply ProvidesRelFibred.tailFibre_subset.
        assert (Hcov : forall m tg,
                   ProvidesRel.In ((n, v), (m, tg)) (inst_prov I) ->
                   ProvidesRel.In ((n, v), (m, tg))
                     (ProvidesRelFibred.tailFibre (inst_prov I) (n, v))).
        { intros m tg H; apply ProvidesRelFibred.mem_tailFibre; split;
            [exact H | reflexivity]. }
        assert (Hfib : installIfFibre (pkgSubInst I (n, v)) (n, v) =
                         installIfFibre I (n, v)).
        { unfold pkgSubInst; apply installIfFibre_subInst; assumption. }
        apply PackageFormulaSet.ext; intro f.
        cbn [dependees embedPkg fst snd].
        rewrite Hfib.
        cbn [pkgSubInst subInst inst_deps inst_prov].
        rewrite !PackageFormulaSet.union_spec, !SOdf.mem_map,
          !SOrf.mem_filterMap,
          !SOtf.mem_map.
        apply or_iff; [| apply or_iff].
        - split.
          + intros [[p' d] [Hin ->]].
            apply DependencyRelFibred.mem_tailFibre in Hin.
            destruct Hin as [Hin ->].
            exists ((n, v), d); split; [exact Hin |].
            cbv beta iota; apply encDep_subInst;
              [exact (dep_pkgNames I (n, v) d Hin) | exact Hown].
          + intros [[p' d] [Hin ->]].
            apply DependencyRelFibred.mem_tailFibre in Hin.
            destruct Hin as [Hin ->].
            assert (Hfb : DependencyRel.In ((n, v), d)
                            (DependencyRelFibred.tailFibre
                              (inst_deps I) (n, v))).
            { apply DependencyRelFibred.mem_tailFibre; split;
                [exact Hin | reflexivity]. }
            exists ((n, v), d); split.
            { apply DependencyRelFibred.mem_tailFibre; split;
                [exact Hfb | reflexivity]. }
            cbv beta iota; symmetry; apply encDep_subInst;
              [exact (dep_pkgNames I (n, v) d Hfb) | exact Hown].
        - split.
          + intros [[p' [m tg]] [Hin Hv]].
            apply ProvidesRelFibred.mem_tailFibre in Hin.
            destruct Hin as [Hin ->].
            apply ProvidesRel.union_spec in Hin.
            assert (Hin' : ProvidesRel.In ((n, v), (m, tg)) (inst_prov I)).
            { destruct Hin as [Hin | Hin].
              - apply ProvidesRelFibred.mem_tailFibre in Hin;
                  exact (proj1 Hin).
              - apply mem_provPreimage in Hin; exact (proj1 Hin). }
            exists ((n, v), (m, tg)); split; [| exact Hv].
            apply ProvidesRelFibred.mem_tailFibre; split;
              [exact Hin' | reflexivity].
          + intros [[p' [m tg]] [Hin Hv]].
            apply ProvidesRelFibred.mem_tailFibre in Hin.
            destruct Hin as [Hin ->].
            exists ((n, v), (m, tg)); split; [| exact Hv].
            apply ProvidesRelFibred.mem_tailFibre; split; [| reflexivity].
            apply ProvidesRel.union_spec; left.
            apply ProvidesRelFibred.mem_tailFibre; split;
              [exact Hin | reflexivity].
        - split.
          + intros [[p B] [Hin ->]].
            exists (p, B); split; [exact Hin |].
            cbv beta iota; apply installIfForm_subInst;
              [ exact (selfName_pkgNames I (n, v) p B Hin)
              | intros a Ha;
                exact (condName_pkgNames I (n, v) p B a Hin Ha)
              | exact Hown ].
          + intros [[p B] [Hin ->]].
            exists (p, B); split; [exact Hin |].
            cbv beta iota; symmetry; apply installIfForm_subInst;
              [ exact (selfName_pkgNames I (n, v) p B Hin)
              | intros a Ha;
                exact (condName_pkgNames I (n, v) p B a Hin Ha)
              | exact Hown ].
      Qed.

      Definition rootNames (I : Inst) : NSet.t :=
        SOwn.map depName (inst_world I).

      Lemma world_rootNames : forall I d,
          WorldSet.In d (inst_world I) -> NSet.In (depName d) (rootNames I).
      Proof.
        intros I d Hd; unfold rootNames.
        apply SOwn.mem_map; exists d; split; [exact Hd | reflexivity].
      Qed.

      Definition rootSubInst (I : Inst) : Inst :=
        subInst I (rootNames I) DependencyRel.empty ProvidesRel.empty
          InstallIfRuleRel.empty (inst_world I).

      Lemma rootSubInst_world : forall I,
          inst_world (rootSubInst I) = inst_world I.
      Proof. reflexivity. Qed.

      Theorem dependees_lookupRoot : forall I,
          dependees I rootPkg = dependees (rootSubInst I) rootPkg.
      Proof.
        intro I; symmetry.
        assert (Hown : ProvidesRel.Subset ProvidesRel.empty (inst_prov I)).
        { intros e He; destruct (ProvidesRel.empty_spec He). }
        cbn [dependees rootPkg]; rewrite rootSubInst_world.
        apply PackageFormulaSet.ext; intro f; rewrite !SOwf.mem_map.
        split; intros [d [Hd ->]]; exists d; split; try exact Hd;
          [| symmetry]; unfold rootSubInst;
          apply encDep_subInst;
          [ exact (world_rootNames I d Hd) | exact Hown
          | exact (world_rootNames I d Hd) | exact Hown ].
      Qed.

      Lemma versions_reduceReal : forall I n,
          PackageFormula.Source.versions (reduceReal I) (Name.Orig n) =
            versions I n.
      Proof.
        intros I n; apply PackageFormula.VSet.ext; intro w.
        rewrite PackageFormula.Source.mem_versions, reduceReal_coreResolution;
          unfold versions.
        rewrite mem_versionsAt; split.
        - intro H; apply coreResolution_at_orig in H.
          destruct H as [[v [Hv ->]] | [q [u [Hprov [Hq ->]]]]];
            [left; exists v | right; exists q, u]; auto.
        - intros [[v [Hv [_ ->]]] | [q [u [Hprov [Hq [_ ->]]]]]].
          + exact (proj2 (coreResolution_embed I _ (n, v)) Hv).
          + apply coreResolution_prov; split; assumption.
      Qed.

      Lemma versions_reduceReal_root : forall I,
          PackageFormula.Source.versions (reduceReal I) Name.Root =
          PackageFormula.VSet.singleton Version.UnitV.
      Proof.
        intro I; apply PackageFormula.VSet.ext; intro w.
        rewrite PackageFormula.Source.mem_versions,
          PackageFormula.VSet.singleton_spec.
        split;
          [apply coreResolution_at_root | intros ->; apply root_reduceReal].
      Qed.

      Lemma reduceDeps_tailFibre : forall I q,
          PackageFormula.PackageSet.In q (reduceReal I) ->
          PackageFormula.Reduction.Lookup.DependencyRelFibred.tailFibre
            (reduceDeps I) q =
          PackageFormula.depEdges q (dependees I q).
      Proof.
        intros I q Hq; apply PackageFormula.DependencyRel.ext; intros [q' f].
        rewrite PackageFormula.Reduction.Lookup.DependencyRelFibred.mem_tailFibre, mem_reduceDeps.
        unfold PackageFormula.depEdges; rewrite PackageFormula.SOfd.mem_map.
        split.
        - intros [[_ Hf] ->]; exists f; split; [exact Hf | reflexivity].
        - intro H; mem_destruct; auto.
      Qed.

      Lemma dependees_core : forall I Vq q,
          PackageFormula.PackageSet.In q (reduceReal I) ->
          Vq Name.Root = PackageFormula.VSet.singleton Version.UnitV ->
          (forall m, Vq (Name.Orig m) = versions I m) ->
          PackageFormula.Reduction.Reduced.dependees
            (PackageFormula.Reduction.reduceDeps (reduceReal I) (reduceDeps I))
            (PackageFormula.Reduction.Name.Orig (fst q),
             PackageFormula.Reduction.Version.Orig (snd q)) =
          PackageFormula.Reduction.Reduced.dependees
            (PackageFormula.Reduction.reduceDepsBy Vq
              (PackageFormula.depEdges q (dependees I q)))
            (PackageFormula.Reduction.Name.Orig (fst q),
             PackageFormula.Reduction.Version.Orig (snd q)).
      Proof.
        intros I Vq [n v] Hq HR HO; cbn [fst snd].
        rewrite (PackageFormula.Reduction.Lookup.dependees_lookupOrigBy _ _ Vq)
          by (intros [| m] _;
              [rewrite HR, versions_reduceReal_root
               | rewrite HO, versions_reduceReal];
              reflexivity).
        rewrite (reduceDeps_tailFibre I (n, v) Hq); reflexivity.
      Qed.

      Theorem dependees_lookupOrigCore : forall I Vq n v,
          PackageSet.In (n, v) (inst_real I) ->
          Vq Name.Root = PackageFormula.VSet.singleton Version.UnitV ->
          (forall m, Vq (Name.Orig m) = versions I m) ->
          PackageFormula.Reduction.Reduced.dependees
            (PackageFormula.Reduction.reduceDeps (reduceReal I) (reduceDeps I))
            (PackageFormula.Reduction.embedPkg (embedPkg (n, v))) =
          PackageFormula.Reduction.Reduced.dependees
            (PackageFormula.Reduction.reduceDepsBy Vq
               (PackageFormula.depEdges (embedPkg (n, v))
                  (dependees (pkgSubInst I (n, v)) (embedPkg (n, v)))))
            (PackageFormula.Reduction.embedPkg (embedPkg (n, v))).
      Proof.
        intros I Vq n v Hnv HR HO; rewrite <- dependees_lookupOrig.
        apply (dependees_core I Vq (embedPkg (n, v))); [| exact HR | exact HO].
        rewrite reduceReal_coreResolution, coreResolution_embed; exact Hnv.
      Qed.

      Theorem dependees_lookupRootCore : forall I Vq,
          Vq Name.Root = PackageFormula.VSet.singleton Version.UnitV ->
          (forall m, Vq (Name.Orig m) = versions I m) ->
          PackageFormula.Reduction.Reduced.dependees
            (PackageFormula.Reduction.reduceDeps (reduceReal I) (reduceDeps I))
            (PackageFormula.Reduction.embedPkg rootPkg) =
          PackageFormula.Reduction.Reduced.dependees
            (PackageFormula.Reduction.reduceDepsBy Vq
               (PackageFormula.depEdges rootPkg
                 (dependees (rootSubInst I) rootPkg)))
            (PackageFormula.Reduction.embedPkg rootPkg).
      Proof.
        intros I Vq HR HO; rewrite <- dependees_lookupRoot.
        exact (dependees_core I Vq rootPkg (root_reduceReal I) HR HO).
      Qed.

      Theorem dependees_lookupProvCore : forall I I' Vq m n v u,
          ProvidesRel.In ((n, v), (m, PVer u)) (inst_prov I) ->
          PackageSet.In (n, v) (inst_real I) ->
          Vq Name.Root = PackageFormula.VSet.singleton Version.UnitV ->
          (forall m, Vq (Name.Orig m) = versions I m) ->
          PackageFormula.Reduction.Reduced.dependees
            (PackageFormula.Reduction.reduceDeps (reduceReal I) (reduceDeps I))
            (PackageFormula.Reduction.embedPkg
              (Name.Orig m, Version.Prov (n, v) u)) =
          PackageFormula.Reduction.Reduced.dependees
            (PackageFormula.Reduction.reduceDepsBy Vq
               (PackageFormula.depEdges (Name.Orig m, Version.Prov (n, v) u)
                  (dependees I' (Name.Orig m, Version.Prov (n, v) u))))
            (PackageFormula.Reduction.embedPkg
              (Name.Orig m, Version.Prov (n, v) u)).
      Proof.
        intros I I' Vq m n v u Hprov Hq HR HO.
        rewrite (dependees_lookupProv I' m n v u),
          <- (dependees_lookupProv I m n v u).
        apply (dependees_core I Vq (Name.Orig m, Version.Prov (n, v) u));
          [| exact HR | exact HO].
        rewrite reduceReal_coreResolution, coreResolution_prov.
        split; assumption.
      Qed.

      Theorem dependees_lookupDisjunctCore : forall I I' Vq q fs i,
          PackageFormula.PackageSet.In q (reduceReal I) ->
          dependees I' q = dependees I q ->
          Vq Name.Root = PackageFormula.VSet.singleton Version.UnitV ->
          (forall m, Vq (Name.Orig m) = versions I m) ->
          PackageFormula.Reduction.Reduced.PackageSet.In
            (PackageFormula.Reduction.Name.Disjunct fs, i)
            (PackageFormula.Reduction.reduceReal
              (PackageFormula.PackageSet.singleton q)
               (PackageFormula.depEdges q (dependees I' q))) ->
          PackageFormula.Reduction.Reduced.dependees
            (PackageFormula.Reduction.reduceDeps (reduceReal I) (reduceDeps I))
            (PackageFormula.Reduction.Name.Disjunct fs, i) =
          PackageFormula.Reduction.Reduced.dependees
            (PackageFormula.Reduction.reduceDepsBy Vq
              (PackageFormula.depEdges q (dependees I' q)))
            (PackageFormula.Reduction.Name.Disjunct fs, i).
      Proof.
        intros I I' Vq q fs i Hq HI HR HO Hin; rewrite HI in Hin |- *.
        assert (Hsub :
          PackageFormula.DependencyRel.Subset
          (PackageFormula.depEdges q (dependees I q))
                         (reduceDeps I)).
        { rewrite <- (reduceDeps_tailFibre I q Hq).
          apply PackageFormula.Reduction.Lookup.DependencyRelFibred.tailFibre_subset. }
        apply (PackageFormula.Reduction.Lookup.dependees_lookupDisjunctBy
                 _ _ _ _ _ _ _ Hsub Hin).
        intros p f [| m] _ _;
          [rewrite HR, versions_reduceReal_root
          | rewrite HO, versions_reduceReal];
          reflexivity.
      Qed.

      Lemma versions_core : forall I n,
          (exists v, PackageFormula.PackageSet.In (n, v) (reduceReal I)) \/
          (exists p h,
              PackageFormula.Reduction.Reduced.DependencyRel.In
                (p, (PackageFormula.Reduction.Name.Orig n, h))
                (PackageFormula.Reduction.reduceDeps (reduceReal I)
                  (reduceDeps I))) ->
          PackageFormula.Reduction.Reduced.versions
            (PackageFormula.Reduction.reduceReal (reduceReal I) (reduceDeps I))
            (PackageFormula.Reduction.Name.Orig n) =
          PackageFormula.Reduction.Reduced.VSet.add
            PackageFormula.Reduction.Version.Bot
            (PackageFormula.Reduction.embedVS
              (PackageFormula.Source.versions (reduceReal I) n)).
      Proof.
        intros I n Hreach.
        destruct Hreach as [[v Hv] | Hreach];
          [rewrite (PackageFormula.Reduction.Lookup.versions_lookupOrig
            _ _ n v n Hv
                      (or_intror eq_refl) eq_refl)
          | rewrite (PackageFormula.Reduction.Lookup.versions_lookupOrig _ _ _ _ n
                       (root_reduceReal I) (or_introl Hreach) eq_refl)];
          rewrite PackageFormula.Reduction.Lookup.versions_reduceReal_bot;
          do 2 f_equal; apply PackageFormula.Source.versions_ext; intro u;
          rewrite PackageFormula.Reduction.Lookup.PackageSetFibred.mem_tailFibre; tauto.
      Qed.

      Theorem versions_lookupOrigCore : forall I n,
          (exists v, PackageSet.In (n, v) (inst_real I)) \/
          (exists p h,
              PackageFormula.Reduction.Reduced.DependencyRel.In
                (p, (PackageFormula.Reduction.Name.Orig (Name.Orig n), h))
                (PackageFormula.Reduction.reduceDeps (reduceReal I)
                  (reduceDeps I))) ->
          PackageFormula.Reduction.Reduced.versions
            (PackageFormula.Reduction.reduceReal (reduceReal I) (reduceDeps I))
            (PackageFormula.Reduction.Name.Orig (Name.Orig n)) =
          PackageFormula.Reduction.Reduced.VSet.add
            PackageFormula.Reduction.Version.Bot
            (PackageFormula.Reduction.embedVS (versions (nameSubInst I n) n)).
      Proof.
        intros I n H; rewrite <- versions_lookupOrig, <- versions_reduceReal.
        apply versions_core.
        destruct H as [[v Hv] | H];
          [left; exists (Version.Orig v) | right; exact H].
        rewrite reduceReal_coreResolution.
        exact (proj2 (coreResolution_embed I _ (n, v)) Hv).
      Qed.

      Theorem versions_lookupRootCore : forall I,
          PackageFormula.Reduction.Reduced.versions
            (PackageFormula.Reduction.reduceReal (reduceReal I) (reduceDeps I))
            (PackageFormula.Reduction.Name.Orig Name.Root) =
          PackageFormula.Reduction.Reduced.VSet.add
            PackageFormula.Reduction.Version.Bot
            (PackageFormula.Reduction.embedVS
              (PackageFormula.VSet.singleton Version.UnitV)).
      Proof.
        intro I; rewrite <- (versions_reduceReal_root I); apply versions_core.
        left; exists Version.UnitV; exact (root_reduceReal I).
      Qed.
    End Lookup.

    Theorem alpine_retraction : forall I S,
        alpineResolution (coreResolution I S) = S.
    Proof.
      intros I S; apply PackageSet.ext; intros [n v].
      rewrite mem_alpineResolution, coreResolution_embed; reflexivity.
    Qed.

    Corollary alpine_core_soundness : forall I S,
        WfInstallIf I ->
        PackageFormula.Reduction.Reduced.IsResolution
          (PackageFormula.Reduction.reduceReal (reduceReal I) (reduceDeps I))
          (PackageFormula.Reduction.reduceDeps (reduceReal I) (reduceDeps I))
          (PackageFormula.Reduction.embedPkg rootPkg) S ->
        IsResolution I
          (alpineResolution
            (PackageFormula.Reduction.packageFormulaResolution S)).
    Proof.
      intros I S Hwf H.
      exact (alpine_soundness I _ Hwf
               (PackageFormula.Reduction.package_formula_soundness _ _ _ S H)).
    Qed.

    Corollary alpine_core_completeness : forall I S,
        WfProvides I -> IsResolution I S ->
        PackageFormula.Reduction.Reduced.IsResolution
          (PackageFormula.Reduction.reduceReal (reduceReal I) (reduceDeps I))
          (PackageFormula.Reduction.reduceDeps (reduceReal I) (reduceDeps I))
          (PackageFormula.Reduction.embedPkg rootPkg)
          (PackageFormula.Reduction.coreResolution (reduceReal I) (reduceDeps I)
             (coreResolution I S)).
    Proof.
      intros I S Hwf H.
      exact (PackageFormula.package_formula_completeness _ _ _ _
               (alpine_completeness I S Hwf H)).
    Qed.

    Corollary alpine_core_retraction : forall I S,
        alpineResolution
          (PackageFormula.Reduction.packageFormulaResolution
             (PackageFormula.Reduction.coreResolution (reduceReal I)
               (reduceDeps I)
                (coreResolution I S)))
        = S.
    Proof.
      intros I S; rewrite PackageFormula.Reduction.package_formula_retraction.
      apply alpine_retraction.
    Qed.
  End ReductionUnder.

  Module Reduction := ReductionUnder LeastDesignation.
End Alpine.
