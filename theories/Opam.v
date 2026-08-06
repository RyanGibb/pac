From Stdlib Require Import MSets List Bool.
From PackageCalculus Require Import Prelude Core Versions VariableFormula.

Create HintDb cmp_opam.
Create Rewrite HintDb cmp_opam.

(* opam's dependency semantics at a fixed environment, translated into the
   variable-formula calculus: filters become variable-comparison atoms in
   the target formulas rather than being evaluated away as pre-processing,
   and the given valuation is pinned through the root's formula, so the
   target's solved-for assignment is forced to agree with it.  Variable
   names X are opam's qualified names (a package-local variable like
   with-test is the instance's p:with-test element of X); values live in
   one totally ordered sort Y, as opam itself compares them. *)
Module Opam (N V : UsualOrderedType) (X : FiniteUsualOrderedType)
    (Y E : UsualOrderedType).
  Module C := Core N V.
  Module Pkg := C.Pkg.
  Module PkgSet := C.PkgSet.
  Module VSet := C.VSet.
  Module Ver := Versions N V.

  Definition Valuation : Type := X.t -> option Y.t.

  (* Filters: variable-against-constant comparisons, definedness tests,
     literals, and connectives.  Variable-against-variable comparisons and
     version-valued variable constraints ({= ocaml:version}) are
     instance-level desugarings under a fixed environment, like string
     interpolation. *)
  Inductive Filter : Type :=
  | FlTrue
  | FlFalse
  | FlCmp (op : CmpOp) (x : X.t) (y : Y.t)
  | FlDef (x : X.t)
  | FlAnd (f g : Filter)
  | FlOr (f g : Filter)
  | FlNot (f : Filter).

  (* Kleene logic with absorption: undef & false = false, undef | true =
     true (the manual's stated rule). *)
  Definition andK (a b : option bool) : option bool :=
    match a, b with
    | Some false, _ => Some false
    | _, Some false => Some false
    | Some true, Some true => Some true
    | _, _ => None
    end.

  Definition orK (a b : option bool) : option bool :=
    match a, b with
    | Some true, _ => Some true
    | _, Some true => Some true
    | Some false, Some false => Some false
    | _, _ => None
    end.

  Definition notK (a : option bool) : option bool :=
    match a with
    | Some b => Some (negb b)
    | None => None
    end.

  Fixpoint evalF (rho : Valuation) (f : Filter) : option bool :=
    match f with
    | FlTrue => Some true
    | FlFalse => Some false
    | FlCmp op x y =>
        match rho x with
        | Some w => Some (cmpOpEvalBy Y.compare op w y)
        | None => None
        end
    | FlDef x =>
        Some (match rho x with Some _ => true | None => false end)
    | FlAnd f g => andK (evalF rho f) (evalF rho g)
    | FlOr f g => orK (evalF rho f) (evalF rho g)
    | FlNot f => notK (evalF rho f)
    end.

  (* A filter is "definitely true" when it evaluates to true; undefined
     defaults to false where a truth value is demanded (the manual's
     context-dependent default for dependency conditions). *)
  Definition defTrue (rho : Valuation) (f : Filter) : bool :=
    match evalF rho f with Some true => true | _ => false end.

  (* Version constraints: pure, variable-free (see the desugaring note on
     Filter). *)
  Inductive VConstraint : Type :=
  | VCTop
  | VCCmp (op : CmpOp) (c : V.t)
  | VCAnd (a b : VConstraint)
  | VCOr (a b : VConstraint)
  | VCNot (a : VConstraint).

  Fixpoint vcHolds (c : VConstraint) (v : V.t) : bool :=
    match c with
    | VCTop => true
    | VCCmp op c => Ver.cmpOpEval op v c
    | VCAnd a b => andb (vcHolds a v) (vcHolds b v)
    | VCOr a b => orb (vcHolds a v) (vcHolds b v)
    | VCNot a => negb (vcHolds a v)
    end.

  (* Filtered package formulas: an atom is a name with a filter and a
     version constraint; mixed brace formulas separate into this shape by
     distributing the atom (the same Empty-neutrality rules make the
     desugaring semantics-preserving). *)
  Inductive OFormula : Type :=
  | OFAtom (n : N.t) (g : Filter) (c : VConstraint)
  | OFAnd (a b : OFormula)
  | OFOr (a b : OFormula).

  Inductive RFormula : Type :=
  | RAtom (n : N.t) (c : VConstraint)
  | RAnd (a b : RFormula)
  | ROr (a b : RFormula).

  (* An atom whose filter is not definitely true is a context-dependent
     neutral element (opam's Empty): dropped from conjunctions and
     disjunctions alike, and a formula reducing entirely to Empty imposes
     nothing.  The manual only specifies the conjunction case; the
     disjunction behaviour follows the implementation's
     OpamFormula.Empty. *)
  Definition rMerge (mk : RFormula -> RFormula -> RFormula)
      (a b : option RFormula) : option RFormula :=
    match a, b with
    | None, b => b
    | a, None => a
    | Some a, Some b => Some (mk a b)
    end.

  Fixpoint redOF (rho : Valuation) (f : OFormula) : option RFormula :=
    match f with
    | OFAtom n g c =>
        if defTrue rho g then Some (RAtom n c) else None
    | OFAnd a b => rMerge RAnd (redOF rho a) (redOF rho b)
    | OFOr a b => rMerge ROr (redOF rho a) (redOF rho b)
    end.

  Fixpoint rSat (S : PkgSet.t) (f : RFormula) : Prop :=
    match f with
    | RAtom n c => exists v, PkgSet.In (n, v) S /\ vcHolds c v = true
    | RAnd a b => rSat S a /\ rSat S b
    | ROr a b => rSat S a \/ rSat S b
    end.

  Definition oSat (rho : Valuation) (S : PkgSet.t) (f : OFormula) : Prop :=
    forall g, redOF rho f = Some g -> rSat S g.

  Module ClsElt := PairUOT Pkg N.
  Module ClsRel := FSetUOT ClsElt.
  Module ESet := FSetUOT E.

  (* The opam instance.  Formula-valued rows are lists: they feed only the
     spec and the translation, and sets would demand formula comparators
     used nowhere.  inst_pins is switch-level (unconditional); pin-depends
     rows are conditional on their owner and carry the URL as an opaque
     value (fetch-time data, not resolution data).
     inst_dpo (depopts) carries no resolution force at all: the manual is
     explicit that a version-constrained depopt does not exclude other
     versions -- that is what conflicts are for -- so depopts are carried
     data gating build behaviour, represented but imposing nothing.
     inst_dxt (depexts) is likewise inert here: opam's solver never sees
     external dependencies, because an external name is a leaf that
     depends on nothing and so cannot decide between opam packages.  The
     rows are read off a finished resolution by depextsOf below, which is
     what the system package manager is then asked to install. *)
  Record Inst : Type := MkInst
    { inst_repo : PkgSet.t
    ; inst_dep : list (Pkg.t * OFormula)
    ; inst_dpo : list (Pkg.t * (N.t * (Filter * VConstraint)))
    ; inst_cfl : list (Pkg.t * (N.t * (Filter * VConstraint)))
    ; inst_cls : ClsRel.t
    ; inst_avl : list (Pkg.t * Filter)
    ; inst_dxt : list (Pkg.t * (E.t * Filter))
    ; inst_pins : PkgSet.t
    ; inst_pind : list (Pkg.t * (Pkg.t * Y.t))
    ; inst_goal : OFormula
    ; inst_inv : OFormula }.

  Definition availOK (rho : Valuation) (I : Inst) (p : Pkg.t) : Prop :=
    forall g, In (p, g) (inst_avl I) -> defTrue rho g = true.

  (* Conflicts and classes exempt the declarer's own name: opam encodes
     both into CUDF, whose conflicts never apply to the declaring package
     -- conflict-class is literally CUDF provides-plus-conflicts. *)
  Record IsResolution (rho : Valuation) (I : Inst) (S : PkgSet.t)
    : Prop := MkRes
    { ores_subset : PkgSet.Subset S (inst_repo I)
    ; ores_version_unique : C.VersionUnique S
    ; ores_available : forall p, PkgSet.In p S -> availOK rho I p
    ; ores_goal : oSat rho S (inst_goal I)
    ; ores_invariant : oSat rho S (inst_inv I)
    ; ores_dep_closure :
        forall p, PkgSet.In p S ->
        forall f, In (p, f) (inst_dep I) -> oSat rho S f
    ; ores_conflict_avoidance :
        forall p, PkgSet.In p S ->
        forall n g c, In (p, (n, (g, c))) (inst_cfl I) ->
          defTrue rho g = true ->
        forall v, PkgSet.In (n, v) S -> fst p <> n ->
          vcHolds c v = true -> False
    ; ores_class_exclusion :
        forall k p q, PkgSet.In p S -> PkgSet.In q S ->
          ClsRel.In (p, k) (inst_cls I) -> ClsRel.In (q, k) (inst_cls I) ->
          fst p <> fst q -> False
    ; ores_pins :
        forall n v, PkgSet.In (n, v) (inst_pins I) ->
        forall v', PkgSet.In (n, v') S -> v' = v
    ; ores_pin_depends :
        forall p, PkgSet.In p S ->
        forall n v u, In (p, ((n, v), u)) (inst_pind I) ->
        forall v', PkgSet.In (n, v') S -> v' = v }.

  (* The system packages a resolution asks for: an output read off S, not
     a constraint on it.  Every depext row owned by a selected package
     whose filter is definitely true contributes its external name. *)
  Definition depextsOf (rho : Valuation) (I : Inst) (S : PkgSet.t)
    : ESet.t :=
    List.fold_right
      (fun r acc =>
         if andb (PkgSet.mem (fst r) S) (defTrue rho (snd (snd r)))
         then ESet.add (fst (snd r)) acc
         else acc)
      ESet.empty (inst_dxt I).

  Lemma mem_depextsOf : forall rho I S e,
      ESet.In e (depextsOf rho I S) <->
      exists p g, PkgSet.In p S /\ In (p, (e, g)) (inst_dxt I) /\
                  defTrue rho g = true.
  Proof.
    intros rho I S e; unfold depextsOf.
    induction (inst_dxt I) as [| [p [e' g]] l IH]; cbn [List.fold_right fst snd].
    - split.
      + intro H; apply ESet.empty_spec in H; destruct H.
      + intros [q [g [_ [[] _]]]].
    - destruct (andb (PkgSet.mem p S) (defTrue rho g)) eqn:Hc.
      + rewrite ESet.add_spec, IH; split.
        * intros [-> | [q [g' [Hq [Hin Hg]]]]].
          -- apply Bool.andb_true_iff in Hc; destruct Hc as [Hm Hg].
             exists p, g; split;
               [apply PkgSet.mem_spec; exact Hm
               | split; [left; reflexivity | exact Hg]].
          -- exists q, g'; split;
               [exact Hq | split; [right; exact Hin | exact Hg]].
        * intros [q [g' [Hq [[Heq | Hin] Hg]]]].
          -- injection Heq as <- <- <-; left; reflexivity.
          -- right; exists q, g'; repeat split; assumption.
      + rewrite IH; split.
        * intros [q [g' [Hq [Hin Hg]]]].
          exists q, g'; split; [exact Hq | split; [right; exact Hin | exact Hg]].
        * intros [q [g' [Hq [[Heq | Hin] Hg]]]].
          -- injection Heq as <- <- <-.
             apply Bool.andb_false_iff in Hc; destruct Hc as [Hm | Hg'].
             ++ apply PkgSet.mem_spec in Hq; rewrite Hq in Hm; discriminate.
             ++ rewrite Hg in Hg'; discriminate.
          -- exists q, g'; repeat split; assumption.
  Qed.

  Module Reduction.
    Module NF := UOTCompareFacts N.
    Module VF' := UOTCompareFacts V.
    Module YF := UOTCompareFacts Y.
    #[local] Hint Rewrite NF.compare_eq_iff
      VF'.compare_eq_iff YF.compare_eq_iff : cmp_opam.
    #[local] Hint Extern 1 => cmp_by NF.compare_antisym : cmp_opam.
    #[local] Hint Extern 1 => cmp_by VF'.compare_antisym : cmp_opam.
    #[local] Hint Extern 1 => cmp_by YF.compare_antisym : cmp_opam.
    #[local] Hint Extern 1 => cmp_by NF.compare_lt_trans : cmp_opam.
    #[local] Hint Extern 1 => cmp_by VF'.compare_lt_trans : cmp_opam.
    #[local] Hint Extern 1 => cmp_by YF.compare_lt_trans : cmp_opam.

    (* Target names: a synthetic root carrying the request (opam has no
       root package -- the goal and switch invariant are formulas) and the
       real opam packages.  There is no name for a system package: a
       depext cannot decide between opam packages, so nothing external
       reaches the target. *)
    Module TName.
      Inductive name : Type :=
      | Root
      | Real (n : N.t).
      Definition t := name.

      Definition compare (x y : t) : comparison :=
        match x, y with
        | Root, Root => Eq
        | Root, _ => Lt
        | _, Root => Gt
        | Real n1, Real n2 => N.compare n1 n2
        end.

      Lemma compare_eq_iff : forall x y, compare x y = Eq <-> x = y.
      Proof. cmp_eq_iff cmp_opam. Qed.

      Lemma compare_antisym : forall x y,
          compare y x = CompOpp (compare x y).
      Proof. cmp_antisym cmp_opam. Qed.

      Lemma compare_lt_trans : forall x y z,
          compare x y = Lt -> compare y z = Lt -> compare x z = Lt.
      Proof. cmp_lt_trans cmp_opam. Qed.
    End TName.
    Module TNOT := UOTFromCompare TName.

    (* The root carries a unit version. *)
    Module TVer.
      Inductive version : Type :=
      | RV (v : V.t)
      | UnitV.
      Definition t := version.

      Definition compare (x y : t) : comparison :=
        match x, y with
        | RV v1, RV v2 => V.compare v1 v2
        | RV _, UnitV => Lt
        | UnitV, RV _ => Gt
        | UnitV, UnitV => Eq
        end.

      Lemma compare_eq_iff : forall x y, compare x y = Eq <-> x = y.
      Proof. cmp_eq_iff cmp_opam. Qed.

      Lemma compare_antisym : forall x y,
          compare y x = CompOpp (compare x y).
      Proof. cmp_antisym cmp_opam. Qed.

      Lemma compare_lt_trans : forall x y z,
          compare x y = Lt -> compare y z = Lt -> compare x z = Lt.
      Proof. cmp_lt_trans cmp_opam. Qed.
    End TVer.
    Module TVOT := UOTFromCompare TVer.

    (* Target values: Y extended with a distinguished undefined element,
       so an unbound variable is pinned to a value and definedness tests
       become ordinary comparisons. *)
    Module YU.
      Inductive yval : Type :=
      | Undef
      | YVal (y : Y.t).
      Definition t := yval.

      Definition compare (x y : t) : comparison :=
        match x, y with
        | Undef, Undef => Eq
        | Undef, YVal _ => Lt
        | YVal _, Undef => Gt
        | YVal a, YVal b => Y.compare a b
        end.

      Lemma compare_eq_iff : forall x y, compare x y = Eq <-> x = y.
      Proof. cmp_eq_iff cmp_opam. Qed.

      Lemma compare_antisym : forall x y,
          compare y x = CompOpp (compare x y).
      Proof. cmp_antisym cmp_opam. Qed.

      Lemma compare_lt_trans : forall x y z,
          compare x y = Lt -> compare y z = Lt -> compare x z = Lt.
      Proof. cmp_lt_trans cmp_opam. Qed.
    End YU.
    Module YUOT := UOTFromCompare YU.
    Module YUF := UOTCompareFacts YUOT.

    Module VF := VariableFormula TNOT TVOT X YUOT.

    Definition pin (rho : Valuation) (x : X.t) : YUOT.t :=
      match rho x with
      | Some y => YU.YVal y
      | None => YU.Undef
      end.

    Definition embedPkg (p : Pkg.t) : VF.Pkg.t :=
      (TName.Real (fst p), TVer.RV (snd p)).
    Definition rootPkg : VF.Pkg.t := (TName.Root, TVer.UnitV).

    Module SOpt := SetOps Pkg VF.Pkg PkgSet VF.PkgSet.
    Definition embedSet (S : PkgSet.t) : VF.PkgSet.t :=
      SOpt.map embedPkg S.

    Module SOvv := SetOps V TVOT VSet VF.VSet.
    Module SOpv := SetOps Pkg V PkgSet VSet.
    Definition realVersions (R : PkgSet.t) (n : N.t) : VSet.t :=
      SOpv.filterMap
        (fun '(m, v) => if N.eq_dec m n then Some v else None) R.

    (* The effective repository: switch pins and availability filters are
       unconditional cuts of R, applied before anything else -- pins and
       availability cut repository membership, not formulas. *)
    Definition pinOKb (Pins : PkgSet.t) (p : Pkg.t) : bool :=
      PkgSet.for_all
        (fun '(m, w) =>
           if N.eq_dec m (fst p)
           then if V.eq_dec w (snd p) then true else false
           else true)
        Pins.

    Definition availb (rho : Valuation) (avl : list (Pkg.t * Filter))
        (p : Pkg.t) : bool :=
      forallb
        (fun '(q, g) => if Pkg.eq_dec q p then defTrue rho g else true)
        avl.

    Definition effRepo (rho : Valuation) (I : Inst) : PkgSet.t :=
      PkgSet.filter
        (fun p => andb (pinOKb (inst_pins I) p) (availb rho (inst_avl I) p))
        (inst_repo I).

    (* VF.Formula has no truth constant; an unsatisfiable dependency on
       the root name provides one. *)
    Definition PFalse : VF.Formula := VF.FDep TName.Root VF.VSet.empty.
    Definition PTrue : VF.Formula := VF.FNeg PFalse.

    (* Filters become variable-comparison formulas: the two-sided Kleene
       encoding (definitely-true and definitely-false halves) is exact --
       negation swaps the halves, so undefined never collapses under a
       negation the way a one-sided defaulting encoding would. *)
    Fixpoint fT (rho : Valuation) (f : Filter) : VF.Formula :=
      match f with
      | FlTrue => PTrue
      | FlFalse => PFalse
      | FlCmp op x y =>
          VF.FConj (VF.FVarCmp x OpNe YU.Undef)
            (VF.FVarCmp x op (YU.YVal y))
      | FlDef x => VF.FVarCmp x OpNe YU.Undef
      | FlAnd f g => VF.FConj (fT rho f) (fT rho g)
      | FlOr f g => VF.FDisj (fT rho f) (fT rho g)
      | FlNot f => fF rho f
      end
    with fF (rho : Valuation) (f : Filter) : VF.Formula :=
      match f with
      | FlTrue => PFalse
      | FlFalse => PTrue
      | FlCmp op x y =>
          VF.FConj (VF.FVarCmp x OpNe YU.Undef)
            (VF.FVarCmp x (cmpComplement op) (YU.YVal y))
      | FlDef x => VF.FVarCmp x OpEq YU.Undef
      | FlAnd f g => VF.FDisj (fF rho f) (fF rho g)
      | FlOr f g => VF.FConj (fF rho f) (fF rho g)
      | FlNot f => fT rho f
      end.

    (* -- lookup-primary layer: the per-name and per-package queries are
       the definitions; the global translation is their aggregation,
       defined after them. -- *)

    (* The versions of a source name available under rho: repository
       versions with availability and switch pins folded in. *)
    Definition srcVersions (rho : Valuation) (I : Inst) (n : N.t)
      : VSet.t :=
      realVersions (effRepo rho I) n.

    (* Encoders consult versions only through an oracle Vq, so slice
       reuse is oracle agreement (the lookup lemmas below). *)
    Definition versSetBy (Vq : N.t -> VSet.t) (n : N.t) (c : VConstraint)
      : VF.VSet.t :=
      SOvv.map TVer.RV (VSet.filter (fun v => vcHolds c v) (Vq n)).

    (* The Empty-neutrality of dropped atoms, lifted into the target: D
       holds when the sub-formula reduces to Empty, S when it reduces to
       something the resolution satisfies.  A conjunction is present when
       either side is, so S also asserts not-both-dropped. *)
    Fixpoint fD (rho : Valuation) (f : OFormula) : VF.Formula :=
      match f with
      | OFAtom _ g _ => VF.FNeg (fT rho g)
      | OFAnd a b => VF.FConj (fD rho a) (fD rho b)
      | OFOr a b => VF.FConj (fD rho a) (fD rho b)
      end.

    Fixpoint fS (rho : Valuation) (Vq : N.t -> VSet.t) (f : OFormula)
      : VF.Formula :=
      match f with
      | OFAtom n g c =>
          VF.FConj (fT rho g) (VF.FDep (TName.Real n) (versSetBy Vq n c))
      | OFAnd a b =>
          VF.FConj
            (VF.FConj (VF.FDisj (fD rho a) (fS rho Vq a))
               (VF.FDisj (fD rho b) (fS rho Vq b)))
            (VF.FNeg (VF.FConj (fD rho a) (fD rho b)))
      | OFOr a b => VF.FDisj (fS rho Vq a) (fS rho Vq b)
      end.

    Definition encodeOF (rho : Valuation) (Vq : N.t -> VSet.t)
        (f : OFormula) : VF.Formula :=
      VF.FDisj (fD rho f) (fS rho Vq f).

    (* The versions a conflict atom forbids; the declarer's own name is
       exempt (CUDF conflicts never apply to their declarer). *)
    Definition confVS (Vq : N.t -> VSet.t) (p : Pkg.t) (n : N.t)
        (c : VConstraint) : VF.VSet.t :=
      if N.eq_dec (fst p) n then VF.VSet.empty else versSetBy Vq n c.

    Definition memberAtom (q : Pkg.t) : VF.Formula :=
      VF.FDep (TName.Real (fst q))
        (VF.VSet.singleton (TVer.RV (snd q))).

    Module FSet := FSetUOT VF.Dependees.
    Module NSet := FSetUOT N.

    Definition ownb {A : Type} (p : Pkg.t) (r : Pkg.t * A) : bool :=
      if Pkg.eq_dec (fst r) p then true else false.

    Definition ownRows {A : Type} (p : Pkg.t) (l : list (Pkg.t * A))
      : list A :=
      List.map snd (List.filter (ownb p) l).

    Definition depForms (rho : Valuation) (Vq : N.t -> VSet.t) (I : Inst)
        (p : Pkg.t) : list VF.Formula :=
      List.map (encodeOF rho Vq) (ownRows p (inst_dep I)).

    Definition cflForm (rho : Valuation) (Vq : N.t -> VSet.t) (p : Pkg.t)
        (nc : N.t * (Filter * VConstraint)) : VF.Formula :=
      VF.FNeg
        (VF.FConj (fT rho (fst (snd nc)))
           (VF.FDep (TName.Real (fst nc))
              (confVS Vq p (fst nc) (snd (snd nc))))).

    Definition cflForms (rho : Valuation) (Vq : N.t -> VSet.t) (I : Inst)
        (p : Pkg.t) : list VF.Formula :=
      List.map (cflForm rho Vq p) (ownRows p (inst_cfl I)).

    (* Conflict classes as pairwise prohibitions: p forbids every
       same-class partner with a different name. *)
    Module SOcf := SetOps ClsElt VF.Dependees ClsRel FSet.
    Definition clsForms (cls : ClsRel.t) (p : Pkg.t) : FSet.t :=
      SOcf.filterMap
        (fun '(q, k) =>
           if ClsRel.mem (p, k) cls
           then
             if N.eq_dec (fst q) (fst p) then None
             else Some (VF.FNeg (memberAtom q))
           else None)
        cls.

    Definition pindForm (Vq : N.t -> VSet.t) (nvu : Pkg.t * Y.t)
      : VF.Formula :=
      VF.FNeg
        (VF.FDep (TName.Real (fst (fst nvu)))
           (SOvv.map TVer.RV
              (VSet.remove (snd (fst nvu)) (Vq (fst (fst nvu)))))).

    Definition pindForms (Vq : N.t -> VSet.t) (I : Inst) (p : Pkg.t)
      : list VF.Formula :=
      List.map (pindForm Vq) (ownRows p (inst_pind I)).

    (* The given environment, pinned through the root: closure at the root
       forces the solved-for assignment to agree with rho pointwise.  This
       conjunction is the only place rho reaches the target, so widening
       an instance to genuinely solve for variables (the paper's freedom)
       is a matter of weakening it. *)
    Definition pinsFormula (rho : Valuation) : VF.Formula :=
      List.fold_right
        (fun x acc => VF.FConj (VF.FVarCmp x OpEq (pin rho x)) acc)
        PTrue X.enum.

    Definition rootForm (rho : Valuation) (Vq : N.t -> VSet.t) (I : Inst)
      : VF.Formula :=
      VF.FConj (pinsFormula rho)
        (VF.FConj (encodeOF rho Vq (inst_goal I))
           (encodeOF rho Vq (inst_inv I))).

    Module SOlf := SetOps Pkg VF.Dependees PkgSet FSet.

    (* THE per-package lookup: a target package's formulas, from its own
       instance rows under the valuation. *)
    Definition dependeesBy (rho : Valuation) (Vq : N.t -> VSet.t)
        (I : Inst) (q : VF.Pkg.t) : FSet.t :=
      match q with
      | (TName.Real n, TVer.RV v) =>
          FSet.union (SOlf.ofList (depForms rho Vq I (n, v)))
            (FSet.union (SOlf.ofList (cflForms rho Vq I (n, v)))
               (FSet.union (clsForms (inst_cls I) (n, v))
                  (SOlf.ofList (pindForms Vq I (n, v)))))
      | (TName.Root, TVer.UnitV) => FSet.singleton (rootForm rho Vq I)
      | _ => FSet.empty
      end.

    Definition dependees (rho : Valuation) (I : Inst) (q : VF.Pkg.t)
      : FSet.t :=
      dependeesBy rho (srcVersions rho I) I q.

    (* The per-target-name version lookup. *)
    Definition versions (rho : Valuation) (I : Inst) (tn : TName.t)
      : VF.VSet.t :=
      match tn with
      | TName.Root => VF.VSet.singleton TVer.UnitV
      | TName.Real n => SOvv.map TVer.RV (srcVersions rho I n)
      end.

    (* -- derived aggregation: the global translation -- *)

    Definition transR (rho : Valuation) (I : Inst) : VF.PkgSet.t :=
      VF.PkgSet.union (embedSet (effRepo rho I))
        (VF.PkgSet.singleton rootPkg).

    Module SOfd := SetOps VF.Dependees VF.DepElt FSet VF.DepRel.
    Definition depEdges (q : VF.Pkg.t) (fs : FSet.t) : VF.DepRel.t :=
      SOfd.map (fun f => (q, f)) fs.

    Module SOqd := SetOps VF.Pkg VF.DepElt VF.PkgSet VF.DepRel.
    Definition transD (rho : Valuation) (I : Inst) : VF.DepRel.t :=
      SOqd.unionMap (fun q => depEdges q (dependees rho I q))
        (transR rho I).

    Definition transS (S : PkgSet.t) : VF.PkgSet.t :=
      VF.PkgSet.union (embedSet S) (VF.PkgSet.singleton rootPkg).

    Module SOtp := SetOps VF.Pkg Pkg VF.PkgSet PkgSet.
    Definition tryInvPkg (q : VF.Pkg.t) : option Pkg.t :=
      match q with
      | (TName.Real n, TVer.RV v) => Some (n, v)
      | _ => None
      end.

    Definition decodeS (S' : VF.PkgSet.t) : PkgSet.t :=
      SOtp.filterMap tryInvPkg S'.
    Lemma embedPkg_inj : forall p q, embedPkg p = embedPkg q -> p = q.
    Proof.
      intros [n v] [m w] H; unfold embedPkg in H; simpl in H.
      injection H as -> ->; reflexivity.
    Qed.

    Lemma mem_realVersions : forall R n v,
        VSet.In v (realVersions R n) <-> PkgSet.In (n, v) R.
    Proof.
      intros R n v; unfold realVersions; rewrite SOpv.mem_filterMap.
      split.
      - intros [[m w] [Hm Hf]]; destruct (N.eq_dec m n) as [-> |];
          [injection Hf as -> | discriminate].
        exact Hm.
      - intro H; exists (n, v); split; [exact H |].
        destruct (N.eq_dec n n) as [_ | NE];
          [reflexivity | contradiction NE; reflexivity].
    Qed.

    Lemma mem_versSetBy : forall Vq n c tv,
        VF.VSet.In tv (versSetBy Vq n c) <->
        exists v, tv = TVer.RV v /\ VSet.In v (Vq n) /\
                  vcHolds c v = true.
    Proof.
      intros Vq n c tv; unfold versSetBy; rewrite SOvv.mem_map.
      split.
      - intros [v [Hv ->]]; apply VSet.filter_spec' in Hv;
          destruct Hv as [Hv Hh].
        exists v; split; [reflexivity | split; [exact Hv | exact Hh]].
      - intros [v [-> [Hm Hh]]]; exists v; split; [| reflexivity].
        apply VSet.filter_spec'; split; [exact Hm | exact Hh].
    Qed.

    Lemma mem_srcVersions : forall rho I n v,
        VSet.In v (srcVersions rho I n) <->
        PkgSet.In (n, v) (effRepo rho I).
    Proof. intros; unfold srcVersions; apply mem_realVersions. Qed.

    Lemma mem_decodeS : forall S' n v,
        PkgSet.In (n, v) (decodeS S') <->
        VF.PkgSet.In (TName.Real n, TVer.RV v) S'.
    Proof.
      intros S' n v; unfold decodeS; rewrite SOtp.mem_filterMap.
      split.
      - intros [[tn tv] [Hm Hf]];
          destruct tn as [| m]; destruct tv as [w |];
          simpl in Hf; try discriminate.
        injection Hf as -> ->; exact Hm.
      - intro H; exists (TName.Real n, TVer.RV v); split;
          [exact H | reflexivity].
    Qed.

    Definition PinOK (Pins : PkgSet.t) (p : Pkg.t) : Prop :=
      forall m w, PkgSet.In (m, w) Pins -> m = fst p -> w = snd p.

    Lemma mem_effRepo : forall rho I p,
        PkgSet.In p (effRepo rho I) <->
        PkgSet.In p (inst_repo I) /\ PinOK (inst_pins I) p /\
        availOK rho I p.
    Proof.
      intros rho I p; unfold effRepo; rewrite PkgSet.filter_spec'.
      rewrite Bool.andb_true_iff; unfold pinOKb, availb.
      rewrite PkgSet.for_all_spec'.
      split.
      - intros [Hr [Hpin Hav]]; split; [exact Hr |]; split.
        + intros m w Hm Hn.
          specialize (Hpin _ Hm); simpl in Hpin.
          destruct (N.eq_dec m (fst p)) as [_ | NE];
            [| contradiction NE].
          destruct (V.eq_dec w (snd p)) as [E | _];
            [exact E | discriminate].
        + intros g Hg.
          rewrite List.forallb_forall in Hav.
          specialize (Hav _ Hg); simpl in Hav.
          destruct (Pkg.eq_dec p p) as [_ | NE];
            [exact Hav | contradiction NE; reflexivity].
      - intros [Hr [Hpin Hav]]; split; [exact Hr |]; split.
        + intros [m w] Hm; simpl.
          destruct (N.eq_dec m (fst p)) as [E | _]; [| reflexivity].
          destruct (V.eq_dec w (snd p)) as [_ | NE]; [reflexivity |].
          contradiction NE; exact (Hpin _ _ Hm E).
        + rewrite List.forallb_forall; intros [q g] Hg; simpl.
          destruct (Pkg.eq_dec q p) as [-> |]; [| reflexivity].
          exact (Hav _ Hg).
    Qed.

    Lemma mem_transR : forall rho I q,
        VF.PkgSet.In q (transR rho I) <->
        (exists p, PkgSet.In p (effRepo rho I) /\ q = embedPkg p) \/
        q = rootPkg.
    Proof.
      intros rho I q; unfold transR, embedSet.
      rewrite VF.PkgSet.union_spec, VF.PkgSet.singleton_spec,
        SOpt.mem_map.
      tauto.
    Qed.

    Lemma mem_transS : forall S q,
        VF.PkgSet.In q (transS S) <->
        (exists p, PkgSet.In p S /\ q = embedPkg p) \/ q = rootPkg.
    Proof.
      intros S q; unfold transS, embedSet.
      rewrite VF.PkgSet.union_spec, VF.PkgSet.singleton_spec,
        SOpt.mem_map.
      tauto.
    Qed.

    Lemma mem_transS_real : forall S n v,
        VF.PkgSet.In (TName.Real n, TVer.RV v) (transS S) <->
        PkgSet.In (n, v) S.
    Proof.
      intros S n v; rewrite mem_transS; split.
      - intros [[p [Hp He]] | He]; [| discriminate].
        destruct p as [m w]; unfold embedPkg in He; simpl in He.
        injection He as -> ->; exact Hp.
      - intro H; left; exists (n, v); split; [exact H | reflexivity].
    Qed.

    Lemma decode_transS : forall S, decodeS (transS S) = S.
    Proof.
      intros S; apply PkgSet.ext; intros [n v].
      rewrite mem_decodeS, mem_transS_real; reflexivity.
    Qed.

    Lemma PTrue_sat : forall S' sigma, VF.Satisfies S' sigma PTrue.
    Proof.
      intros S' sigma; simpl; intros [tv [Htv _]].
      destruct (VF.VSet.empty_spec Htv).
    Qed.

    Lemma PFalse_unsat : forall S' sigma,
        ~ VF.Satisfies S' sigma PFalse.
    Proof.
      intros S' sigma [tv [Htv _]].
      destruct (VF.VSet.empty_spec Htv).
    Qed.

    Lemma andK_true_iff : forall a b,
        andK a b = Some true <-> a = Some true /\ b = Some true.
    Proof. intros [[|]|] [[|]|]; simpl; intuition congruence. Qed.

    Lemma andK_false_iff : forall a b,
        andK a b = Some false <-> a = Some false \/ b = Some false.
    Proof. intros [[|]|] [[|]|]; simpl; intuition congruence. Qed.

    Lemma orK_true_iff : forall a b,
        orK a b = Some true <-> a = Some true \/ b = Some true.
    Proof. intros [[|]|] [[|]|]; simpl; intuition congruence. Qed.

    Lemma orK_false_iff : forall a b,
        orK a b = Some false <-> a = Some false /\ b = Some false.
    Proof. intros [[|]|] [[|]|]; simpl; intuition congruence. Qed.

    Lemma notK_true_iff : forall a,
        notK a = Some true <-> a = Some false.
    Proof. intros [[|]|]; simpl; intuition congruence. Qed.

    Lemma notK_false_iff : forall a,
        notK a = Some false <-> a = Some true.
    Proof. intros [[|]|]; simpl; intuition congruence. Qed.

    Lemma opEvalY_vals : forall op w y,
        VF.opEvalY op (YU.YVal w) (YU.YVal y) =
        cmpOpEvalBy Y.compare op w y.
    Proof. intros [ | | | | | ] w y; reflexivity. Qed.

    Lemma opEvalY_ne_undef : forall a,
        VF.opEvalY OpNe a YU.Undef = true <-> a <> YU.Undef.
    Proof.
      intros [| y]; simpl; split; intro H;
        try discriminate; try reflexivity;
        try (contradiction H; reflexivity); congruence.
    Qed.

    Lemma opEqY_iff : forall a b, VF.opEvalY OpEq a b = true <-> a = b.
    Proof.
      intros a b; split.
      - intro H; apply YU.compare_eq_iff.
        destruct (YU.compare a b) eqn:C; [reflexivity | |];
          exfalso; revert H;
          change (VF.opEvalY OpEq a b) with
            (match YU.compare a b with Eq => true | _ => false end);
          rewrite C; discriminate.
      - intro H; subst b.
        change (match YU.compare a a with Eq => true | _ => false end
                = true).
        rewrite (proj2 (YU.compare_eq_iff a a) eq_refl); reflexivity.
    Qed.

    Lemma defTrue_iff : forall rho g,
        defTrue rho g = true <-> evalF rho g = Some true.
    Proof.
      intros rho g; unfold defTrue.
      destruct (evalF rho g) as [[|]|]; intuition congruence.
    Qed.

    Lemma TF_correct : forall rho S' sigma,
        (forall x, sigma x = pin rho x) ->
        forall f,
          (VF.Satisfies S' sigma (fT rho f) <->
           evalF rho f = Some true) /\
          (VF.Satisfies S' sigma (fF rho f) <->
           evalF rho f = Some false).
    Proof.
      intros rho S' sigma Hsig.
      induction f as [| | op x y | x | a IHa b IHb | a IHa b IHb
                      | a IHa]; simpl.
      - split; [split | split].
        + intros _; reflexivity.
        + intros _; exact (PTrue_sat S' sigma).
        + intro H; destruct (PFalse_unsat S' sigma H).
        + intro H; discriminate H.
      - split; [split | split].
        + intro H; destruct (PFalse_unsat S' sigma H).
        + intro H; discriminate H.
        + intros _; reflexivity.
        + intros _; exact (PTrue_sat S' sigma).
      - rewrite !Hsig; unfold pin; destruct (rho x) as [w |].
        + split; split.
          * intros [_ Hc]; rewrite opEvalY_vals in Hc.
            rewrite Hc; reflexivity.
          * intro H; injection H as H; split;
              [apply opEvalY_ne_undef; discriminate
              | rewrite opEvalY_vals, H; reflexivity].
          * intros [_ Hc]; rewrite opEvalY_vals in Hc.
            rewrite cmpOpEvalBy_complement in Hc.
            apply Bool.negb_true_iff in Hc; rewrite Hc; reflexivity.
          * intro H; injection H as H; split;
              [apply opEvalY_ne_undef; discriminate |].
            rewrite opEvalY_vals, cmpOpEvalBy_complement, H;
              reflexivity.
        + split; split.
          * intros [Hd _]; apply opEvalY_ne_undef in Hd.
            contradiction Hd; reflexivity.
          * discriminate.
          * intros [Hd _]; apply opEvalY_ne_undef in Hd.
            contradiction Hd; reflexivity.
          * discriminate.
      - rewrite !Hsig; unfold pin; destruct (rho x) as [w |].
        + split; split.
          * intros _; reflexivity.
          * intros _; apply opEvalY_ne_undef; discriminate.
          * intro H; apply opEqY_iff in H; discriminate.
          * discriminate.
        + split; split.
          * intro H; apply opEvalY_ne_undef in H.
            contradiction H; reflexivity.
          * discriminate.
          * intros _; reflexivity.
          * intros _; apply opEqY_iff; reflexivity.
      - destruct IHa as [IHaT IHaF]; destruct IHb as [IHbT IHbF].
        split.
        + rewrite andK_true_iff; simpl; rewrite IHaT, IHbT; tauto.
        + rewrite andK_false_iff; simpl; rewrite IHaF, IHbF; tauto.
      - destruct IHa as [IHaT IHaF]; destruct IHb as [IHbT IHbF].
        split.
        + rewrite orK_true_iff; simpl; rewrite IHaT, IHbT; tauto.
        + rewrite orK_false_iff; simpl; rewrite IHaF, IHbF; tauto.
      - destruct IHa as [IHaT IHaF].
        split; [rewrite notK_true_iff | rewrite notK_false_iff];
          tauto.
    Qed.

    Lemma fD_correct : forall rho S' sigma,
        (forall x, sigma x = pin rho x) ->
        forall f,
          VF.Satisfies S' sigma (fD rho f) <-> redOF rho f = None.
    Proof.
      intros rho S' sigma Hsig.
      induction f as [n g c | a IHa b IHb | a IHa b IHb]; simpl.
      - destruct (TF_correct rho S' sigma Hsig g) as [HT _].
        destruct (defTrue rho g) eqn:Hg.
        + apply defTrue_iff in Hg; split;
            [intro H; contradiction (H (proj2 HT Hg)) | discriminate].
        + split; [intros _; reflexivity |].
          intros _ Hs; apply HT in Hs.
          apply defTrue_iff in Hs; rewrite Hs in Hg; discriminate.
      - rewrite IHa, IHb.
        destruct (redOF rho a); destruct (redOF rho b); simpl;
          intuition congruence.
      - rewrite IHa, IHb.
        destruct (redOF rho a); destruct (redOF rho b); simpl;
          intuition congruence.
    Qed.

    Lemma fS_absent : forall rho Vq S' sigma,
        (forall x, sigma x = pin rho x) ->
        forall f, redOF rho f = None ->
          ~ VF.Satisfies S' sigma (fS rho Vq f).
    Proof.
      intros rho Vq S' sigma Hsig.
      induction f as [n g c | a IHa b IHb | a IHa b IHb]; simpl.
      - destruct (defTrue rho g) eqn:Hg; [discriminate |].
        intros _ [HT _].
        destruct (TF_correct rho S' sigma Hsig g) as [HTi _].
        apply HTi in HT; apply defTrue_iff in HT.
        rewrite HT in Hg; discriminate.
      - intro H.
        destruct (redOF rho a) eqn:Ha; destruct (redOF rho b) eqn:Hb;
          simpl in H; try discriminate.
        intros [_ Hne]; apply Hne; split;
          apply (fD_correct rho S' sigma Hsig); assumption.
      - intro H.
        destruct (redOF rho a) eqn:Ha; destruct (redOF rho b) eqn:Hb;
          simpl in H; try discriminate.
        intros [Hs | Hs];
          [exact (IHa eq_refl Hs) | exact (IHb eq_refl Hs)].
    Qed.

    Lemma fS_correct : forall rho Vq S' sigma,
        (forall x, sigma x = pin rho x) ->
        (forall n v, PkgSet.In (n, v) (decodeS S') ->
                     VSet.In v (Vq n)) ->
        forall f g, redOF rho f = Some g ->
          (VF.Satisfies S' sigma (fS rho Vq f) <->
           rSat (decodeS S') g).
    Proof.
      intros rho Vq S' sigma Hsig HV.
      induction f as [n g0 c | a IHa b IHb | a IHa b IHb];
        intros g Hred; simpl in Hred; simpl.
      - destruct (defTrue rho g0) eqn:Hg; [| discriminate].
        injection Hred as <-; simpl.
        destruct (TF_correct rho S' sigma Hsig g0) as [HT _].
        apply defTrue_iff in Hg.
        split.
        + intros [_ [tv [Htv Hm]]].
          apply mem_versSetBy in Htv;
            destruct Htv as [v [-> [Hra Hh]]].
          exists v; split; [apply mem_decodeS; exact Hm | exact Hh].
        + intros [v [Hv Hh]]; split; [apply HT; exact Hg |].
          assert (Hvq := HV _ _ Hv).
          apply mem_decodeS in Hv.
          exists (TVer.RV v); split; [| exact Hv].
          apply mem_versSetBy; exists v; split;
            [reflexivity | split; [exact Hvq | exact Hh]].
      - destruct (redOF rho a) eqn:Ha; destruct (redOF rho b) eqn:Hb;
          simpl in Hred; try discriminate; injection Hred as <-;
          simpl.
        + assert (Da : ~ VF.Satisfies S' sigma (fD rho a)).
          { intro H; apply (fD_correct rho S' sigma Hsig) in H;
              congruence. }
          assert (Db : ~ VF.Satisfies S' sigma (fD rho b)).
          { intro H; apply (fD_correct rho S' sigma Hsig) in H;
              congruence. }
          rewrite <- (IHa _ eq_refl), <- (IHb _ eq_refl).
          split.
          * intros [[[Hda | Hsa] [Hdb | Hsb]] _];
              try contradiction; split; assumption.
          * intros [Hsa Hsb]; split;
              [split; right; assumption
              | intros [Hda _]; exact (Da Hda)].
        + assert (Da : ~ VF.Satisfies S' sigma (fD rho a)).
          { intro H; apply (fD_correct rho S' sigma Hsig) in H;
              congruence. }
          rewrite <- (IHa _ eq_refl).
          split.
          * intros [[[Hda | Hsa] _] _]; [contradiction | exact Hsa].
          * intro Hsa; split;
              [split;
                [right; exact Hsa
                | left; apply (fD_correct rho S' sigma Hsig);
                  exact Hb]
              | intros [Hda _]; exact (Da Hda)].
        + assert (Db : ~ VF.Satisfies S' sigma (fD rho b)).
          { intro H; apply (fD_correct rho S' sigma Hsig) in H;
              congruence. }
          rewrite <- (IHb _ eq_refl).
          split.
          * intros [[_ [Hdb | Hsb]] _]; [contradiction | exact Hsb].
          * intro Hsb; split;
              [split;
                [left; apply (fD_correct rho S' sigma Hsig); exact Ha
                | right; exact Hsb]
              | intros [_ Hdb]; exact (Db Hdb)].
      - destruct (redOF rho a) eqn:Ha; destruct (redOF rho b) eqn:Hb;
          simpl in Hred; try discriminate; injection Hred as <-;
          simpl.
        + rewrite <- (IHa _ eq_refl), <- (IHb _ eq_refl); tauto.
        + rewrite <- (IHa _ eq_refl).
          split; [| intro H; left; exact H].
          intros [H | H]; [exact H |].
          destruct (fS_absent rho Vq S' sigma Hsig b Hb H).
        + rewrite <- (IHb _ eq_refl).
          split; [| intro H; right; exact H].
          intros [H | H]; [| exact H].
          destruct (fS_absent rho Vq S' sigma Hsig a Ha H).
    Qed.

    Lemma encodeOF_correct : forall rho Vq S' sigma,
        (forall x, sigma x = pin rho x) ->
        (forall n v, PkgSet.In (n, v) (decodeS S') ->
                     VSet.In v (Vq n)) ->
        forall f,
          (VF.Satisfies S' sigma (encodeOF rho Vq f) <->
           oSat rho (decodeS S') f).
    Proof.
      intros rho Vq S' sigma Hsig HV f; unfold encodeOF, oSat; simpl.
      destruct (redOF rho f) as [g |] eqn:Hred.
      - split.
        + intros [Hd | Hs] g' Hg'; injection Hg' as <-.
          * apply (fD_correct rho S' sigma Hsig) in Hd; congruence.
          * apply (fS_correct rho Vq S' sigma Hsig HV _ _ Hred);
              exact Hs.
        + intro H; right.
          apply (fS_correct rho Vq S' sigma Hsig HV _ _ Hred).
          apply H; reflexivity.
      - split.
        + intros _ g' Hg'; discriminate.
        + intros _; left.
          apply (fD_correct rho S' sigma Hsig); exact Hred.
    Qed.

    Lemma pins_aux : forall rho S' sigma l,
        VF.Satisfies S' sigma
          (List.fold_right
             (fun x acc => VF.FConj (VF.FVarCmp x OpEq (pin rho x)) acc)
             PTrue l) <->
        (forall x, In x l -> sigma x = pin rho x).
    Proof.
      intros rho S' sigma; induction l as [| x l IH]; simpl.
      - split; [intros _ x [] | intros _; exact (PTrue_sat S' sigma)].
      - rewrite IH; split.
        + intros [Hx Hl] x' [-> | Hin];
            [apply opEqY_iff; exact Hx | exact (Hl _ Hin)].
        + intro H; split;
            [apply opEqY_iff; apply H; left; reflexivity
            | intros x' Hin; apply H; right; exact Hin].
    Qed.

    Lemma pins_pin : forall rho S' sigma,
        VF.Satisfies S' sigma (pinsFormula rho) <->
        (forall x, sigma x = pin rho x).
    Proof.
      intros rho S' sigma; unfold pinsFormula; rewrite pins_aux.
      split; [intros H x; apply H, X.enum_complete | auto].
    Qed.

    Lemma ownRows_in : forall (A : Type) (p : Pkg.t)
        (l : list (Pkg.t * A)) (a : A),
        In a (ownRows p l) <-> In (p, a) l.
    Proof.
      intros A p l a; unfold ownRows, ownb.
      rewrite List.in_map_iff; split.
      - intros [[q b] [Hb Hf]]; simpl in Hb; subst b.
        apply List.filter_In in Hf; destruct Hf as [Hin Ht];
          simpl in Ht.
        destruct (Pkg.eq_dec q p) as [-> |]; [exact Hin | discriminate].
      - intro H; exists (p, a); split; [reflexivity |].
        apply List.filter_In; split; [exact H | simpl].
        destruct (Pkg.eq_dec p p) as [_ | NE];
          [reflexivity | contradiction NE; reflexivity].
    Qed.

    Lemma mem_dependees_real : forall rho Vq I n v f,
        FSet.In f (dependeesBy rho Vq I (TName.Real n, TVer.RV v)) <->
        (exists f0, In ((n, v), f0) (inst_dep I) /\
                    f = encodeOF rho Vq f0) \/
        (exists nc, In ((n, v), nc) (inst_cfl I) /\
                    f = cflForm rho Vq (n, v) nc) \/
        (exists q k, ClsRel.In ((n, v), k) (inst_cls I) /\
                     ClsRel.In (q, k) (inst_cls I) /\ fst q <> n /\
                     f = VF.FNeg (memberAtom q)) \/
        (exists nvu, In ((n, v), nvu) (inst_pind I) /\
                     f = pindForm Vq nvu).
    Proof.
      intros rho Vq I n v f; simpl.
      rewrite !FSet.union_spec, !SOlf.mem_ofList.
      unfold depForms, cflForms, pindForms.
      rewrite !List.in_map_iff.
      unfold clsForms; rewrite SOcf.mem_filterMap.
      split.
      - intros [H | [H | [H | H]]].
        + destruct H as [f0 [He Hf0]]; apply ownRows_in in Hf0.
          left; exists f0; auto.
        + destruct H as [nc [He Hnc]]; apply ownRows_in in Hnc.
          right; left; exists nc; auto.
        + destruct H as [[q k] [Hq He]]; cbn beta iota in He.
          revert He.
          match goal with
          | |- (if ?b then _ else _) = _ -> _ => destruct b eqn:Hm
          end; [| intro He; cbn iota in He; discriminate He].
          cbn iota.
          apply ClsRel.mem_spec in Hm.
          match goal with
          | |- (if ?d then _ else _) = _ -> _ => destruct d as [E | NE]
          end; intro He; cbn iota in He; [discriminate He |].
          injection He as <-.
          right; right; left; exists q, k; simpl in NE; auto.
        + destruct H as [nvu [He Hnvu]]; apply ownRows_in in Hnvu.
          right; right; right; exists nvu; auto.
      - intros [H | [H | [H | H]]].
        + destruct H as [f0 [Hin ->]].
          left; exists f0; split;
            [reflexivity | apply ownRows_in; exact Hin].
        + destruct H as [nc [Hin ->]].
          right; left; exists nc; split;
            [reflexivity | apply ownRows_in; exact Hin].
        + destruct H as [q [k [Hp [Hq [NE ->]]]]].
          right; right; left; exists (q, k); split; [exact Hq |].
          cbn beta iota.
          match goal with
          | |- (if ?b then _ else _) = _ =>
              assert (Hb : b = true)
                by (apply ClsRel.mem_spec; exact Hp);
              rewrite Hb
          end.
          match goal with
          | |- (if ?d then _ else _) = _ => destruct d as [E | _]
          end; [simpl in E; contradiction NE; exact E | reflexivity].
        + destruct H as [nvu [Hin ->]].
          right; right; right; exists nvu; split;
            [reflexivity | apply ownRows_in; exact Hin].
    Qed.

    Lemma mem_transD : forall rho I q f,
        VF.DepRel.In (q, f) (transD rho I) <->
        VF.PkgSet.In q (transR rho I) /\
        FSet.In f (dependees rho I q).
    Proof.
      intros rho I q f; unfold transD; rewrite SOqd.mem_unionMap.
      split.
      - intros [q0 [Hq0 Hf]]; unfold depEdges in Hf.
        apply SOfd.mem_map in Hf; destruct Hf as [f0 [Hf0 He]].
        injection He as <- <-; split; assumption.
      - intros [Hq Hf]; exists q; split; [exact Hq |].
        unfold depEdges; apply SOfd.mem_map; exists f; split;
          [exact Hf | reflexivity].
    Qed.

    (* Selected packages live in the effective repository: the source
       fields for subset, pins and availability say exactly that. *)
    Lemma res_sub_eff : forall rho I S,
        IsResolution rho I S -> PkgSet.Subset S (effRepo rho I).
    Proof.
      intros rho I S HR [n v] Hp; apply mem_effRepo.
      split; [exact (ores_subset _ _ _ HR _ Hp) |].
      split.
      - intros m w Hm Hn; simpl in Hn; subst m.
        symmetry; exact (ores_pins _ _ _ HR _ _ Hm _ Hp).
      - exact (ores_available _ _ _ HR _ Hp).
    Qed.

    Theorem opam_soundness : forall rho I S' sigma,
        VF.IsResolution (transR rho I) (transD rho I) rootPkg S' sigma ->
        IsResolution rho I (decodeS S').
    Proof.
      intros rho I S' sigma HR.
      assert (Hsub : forall n v,
                 PkgSet.In (n, v) (decodeS S') ->
                 PkgSet.In (n, v) (effRepo rho I)).
      { intros n v Hnv; apply mem_decodeS in Hnv.
        apply (VF.res_subset _ _ _ _ _ HR) in Hnv.
        apply mem_transR in Hnv.
        destruct Hnv as [[p [Hp He]] | He]; [| discriminate].
        destruct p as [m w]; unfold embedPkg in He; simpl in He.
        injection He as -> ->; exact Hp. }
      assert (HV : forall n v,
                 PkgSet.In (n, v) (decodeS S') ->
                 VSet.In v (srcVersions rho I n)).
      { intros n v Hnv; apply mem_srcVersions, Hsub; exact Hnv. }
      assert (Hemb : forall n v,
                 PkgSet.In (n, v) (decodeS S') ->
                 VF.PkgSet.In (embedPkg (n, v)) S').
      { intros n v Hnv; apply mem_decodeS in Hnv; exact Hnv. }
      assert (Hroot := VF.res_root_mem _ _ _ _ _ HR).
      assert (HrootR : VF.PkgSet.In rootPkg (transR rho I)).
      { apply mem_transR; right; reflexivity. }
      assert (Hrow : VF.DepRel.In (rootPkg, rootForm rho
                       (srcVersions rho I) I) (transD rho I)).
      { apply mem_transD; split; [exact HrootR |].
        simpl; apply FSet.singleton_spec; reflexivity. }
      assert (Hrootrow :=
                VF.res_formula_closure _ _ _ _ _ HR _ Hroot _ Hrow).
      simpl in Hrootrow.
      destruct Hrootrow as [Hpins [Hgoal Hinv]].
      assert (Hsig : forall x, sigma x = pin rho x).
      { apply (pins_pin rho S' sigma); exact Hpins. }
      assert (Hdeps : forall n v f,
                 PkgSet.In (n, v) (decodeS S') ->
                 FSet.In f (dependees rho I (embedPkg (n, v))) ->
                 VF.Satisfies S' sigma f).
      { intros n v f Hnv Hf.
        apply (VF.res_formula_closure _ _ _ _ _ HR _ (Hemb _ _ Hnv)).
        apply mem_transD; split; [| exact Hf].
        apply mem_transR; left; exists (n, v); split;
          [exact (Hsub _ _ Hnv) | reflexivity]. }
      constructor.
      - intros [n v] Hp.
        assert (H := Hsub _ _ Hp); apply mem_effRepo in H; tauto.
      - intros n v v' Hv Hv'.
        apply mem_decodeS in Hv, Hv'.
        assert (E := VF.res_version_unique _ _ _ _ _ HR
                       (TName.Real n) _ _ Hv Hv').
        injection E as ->; reflexivity.
      - intros [n v] Hp.
        assert (H := Hsub _ _ Hp); apply mem_effRepo in H; tauto.
      - apply (encodeOF_correct rho _ _ _ Hsig HV); exact Hgoal.
      - apply (encodeOF_correct rho _ _ _ Hsig HV); exact Hinv.
      - intros [n v] Hp f Hf.
        assert (Hs : VF.Satisfies S' sigma
                       (encodeOF rho (srcVersions rho I) f)).
        { apply (Hdeps _ _ _ Hp); unfold dependees.
          apply mem_dependees_real; left; exists f; auto. }
        apply (encodeOF_correct rho _ _ _ Hsig HV) in Hs; exact Hs.
      - intros [pn pv] Hp n g c Hrowc Hg v Hv Hne Hh.
        assert (Hs : VF.Satisfies S' sigma
                       (cflForm rho (srcVersions rho I) (pn, pv)
                          (n, (g, c)))).
        { apply (Hdeps _ _ _ Hp); unfold dependees.
          apply mem_dependees_real; right; left.
          exists (n, (g, c)); auto. }
        unfold cflForm in Hs; simpl in Hs; apply Hs; clear Hs; split.
        + destruct (TF_correct rho S' sigma Hsig g) as [HT _].
          apply HT, defTrue_iff; exact Hg.
        + exists (TVer.RV v); split; [| apply mem_decodeS; exact Hv].
          unfold confVS.
          destruct (N.eq_dec (fst (pn, pv)) n) as [E | _];
            [contradiction Hne; exact E |].
          apply mem_versSetBy; exists v; split;
            [reflexivity
            | split; [exact (HV _ _ Hv) | exact Hh]].
      - intros k [pn pv] [qn qv] Hp Hq Hpk Hqk Hne.
        assert (Hs : VF.Satisfies S' sigma
                       (VF.FNeg (memberAtom (qn, qv)))).
        { apply (Hdeps _ _ _ Hp); unfold dependees.
          apply mem_dependees_real; right; right; left.
          exists (qn, qv), k; simpl.
          repeat split; try assumption.
          exact (not_eq_sym Hne). }
        simpl in Hs; apply Hs; clear Hs.
        exists (TVer.RV qv); split;
          [apply VF.VSet.singleton_spec; reflexivity
          | apply mem_decodeS; exact Hq].
      - intros n v Hpin v' Hv'.
        assert (H := Hsub _ _ Hv'); apply mem_effRepo in H.
        destruct H as [_ [Hp _]]; symmetry.
        exact (Hp _ _ Hpin eq_refl).
      - intros [pn pv] Hp n v u Hrowc v' Hv'.
        assert (Hs : VF.Satisfies S' sigma
                       (pindForm (srcVersions rho I) ((n, v), u))).
        { apply (Hdeps _ _ _ Hp); unfold dependees.
          apply mem_dependees_real; right; right; right.
          exists ((n, v), u); auto. }
        unfold pindForm in Hs; simpl in Hs.
        destruct (V.eq_dec v' v) as [E | NE]; [exact E |].
        exfalso; apply Hs.
        exists (TVer.RV v'); split;
          [| apply mem_decodeS; exact Hv'].
        apply SOvv.mem_map; exists v'; split; [| reflexivity].
        apply VSet.remove_spec; split;
          [exact (HV _ _ Hv') | exact NE].
    Qed.

    Theorem opam_completeness : forall rho I S,
        IsResolution rho I S ->
        VF.IsResolution (transR rho I) (transD rho I) rootPkg
          (transS S) (pin rho).
    Proof.
      intros rho I S HR.
      assert (Hse := res_sub_eff _ _ _ HR).
      assert (Hsig : forall x, pin rho x = pin rho x)
        by (intro x; reflexivity).
      assert (HV : forall n v,
                 PkgSet.In (n, v) (decodeS (transS S)) ->
                 VSet.In v (srcVersions rho I n)).
      { intros n v Hm; rewrite decode_transS in Hm.
        apply mem_srcVersions; exact (Hse _ Hm). }
      constructor.
      - intros q Hq; apply mem_transS in Hq; apply mem_transR.
        destruct Hq as [[p [Hp ->]] | H]; [| tauto].
        left; exists p; split; [exact (Hse _ Hp) | reflexivity].
      - apply mem_transS; right; reflexivity.
      - intros p' Hp' f' Hf'.
        apply mem_transD in Hf'; destruct Hf' as [_ Hf'].
        apply mem_transS in Hp'.
        destruct Hp' as [[[pn pv] [Hp0 ->]] | ->].
        + unfold dependees in Hf'.
          apply mem_dependees_real in Hf'.
          destruct Hf'
            as [[f0 [Hin ->]] | [[nc [Hin ->]]
               | [[q [k [Hpk [Hqk [NE ->]]]]] | [nvu [Hin ->]]]]].
          * apply (encodeOF_correct rho _ _ _ Hsig HV).
            rewrite decode_transS.
            exact (ores_dep_closure _ _ _ HR _ Hp0 _ Hin).
          * destruct nc as [n [g c]]; unfold cflForm; simpl.
            intros [HT [tv [Htv Hm]]].
            destruct (TF_correct rho (transS S) (pin rho) Hsig g)
              as [HTi _].
            apply HTi in HT; apply defTrue_iff in HT.
            unfold confVS in Htv.
            destruct (N.eq_dec (fst (pn, pv)) n) as [| Hne].
            { destruct (VF.VSet.empty_spec Htv). }
            apply mem_versSetBy in Htv;
              destruct Htv as [v [-> [Hra Hh]]].
            apply mem_transS_real in Hm.
            exact (ores_conflict_avoidance _ _ _ HR _ Hp0 _ _ _ Hin
                     HT _ Hm Hne Hh).
          * destruct q as [qn qv]; simpl.
            intros [tv [Htv Hm]].
            apply VF.VSet.singleton_spec in Htv; subst tv.
            apply mem_transS_real in Hm.
            exact (ores_class_exclusion _ _ _ HR _ _ _ Hp0 Hm
                     Hpk Hqk (not_eq_sym NE)).
          * destruct nvu as [[n v] u]; unfold pindForm; simpl.
            intros [tv [Htv Hm]].
            apply SOvv.mem_map in Htv; destruct Htv as [v' [Hv' ->]].
            apply VSet.remove_spec in Hv'; destruct Hv' as [_ NE].
            apply mem_transS_real in Hm.
            exact (NE (ores_pin_depends _ _ _ HR _ Hp0 _ _ _ Hin
                         _ Hm)).
        + simpl in Hf'; apply FSet.singleton_spec in Hf'; subst f'.
          unfold rootForm; simpl; split;
            [apply (pins_pin rho (transS S) (pin rho)); exact Hsig |].
          split; apply (encodeOF_correct rho _ _ _ Hsig HV);
            rewrite decode_transS;
            [exact (ores_goal _ _ _ HR) | exact (ores_invariant _ _ _ HR)].
      - intros tn tv tv' Hv Hv'.
        apply mem_transS in Hv, Hv'.
        destruct Hv as [[[n v] [Hp He]] | He];
          destruct Hv' as [[[n' w] [Hq He']] | He'];
          unfold embedPkg, rootPkg in *;
          injection He as E1 E2; injection He' as E1' E2';
          subst; simpl in *; try discriminate; try reflexivity.
        injection E1' as ->.
        f_equal.
        exact (ores_version_unique _ _ _ HR _ _ _ Hp Hq).
    Qed.

    (* -- slice reuse: the lookup lemmas.  A package's rows read the
       instance only at its own rows and at the versions of the names
       they mention, so a name-restricted repository and owner-filtered
       rows answer the same queries -- what lets a driver hold the
       archive in per-name tables. -- *)

    Module PkgPre := PreimageOfKeys N Pkg NSet PkgSet.
    Definition nameRestrict (ns : NSet.t) (R : PkgSet.t) : PkgSet.t :=
      PkgPre.ofKeys fst ns R.

    Fixpoint ofNames (f : OFormula) : NSet.t :=
      match f with
      | OFAtom n _ _ => NSet.singleton n
      | OFAnd a b => NSet.union (ofNames a) (ofNames b)
      | OFOr a b => NSet.union (ofNames a) (ofNames b)
      end.

    Definition listNames {A : Type} (nm : A -> NSet.t) (l : list A)
      : NSet.t :=
      List.fold_right (fun a acc => NSet.union (nm a) acc) NSet.empty l.

    Definition rowNames (I : Inst) (p : Pkg.t) : NSet.t :=
      NSet.union (listNames ofNames (ownRows p (inst_dep I)))
        (NSet.union
           (listNames (fun nc => NSet.singleton (fst nc))
              (ownRows p (inst_cfl I)))
           (listNames (fun nvu => NSet.singleton (fst (fst nvu)))
              (ownRows p (inst_pind I)))).

    Definition clsSlice (cls : ClsRel.t) (p : Pkg.t) : ClsRel.t :=
      ClsRel.filter (fun qk => ClsRel.mem (p, snd qk) cls) cls.

    Definition pkgSlice (I : Inst) (p : Pkg.t) : Inst :=
      MkInst (nameRestrict (rowNames I p) (inst_repo I))
        (List.filter (ownb p) (inst_dep I))
        (List.filter (ownb p) (inst_dpo I))
        (List.filter (ownb p) (inst_cfl I))
        (clsSlice (inst_cls I) p)
        (inst_avl I)
        (List.filter (ownb p) (inst_dxt I))
        (inst_pins I)
        (List.filter (ownb p) (inst_pind I))
        (inst_goal I) (inst_inv I).

    Definition nameSlice (I : Inst) (n : N.t) : Inst :=
      MkInst (nameRestrict (NSet.singleton n) (inst_repo I))
        (inst_dep I) (inst_dpo I) (inst_cfl I) (inst_cls I)
        (inst_avl I) (inst_dxt I) (inst_pins I)
        (inst_pind I) (inst_goal I) (inst_inv I).

    Definition rootSlice (I : Inst) : Inst :=
      MkInst
        (nameRestrict
           (NSet.union (ofNames (inst_goal I)) (ofNames (inst_inv I)))
           (inst_repo I))
        nil nil nil ClsRel.empty (inst_avl I) nil
        (inst_pins I) nil (inst_goal I) (inst_inv I).

    Lemma srcVersions_restrict : forall rho I ns n,
        NSet.In n ns ->
        realVersions
          (effRepo rho
             (MkInst (nameRestrict ns (inst_repo I)) (inst_dep I)
                (inst_dpo I) (inst_cfl I) (inst_cls I) (inst_avl I)
                (inst_dxt I) (inst_pins I) (inst_pind I)
                (inst_goal I) (inst_inv I))) n =
        srcVersions rho I n.
    Proof.
      intros rho I ns n Hn; apply VSet.ext; intro v.
      rewrite mem_realVersions.
      unfold srcVersions; rewrite mem_realVersions.
      rewrite !mem_effRepo; simpl.
      unfold nameRestrict; rewrite PkgPre.mem_ofKeys; simpl.
      unfold PinOK, availOK; simpl; intuition.
    Qed.

    Lemma srcVersions_slice_agree : forall rho I sl ns n,
        inst_repo sl = nameRestrict ns (inst_repo I) ->
        inst_avl sl = inst_avl I -> inst_pins sl = inst_pins I ->
        NSet.In n ns ->
        srcVersions rho sl n = srcVersions rho I n.
    Proof.
      intros rho I sl ns n Hr Ha Hp Hn.
      unfold srcVersions at 1.
      assert (E : effRepo rho sl =
                  effRepo rho
                    (MkInst (nameRestrict ns (inst_repo I)) (inst_dep I)
                       (inst_dpo I) (inst_cfl I) (inst_cls I)
                       (inst_avl I) (inst_dxt I)
                       (inst_pins I) (inst_pind I) (inst_goal I)
                       (inst_inv I))).
      { unfold effRepo; rewrite Hr, Ha, Hp; reflexivity. }
      rewrite E; apply (srcVersions_restrict rho I ns n Hn).
    Qed.

    Lemma versSetBy_agree : forall Vq Vq' n c,
        Vq n = Vq' n -> versSetBy Vq n c = versSetBy Vq' n c.
    Proof. intros Vq Vq' n c H; unfold versSetBy; rewrite H;
      reflexivity. Qed.

    Lemma fS_agree : forall rho Vq Vq' f,
        (forall n, NSet.In n (ofNames f) -> Vq n = Vq' n) ->
        fS rho Vq f = fS rho Vq' f.
    Proof.
      intros rho Vq Vq'.
      induction f as [n g c | a IHa b IHb | a IHa b IHb]; intro H;
        simpl.
      - rewrite (versSetBy_agree Vq Vq' n c); [reflexivity |].
        apply H; simpl; apply NSet.singleton_spec; reflexivity.
      - rewrite IHa, IHb; try reflexivity;
          intros n Hn; apply H; simpl; apply NSet.union_spec;
          [right | left]; exact Hn.
      - rewrite IHa, IHb; try reflexivity;
          intros n Hn; apply H; simpl; apply NSet.union_spec;
          [right | left]; exact Hn.
    Qed.

    Lemma encodeOF_agree : forall rho Vq Vq' f,
        (forall n, NSet.In n (ofNames f) -> Vq n = Vq' n) ->
        encodeOF rho Vq f = encodeOF rho Vq' f.
    Proof.
      intros rho Vq Vq' f H; unfold encodeOF.
      rewrite (fS_agree rho Vq Vq' f H); reflexivity.
    Qed.

    Lemma cflForm_agree : forall rho Vq Vq' p nc,
        Vq (fst nc) = Vq' (fst nc) ->
        cflForm rho Vq p nc = cflForm rho Vq' p nc.
    Proof.
      intros rho Vq Vq' p [n [g c]] H; unfold cflForm, confVS; simpl.
      simpl in H.
      destruct (N.eq_dec (fst p) n); [reflexivity |].
      rewrite (versSetBy_agree Vq Vq' n c H); reflexivity.
    Qed.

    Lemma pindForm_agree : forall Vq Vq' nvu,
        Vq (fst (fst nvu)) = Vq' (fst (fst nvu)) ->
        pindForm Vq nvu = pindForm Vq' nvu.
    Proof.
      intros Vq Vq' [[n v] u] H; unfold pindForm; simpl in *.
      rewrite H; reflexivity.
    Qed.

    Lemma listNames_in : forall (A : Type) (nm : A -> NSet.t) l n a,
        In a l -> NSet.In n (nm a) -> NSet.In n (listNames nm l).
    Proof.
      intros A nm l n a; induction l as [| b l IH]; simpl;
        [intros [] |].
      intros [-> | Hin] Hn; apply NSet.union_spec;
        [left; exact Hn | right; exact (IH Hin Hn)].
    Qed.

    Lemma filter_idem : forall (A : Type) (f : A -> bool) l,
        List.filter f (List.filter f l) = List.filter f l.
    Proof.
      intros A f; induction l as [| a l IH]; simpl; [reflexivity |].
      destruct (f a) eqn:Hf; simpl; [rewrite Hf, IH | rewrite IH];
        reflexivity.
    Qed.

    Lemma own_filter_in : forall (A : Type) p (a : A) l,
        In (p, a) (List.filter (ownb p) l) <-> In (p, a) l.
    Proof.
      intros A p a l; rewrite List.filter_In; unfold ownb; simpl.
      destruct (Pkg.eq_dec p p) as [_ | NE];
        [intuition | contradiction NE; reflexivity].
    Qed.

    Theorem versions_lookupReal : forall rho I n,
        versions rho (nameSlice I n) (TName.Real n) =
        versions rho I (TName.Real n).
    Proof.
      intros rho I n; simpl.
      rewrite (srcVersions_slice_agree rho I (nameSlice I n)
                 (NSet.singleton n) n); try reflexivity.
      apply NSet.singleton_spec; reflexivity.
    Qed.

    Theorem dependees_lookupRoot : forall rho I,
        dependees rho (rootSlice I) rootPkg = dependees rho I rootPkg.
    Proof.
      intros rho I; unfold dependees; simpl.
      unfold rootForm; simpl.
      assert (Hg : forall n,
                 NSet.In n (ofNames (inst_goal I)) ->
                 srcVersions rho (rootSlice I) n = srcVersions rho I n).
      { intros n Hn.
        apply (srcVersions_slice_agree rho I (rootSlice I)
                 (NSet.union (ofNames (inst_goal I))
                    (ofNames (inst_inv I))) n); try reflexivity.
        apply NSet.union_spec; left; exact Hn. }
      assert (Hi : forall n,
                 NSet.In n (ofNames (inst_inv I)) ->
                 srcVersions rho (rootSlice I) n = srcVersions rho I n).
      { intros n Hn.
        apply (srcVersions_slice_agree rho I (rootSlice I)
                 (NSet.union (ofNames (inst_goal I))
                    (ofNames (inst_inv I))) n); try reflexivity.
        apply NSet.union_spec; right; exact Hn. }
      rewrite (encodeOF_agree rho _ _ _ Hg).
      rewrite (encodeOF_agree rho _ _ _ Hi).
      reflexivity.
    Qed.

    Theorem dependees_lookupReal : forall rho I n v,
        dependees rho (pkgSlice I (n, v)) (embedPkg (n, v)) =
        dependees rho I (embedPkg (n, v)).
    Proof.
      intros rho I n v; unfold dependees.
      assert (HVq : forall m, NSet.In m (rowNames I (n, v)) ->
                 srcVersions rho (pkgSlice I (n, v)) m =
                 srcVersions rho I m).
      { intros m Hm.
        apply (srcVersions_slice_agree rho I (pkgSlice I (n, v))
                 (rowNames I (n, v)) m); reflexivity || exact Hm. }
      apply FSet.ext; intro f.
      unfold embedPkg; cbn [fst snd].
      rewrite !mem_dependees_real.
      cbn [pkgSlice inst_dep inst_cfl inst_cls inst_pind].
      split.
      - intros [H | [H | [H | H]]].
        + destruct H as [f0 [Hin ->]].
          apply (proj1 (own_filter_in _ _ _ _)) in Hin.
          left; exists f0; split; [exact Hin |].
          apply encodeOF_agree; intros m Hm; apply HVq.
          unfold rowNames; apply NSet.union_spec; left.
          apply (listNames_in _ _ _ _ f0);
            [apply ownRows_in; exact Hin | exact Hm].
        + destruct H as [nc [Hin ->]].
          apply (proj1 (own_filter_in _ _ _ _)) in Hin.
          right; left; exists nc; split; [exact Hin |].
          apply cflForm_agree; apply HVq.
          unfold rowNames; apply NSet.union_spec; right.
          apply NSet.union_spec; left.
          apply (listNames_in _ _ _ _ nc);
            [apply ownRows_in; exact Hin
            | apply NSet.singleton_spec; reflexivity].
        + destruct H as [q [k [Hpk [Hqk [NE ->]]]]].
          unfold clsSlice in Hpk, Hqk.
          apply ClsRel.filter_spec' in Hpk; destruct Hpk as [Hpk _].
          apply ClsRel.filter_spec' in Hqk; destruct Hqk as [Hqk _].
          right; right; left; exists q, k; auto.
        + destruct H as [nvu [Hin ->]].
          apply (proj1 (own_filter_in _ _ _ _)) in Hin.
          right; right; right; exists nvu; split;
            [exact Hin |].
          apply pindForm_agree; apply HVq.
          unfold rowNames; apply NSet.union_spec; right.
          apply NSet.union_spec; right.
          apply (listNames_in _ _ _ _ nvu);
            [apply ownRows_in; exact Hin
            | apply NSet.singleton_spec; reflexivity].
      - intros [H | [H | [H | H]]].
        + destruct H as [f0 [Hin ->]].
          left; exists f0; split;
            [apply (proj2 (own_filter_in _ _ _ _)); exact Hin |].
          apply encodeOF_agree; intros m Hm; symmetry; apply HVq.
          unfold rowNames; apply NSet.union_spec; left.
          apply (listNames_in _ _ _ _ f0);
            [apply ownRows_in; exact Hin | exact Hm].
        + destruct H as [nc [Hin ->]].
          right; left; exists nc; split;
            [apply (proj2 (own_filter_in _ _ _ _)); exact Hin |].
          apply cflForm_agree; symmetry; apply HVq.
          unfold rowNames; apply NSet.union_spec; right.
          apply NSet.union_spec; left.
          apply (listNames_in _ _ _ _ nc);
            [apply ownRows_in; exact Hin
            | apply NSet.singleton_spec; reflexivity].
        + destruct H as [q [k [Hpk [Hqk [NE ->]]]]].
          right; right; left; exists q, k.
          repeat split; try assumption.
          * unfold clsSlice; apply ClsRel.filter_spec'; split;
              [exact Hpk | simpl].
            apply ClsRel.mem_spec; exact Hpk.
          * unfold clsSlice; apply ClsRel.filter_spec'; split;
              [exact Hqk | simpl].
            apply ClsRel.mem_spec; exact Hpk.
        + destruct H as [nvu [Hin ->]].
          right; right; right; exists nvu; split;
            [apply (proj2 (own_filter_in _ _ _ _)); exact Hin |].
          apply pindForm_agree; symmetry; apply HVq.
          unfold rowNames; apply NSet.union_spec; right.
          apply NSet.union_spec; right.
          apply (listNames_in _ _ _ _ nvu);
            [apply ownRows_in; exact Hin
            | apply NSet.singleton_spec; reflexivity].
    Qed.
  End Reduction.

End Opam.
