From Stdlib Require Import MSets List Bool.
From PackageCalculus Require Import Prelude Core Versions PackageFormula.

Create HintDb cmp_opam.
Create Rewrite HintDb cmp_opam.

(* opam's dependency semantics at a fixed environment, translated into the
   package-formula calculus.  The source language has filters, so the
   calculus below does; the reduction evaluates every one of them against
   the given valuation as it runs, which is what opam's own pre-pass does
   before its solver ever sees a formula, and so emits plain package
   formulas.  Variable names X are opam's qualified names (a package-local
   variable like with-test is the instance's p:with-test element of X);
   values live in one totally ordered sort Y, as opam itself compares
   them. *)
Module Opam (N V X Y E : UsualOrderedType).
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
    #[local] Hint Rewrite NF.compare_eq_iff VF'.compare_eq_iff : cmp_opam.
    #[local] Hint Extern 1 => cmp_by NF.compare_antisym : cmp_opam.
    #[local] Hint Extern 1 => cmp_by VF'.compare_antisym : cmp_opam.
    #[local] Hint Extern 1 => cmp_by NF.compare_lt_trans : cmp_opam.
    #[local] Hint Extern 1 => cmp_by VF'.compare_lt_trans : cmp_opam.

    (* Target names: a synthetic root carrying the request (opam has no
       root package -- the goal and switch invariant are formulas), the
       real opam packages, and one shared gadget per conflict class.
       There is no name for a filter variable: the reduction evaluates
       filters under rho as opam's own pre-pass does, so no variable
       survives into the target.  There is no name for a system package
       either: a depext cannot decide between opam packages, so nothing
       external reaches the target.

       Cls is a separate constructor rather than Real applied to the class
       name because the two namespaces overlap: opam's ocaml-system is
       both a conflict class (declared by system-mingw and system-msvc)
       and a package, and that package declares the unrelated class
       ocaml-core-compiler.  Conflating them would fuse one name's
       versions with another class's claimants. *)
    Module TName.
      Inductive name : Type :=
      | Root
      | Real (n : N.t)
      | Cls (k : N.t).
      Definition t := name.

      Definition compare (x y : t) : comparison :=
        match x, y with
        | Root, Root => Eq
        | Root, _ => Lt
        | _, Root => Gt
        | Real n1, Real n2 => N.compare n1 n2
        | Real _, _ => Lt
        | _, Real _ => Gt
        | Cls k1, Cls k2 => N.compare k1 k2
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

    (* The root carries a unit version; a class gadget's versions are the
       names of the class's declarers.  Keying them by name and not by
       package is what reproduces opam's rule, which is stated over names
       ("any two packages having a common conflict class") and implemented
       by removing the declarer's own name from the member map: every
       version of a member claims the same gadget version, so two versions
       of one package never exclude each other through a class, while two
       different names claiming one gadget version are ruled out by the
       target's version uniqueness. *)
    Module TVer.
      Inductive version : Type :=
      | RV (v : V.t)
      | UnitV
      | NV (n : N.t).
      Definition t := version.

      Definition compare (x y : t) : comparison :=
        match x, y with
        | RV v1, RV v2 => V.compare v1 v2
        | RV _, _ => Lt
        | _, RV _ => Gt
        | UnitV, UnitV => Eq
        | UnitV, _ => Lt
        | _, UnitV => Gt
        | NV n1, NV n2 => N.compare n1 n2
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

    Module PF := PackageFormula TNOT TVOT.

    Definition embedPkg (p : Pkg.t) : PF.Pkg.t :=
      (TName.Real (fst p), TVer.RV (snd p)).
    Definition rootPkg : PF.Pkg.t := (TName.Root, TVer.UnitV).

    Module SOpt := SetOps Pkg PF.Pkg PkgSet PF.PkgSet.
    Definition embedSet (S : PkgSet.t) : PF.PkgSet.t :=
      SOpt.map embedPkg S.

    Module SOvv := SetOps V TVOT VSet PF.VSet.
    Module SOpv := SetOps Pkg V PkgSet VSet.
    Definition realVersions (R : PkgSet.t) (n : N.t) : VSet.t :=
      SOpv.filterMap
        (fun '(m, v) => if N.eq_dec m n then Some v else None) R.

    (* The effective repository: switch pins and availability filters are
       unconditional cuts of R, applied before anything else -- pins and
       availability cut repository membership, not formulas.  availb is
       where an available: field meets rho. *)
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

    (* PF.Formula has no truth constant; an unsatisfiable dependency on
       the root name provides one, and its negation the other. *)
    Definition PFalse : PF.Formula := PF.FDep TName.Root PF.VSet.empty.
    Definition PTrue : PF.Formula := PF.FNeg PFalse.

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
      : PF.VSet.t :=
      SOvv.map TVer.RV (VSet.filter (fun v => vcHolds c v) (Vq n)).

    (* redOF has already evaluated every filter under rho and deleted the
       atoms opam's Empty absorbs, so what is left is an unguarded
       formula and encodes one constructor at a time. *)
    Fixpoint encR (Vq : N.t -> VSet.t) (g : RFormula) : PF.Formula :=
      match g with
      | RAtom n c => PF.FDep (TName.Real n) (versSetBy Vq n c)
      | RAnd a b => PF.FConj (encR Vq a) (encR Vq b)
      (* Reversed: the target prefers a disjunction's right branch (Zero
         selects the left and One the right, and One is the larger), while
         opam prefers the alternative written first.  The swap is only
         ever preference -- disjunction is commutative. *)
      | ROr a b => PF.FDisj (encR Vq b) (encR Vq a)
      end.

    (* A formula every one of whose atoms rho gated away is opam's Empty,
       and imposes nothing. *)
    Definition encodeOF (rho : Valuation) (Vq : N.t -> VSet.t)
        (f : OFormula) : PF.Formula :=
      match redOF rho f with
      | Some g => encR Vq g
      | None => PTrue
      end.

    (* The versions a conflict atom forbids; the declarer's own name is
       exempt (CUDF conflicts never apply to their declarer). *)
    Definition confVS (Vq : N.t -> VSet.t) (p : Pkg.t) (n : N.t)
        (c : VConstraint) : PF.VSet.t :=
      if N.eq_dec (fst p) n then PF.VSet.empty else versSetBy Vq n c.

    Module FSet := FSetUOT PF.Dependees.
    Module NSet := FSetUOT N.

    Definition ownb {A : Type} (p : Pkg.t) (r : Pkg.t * A) : bool :=
      if Pkg.eq_dec (fst r) p then true else false.

    Definition ownRows {A : Type} (p : Pkg.t) (l : list (Pkg.t * A))
      : list A :=
      List.map snd (List.filter (ownb p) l).

    Definition depForms (rho : Valuation) (Vq : N.t -> VSet.t) (I : Inst)
        (p : Pkg.t) : list PF.Formula :=
      List.map (encodeOF rho Vq) (ownRows p (inst_dep I)).

    (* A conflict whose filter rho makes false is not a conflict. *)
    Definition cflForm (rho : Valuation) (Vq : N.t -> VSet.t) (p : Pkg.t)
        (nc : N.t * (Filter * VConstraint)) : PF.Formula :=
      if defTrue rho (fst (snd nc))
      then
        PF.FNeg
          (PF.FDep (TName.Real (fst nc))
             (confVS Vq p (fst nc) (snd (snd nc))))
      else PTrue.

    Definition cflForms (rho : Valuation) (Vq : N.t -> VSet.t) (I : Inst)
        (p : Pkg.t) : list PF.Formula :=
      List.map (cflForm rho Vq p) (ownRows p (inst_cfl I)).

    (* Conflict classes through a shared gadget, one package per class,
       whose versions are the declaring names.  A declarer depends on its
       class's gadget at its own name, so two declarers of different names
       demand two versions of one gadget name and version uniqueness
       refuses them -- the same exclusion opam writes as a quadratic web
       of pairwise conflicts, by a linear mechanism: a class of n
       declarers costs n edges here and n^2 there, which on opam's own
       largest class is a couple of hundred terms against tens of
       thousands. *)
    Module SOcf := SetOps ClsElt PF.Dependees ClsRel FSet.
    Definition clsForms (cls : ClsRel.t) (p : Pkg.t) : FSet.t :=
      SOcf.filterMap
        (fun '(q, k) =>
           if Pkg.eq_dec q p
           then Some (PF.FDep (TName.Cls k)
                        (PF.VSet.singleton (TVer.NV (fst p))))
           else None)
        cls.

    (* The gadget packages themselves: one version per declaring name of
       each class.  They carry no outgoing formula (dependeesBy answers
       FSet.empty at them), so they constrain only by being claimed. *)
    Module SOcp := SetOps ClsElt PF.Pkg ClsRel PF.PkgSet.
    Definition clsPkg (qk : ClsElt.t) : PF.Pkg.t :=
      (TName.Cls (snd qk), TVer.NV (fst (fst qk))).

    Definition clsPkgs (cls : ClsRel.t) : PF.PkgSet.t :=
      SOcp.map clsPkg cls.

    (* The gadget versions a class has: the names that declare it. *)
    Module SOcv := SetOps ClsElt TVOT ClsRel PF.VSet.
    Definition clsVersions (cls : ClsRel.t) (k : N.t) : PF.VSet.t :=
      SOcv.filterMap
        (fun '(q, k') =>
           if N.eq_dec k' k then Some (TVer.NV (fst q)) else None)
        cls.

    Definition pindForm (Vq : N.t -> VSet.t) (nvu : Pkg.t * Y.t)
      : PF.Formula :=
      PF.FNeg
        (PF.FDep (TName.Real (fst (fst nvu)))
           (SOvv.map TVer.RV
              (VSet.remove (snd (fst nvu)) (Vq (fst (fst nvu)))))).

    Definition pindForms (Vq : N.t -> VSet.t) (I : Inst) (p : Pkg.t)
      : list PF.Formula :=
      List.map (pindForm Vq) (ownRows p (inst_pind I)).

    Definition rootForm (rho : Valuation) (Vq : N.t -> VSet.t) (I : Inst)
      : PF.Formula :=
      PF.FConj (encodeOF rho Vq (inst_goal I))
        (encodeOF rho Vq (inst_inv I)).

    Module SOlf := SetOps Pkg PF.Dependees PkgSet FSet.

    (* THE per-package lookup: a target package's formulas, from its own
       instance rows under the valuation. *)
    Definition dependeesBy (rho : Valuation) (Vq : N.t -> VSet.t)
        (I : Inst) (q : PF.Pkg.t) : FSet.t :=
      match q with
      | (TName.Real n, TVer.RV v) =>
          FSet.union (SOlf.ofList (depForms rho Vq I (n, v)))
            (FSet.union (SOlf.ofList (cflForms rho Vq I (n, v)))
               (FSet.union (clsForms (inst_cls I) (n, v))
                  (SOlf.ofList (pindForms Vq I (n, v)))))
      | (TName.Root, TVer.UnitV) => FSet.singleton (rootForm rho Vq I)
      | _ => FSet.empty
      end.

    Definition dependees (rho : Valuation) (I : Inst) (q : PF.Pkg.t)
      : FSet.t :=
      dependeesBy rho (srcVersions rho I) I q.

    (* The per-target-name version lookup. *)
    Definition versions (rho : Valuation) (I : Inst) (tn : TName.t)
      : PF.VSet.t :=
      match tn with
      | TName.Root => PF.VSet.singleton TVer.UnitV
      | TName.Real n => SOvv.map TVer.RV (srcVersions rho I n)
      | TName.Cls k => clsVersions (inst_cls I) k
      end.

    (* -- derived aggregation: the global translation -- *)

    Definition transR (rho : Valuation) (I : Inst) : PF.PkgSet.t :=
      PF.PkgSet.union (embedSet (effRepo rho I))
        (PF.PkgSet.union (PF.PkgSet.singleton rootPkg)
           (clsPkgs (inst_cls I))).

    Module SOfd := SetOps PF.Dependees PF.DepElt FSet PF.DepRel.
    Definition depEdges (q : PF.Pkg.t) (fs : FSet.t) : PF.DepRel.t :=
      SOfd.map (fun f => (q, f)) fs.

    Module SOqd := SetOps PF.Pkg PF.DepElt PF.PkgSet PF.DepRel.
    Definition transD (rho : Valuation) (I : Inst) : PF.DepRel.t :=
      SOqd.unionMap (fun q => depEdges q (dependees rho I q))
        (transR rho I).

    (* The gadget versions a selection claims: one per class a selected
       package declares, at that package's name. *)
    Definition clsSel (cls : ClsRel.t) (S : PkgSet.t) : PF.PkgSet.t :=
      SOcp.map clsPkg (ClsRel.filter (fun qk => PkgSet.mem (fst qk) S) cls).

    Definition transS (cls : ClsRel.t) (S : PkgSet.t) : PF.PkgSet.t :=
      PF.PkgSet.union (embedSet S)
        (PF.PkgSet.union (PF.PkgSet.singleton rootPkg) (clsSel cls S)).

    Module SOtp := SetOps PF.Pkg Pkg PF.PkgSet PkgSet.
    Definition tryInvPkg (q : PF.Pkg.t) : option Pkg.t :=
      match q with
      | (TName.Real n, TVer.RV v) => Some (n, v)
      | _ => None
      end.

    Definition decodeS (S' : PF.PkgSet.t) : PkgSet.t :=
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
        PF.VSet.In tv (versSetBy Vq n c) <->
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
        PF.PkgSet.In (TName.Real n, TVer.RV v) S'.
    Proof.
      intros S' n v; unfold decodeS; rewrite SOtp.mem_filterMap.
      split.
      - intros [[tn tv] [Hm Hf]];
          destruct tn as [| m | k]; destruct tv as [w | | m'];
          simpl in Hf; try discriminate.
        injection Hf as -> ->; exact Hm.
      - intro H; exists (TName.Real n, TVer.RV v); split;
          [exact H | reflexivity].
    Qed.

    Lemma mem_clsPkgs : forall cls q,
        PF.PkgSet.In q (clsPkgs cls) <->
        exists p k, ClsRel.In (p, k) cls /\
                    q = (TName.Cls k, TVer.NV (fst p)).
    Proof.
      intros cls q; unfold clsPkgs; rewrite SOcp.mem_map; split.
      - intros [[p k] [Hm ->]]; exists p, k; split;
          [exact Hm | reflexivity].
      - intros [p [k [Hm ->]]]; exists (p, k); split;
          [exact Hm | reflexivity].
    Qed.

    Lemma mem_clsSel : forall cls S q,
        PF.PkgSet.In q (clsSel cls S) <->
        exists p k, PkgSet.In p S /\ ClsRel.In (p, k) cls /\
                    q = (TName.Cls k, TVer.NV (fst p)).
    Proof.
      intros cls S q; unfold clsSel; rewrite SOcp.mem_map; split.
      - intros [[p k] [Hm ->]]; apply ClsRel.filter_spec' in Hm;
          destruct Hm as [Hm Hs]; simpl in Hs.
        exists p, k; split;
          [apply PkgSet.mem_spec; exact Hs
          | split; [exact Hm | reflexivity]].
      - intros [p [k [Hs [Hm ->]]]]; exists (p, k); split;
          [| reflexivity].
        apply ClsRel.filter_spec'; split;
          [exact Hm | simpl; apply PkgSet.mem_spec; exact Hs].
    Qed.

    Lemma mem_clsVersions : forall cls k tv,
        PF.VSet.In tv (clsVersions cls k) <->
        exists p, ClsRel.In (p, k) cls /\ tv = TVer.NV (fst p).
    Proof.
      intros cls k tv; unfold clsVersions; rewrite SOcv.mem_filterMap.
      split.
      - intros [[p k'] [Hm Hf]]; cbn beta iota in Hf.
        destruct (N.eq_dec k' k) as [-> |]; [| discriminate].
        injection Hf as <-; exists p; split; [exact Hm | reflexivity].
      - intros [p [Hm ->]]; exists (p, k); split; [exact Hm |].
        cbn beta iota; destruct (N.eq_dec k k) as [_ | NE];
          [reflexivity | contradiction NE; reflexivity].
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
        PF.PkgSet.In q (transR rho I) <->
        (exists p, PkgSet.In p (effRepo rho I) /\ q = embedPkg p) \/
        q = rootPkg \/
        (exists p k, ClsRel.In (p, k) (inst_cls I) /\
                     q = (TName.Cls k, TVer.NV (fst p))).
    Proof.
      intros rho I q; unfold transR, embedSet.
      rewrite !PF.PkgSet.union_spec, PF.PkgSet.singleton_spec,
        SOpt.mem_map, mem_clsPkgs.
      tauto.
    Qed.

    Lemma mem_transS : forall cls S q,
        PF.PkgSet.In q (transS cls S) <->
        (exists p, PkgSet.In p S /\ q = embedPkg p) \/ q = rootPkg \/
        (exists p k, PkgSet.In p S /\ ClsRel.In (p, k) cls /\
                     q = (TName.Cls k, TVer.NV (fst p))).
    Proof.
      intros cls S q; unfold transS, embedSet.
      rewrite !PF.PkgSet.union_spec, PF.PkgSet.singleton_spec,
        SOpt.mem_map, mem_clsSel.
      tauto.
    Qed.

    Lemma mem_transS_real : forall cls S n v,
        PF.PkgSet.In (TName.Real n, TVer.RV v) (transS cls S) <->
        PkgSet.In (n, v) S.
    Proof.
      intros cls S n v; rewrite mem_transS; split.
      - intros [[p [Hp He]] | [He | [p [k [_ [_ He]]]]]];
          try discriminate.
        destruct p as [m w]; unfold embedPkg in He; simpl in He.
        injection He as -> ->; exact Hp.
      - intro H; left; exists (n, v); split; [exact H | reflexivity].
    Qed.

    Lemma decode_transS : forall cls S, decodeS (transS cls S) = S.
    Proof.
      intros cls S; apply PkgSet.ext; intros [n v].
      rewrite mem_decodeS, mem_transS_real; reflexivity.
    Qed.

    (* Each target name draws its versions from one branch of transS, so
       version uniqueness splits three ways rather than nine. *)
    Lemma transS_at_root : forall cls S tv,
        PF.PkgSet.In (TName.Root, tv) (transS cls S) -> tv = TVer.UnitV.
    Proof.
      intros cls S tv H; apply mem_transS in H.
      destruct H as [[[m w] [_ He]] | [He | [p [k [_ [_ He]]]]]];
        unfold embedPkg, rootPkg in He; try discriminate.
      injection He as ->; reflexivity.
    Qed.

    Lemma transS_at_real : forall cls S n tv,
        PF.PkgSet.In (TName.Real n, tv) (transS cls S) ->
        exists v, tv = TVer.RV v /\ PkgSet.In (n, v) S.
    Proof.
      intros cls S n tv H; apply mem_transS in H.
      destruct H as [[[m w] [Hp He]] | [He | [p [k [_ [_ He]]]]]];
        unfold embedPkg, rootPkg in He; cbn [fst snd] in He;
        try discriminate.
      injection He as -> ->; exists w; split; [reflexivity | exact Hp].
    Qed.

    Lemma transS_at_cls : forall cls S k tv,
        PF.PkgSet.In (TName.Cls k, tv) (transS cls S) ->
        exists p, tv = TVer.NV (fst p) /\ PkgSet.In p S /\
                  ClsRel.In (p, k) cls.
    Proof.
      intros cls S k tv H; apply mem_transS in H.
      destruct H as [[[m w] [_ He]] | [He | [p [k' [Hp [Hpk He]]]]]];
        unfold embedPkg, rootPkg in He; cbn [fst snd] in He;
        try discriminate.
      injection He as -> ->; exists p; split;
        [reflexivity | split; [exact Hp | exact Hpk]].
    Qed.

    Lemma PTrue_sat : forall S', PF.Satisfies S' PTrue.
    Proof.
      intros S'; simpl; intros [tv [Htv _]].
      destruct (PF.VSet.empty_spec Htv).
    Qed.

    Lemma PFalse_unsat : forall S', ~ PF.Satisfies S' PFalse.
    Proof.
      intros S' [tv [Htv _]].
      destruct (PF.VSet.empty_spec Htv).
    Qed.

    Lemma defTrue_iff : forall rho g,
        defTrue rho g = true <-> evalF rho g = Some true.
    Proof.
      intros rho g; unfold defTrue.
      destruct (evalF rho g) as [[|]|]; intuition congruence.
    Qed.

    Lemma encR_correct : forall Vq S',
        (forall n v, PkgSet.In (n, v) (decodeS S') -> VSet.In v (Vq n)) ->
        forall g, PF.Satisfies S' (encR Vq g) <-> rSat (decodeS S') g.
    Proof.
      intros Vq S' HV.
      induction g as [n c | a IHa b IHb | a IHa b IHb]; simpl.
      - split.
        + intros [tv [Htv Hm]].
          apply mem_versSetBy in Htv; destruct Htv as [v [-> [_ Hh]]].
          exists v; split; [apply mem_decodeS; exact Hm | exact Hh].
        + intros [v [Hv Hh]].
          assert (Hvq := HV _ _ Hv).
          apply mem_decodeS in Hv.
          exists (TVer.RV v); split; [| exact Hv].
          apply mem_versSetBy; exists v; split;
            [reflexivity | split; [exact Hvq | exact Hh]].
      - rewrite IHa, IHb; reflexivity.
      - rewrite IHa, IHb; tauto.
    Qed.

    Lemma encodeOF_correct : forall rho Vq S',
        (forall n v, PkgSet.In (n, v) (decodeS S') -> VSet.In v (Vq n)) ->
        forall f,
          PF.Satisfies S' (encodeOF rho Vq f) <-> oSat rho (decodeS S') f.
    Proof.
      intros rho Vq S' HV f; unfold encodeOF, oSat.
      destruct (redOF rho f) as [g |] eqn:Hred.
      - rewrite (encR_correct Vq S' HV g); split.
        + intros H g' Hg'; injection Hg' as <-; exact H.
        + intro H; apply H; reflexivity.
      - split; [intros _ g' Hg'; discriminate |].
        intros _; exact (PTrue_sat S').
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
        (exists k, ClsRel.In ((n, v), k) (inst_cls I) /\
                   f = PF.FDep (TName.Cls k)
                         (PF.VSet.singleton (TVer.NV n))) \/
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
          revert Hq; revert He.
          match goal with
          | |- (if ?d then _ else _) = _ -> _ => destruct d as [-> | NE]
          end; intro He; cbn iota in He; [| discriminate He].
          injection He as <-; intro Hq.
          right; right; left; exists k; auto.
        + destruct H as [nvu [He Hnvu]]; apply ownRows_in in Hnvu.
          right; right; right; exists nvu; auto.
      - intros [H | [H | [H | H]]].
        + destruct H as [f0 [Hin ->]].
          left; exists f0; split;
            [reflexivity | apply ownRows_in; exact Hin].
        + destruct H as [nc [Hin ->]].
          right; left; exists nc; split;
            [reflexivity | apply ownRows_in; exact Hin].
        + destruct H as [k [Hp ->]].
          right; right; left; exists ((n, v), k); split; [exact Hp |].
          cbn beta iota.
          match goal with
          | |- (if ?d then _ else _) = _ => destruct d as [_ | NE]
          end; [reflexivity | contradiction NE; reflexivity].
        + destruct H as [nvu [Hin ->]].
          right; right; right; exists nvu; split;
            [reflexivity | apply ownRows_in; exact Hin].
    Qed.

    Lemma mem_transD : forall rho I q f,
        PF.DepRel.In (q, f) (transD rho I) <->
        PF.PkgSet.In q (transR rho I) /\
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

    Theorem opam_soundness : forall rho I S',
        PF.IsResolution (transR rho I) (transD rho I) rootPkg S' ->
        IsResolution rho I (decodeS S').
    Proof.
      intros rho I S' HR.
      assert (Hsub : forall n v,
                 PkgSet.In (n, v) (decodeS S') ->
                 PkgSet.In (n, v) (effRepo rho I)).
      { intros n v Hnv; apply mem_decodeS in Hnv.
        apply (PF.res_subset _ _ _ _ HR) in Hnv.
        apply mem_transR in Hnv.
        destruct Hnv as [[p [Hp He]] | [He | [p [k [_ He]]]]];
          try discriminate.
        destruct p as [m w]; unfold embedPkg in He; simpl in He.
        injection He as -> ->; exact Hp. }
      assert (HV : forall n v,
                 PkgSet.In (n, v) (decodeS S') ->
                 VSet.In v (srcVersions rho I n)).
      { intros n v Hnv; apply mem_srcVersions, Hsub; exact Hnv. }
      assert (Hemb : forall n v,
                 PkgSet.In (n, v) (decodeS S') ->
                 PF.PkgSet.In (embedPkg (n, v)) S').
      { intros n v Hnv; apply mem_decodeS in Hnv; exact Hnv. }
      assert (Hroot := PF.res_root_mem _ _ _ _ HR).
      assert (HrootR : PF.PkgSet.In rootPkg (transR rho I)).
      { apply mem_transR; right; left; reflexivity. }
      assert (Hrow : PF.DepRel.In (rootPkg, rootForm rho
                       (srcVersions rho I) I) (transD rho I)).
      { apply mem_transD; split; [exact HrootR |].
        unfold dependees, dependeesBy, rootPkg.
        apply FSet.singleton_spec; reflexivity. }
      assert (Hrootrow :=
                PF.res_formula_closure _ _ _ _ HR _ Hroot _ Hrow).
      unfold rootForm in Hrootrow; cbn [PF.Satisfies] in Hrootrow.
      destruct Hrootrow as [Hgoal Hinv].
      assert (Hdeps : forall n v f,
                 PkgSet.In (n, v) (decodeS S') ->
                 FSet.In f (dependees rho I (embedPkg (n, v))) ->
                 PF.Satisfies S' f).
      { intros n v f Hnv Hf.
        apply (PF.res_formula_closure _ _ _ _ HR _ (Hemb _ _ Hnv)).
        apply mem_transD; split; [| exact Hf].
        apply mem_transR; left; exists (n, v); split;
          [exact (Hsub _ _ Hnv) | reflexivity]. }
      constructor.
      - intros [n v] Hp.
        assert (H := Hsub _ _ Hp); apply mem_effRepo in H; tauto.
      - intros n v v' Hv Hv'.
        apply mem_decodeS in Hv, Hv'.
        assert (E := PF.res_version_unique _ _ _ _ HR
                       (TName.Real n) _ _ Hv Hv').
        injection E as ->; reflexivity.
      - intros [n v] Hp.
        assert (H := Hsub _ _ Hp); apply mem_effRepo in H; tauto.
      - apply (encodeOF_correct rho _ _ HV); exact Hgoal.
      - apply (encodeOF_correct rho _ _ HV); exact Hinv.
      - intros [n v] Hp f Hf.
        assert (Hs : PF.Satisfies S'
                       (encodeOF rho (srcVersions rho I) f)).
        { apply (Hdeps _ _ _ Hp); unfold dependees.
          apply mem_dependees_real; left; exists f; auto. }
        apply (encodeOF_correct rho _ _ HV) in Hs; exact Hs.
      - intros [pn pv] Hp n g c Hrowc Hg v Hv Hne Hh.
        assert (Hs : PF.Satisfies S'
                       (cflForm rho (srcVersions rho I) (pn, pv)
                          (n, (g, c)))).
        { apply (Hdeps _ _ _ Hp); unfold dependees.
          apply mem_dependees_real; right; left.
          exists (n, (g, c)); auto. }
        unfold cflForm in Hs; cbn [fst snd] in Hs; rewrite Hg in Hs.
        cbn [PF.Satisfies] in Hs; apply Hs; clear Hs.
        exists (TVer.RV v); split; [| apply mem_decodeS; exact Hv].
        unfold confVS.
        destruct (N.eq_dec (fst (pn, pv)) n) as [E | _];
          [contradiction Hne; exact E |].
        apply mem_versSetBy; exists v; split;
          [reflexivity
          | split; [exact (HV _ _ Hv) | exact Hh]].
      (* Both declarers claim the class gadget, each at its own name; two
         versions of the one gadget name is what version uniqueness
         refuses. *)
      - intros k [pn pv] [qn qv] Hp Hq Hpk Hqk Hne.
        assert (Hcl : forall m w,
                   PkgSet.In (m, w) (decodeS S') ->
                   ClsRel.In ((m, w), k) (inst_cls I) ->
                   PF.PkgSet.In (TName.Cls k, TVer.NV m) S').
        { intros m w Hm Hmk.
          assert (Hs : PF.Satisfies S'
                         (PF.FDep (TName.Cls k)
                            (PF.VSet.singleton (TVer.NV m)))).
          { apply (Hdeps _ _ _ Hm); unfold dependees.
            apply mem_dependees_real; right; right; left.
            exists k; split; [exact Hmk | reflexivity]. }
          destruct Hs as [tv [Htv Hin]].
          apply PF.VSet.singleton_spec in Htv; subst tv; exact Hin. }
        assert (E := PF.res_version_unique _ _ _ _ HR (TName.Cls k)
                       _ _ (Hcl _ _ Hp Hpk) (Hcl _ _ Hq Hqk)).
        injection E as ->; simpl in Hne; contradiction Hne;
          reflexivity.
      - intros n v Hpin v' Hv'.
        assert (H := Hsub _ _ Hv'); apply mem_effRepo in H.
        destruct H as [_ [Hp _]]; symmetry.
        exact (Hp _ _ Hpin eq_refl).
      - intros [pn pv] Hp n v u Hrowc v' Hv'.
        assert (Hs : PF.Satisfies S'
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
        PF.IsResolution (transR rho I) (transD rho I) rootPkg
          (transS (inst_cls I) S).
    Proof.
      intros rho I S HR.
      assert (Hse := res_sub_eff _ _ _ HR).
      assert (HV : forall n v,
                 PkgSet.In (n, v) (decodeS (transS (inst_cls I) S)) ->
                 VSet.In v (srcVersions rho I n)).
      { intros n v Hm; rewrite decode_transS in Hm.
        apply mem_srcVersions; exact (Hse _ Hm). }
      constructor.
      - intros q Hq; apply mem_transS in Hq; apply mem_transR.
        destruct Hq as [[p [Hp ->]] | [H | [p [k [_ [Hpk ->]]]]]];
          [| tauto |].
        + left; exists p; split; [exact (Hse _ Hp) | reflexivity].
        + right; right; exists p, k; split; [exact Hpk | reflexivity].
      - apply mem_transS; right; left; reflexivity.
      - intros p' Hp' f' Hf'.
        apply mem_transD in Hf'; destruct Hf' as [_ Hf'].
        apply mem_transS in Hp'.
        destruct Hp' as [[[pn pv] [Hp0 ->]] | [-> | [p [k [_ [_ ->]]]]]].
        + unfold dependees in Hf'.
          apply mem_dependees_real in Hf'.
          destruct Hf'
            as [[f0 [Hin ->]] | [[nc [Hin ->]]
               | [[k [Hpk ->]] | [nvu [Hin ->]]]]].
          * apply (encodeOF_correct rho _ _ HV).
            rewrite decode_transS.
            exact (ores_dep_closure _ _ _ HR _ Hp0 _ Hin).
          * destruct nc as [n [g c]]; unfold cflForm; cbn [fst snd].
            destruct (defTrue rho g) eqn:Hg;
              [| exact (PTrue_sat (transS (inst_cls I) S))].
            cbn [PF.Satisfies]; intros [tv [Htv Hm]].
            unfold confVS in Htv.
            destruct (N.eq_dec (fst (pn, pv)) n) as [| Hne].
            { destruct (PF.VSet.empty_spec Htv). }
            apply mem_versSetBy in Htv;
              destruct Htv as [v [-> [Hra Hh]]].
            apply mem_transS_real in Hm.
            exact (ores_conflict_avoidance _ _ _ HR _ Hp0 _ _ _ Hin
                     Hg _ Hm Hne Hh).
          * cbn [PF.Satisfies].
            exists (TVer.NV pn); split;
              [apply PF.VSet.singleton_spec; reflexivity |].
            apply mem_transS; right; right.
            exists (pn, pv), k; split;
              [exact Hp0 | split; [exact Hpk | reflexivity]].
          * destruct nvu as [[n v] u]; unfold pindForm; simpl.
            intros [tv [Htv Hm]].
            apply SOvv.mem_map in Htv; destruct Htv as [v' [Hv' ->]].
            apply VSet.remove_spec in Hv'; destruct Hv' as [_ NE].
            apply mem_transS_real in Hm.
            exact (NE (ores_pin_depends _ _ _ HR _ Hp0 _ _ _ Hin
                         _ Hm)).
        + unfold dependees, dependeesBy, rootPkg in Hf'.
          apply FSet.singleton_spec in Hf'; subst f'.
          unfold rootForm; cbn [PF.Satisfies].
          split; apply (encodeOF_correct rho _ _ HV);
            rewrite decode_transS;
            [exact (ores_goal _ _ _ HR) | exact (ores_invariant _ _ _ HR)].
        (* a class gadget carries no outgoing formula *)
        + unfold dependees, dependeesBy in Hf'; cbn beta iota in Hf'.
          destruct (FSet.empty_spec Hf').
      - intros tn tv tv' Hv Hv'; destruct tn as [| n | k].
        + rewrite (transS_at_root _ _ _ Hv),
            (transS_at_root _ _ _ Hv'); reflexivity.
        + destruct (transS_at_real _ _ _ _ Hv) as [v [-> Hp]].
          destruct (transS_at_real _ _ _ _ Hv') as [w [-> Hq]].
          f_equal; exact (ores_version_unique _ _ _ HR _ _ _ Hp Hq).
        + destruct (transS_at_cls _ _ _ _ Hv) as [p [-> [Hp Hpk]]].
          destruct (transS_at_cls _ _ _ _ Hv') as [q [-> [Hq Hqk]]].
          f_equal.
          destruct (N.eq_dec (fst p) (fst q)) as [E | NE];
            [exact E |].
          destruct (ores_class_exclusion _ _ _ HR _ _ _ Hp Hq
                      Hpk Hqk NE).
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

    (* A package's class formulas read only its own declarations: the
       gadget carries the partners, so no row of a partner is consulted
       here.  A class name's versions are the other way round -- the whole
       preimage of the relation at that class -- and that is the one
       lookup whose slice no single package's rows determine. *)
    Definition clsSlice (cls : ClsRel.t) (p : Pkg.t) : ClsRel.t :=
      ClsRel.filter
        (fun qk => if Pkg.eq_dec (fst qk) p then true else false) cls.

    Definition clsNameSlice (cls : ClsRel.t) (k : N.t) : ClsRel.t :=
      ClsRel.filter
        (fun qk => if N.eq_dec (snd qk) k then true else false) cls.

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

    Definition classSlice (I : Inst) (k : N.t) : Inst :=
      MkInst PkgSet.empty nil nil nil (clsNameSlice (inst_cls I) k)
        nil nil PkgSet.empty nil (inst_goal I) (inst_inv I).

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

    (* redOF only ever keeps atoms of f, so agreeing on f's names is
       enough to fix the encoding of whatever f reduces to. *)
    Lemma encR_agree : forall rho Vq Vq' f,
        (forall n, NSet.In n (ofNames f) -> Vq n = Vq' n) ->
        forall g, redOF rho f = Some g -> encR Vq g = encR Vq' g.
    Proof.
      intros rho Vq Vq'.
      induction f as [n g0 c | a IHa b IHb | a IHa b IHb];
        intros H g Hred; simpl in Hred.
      - destruct (defTrue rho g0); [| discriminate].
        injection Hred as <-; simpl.
        rewrite (versSetBy_agree Vq Vq' n c); [reflexivity |].
        apply H; simpl; apply NSet.singleton_spec; reflexivity.
      - assert (Ha : forall m, NSet.In m (ofNames a) -> Vq m = Vq' m).
        { intros m Hm; apply H; simpl; apply NSet.union_spec;
            left; exact Hm. }
        assert (Hb : forall m, NSet.In m (ofNames b) -> Vq m = Vq' m).
        { intros m Hm; apply H; simpl; apply NSet.union_spec;
            right; exact Hm. }
        destruct (redOF rho a) eqn:Ea; destruct (redOF rho b) eqn:Eb;
          simpl in Hred; try discriminate; injection Hred as <-;
          simpl.
        + rewrite (IHa Ha _ eq_refl), (IHb Hb _ eq_refl); reflexivity.
        + exact (IHa Ha _ eq_refl).
        + exact (IHb Hb _ eq_refl).
      - assert (Ha : forall m, NSet.In m (ofNames a) -> Vq m = Vq' m).
        { intros m Hm; apply H; simpl; apply NSet.union_spec;
            left; exact Hm. }
        assert (Hb : forall m, NSet.In m (ofNames b) -> Vq m = Vq' m).
        { intros m Hm; apply H; simpl; apply NSet.union_spec;
            right; exact Hm. }
        destruct (redOF rho a) eqn:Ea; destruct (redOF rho b) eqn:Eb;
          simpl in Hred; try discriminate; injection Hred as <-;
          simpl.
        + rewrite (IHa Ha _ eq_refl), (IHb Hb _ eq_refl); reflexivity.
        + exact (IHa Ha _ eq_refl).
        + exact (IHb Hb _ eq_refl).
    Qed.

    Lemma encodeOF_agree : forall rho Vq Vq' f,
        (forall n, NSet.In n (ofNames f) -> Vq n = Vq' n) ->
        encodeOF rho Vq f = encodeOF rho Vq' f.
    Proof.
      intros rho Vq Vq' f H; unfold encodeOF.
      destruct (redOF rho f) as [g |] eqn:Hred;
        [exact (encR_agree rho Vq Vq' f H g Hred) | reflexivity].
    Qed.

    Lemma cflForm_agree : forall rho Vq Vq' p nc,
        Vq (fst nc) = Vq' (fst nc) ->
        cflForm rho Vq p nc = cflForm rho Vq' p nc.
    Proof.
      intros rho Vq Vq' p [n [g c]] H; unfold cflForm, confVS;
        cbn [fst snd].
      cbn [fst snd] in H.
      destruct (defTrue rho g); [| reflexivity].
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

    (* The one lookup whose slice is a preimage: answering it needs every
       declarer of k, which no single package's rows name.  A driver
       uncovering the repository as it goes must therefore recompute this
       answer at every ask rather than hold it, so a declarer parsed later
       is simply there. *)
    Theorem versions_lookupCls : forall rho I k,
        versions rho (classSlice I k) (TName.Cls k) =
        versions rho I (TName.Cls k).
    Proof.
      intros rho I k; cbn [versions classSlice inst_cls].
      apply PF.VSet.ext; intro tv; rewrite !mem_clsVersions.
      unfold clsNameSlice; split.
      - intros [p [Hm ->]]; apply ClsRel.filter_spec' in Hm.
        exists p; split; [tauto | reflexivity].
      - intros [p [Hm ->]]; exists p; split; [| reflexivity].
        apply ClsRel.filter_spec'; split; [exact Hm | cbn [snd]].
        destruct (N.eq_dec k k) as [_ | NE];
          [reflexivity | contradiction NE; reflexivity].
    Qed.

    Theorem dependees_lookupRoot : forall rho I,
        dependees rho (rootSlice I) rootPkg = dependees rho I rootPkg.
    Proof.
      intros rho I; unfold dependees, dependeesBy, rootPkg.
      unfold rootForm.
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
      cbn [rootSlice inst_goal inst_inv].
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
        + destruct H as [k [Hpk ->]].
          unfold clsSlice in Hpk.
          apply ClsRel.filter_spec' in Hpk; destruct Hpk as [Hpk _].
          right; right; left; exists k; auto.
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
        + destruct H as [k [Hpk ->]].
          right; right; left; exists k; split; [| reflexivity].
          unfold clsSlice; apply ClsRel.filter_spec'; split;
            [exact Hpk | cbn [fst]].
          destruct (Pkg.eq_dec (n, v) (n, v)) as [_ | NE];
            [reflexivity | contradiction NE; reflexivity].
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
