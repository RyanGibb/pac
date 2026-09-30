From Stdlib Require Import MSets List Bool.
From PackageCalculus Require Import Prelude Core Versions PackageFormula
  ConflictClass.

Create HintDb cmp_opam.
Create Rewrite HintDb cmp_opam.

Module Opam (N V X Y E : UsualOrderedType).
  (* Its core shared, so that a class relation here is the conflict-class
     calculus' own and its class lookups apply as they stand. *)
  Module Cls := ConflictClass N V.
  Module C := Cls.C.
  Module Pkg := C.Pkg.
  Module PkgSet := C.PkgSet.
  Module VSet := C.VSet.
  Module Ver := Versions N V.

  Definition Valuation : Type := X.t -> option Y.t.

  Inductive Filter : Type :=
  | FlTrue
  | FlFalse
  | FlCmp (op : CmpOp) (x : X.t) (y : Y.t)
  | FlDef (x : X.t)
  | FlAnd (c1 c2 : Filter)
  | FlOr (c1 c2 : Filter)
  | FlNot (c' : Filter).

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

  Fixpoint evalF (sigma : Valuation) (c : Filter) : option bool :=
    match c with
    | FlTrue => Some true
    | FlFalse => Some false
    | FlCmp op x y =>
        match sigma x with
        | Some w => Some (cmpOpEvalBy Y.compare op w y)
        | None => None
        end
    | FlDef x =>
        Some (match sigma x with Some _ => true | None => false end)
    | FlAnd c1 c2 => andK (evalF sigma c1) (evalF sigma c2)
    | FlOr c1 c2 => orK (evalF sigma c1) (evalF sigma c2)
    | FlNot c' => notK (evalF sigma c')
    end.

  Definition defTrue (sigma : Valuation) (c : Filter) : bool :=
    match evalF sigma c with Some true => true | _ => false end.

  Inductive VConstraint : Type :=
  | VCTop
  | VCCmp (op : CmpOp) (c : V.t)
  | VCAnd (a b : VConstraint)
  | VCOr (a b : VConstraint)
  | VCNot (a : VConstraint).

  Fixpoint vcHolds (phi : VConstraint) (v : V.t) : bool :=
    match phi with
    | VCTop => true
    | VCCmp op c => Ver.cmpOpEval op v c
    | VCAnd a b => andb (vcHolds a v) (vcHolds b v)
    | VCOr a b => orb (vcHolds a v) (vcHolds b v)
    | VCNot a => negb (vcHolds a v)
    end.

  Inductive OFormula : Type :=
  | OFAtom (n : N.t) (c : Filter) (phi : VConstraint)
  | OFAnd (a b : OFormula)
  | OFOr (a b : OFormula).

  Inductive RFormula : Type :=
  | RAtom (n : N.t) (phi : VConstraint)
  | RAnd (a b : RFormula)
  | ROr (a b : RFormula).

  Definition rMerge (mk : RFormula -> RFormula -> RFormula)
      (a b : option RFormula) : option RFormula :=
    match a, b with
    | None, b => b
    | a, None => a
    | Some a, Some b => Some (mk a b)
    end.

  Fixpoint redOF (sigma : Valuation) (d : OFormula) : option RFormula :=
    match d with
    | OFAtom n c phi =>
        if defTrue sigma c then Some (RAtom n phi) else None
    | OFAnd a b => rMerge RAnd (redOF sigma a) (redOF sigma b)
    | OFOr a b => rMerge ROr (redOF sigma a) (redOF sigma b)
    end.

  Fixpoint rSat (S : PkgSet.t) (f : RFormula) : Prop :=
    match f with
    | RAtom n phi => exists v, PkgSet.In (n, v) S /\ vcHolds phi v = true
    | RAnd a b => rSat S a /\ rSat S b
    | ROr a b => rSat S a \/ rSat S b
    end.

  Definition oSat (sigma : Valuation) (S : PkgSet.t) (d : OFormula) : Prop :=
    forall g, redOF sigma d = Some g -> rSat S g.

  Module ClsElt := Cls.InClassElt.
  Module ClsRel := Cls.InClassRel.
  Module ESet := FSetUOT E.

  (* Formula-valued relations are lists: they feed only the spec and the
     translation, and sets would demand formula comparators used nowhere. *)
  Record Inst : Type := MkInst
    { inst_repo : PkgSet.t
    ; inst_dep : list (Pkg.t * OFormula)
    ; inst_cfl : list (Pkg.t * (N.t * (Filter * VConstraint)))
    ; inst_cls : ClsRel.t
    ; inst_avl : list (Pkg.t * Filter)
    ; inst_dxt : list (Pkg.t * (E.t * Filter))
    ; inst_pins : PkgSet.t
    ; inst_pind : list (Pkg.t * (Pkg.t * Y.t))
    ; inst_query : OFormula
    ; inst_inv : OFormula }.

  Definition availOK (sigma : Valuation) (I : Inst) (p : Pkg.t) : Prop :=
    forall c, In (p, c) (inst_avl I) -> defTrue sigma c = true.

  Record IsResolution (sigma : Valuation) (I : Inst) (S : PkgSet.t)
    : Prop := MkRes
    { res_subset : PkgSet.Subset S (inst_repo I)
    ; res_version_unique : C.VersionUnique S
    ; res_available : forall p, PkgSet.In p S -> availOK sigma I p
    ; res_request : oSat sigma S (inst_query I) /\ oSat sigma S (inst_inv I)
    ; res_dep_closure :
        forall p, PkgSet.In p S ->
        forall d, In (p, d) (inst_dep I) -> oSat sigma S d
    ; res_conflict_avoidance :
        forall n v, PkgSet.In (n, v) S ->
        forall m c phi, In ((n, v), (m, (c, phi))) (inst_cfl I) ->
          defTrue sigma c = true ->
        ~ exists u, PkgSet.In (m, u) S /\ m <> n /\ vcHolds phi u = true
    ; res_class_exclusion : Cls.ClassExclusion (inst_cls I) S
    ; res_pins :
        forall n v, PkgSet.In (n, v) (inst_pins I) ->
        forall v', PkgSet.In (n, v') S -> v' = v
    ; res_pin_depends :
        forall p, PkgSet.In p S -> PkgSet.In p (inst_pins I) ->
        forall m u y, In (p, ((m, u), y)) (inst_pind I) ->
        forall u', PkgSet.In (m, u') S -> u' = u }.

  Definition depextsOf (sigma : Valuation) (I : Inst) (S : PkgSet.t)
    : ESet.t :=
    List.fold_right
      (fun r acc =>
         if andb (PkgSet.mem (fst r) S) (defTrue sigma (snd (snd r)))
         then ESet.add (fst (snd r)) acc
         else acc)
      ESet.empty (inst_dxt I).

  Lemma mem_depextsOf : forall sigma I S e,
      ESet.In e (depextsOf sigma I S) <->
      exists p c, PkgSet.In p S /\ In (p, (e, c)) (inst_dxt I) /\
                  defTrue sigma c = true.
  Proof.
    intros sigma I S e; unfold depextsOf.
    induction (inst_dxt I) as [| [p [e' c]] l IH];
      cbn [List.fold_right fst snd].
    - split.
      + intro H; apply ESet.empty_spec in H; destruct H.
      + intros [q [c [_ [[] _]]]].
    - destruct (andb (PkgSet.mem p S) (defTrue sigma c)) eqn:Hc.
      + rewrite ESet.add_spec, IH; split.
        * intros [-> | [q [c' [Hq [Hin Hg]]]]].
          -- apply Bool.andb_true_iff in Hc; destruct Hc as [Hm Hg].
             exists p, c; split;
               [apply PkgSet.mem_spec; exact Hm
               | split; [left; reflexivity | exact Hg]].
          -- exists q, c'; split;
               [exact Hq | split; [right; exact Hin | exact Hg]].
        * intros [q [c' [Hq [[Heq | Hin] Hg]]]].
          -- injection Heq as <- <- <-; left; reflexivity.
          -- right; exists q, c'; repeat split; assumption.
      + rewrite IH; split.
        * intros [q [c' [Hq [Hin Hg]]]].
          exists q, c'; split;
            [exact Hq | split; [right; exact Hin | exact Hg]].
        * intros [q [c' [Hq [[Heq | Hin] Hg]]]].
          -- injection Heq as <- <- <-.
             apply Bool.andb_false_iff in Hc; destruct Hc as [Hm | Hg'].
             ++ apply PkgSet.mem_spec in Hq; rewrite Hq in Hm; discriminate.
             ++ rewrite Hg in Hg'; discriminate.
          -- exists q, c'; repeat split; assumption.
  Qed.

  Module Reduction.
    Module NF := UOTCompareFacts N.
    Module VF' := UOTCompareFacts V.
    #[local] Hint Rewrite NF.compare_eq_iff VF'.compare_eq_iff : cmp_opam.
    #[local] Hint Extern 1 => cmp_by NF.compare_antisym : cmp_opam.
    #[local] Hint Extern 1 => cmp_by VF'.compare_antisym : cmp_opam.
    #[local] Hint Extern 1 => cmp_by NF.compare_lt_trans : cmp_opam.
    #[local] Hint Extern 1 => cmp_by VF'.compare_lt_trans : cmp_opam.

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

    Definition pinOKb (Pins : PkgSet.t) (p : Pkg.t) : bool :=
      PkgSet.for_all
        (fun '(m, w) =>
           if N.eq_dec m (fst p)
           then if V.eq_dec w (snd p) then true else false
           else true)
        Pins.

    Definition availb (sigma : Valuation) (avl : list (Pkg.t * Filter))
        (p : Pkg.t) : bool :=
      forallb
        (fun '(q, c) => if Pkg.eq_dec q p then defTrue sigma c else true)
        avl.

    Definition effRepo (sigma : Valuation) (I : Inst) : PkgSet.t :=
      PkgSet.filter
        (fun p => andb (pinOKb (inst_pins I) p) (availb sigma (inst_avl I) p))
        (inst_repo I).

    Definition PTrue : PF.Formula :=
      PF.FDep TName.Root (PF.VSet.singleton TVer.UnitV).

    Definition srcVersions (sigma : Valuation) (I : Inst) (n : N.t)
      : VSet.t :=
      C.versions (effRepo sigma I) n.

    Definition versSetBy (Vq : N.t -> VSet.t) (n : N.t) (phi : VConstraint)
      : PF.VSet.t :=
      SOvv.map TVer.RV (VSet.filter (fun v => vcHolds phi v) (Vq n)).

    Fixpoint encR (Vq : N.t -> VSet.t) (g : RFormula) : PF.Formula :=
      match g with
      | RAtom n phi => PF.FDep (TName.Real n) (versSetBy Vq n phi)
      | RAnd a b => PF.FConj (encR Vq a) (encR Vq b)
      | ROr a b => PF.FDisj (encR Vq b) (encR Vq a)
      end.

    Definition encodeOF (sigma : Valuation) (Vq : N.t -> VSet.t)
        (d : OFormula) : PF.Formula :=
      match redOF sigma d with
      | Some g => encR Vq g
      | None => PTrue
      end.

    Definition confVS (Vq : N.t -> VSet.t) (p : Pkg.t) (n : N.t)
        (phi : VConstraint) : PF.VSet.t :=
      if N.eq_dec (fst p) n then PF.VSet.empty else versSetBy Vq n phi.

    Module FSet := FSetUOT PF.Dependees.
    Module NSet := C.NSet.

    Definition ownb {A : Type} (p : Pkg.t) (r : Pkg.t * A) : bool :=
      if Pkg.eq_dec (fst r) p then true else false.

    Definition ownedBy {A : Type} (p : Pkg.t) (l : list (Pkg.t * A))
      : list A :=
      List.map snd (List.filter (ownb p) l).

    Definition depForms (sigma : Valuation) (Vq : N.t -> VSet.t) (I : Inst)
        (p : Pkg.t) : list PF.Formula :=
      List.map (encodeOF sigma Vq) (ownedBy p (inst_dep I)).

    Definition cflForm (sigma : Valuation) (Vq : N.t -> VSet.t) (p : Pkg.t)
        (nc : N.t * (Filter * VConstraint)) : PF.Formula :=
      if defTrue sigma (fst (snd nc))
      then
        PF.FNeg
          (PF.FDep (TName.Real (fst nc))
             (confVS Vq p (fst nc) (snd (snd nc))))
      else PTrue.

    Definition cflForms (sigma : Valuation) (Vq : N.t -> VSet.t) (I : Inst)
        (p : Pkg.t) : list PF.Formula :=
      List.map (cflForm sigma Vq p) (ownedBy p (inst_cfl I)).

    Module SOcf := SetOps ClsElt PF.Dependees ClsRel FSet.
    Definition clsForms (cls : ClsRel.t) (p : Pkg.t) : FSet.t :=
      SOcf.filterMap
        (fun '(q, k) =>
           if Pkg.eq_dec q p
           then Some (PF.FDep (TName.Cls k)
                        (PF.VSet.singleton (TVer.NV (fst p))))
           else None)
        cls.

    Module SOcp := SetOps ClsElt PF.Pkg ClsRel PF.PkgSet.
    Definition clsPkg (qk : ClsElt.t) : PF.Pkg.t :=
      (TName.Cls (snd qk), TVer.NV (fst (fst qk))).

    Definition clsPkgs (cls : ClsRel.t) : PF.PkgSet.t :=
      SOcp.map clsPkg cls.

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
      if PkgSet.mem p (inst_pins I)
      then List.map (pindForm Vq) (ownedBy p (inst_pind I))
      else nil.

    Definition rootForm (sigma : Valuation) (Vq : N.t -> VSet.t) (I : Inst)
      : PF.Formula :=
      PF.FConj (encodeOF sigma Vq (inst_query I))
        (encodeOF sigma Vq (inst_inv I)).

    Module SOlf := SetOps Pkg PF.Dependees PkgSet FSet.

    Definition dependeesBy (sigma : Valuation) (Vq : N.t -> VSet.t)
        (I : Inst) (q : PF.Pkg.t) : FSet.t :=
      match q with
      | (TName.Real n, TVer.RV v) =>
          FSet.union (SOlf.ofList (depForms sigma Vq I (n, v)))
            (FSet.union (SOlf.ofList (cflForms sigma Vq I (n, v)))
               (FSet.union (clsForms (inst_cls I) (n, v))
                  (SOlf.ofList (pindForms Vq I (n, v)))))
      | (TName.Root, TVer.UnitV) => FSet.singleton (rootForm sigma Vq I)
      | _ => FSet.empty
      end.

    Definition dependees (sigma : Valuation) (I : Inst) (q : PF.Pkg.t)
      : FSet.t :=
      let R := effRepo sigma I in dependeesBy sigma (C.versions R) I q.

    Definition versions (sigma : Valuation) (I : Inst) (m : TName.t)
      : PF.VSet.t :=
      match m with
      | TName.Root => PF.VSet.singleton TVer.UnitV
      | TName.Real n => SOvv.map TVer.RV (srcVersions sigma I n)
      | TName.Cls k => clsVersions (inst_cls I) k
      end.

    Definition reduceReal (sigma : Valuation) (I : Inst) : PF.PkgSet.t :=
      PF.PkgSet.union (embedSet (effRepo sigma I))
        (PF.PkgSet.union (PF.PkgSet.singleton rootPkg)
           (clsPkgs (inst_cls I))).

    Module SOfd := SetOps PF.Dependees PF.DepElt FSet PF.DepRel.
    Definition depEdges (q : PF.Pkg.t) (psis : FSet.t) : PF.DepRel.t :=
      SOfd.map (fun psi => (q, psi)) psis.

    Module SOqd := SetOps PF.Pkg PF.DepElt PF.PkgSet PF.DepRel.
    Definition reduceDeps (sigma : Valuation) (I : Inst) : PF.DepRel.t :=
      SOqd.unionMap (fun q => depEdges q (dependees sigma I q))
        (reduceReal sigma I).

    Definition clsSel (cls : ClsRel.t) (S : PkgSet.t) : PF.PkgSet.t :=
      SOcp.map clsPkg (ClsRel.filter (fun qk => PkgSet.mem (fst qk) S) cls).

    Definition coreResolution (cls : ClsRel.t) (S : PkgSet.t) : PF.PkgSet.t :=
      PF.PkgSet.union (embedSet S)
        (PF.PkgSet.union (PF.PkgSet.singleton rootPkg) (clsSel cls S)).

    Module SOtp := SetOps PF.Pkg Pkg PF.PkgSet PkgSet.
    Definition tryInvPkg (q : PF.Pkg.t) : option Pkg.t :=
      match q with
      | (TName.Real n, TVer.RV v) => Some (n, v)
      | _ => None
      end.

    Definition opamResolution (S' : PF.PkgSet.t) : PkgSet.t :=
      SOtp.filterMap tryInvPkg S'.

    Lemma mem_versSetBy : forall Vq n phi u,
        PF.VSet.In u (versSetBy Vq n phi) <->
        exists v, u = TVer.RV v /\ VSet.In v (Vq n) /\
                  vcHolds phi v = true.
    Proof.
      intros Vq n phi u; unfold versSetBy; rewrite SOvv.mem_map.
      split.
      - intros [v [Hv ->]]; apply VSet.filter_spec' in Hv;
          destruct Hv as [Hv Hh].
        exists v; split; [reflexivity | split; [exact Hv | exact Hh]].
      - intros [v [-> [Hm Hh]]]; exists v; split; [| reflexivity].
        apply VSet.filter_spec'; split; [exact Hm | exact Hh].
    Qed.

    Lemma mem_srcVersions : forall sigma I n v,
        VSet.In v (srcVersions sigma I n) <->
        PkgSet.In (n, v) (effRepo sigma I).
    Proof. intros; unfold srcVersions; apply C.mem_versions. Qed.

    Lemma mem_opamResolution : forall S' n v,
        PkgSet.In (n, v) (opamResolution S') <->
        PF.PkgSet.In (TName.Real n, TVer.RV v) S'.
    Proof.
      intros S' n v; unfold opamResolution; rewrite SOtp.mem_filterMap.
      split.
      - intros [[o u] [Hm Hf]];
          destruct o as [| m | k]; destruct u as [w | | m'];
          simpl in Hf; try discriminate.
        injection Hf as -> ->; exact Hm.
      - intro H; exists (TName.Real n, TVer.RV v); split;
          [exact H | reflexivity].
    Qed.

    Lemma mem_clsPkgs : forall cls q,
        PF.PkgSet.In q (clsPkgs cls) <->
        exists n v k, ClsRel.In ((n, v), k) cls /\
                      q = (TName.Cls k, TVer.NV n).
    Proof.
      intros cls q; unfold clsPkgs; rewrite SOcp.mem_map; split.
      - intros [[[n v] k] [Hm ->]]; exists n, v, k; split;
          [exact Hm | reflexivity].
      - intros [n [v [k [Hm ->]]]]; exists ((n, v), k); split;
          [exact Hm | reflexivity].
    Qed.

    Lemma mem_clsSel : forall cls S q,
        PF.PkgSet.In q (clsSel cls S) <->
        exists n v k, PkgSet.In (n, v) S /\ ClsRel.In ((n, v), k) cls /\
                      q = (TName.Cls k, TVer.NV n).
    Proof.
      intros cls S q; unfold clsSel; rewrite SOcp.mem_map; split.
      - intros [[[n v] k] [Hm ->]]; apply ClsRel.filter_spec' in Hm;
          destruct Hm as [Hm Hs]; simpl in Hs.
        exists n, v, k; split;
          [apply PkgSet.mem_spec; exact Hs
          | split; [exact Hm | reflexivity]].
      - intros [n [v [k [Hs [Hm ->]]]]]; exists ((n, v), k); split;
          [| reflexivity].
        apply ClsRel.filter_spec'; split;
          [exact Hm | simpl; apply PkgSet.mem_spec; exact Hs].
    Qed.

    Lemma mem_clsVersions : forall cls k w,
        PF.VSet.In w (clsVersions cls k) <->
        exists n v, ClsRel.In ((n, v), k) cls /\ w = TVer.NV n.
    Proof.
      intros cls k w; unfold clsVersions; rewrite SOcv.mem_filterMap.
      split.
      - intros [[[n v] k'] [Hm Hf]]; cbn beta iota in Hf.
        destruct (N.eq_dec k' k) as [-> |]; [| discriminate].
        injection Hf as <-; exists n, v; split; [exact Hm | reflexivity].
      - intros [n [v [Hm ->]]]; exists ((n, v), k); split; [exact Hm |].
        cbn beta iota; rewrite dec_refl; reflexivity.
    Qed.

    Definition PinOK (Pins : PkgSet.t) (p : Pkg.t) : Prop :=
      forall m w, PkgSet.In (m, w) Pins -> m = fst p -> w = snd p.

    Lemma mem_effRepo : forall sigma I p,
        PkgSet.In p (effRepo sigma I) <->
        PkgSet.In p (inst_repo I) /\ PinOK (inst_pins I) p /\
        availOK sigma I p.
    Proof.
      intros sigma I p; unfold effRepo; rewrite PkgSet.filter_spec'.
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
        + intros c Hg.
          rewrite List.forallb_forall in Hav.
          specialize (Hav _ Hg); simpl in Hav; rewrite dec_refl in Hav.
          exact Hav.
      - intros [Hr [Hpin Hav]]; split; [exact Hr |]; split.
        + intros [m w] Hm; simpl.
          destruct (N.eq_dec m (fst p)) as [E | _]; [| reflexivity].
          destruct (V.eq_dec w (snd p)) as [_ | NE]; [reflexivity |].
          contradiction NE; exact (Hpin _ _ Hm E).
        + rewrite List.forallb_forall; intros [q c] Hg; simpl.
          destruct (Pkg.eq_dec q p) as [-> |]; [| reflexivity].
          exact (Hav _ Hg).
    Qed.

    Lemma mem_reduceReal : forall sigma I q,
        PF.PkgSet.In q (reduceReal sigma I) <->
        (exists p, PkgSet.In p (effRepo sigma I) /\ q = embedPkg p) \/
        q = rootPkg \/
        (exists n v k, ClsRel.In ((n, v), k) (inst_cls I) /\
                       q = (TName.Cls k, TVer.NV n)).
    Proof.
      intros sigma I q; unfold reduceReal, embedSet.
      rewrite !PF.PkgSet.union_spec, PF.PkgSet.singleton_spec,
        SOpt.mem_map, mem_clsPkgs.
      tauto.
    Qed.

    Lemma mem_coreResolution : forall cls S q,
        PF.PkgSet.In q (coreResolution cls S) <->
        (exists p, PkgSet.In p S /\ q = embedPkg p) \/ q = rootPkg \/
        (exists n v k, PkgSet.In (n, v) S /\ ClsRel.In ((n, v), k) cls /\
                       q = (TName.Cls k, TVer.NV n)).
    Proof.
      intros cls S q; unfold coreResolution, embedSet.
      rewrite !PF.PkgSet.union_spec, PF.PkgSet.singleton_spec,
        SOpt.mem_map, mem_clsSel.
      tauto.
    Qed.

    Lemma mem_coreResolution_real : forall cls S n v,
        PF.PkgSet.In (TName.Real n, TVer.RV v) (coreResolution cls S) <->
        PkgSet.In (n, v) S.
    Proof.
      intros cls S n v; rewrite mem_coreResolution; split.
      - intros [[p [Hp He]] | [He | [n' [v' [k [_ [_ He]]]]]]];
          try discriminate.
        destruct p as [m w]; unfold embedPkg in He; simpl in He.
        injection He as -> ->; exact Hp.
      - intro H; left; exists (n, v); split; [exact H | reflexivity].
    Qed.

    Theorem opam_retraction : forall cls S,
        opamResolution (coreResolution cls S) = S.
    Proof.
      intros cls S; apply PkgSet.ext; intros [n v].
      rewrite mem_opamResolution, mem_coreResolution_real; reflexivity.
    Qed.

    (* Each of the core's names draws its versions from one branch of
       coreResolution, so version uniqueness splits three ways rather than
       nine. *)
    Lemma coreResolution_at_root : forall cls S v,
        PF.PkgSet.In (TName.Root, v) (coreResolution cls S) -> v = TVer.UnitV.
    Proof.
      intros cls S v H; apply mem_coreResolution in H.
      destruct H as [[[m w] [_ He]] | [He | [n [v' [k [_ [_ He]]]]]]];
        unfold embedPkg, rootPkg in He; try discriminate.
      injection He as ->; reflexivity.
    Qed.

    Lemma coreResolution_at_real : forall cls S n u,
        PF.PkgSet.In (TName.Real n, u) (coreResolution cls S) ->
        exists v, u = TVer.RV v /\ PkgSet.In (n, v) S.
    Proof.
      intros cls S n u H; apply mem_coreResolution in H.
      destruct H as [[[m w] [Hp He]] | [He | [n' [v' [k [_ [_ He]]]]]]];
        unfold embedPkg, rootPkg in He; cbn [fst snd] in He;
        try discriminate.
      injection He as -> ->; exists w; split; [reflexivity | exact Hp].
    Qed.

    Lemma coreResolution_at_cls : forall cls S k w,
        PF.PkgSet.In (TName.Cls k, w) (coreResolution cls S) ->
        exists n v, w = TVer.NV n /\ PkgSet.In (n, v) S /\
                    ClsRel.In ((n, v), k) cls.
    Proof.
      intros cls S k w H; apply mem_coreResolution in H.
      destruct H as [[[m u] [_ He]] | [He | [n [v [k' [Hp [Hpk He]]]]]]];
        unfold embedPkg, rootPkg in He; cbn [fst snd] in He;
        try discriminate.
      injection He as -> ->; exists n, v; split;
        [reflexivity | split; [exact Hp | exact Hpk]].
    Qed.

    Lemma PTrue_sat : forall S',
        PF.PkgSet.In rootPkg S' -> PF.Satisfies S' PTrue.
    Proof.
      intros S' Hr; exists TVer.UnitV; split;
        [apply PF.VSet.singleton_spec; reflexivity | exact Hr].
    Qed.

    Lemma encR_correct : forall Vq S',
        (forall n v,
            PkgSet.In (n, v) (opamResolution S') -> VSet.In v (Vq n)) ->
        forall g, PF.Satisfies S' (encR Vq g) <-> rSat (opamResolution S') g.
    Proof.
      intros Vq S' HV.
      induction g as [n phi | a IHa b IHb | a IHa b IHb]; simpl.
      - split.
        + intros [u [Hu Hm]].
          apply mem_versSetBy in Hu; destruct Hu as [v [-> [_ Hh]]].
          exists v; split; [apply mem_opamResolution; exact Hm | exact Hh].
        + intros [v [Hv Hh]].
          assert (Hvq := HV _ _ Hv).
          apply mem_opamResolution in Hv.
          exists (TVer.RV v); split; [| exact Hv].
          apply mem_versSetBy; exists v; split;
            [reflexivity | split; [exact Hvq | exact Hh]].
      - rewrite IHa, IHb; reflexivity.
      - rewrite IHa, IHb; tauto.
    Qed.

    Lemma encodeOF_correct : forall sigma Vq S',
        (forall n v,
            PkgSet.In (n, v) (opamResolution S') -> VSet.In v (Vq n)) ->
        PF.PkgSet.In rootPkg S' ->
        forall d,
          PF.Satisfies S' (encodeOF sigma Vq d) <->
          oSat sigma (opamResolution S') d.
    Proof.
      intros sigma Vq S' HV Hr d; unfold encodeOF, oSat.
      destruct (redOF sigma d) as [g |] eqn:Hred.
      - rewrite (encR_correct Vq S' HV g); split.
        + intros H g' Hg'; injection Hg' as <-; exact H.
        + intro H; apply H; reflexivity.
      - split; [intros _ g' Hg'; discriminate |].
        intros _; exact (PTrue_sat S' Hr).
    Qed.

    Lemma ownedBy_in : forall (A : Type) (p : Pkg.t)
        (l : list (Pkg.t * A)) (a : A),
        In a (ownedBy p l) <-> In (p, a) l.
    Proof.
      intros A p l a; unfold ownedBy, ownb.
      rewrite List.in_map_iff; split.
      - intros [[q b] [Hb Hf]]; simpl in Hb; subst b.
        apply List.filter_In in Hf; destruct Hf as [Hin Ht];
          simpl in Ht.
        destruct (Pkg.eq_dec q p) as [-> |]; [exact Hin | discriminate].
      - intro H; exists (p, a); split; [reflexivity |].
        apply List.filter_In; split; [exact H | simpl; apply dec_refl].
    Qed.

    Lemma in_pindForms : forall Vq I p psi,
        In psi (pindForms Vq I p) <->
        PkgSet.In p (inst_pins I) /\
        exists nvu, In (p, nvu) (inst_pind I) /\ psi = pindForm Vq nvu.
    Proof.
      intros Vq I p psi; unfold pindForms.
      destruct (PkgSet.mem p (inst_pins I)) eqn:Hm.
      - apply PkgSet.mem_spec in Hm.
        rewrite List.in_map_iff; split.
        + intros [nvu [<- Hin]]; split; [exact Hm |].
          exists nvu; split; [apply ownedBy_in; exact Hin | reflexivity].
        + intros [_ [nvu [Hin ->]]]; exists nvu; split;
            [reflexivity | apply ownedBy_in; exact Hin].
      - split; [intros [] |].
        intros [Hp _]; apply PkgSet.mem_spec in Hp; rewrite Hp in Hm;
          discriminate.
    Qed.

    Lemma mem_dependees_real : forall sigma Vq I n v psi,
        FSet.In psi (dependeesBy sigma Vq I (TName.Real n, TVer.RV v)) <->
        (exists d, In ((n, v), d) (inst_dep I) /\
                    psi = encodeOF sigma Vq d) \/
        (exists nc, In ((n, v), nc) (inst_cfl I) /\
                    psi = cflForm sigma Vq (n, v) nc) \/
        (exists k, ClsRel.In ((n, v), k) (inst_cls I) /\
                   psi = PF.FDep (TName.Cls k)
                         (PF.VSet.singleton (TVer.NV n))) \/
        (PkgSet.In (n, v) (inst_pins I) /\
         exists nvu, In ((n, v), nvu) (inst_pind I) /\
                     psi = pindForm Vq nvu).
    Proof.
      intros sigma Vq I n v psi; simpl.
      rewrite !FSet.union_spec, !SOlf.mem_ofList, in_pindForms.
      unfold depForms, cflForms.
      rewrite !List.in_map_iff.
      unfold clsForms; rewrite SOcf.mem_filterMap.
      split.
      - intros [H | [H | [H | H]]].
        + destruct H as [d [He Hf0]]; apply ownedBy_in in Hf0.
          left; exists d; auto.
        + destruct H as [nc [He Hnc]]; apply ownedBy_in in Hnc.
          right; left; exists nc; auto.
        + destruct H as [[q k] [Hq He]]; cbn beta iota in He.
          destruct (Pkg.eq_dec q (n, v)) as [-> |]; [| discriminate He].
          mem_destruct; right; right; left; exists k; auto.
        + right; right; right; exact H.
      - intros [H | [H | [H | H]]].
        + destruct H as [d [Hin ->]].
          left; exists d; split;
            [reflexivity | apply ownedBy_in; exact Hin].
        + destruct H as [nc [Hin ->]].
          right; left; exists nc; split;
            [reflexivity | apply ownedBy_in; exact Hin].
        + destruct H as [k [Hp ->]].
          right; right; left; exists ((n, v), k); split; [exact Hp |].
          cbn beta iota; rewrite dec_refl; reflexivity.
        + right; right; right; exact H.
    Qed.

    Lemma mem_reduceDeps : forall sigma I q psi,
        PF.DepRel.In (q, psi) (reduceDeps sigma I) <->
        PF.PkgSet.In q (reduceReal sigma I) /\
        FSet.In psi (dependees sigma I q).
    Proof.
      intros sigma I q psi; unfold reduceDeps; rewrite SOqd.mem_unionMap.
      split.
      - intros [q0 [Hq0 Hf]]; unfold depEdges in Hf.
        apply SOfd.mem_map in Hf; mem_destruct; split; assumption.
      - intros [Hq Hf]; exists q; split; [exact Hq |].
        unfold depEdges; apply SOfd.mem_map; exists psi; split;
          [exact Hf | reflexivity].
    Qed.

    Lemma res_sub_eff : forall sigma I S,
        IsResolution sigma I S -> PkgSet.Subset S (effRepo sigma I).
    Proof.
      intros sigma I S HR [n v] Hp; apply mem_effRepo.
      split; [exact (res_subset _ _ _ HR _ Hp) |].
      split.
      - intros m w Hm Hn; simpl in Hn; subst m.
        symmetry; exact (res_pins _ _ _ HR _ _ Hm _ Hp).
      - exact (res_available _ _ _ HR _ Hp).
    Qed.

    Theorem opam_soundness : forall sigma I S',
        PF.IsResolution (reduceReal sigma I) (reduceDeps sigma I) rootPkg S' ->
        IsResolution sigma I (opamResolution S').
    Proof.
      intros sigma I S' HR.
      assert (Hsub : forall n v,
                 PkgSet.In (n, v) (opamResolution S') ->
                 PkgSet.In (n, v) (effRepo sigma I)).
      { intros n v Hnv; apply mem_opamResolution in Hnv.
        apply (PF.res_subset _ _ _ _ HR) in Hnv.
        apply mem_reduceReal in Hnv.
        destruct Hnv as [[p [Hp He]] | [He | [n' [v' [k [_ He]]]]]];
          try discriminate.
        destruct p as [m w]; unfold embedPkg in He; simpl in He.
        injection He as -> ->; exact Hp. }
      assert (HV : forall n v,
                 PkgSet.In (n, v) (opamResolution S') ->
                 VSet.In v (srcVersions sigma I n)).
      { intros n v Hnv; apply mem_srcVersions, Hsub; exact Hnv. }
      assert (Hemb : forall n v,
                 PkgSet.In (n, v) (opamResolution S') ->
                 PF.PkgSet.In (embedPkg (n, v)) S').
      { intros n v Hnv; apply mem_opamResolution in Hnv; exact Hnv. }
      assert (Hroot := PF.res_root_mem _ _ _ _ HR).
      assert (HrootR : PF.PkgSet.In rootPkg (reduceReal sigma I)).
      { apply mem_reduceReal; right; left; reflexivity. }
      assert (Hdep : PF.DepRel.In (rootPkg, rootForm sigma
                       (srcVersions sigma I) I) (reduceDeps sigma I)).
      { apply mem_reduceDeps; split; [exact HrootR |].
        unfold dependees, dependeesBy, rootPkg.
        apply FSet.singleton_spec; reflexivity. }
      assert (Hrootdep :=
                PF.res_formula_closure _ _ _ _ HR _ Hroot _ Hdep).
      unfold rootForm in Hrootdep; cbn [PF.Satisfies] in Hrootdep.
      destruct Hrootdep as [Hquery Hinv].
      assert (Hdeps : forall n v psi,
                 PkgSet.In (n, v) (opamResolution S') ->
                 FSet.In psi (dependees sigma I (embedPkg (n, v))) ->
                 PF.Satisfies S' psi).
      { intros n v psi Hnv Hf.
        apply (PF.res_formula_closure _ _ _ _ HR _ (Hemb _ _ Hnv)).
        apply mem_reduceDeps; split; [| exact Hf].
        apply mem_reduceReal; left; exists (n, v); split;
          [exact (Hsub _ _ Hnv) | reflexivity]. }
      constructor.
      - intros [n v] Hp.
        assert (H := Hsub _ _ Hp); apply mem_effRepo in H; tauto.
      - intros n v v' Hv Hv'.
        apply mem_opamResolution in Hv, Hv'.
        assert (E := PF.res_version_unique _ _ _ _ HR
                       (TName.Real n) _ _ Hv Hv').
        injection E as ->; reflexivity.
      - intros [n v] Hp.
        assert (H := Hsub _ _ Hp); apply mem_effRepo in H; tauto.
      - split; apply (encodeOF_correct sigma _ _ HV Hroot);
          [exact Hquery | exact Hinv].
      - intros [n v] Hp d Hf.
        assert (Hs : PF.Satisfies S'
                       (encodeOF sigma (srcVersions sigma I) d)).
        { apply (Hdeps _ _ _ Hp); unfold dependees.
          apply mem_dependees_real; left; exists d; auto. }
        apply (encodeOF_correct sigma _ _ HV Hroot) in Hs; exact Hs.
      - intros pn pv Hp n c phi Hcfl Hg [v [Hv [Hne Hh]]].
        assert (Hs : PF.Satisfies S'
                       (cflForm sigma (srcVersions sigma I) (pn, pv)
                          (n, (c, phi)))).
        { apply (Hdeps _ _ _ Hp); unfold dependees.
          apply mem_dependees_real; right; left.
          exists (n, (c, phi)); auto. }
        unfold cflForm in Hs; cbn [fst snd] in Hs; rewrite Hg in Hs.
        cbn [PF.Satisfies] in Hs; apply Hs; clear Hs.
        exists (TVer.RV v); split; [| apply mem_opamResolution; exact Hv].
        unfold confVS.
        destruct (N.eq_dec (fst (pn, pv)) n) as [E | _];
          [contradiction Hne; symmetry; exact E |].
        apply mem_versSetBy; exists v; split;
          [reflexivity
          | split; [exact (HV _ _ Hv) | exact Hh]].
      - intros k [pn pv] [qn qv] Hp Hq Hpk Hqk.
        assert (Hcl : forall m w,
                   PkgSet.In (m, w) (opamResolution S') ->
                   ClsRel.In ((m, w), k) (inst_cls I) ->
                   PF.PkgSet.In (TName.Cls k, TVer.NV m) S').
        { intros m w Hm Hmk.
          assert (Hs : PF.Satisfies S'
                         (PF.FDep (TName.Cls k)
                            (PF.VSet.singleton (TVer.NV m)))).
          { apply (Hdeps _ _ _ Hm); unfold dependees.
            apply mem_dependees_real; right; right; left.
            exists k; split; [exact Hmk | reflexivity]. }
          destruct Hs as [v [Hv Hin]].
          apply PF.VSet.singleton_spec in Hv; subst v; exact Hin. }
        assert (E := PF.res_version_unique _ _ _ _ HR (TName.Cls k)
                       _ _ (Hcl _ _ Hp Hpk) (Hcl _ _ Hq Hqk)).
        injection E as ->.
        apply mem_opamResolution in Hp, Hq.
        assert (E := PF.res_version_unique _ _ _ _ HR
                       (TName.Real qn) _ _ Hp Hq).
        injection E as ->; reflexivity.
      - intros n v Hpin v' Hv'.
        assert (H := Hsub _ _ Hv'); apply mem_effRepo in H.
        destruct H as [_ [Hp _]]; symmetry.
        exact (Hp _ _ Hpin eq_refl).
      - intros [pn pv] Hp Hpin n v u Hpind v' Hv'.
        assert (Hs : PF.Satisfies S'
                       (pindForm (srcVersions sigma I) ((n, v), u))).
        { apply (Hdeps _ _ _ Hp); unfold dependees.
          apply mem_dependees_real; right; right; right.
          split; [exact Hpin | exists ((n, v), u); auto]. }
        unfold pindForm in Hs; simpl in Hs.
        destruct (V.eq_dec v' v) as [E | NE]; [exact E |].
        exfalso; apply Hs.
        exists (TVer.RV v'); split;
          [| apply mem_opamResolution; exact Hv'].
        apply SOvv.mem_map; exists v'; split; [| reflexivity].
        apply VSet.remove_spec; split;
          [exact (HV _ _ Hv') | exact NE].
    Qed.

    Theorem opam_completeness : forall sigma I S,
        IsResolution sigma I S ->
        PF.IsResolution (reduceReal sigma I) (reduceDeps sigma I) rootPkg
          (coreResolution (inst_cls I) S).
    Proof.
      intros sigma I S HR.
      assert (Hse := res_sub_eff _ _ _ HR).
      assert (HV : forall n v,
                 PkgSet.In (n, v)
                   (opamResolution (coreResolution (inst_cls I) S)) ->
                 VSet.In v (srcVersions sigma I n)).
      { intros n v Hm; rewrite opam_retraction in Hm.
        apply mem_srcVersions; exact (Hse _ Hm). }
      assert (Hr : PF.PkgSet.In rootPkg (coreResolution (inst_cls I) S))
        by (apply mem_coreResolution; right; left; reflexivity).
      constructor.
      - intros q Hq; apply mem_coreResolution in Hq; apply mem_reduceReal.
        destruct Hq as [[p [Hp ->]] | [H | [n [v [k [_ [Hpk ->]]]]]]];
          [| tauto |].
        + left; exists p; split; [exact (Hse _ Hp) | reflexivity].
        + right; right; exists n, v, k; split; [exact Hpk | reflexivity].
      - apply mem_coreResolution; right; left; reflexivity.
      - intros p' Hp' psi' Hf'.
        apply mem_reduceDeps in Hf'; destruct Hf' as [_ Hf'].
        apply mem_coreResolution in Hp'.
        destruct Hp' as [[[pn pv] [Hp0 ->]] | [-> | [n [v [k [_ [_ ->]]]]]]].
        + unfold dependees in Hf'.
          apply mem_dependees_real in Hf'.
          destruct Hf'
            as [[d [Hin ->]] | [[nc [Hin ->]]
               | [[k [Hpk ->]] | [Hpin [nvu [Hin ->]]]]]].
          * apply (encodeOF_correct sigma _ _ HV Hr).
            rewrite opam_retraction.
            exact (res_dep_closure _ _ _ HR _ Hp0 _ Hin).
          * destruct nc as [n [c phi]]; unfold cflForm; cbn [fst snd].
            destruct (defTrue sigma c) eqn:Hg;
              [| exact (PTrue_sat (coreResolution (inst_cls I) S) Hr)].
            cbn [PF.Satisfies]; intros [u [Hu Hm]].
            unfold confVS in Hu.
            destruct (N.eq_dec (fst (pn, pv)) n) as [| Hne].
            { destruct (PF.VSet.empty_spec Hu). }
            apply mem_versSetBy in Hu;
              destruct Hu as [v [-> [Hra Hh]]].
            apply mem_coreResolution_real in Hm.
            exact (res_conflict_avoidance _ _ _ HR _ _ Hp0 _ _ _ Hin Hg
                     (ex_intro _ v
                        (conj Hm (conj (fun E => Hne (eq_sym E)) Hh)))).
          * cbn [PF.Satisfies].
            exists (TVer.NV pn); split;
              [apply PF.VSet.singleton_spec; reflexivity |].
            apply mem_coreResolution; right; right.
            exists pn, pv, k; split;
              [exact Hp0 | split; [exact Hpk | reflexivity]].
          * destruct nvu as [[n v] u]; unfold pindForm; simpl.
            intros [w [Hw Hm]].
            apply SOvv.mem_map in Hw; destruct Hw as [v' [Hv' ->]].
            apply VSet.remove_spec in Hv'; destruct Hv' as [_ NE].
            apply mem_coreResolution_real in Hm.
            exact (NE (res_pin_depends _ _ _ HR _ Hp0 Hpin _ _ _ Hin
                         _ Hm)).
        + unfold dependees, dependeesBy, rootPkg in Hf'.
          apply FSet.singleton_spec in Hf'; subst psi'.
          unfold rootForm; cbn [PF.Satisfies].
          split; apply (encodeOF_correct sigma _ _ HV Hr);
            rewrite opam_retraction;
            [exact (proj1 (res_request _ _ _ HR))
            | exact (proj2 (res_request _ _ _ HR))].
        + unfold dependees, dependeesBy in Hf'; cbn beta iota in Hf'.
          destruct (FSet.empty_spec Hf').
      - intros m u u' Hv Hv'; destruct m as [| n | k].
        + rewrite (coreResolution_at_root _ _ _ Hv),
            (coreResolution_at_root _ _ _ Hv'); reflexivity.
        + destruct (coreResolution_at_real _ _ _ _ Hv) as [v [-> Hp]].
          destruct (coreResolution_at_real _ _ _ _ Hv') as [w [-> Hq]].
          f_equal; exact (res_version_unique _ _ _ HR _ _ _ Hp Hq).
        + destruct (coreResolution_at_cls _ _ _ _ Hv)
            as [pn [pv [-> [Hp Hpk]]]].
          destruct (coreResolution_at_cls _ _ _ _ Hv')
            as [qn [qv [-> [Hq Hqk]]]].
          injection (res_class_exclusion _ _ _ HR _ _ _ Hp Hq Hpk Hqk)
            as -> _; reflexivity.
    Qed.

    Corollary opam_core_soundness : forall sigma I S,
        PF.Reduction.T.IsResolution
          (PF.Reduction.reduceReal (reduceReal sigma I) (reduceDeps sigma I))
          (PF.Reduction.reduceDeps (reduceReal sigma I) (reduceDeps sigma I))
          (PF.Reduction.embedPkg rootPkg) S ->
        IsResolution sigma I
          (opamResolution (PF.Reduction.packageFormulaResolution S)).
    Proof.
      intros sigma I S H.
      exact (opam_soundness sigma I _
               (PF.Reduction.package_formula_soundness _ _ _ S H)).
    Qed.

    Corollary opam_core_completeness : forall sigma I S,
        IsResolution sigma I S ->
        PF.Reduction.T.IsResolution
          (PF.Reduction.reduceReal (reduceReal sigma I) (reduceDeps sigma I))
          (PF.Reduction.reduceDeps (reduceReal sigma I) (reduceDeps sigma I))
          (PF.Reduction.embedPkg rootPkg)
          (PF.Reduction.coreResolution (reduceReal sigma I)
             (reduceDeps sigma I) (coreResolution (inst_cls I) S)).
    Proof.
      intros sigma I S H.
      exact (PF.package_formula_completeness _ _ _ _
               (opam_completeness sigma I S H)).
    Qed.

    Corollary opam_core_retraction : forall sigma I S,
        opamResolution
          (PF.Reduction.packageFormulaResolution
             (PF.Reduction.coreResolution (reduceReal sigma I)
                (reduceDeps sigma I) (coreResolution (inst_cls I) S)))
        = S.
    Proof.
      intros sigma I S; rewrite PF.Reduction.package_formula_retraction.
      apply opam_retraction.
    Qed.

    Module Lookup.
      Fixpoint ofNames (d : OFormula) : NSet.t :=
        match d with
        | OFAtom n _ _ => NSet.singleton n
        | OFAnd a b => NSet.union (ofNames a) (ofNames b)
        | OFOr a b => NSet.union (ofNames a) (ofNames b)
        end.

      Definition listNames {A : Type} (names : A -> NSet.t) (l : list A)
        : NSet.t :=
        List.fold_right (fun a acc => NSet.union (names a) acc) NSet.empty l.

      Definition declaredNames (I : Inst) (p : Pkg.t) : NSet.t :=
        NSet.union (listNames ofNames (ownedBy p (inst_dep I)))
          (NSet.union
             (listNames (fun nc => NSet.singleton (fst nc))
                (ownedBy p (inst_cfl I)))
             (listNames (fun nvu => NSet.singleton (fst (fst nvu)))
                (ownedBy p (inst_pind I)))).

      Definition clsFibre (cls : ClsRel.t) (p : Pkg.t) : ClsRel.t :=
        ClsRel.filter
          (fun qk => if Pkg.eq_dec (fst qk) p then true else false) cls.

      Definition pkgSubInst (I : Inst) (p : Pkg.t) : Inst :=
        MkInst (C.namePreimage (inst_repo I) (declaredNames I p))
          (List.filter (ownb p) (inst_dep I))
          (List.filter (ownb p) (inst_cfl I))
          (clsFibre (inst_cls I) p)
          (inst_avl I)
          (List.filter (ownb p) (inst_dxt I))
          (inst_pins I)
          (List.filter (ownb p) (inst_pind I))
          (inst_query I) (inst_inv I).

      Definition declSubInst (I : Inst) (p : Pkg.t) : Inst :=
        MkInst PkgSet.empty
          (List.filter (ownb p) (inst_dep I))
          (List.filter (ownb p) (inst_cfl I))
          (clsFibre (inst_cls I) p)
          nil
          (List.filter (ownb p) (inst_dxt I))
          (inst_pins I)
          (List.filter (ownb p) (inst_pind I))
          (inst_query I) (inst_inv I).

      Definition nameSubInst (I : Inst) (n : N.t) : Inst :=
        MkInst (C.namePreimage (inst_repo I) (NSet.singleton n))
          (inst_dep I) (inst_cfl I) (inst_cls I)
          (inst_avl I) (inst_dxt I) (inst_pins I)
          (inst_pind I) (inst_query I) (inst_inv I).

      Definition classSubInst (I : Inst) (k : N.t) : Inst :=
        MkInst PkgSet.empty nil nil
          (Cls.Reduction.Lookup.classRelAt (inst_cls I) k)
          nil nil PkgSet.empty nil (inst_query I) (inst_inv I).

      Definition rootSubInst (I : Inst) : Inst :=
        MkInst
          (C.namePreimage (inst_repo I)
             (NSet.union (ofNames (inst_query I)) (ofNames (inst_inv I))))
          nil nil ClsRel.empty (inst_avl I) nil
          (inst_pins I) nil (inst_query I) (inst_inv I).

      Lemma srcVersions_restrict : forall sigma I ns n,
          NSet.In n ns ->
          C.versions
            (effRepo sigma
               (MkInst (C.namePreimage (inst_repo I) ns) (inst_dep I)
                  (inst_cfl I) (inst_cls I) (inst_avl I)
                  (inst_dxt I) (inst_pins I) (inst_pind I)
                  (inst_query I) (inst_inv I))) n =
          srcVersions sigma I n.
      Proof.
        intros sigma I ns n Hn; apply VSet.ext; intro v.
        rewrite C.mem_versions.
        unfold srcVersions; rewrite C.mem_versions.
        rewrite !mem_effRepo; simpl.
        rewrite C.mem_namePreimage; simpl.
        unfold PinOK, availOK; simpl; intuition.
      Qed.

      Lemma srcVersions_subInst_agree : forall sigma I sl ns n,
          inst_repo sl = C.namePreimage (inst_repo I) ns ->
          inst_avl sl = inst_avl I -> inst_pins sl = inst_pins I ->
          NSet.In n ns ->
          srcVersions sigma sl n = srcVersions sigma I n.
      Proof.
        intros sigma I sl ns n Hr Ha Hp Hn.
        unfold srcVersions at 1.
        assert (E : effRepo sigma sl =
                    effRepo sigma
                      (MkInst (C.namePreimage (inst_repo I) ns) (inst_dep I)
                         (inst_cfl I) (inst_cls I)
                         (inst_avl I) (inst_dxt I)
                         (inst_pins I) (inst_pind I) (inst_query I)
                         (inst_inv I))).
        { unfold effRepo; rewrite Hr, Ha, Hp; reflexivity. }
        rewrite E; apply (srcVersions_restrict sigma I ns n Hn).
      Qed.

      Lemma versSetBy_agree : forall Vq Vq' n phi,
          Vq n = Vq' n -> versSetBy Vq n phi = versSetBy Vq' n phi.
      Proof. intros Vq Vq' n phi H; unfold versSetBy; rewrite H;
        reflexivity. Qed.

      Lemma encR_agree : forall sigma Vq Vq' d,
          (forall n, NSet.In n (ofNames d) -> Vq n = Vq' n) ->
          forall g, redOF sigma d = Some g -> encR Vq g = encR Vq' g.
      Proof.
        intros sigma Vq Vq'.
        induction d as [n c phi | a IHa b IHb | a IHa b IHb];
          intros H g Hred; simpl in Hred.
        2,3: assert (Ha : forall m, NSet.In m (ofNames a) -> Vq m = Vq' m)
               by (intros m Hm; apply H; simpl; apply NSet.union_spec; auto);
          assert (Hb : forall m, NSet.In m (ofNames b) -> Vq m = Vq' m)
            by (intros m Hm; apply H; simpl; apply NSet.union_spec; auto);
          destruct (redOF sigma a) eqn:Ea; destruct (redOF sigma b) eqn:Eb;
            simpl in Hred; try discriminate; injection Hred as <-; simpl;
            [rewrite (IHa Ha _ eq_refl), (IHb Hb _ eq_refl); reflexivity
            | exact (IHa Ha _ eq_refl) | exact (IHb Hb _ eq_refl)].
        destruct (defTrue sigma c); [| discriminate].
        injection Hred as <-; simpl.
        rewrite (versSetBy_agree Vq Vq' n phi); [reflexivity |].
        apply H; simpl; apply NSet.singleton_spec; reflexivity.
      Qed.

      Lemma encodeOF_agree : forall sigma Vq Vq' d,
          (forall n, NSet.In n (ofNames d) -> Vq n = Vq' n) ->
          encodeOF sigma Vq d = encodeOF sigma Vq' d.
      Proof.
        intros sigma Vq Vq' d H; unfold encodeOF.
        destruct (redOF sigma d) as [g |] eqn:Hred;
          [exact (encR_agree sigma Vq Vq' d H g Hred) | reflexivity].
      Qed.

      Lemma cflForm_agree : forall sigma Vq Vq' p nc,
          Vq (fst nc) = Vq' (fst nc) ->
          cflForm sigma Vq p nc = cflForm sigma Vq' p nc.
      Proof.
        intros sigma Vq Vq' p [n [c phi]] H; unfold cflForm, confVS;
          cbn [fst snd].
        cbn [fst snd] in H.
        destruct (defTrue sigma c); [| reflexivity].
        destruct (N.eq_dec (fst p) n); [reflexivity |].
        rewrite (versSetBy_agree Vq Vq' n phi H); reflexivity.
      Qed.

      Lemma pindForm_agree : forall Vq Vq' nvu,
          Vq (fst (fst nvu)) = Vq' (fst (fst nvu)) ->
          pindForm Vq nvu = pindForm Vq' nvu.
      Proof.
        intros Vq Vq' [[n v] u] H; unfold pindForm; simpl in *.
        rewrite H; reflexivity.
      Qed.

      Lemma listNames_in : forall (A : Type) (names : A -> NSet.t) l n a,
          In a l -> NSet.In n (names a) -> NSet.In n (listNames names l).
      Proof.
        intros A names l n a; induction l as [| b l IH]; simpl;
          [intros [] |].
        intros [-> | Hin] Hn; apply NSet.union_spec;
          [left; exact Hn | right; exact (IH Hin Hn)].
      Qed.

      Lemma ownedBy_filter : forall (A : Type) p (l : list (Pkg.t * A)),
          ownedBy p (List.filter (ownb p) l) = ownedBy p l.
      Proof.
        intros A p l; unfold ownedBy; f_equal.
        induction l as [| a l IH]; simpl; [reflexivity |].
        destruct (ownb p a) eqn:E; simpl; rewrite ?E, IH; reflexivity.
      Qed.

      Theorem versions_lookupOrig : forall sigma I n,
          versions sigma I (TName.Real n) =
          versions sigma (nameSubInst I n) (TName.Real n).
      Proof.
        intros sigma I n; simpl; symmetry.
        rewrite (srcVersions_subInst_agree sigma I (nameSubInst I n)
                   (NSet.singleton n) n); try reflexivity.
        apply NSet.singleton_spec; reflexivity.
      Qed.

      Module SOcd := SetOps ClsElt Pkg ClsRel PkgSet.
      Definition declarers (cls : ClsRel.t) : PkgSet.t := SOcd.map fst cls.

      Lemma clsVersions_reduceReal : forall cls R k v,
          (forall q k', ClsRel.In (q, k') cls -> PkgSet.In q R) ->
          PF.VSet.In v (clsVersions cls k) <->
          exists n, v = TVer.NV n /\
            Cls.Reduction.T.VSet.In (Cls.Reduction.Version.Name n)
              (Cls.Reduction.T.versions (Cls.Reduction.reduceReal R cls)
                 (Cls.Reduction.Name.Cls k)).
      Proof.
        intros cls R k v HR.
        rewrite mem_clsVersions, Cls.Reduction.Lookup.versions_cls.
        split.
        - intros [n [u [Hq ->]]]; exists n; split; [reflexivity |].
          apply Cls.Reduction.Lookup.SOpv.mem_map; exists (n, u); split;
            [apply Cls.Reduction.Lookup.mem_inClass; split;
               [exact (HR _ _ Hq) | exact Hq]
            | reflexivity].
        - intros [n [-> Hn]]; apply Cls.Reduction.Lookup.SOpv.mem_map in Hn.
          destruct Hn as [[m u] [Hq E]]; injection E as ->.
          apply Cls.Reduction.Lookup.mem_inClass in Hq.
          exists m, u; split; [exact (proj2 Hq) | reflexivity].
      Qed.

      Theorem versions_lookupClass : forall sigma I k,
          versions sigma I (TName.Cls k) =
          versions sigma (classSubInst I k) (TName.Cls k).
      Proof.
        intros sigma I k; symmetry; cbn [versions classSubInst inst_cls].
        assert (HD : forall q k', ClsRel.In (q, k') (inst_cls I) ->
                       PkgSet.In q (declarers (inst_cls I)))
          by (intros q k' H; apply SOcd.mem_map; exists (q, k');
              split; [exact H | reflexivity]).
        apply PF.VSet.ext; intro v.
        rewrite (clsVersions_reduceReal (inst_cls I) _ _ _ HD),
          (Cls.Reduction.Lookup.versions_lookupClass (declarers (inst_cls I))).
        apply clsVersions_reduceReal; intros q k' H.
        apply Cls.Reduction.Lookup.mem_classRelAt in H; destruct H as [H ->].
        apply Cls.Reduction.Lookup.mem_inClass; split;
          [exact (HD _ _ H) | exact H].
      Qed.

      Lemma versions_class_mono : forall sigma I' I k,
          ClsRel.Subset (inst_cls I') (inst_cls I) ->
          PF.VSet.Subset (versions sigma I' (TName.Cls k))
            (versions sigma I (TName.Cls k)).
      Proof.
        intros sigma I' I k HC v; cbn [versions]; rewrite !mem_clsVersions.
        intros [n [u [Hp ->]]]; exists n, u; split;
          [exact (HC _ Hp) | reflexivity].
      Qed.

      Theorem dependees_lookupRoot : forall sigma I,
          dependees sigma I rootPkg = dependees sigma (rootSubInst I) rootPkg.
      Proof.
        intros sigma I; symmetry; unfold dependees, dependeesBy, rootPkg, rootForm.
        assert (H : forall n,
                   NSet.In n (NSet.union (ofNames (inst_query I))
                                (ofNames (inst_inv I))) ->
                   srcVersions sigma (rootSubInst I) n = srcVersions sigma I n)
          by (intros n Hn;
              apply (srcVersions_subInst_agree sigma I (rootSubInst I)
                       (NSet.union (ofNames (inst_query I))
                          (ofNames (inst_inv I))) n);
              reflexivity || exact Hn).
        cbn [rootSubInst inst_query inst_inv].
        rewrite !(encodeOF_agree sigma (srcVersions sigma (rootSubInst I))
                    (srcVersions sigma I))
          by (intros n Hn; apply H, NSet.union_spec; auto).
        reflexivity.
      Qed.

      Theorem dependeesBy_lookupOrig : forall sigma I Vq n v,
          (forall m, NSet.In m (declaredNames I (n, v)) ->
             Vq m = srcVersions sigma (nameSubInst I m) m) ->
          dependees sigma I (embedPkg (n, v)) =
          dependeesBy sigma Vq (declSubInst I (n, v)) (embedPkg (n, v)).
      Proof.
        intros sigma I Vq n v HV; symmetry.
        assert (HVq : forall m, NSet.In m (declaredNames I (n, v)) ->
                   Vq m = srcVersions sigma I m).
        { intros m Hm; rewrite (HV m Hm).
          apply (srcVersions_subInst_agree sigma I (nameSubInst I m)
                   (NSet.singleton m) m); try reflexivity.
          apply NSet.singleton_spec; reflexivity. }
        unfold dependees, embedPkg, declaredNames in *;
          cbn [fst snd dependeesBy].
        unfold depForms, cflForms, pindForms.
        cbn [declSubInst inst_dep inst_cfl inst_cls inst_pins inst_pind].
        rewrite !ownedBy_filter.
        f_equal; [| f_equal; [| f_equal]].
        - f_equal; apply List.map_ext_in; intros psi0 Hin.
          apply encodeOF_agree; intros m Hm; apply HVq.
          apply NSet.union_spec; left; exact (listNames_in _ _ _ _ _ Hin Hm).
        - f_equal; apply List.map_ext_in; intros [m nc] Hin.
          apply cflForm_agree, HVq; rewrite !NSet.union_spec; right; left.
          apply (listNames_in _ _ _ _ _ Hin), NSet.singleton_spec; reflexivity.
        - apply FSet.ext; intro psi; apply SOcf.filterMap_restrict.
          + intros qk Hqk; apply ClsRel.filter_spec' in Hqk; apply Hqk.
          + intros [q k] Hqk Hf; apply ClsRel.filter_spec'.
            split; [exact Hqk |].
            cbn beta iota in Hf; cbn [fst].
            destruct (Pkg.eq_dec q (n, v)); [reflexivity | discriminate Hf].
        - destruct (PkgSet.mem (n, v) (inst_pins I)); [| reflexivity].
          f_equal; apply List.map_ext_in; intros nvu Hin.
          apply pindForm_agree, HVq; rewrite !NSet.union_spec; right; right.
          apply (listNames_in _ _ _ _ _ Hin), NSet.singleton_spec; reflexivity.
      Qed.

      Theorem dependees_lookupOrig : forall sigma I n v,
          dependees sigma I (embedPkg (n, v)) =
          dependees sigma (pkgSubInst I (n, v)) (embedPkg (n, v)).
      Proof.
        intros sigma I n v.
        rewrite (dependeesBy_lookupOrig sigma I
                      (srcVersions sigma (pkgSubInst I (n, v))) n v);
          [reflexivity |].
        intros m Hm.
        rewrite (srcVersions_subInst_agree sigma I (pkgSubInst I (n, v))
                   (declaredNames I (n, v)) m); try reflexivity; [| exact Hm].
        symmetry; apply (srcVersions_subInst_agree sigma I (nameSubInst I m)
                           (NSet.singleton m) m); try reflexivity.
        apply NSet.singleton_spec; reflexivity.
      Qed.

      Lemma versions_reduceReal : forall sigma I n,
          PF.C.versions (reduceReal sigma I) n = versions sigma I n.
      Proof.
        intros sigma I m; apply PF.VSet.ext; intro u.
        rewrite PF.C.mem_versions, mem_reduceReal.
        destruct m as [| n | k]; cbn [versions].
        - rewrite PF.VSet.singleton_spec; split.
          + intros [[p [_ E]] | [E | [n' [v' [k [_ E]]]]]];
              unfold embedPkg, rootPkg in E; try discriminate E.
            injection E as ->; reflexivity.
          + intros ->; right; left; reflexivity.
        - rewrite SOvv.mem_map; split.
          + intros [[[m w] [Hp E]] | [E | [n' [v' [k [_ E]]]]]];
              unfold embedPkg, rootPkg in E; cbn [fst snd] in E;
              try discriminate E.
            injection E as -> ->; exists w; split;
              [apply mem_srcVersions; exact Hp | reflexivity].
          + intros [v [Hv ->]]; left; exists (n, v); split;
              [apply mem_srcVersions; exact Hv | reflexivity].
        - rewrite mem_clsVersions; split.
          + intros [[p [_ E]] | [E | [m' [u' [k' [Hpk E]]]]]];
              unfold embedPkg, rootPkg in E; try discriminate E.
            injection E as -> ->; exists m', u'; split;
              [exact Hpk | reflexivity].
          + intros [m' [u' [Hpk ->]]]; right; right; exists m', u', k; split;
              [exact Hpk | reflexivity].
      Qed.

      Lemma reduceDeps_tailFibre : forall sigma I q,
          PF.PkgSet.In q (reduceReal sigma I) ->
          PF.Reduction.Lookup.DepRelFibred.tailFibre (reduceDeps sigma I) q =
          depEdges q (dependees sigma I q).
      Proof.
        intros sigma I q Hq; apply PF.DepRel.ext; intros [q' psi].
        rewrite PF.Reduction.Lookup.DepRelFibred.mem_tailFibre, mem_reduceDeps.
        unfold depEdges; rewrite SOfd.mem_map.
        split.
        - intros [[_ Hf] ->]; exists psi; split; [exact Hf | reflexivity].
        - intros [psi0 [Hf0 E]]; mem_destruct.
          split; [split; [exact Hq | exact Hf0] | reflexivity].
      Qed.

      Lemma negNames_encR : forall Vq g m,
          ~ PF.Reduction.NSet.In m (PF.Reduction.Lookup.negNames (encR Vq g)).
      Proof.
        intros Vq g m;
          induction g as [n phi | a IHa b IHb | a IHa b IHb];
          cbn [encR PF.Reduction.Lookup.negNames].
        - apply PF.Reduction.NSet.empty_spec.
        - rewrite PF.Reduction.NSet.union_spec; tauto.
        - rewrite PF.Reduction.NSet.union_spec; tauto.
      Qed.

      Lemma dependees_negNames : forall sigma Vq I q psi m,
          FSet.In psi (dependeesBy sigma Vq I q) ->
          PF.Reduction.NSet.In m (PF.Reduction.Lookup.negNames psi) ->
          exists n, m = TName.Real n.
      Proof.
        intros sigma Vq I [o u] psi m Hf Hx.
        assert (HT : ~ PF.Reduction.NSet.In m
                         (PF.Reduction.Lookup.negNames PTrue))
          by apply PF.Reduction.NSet.empty_spec.
        assert (Henc : forall d,
                   ~ PF.Reduction.NSet.In m
                       (PF.Reduction.Lookup.negNames (encodeOF sigma Vq d))).
        { intro d; unfold encodeOF.
          destruct (redOF sigma d); [apply negNames_encR | exact HT]. }
        destruct o as [| n' | k]; destruct u as [v | | n];
          try (cbn [dependeesBy] in Hf; destruct (FSet.empty_spec Hf)).
        - cbn [dependeesBy] in Hf; apply FSet.singleton_spec in Hf; subst psi.
          unfold rootForm in Hx; cbn [PF.Reduction.Lookup.negNames] in Hx.
          apply PF.Reduction.NSet.union_spec in Hx.
          destruct Hx as [Hx | Hx]; destruct (Henc _ Hx).
        - apply mem_dependees_real in Hf.
          destruct Hf as [[d [_ ->]] | [[[nc [c phi]] [_ ->]]
                           | [[k [_ ->]] | [_ [[[n u] y] [_ ->]]]]]].
          + destruct (Henc d Hx).
          + unfold cflForm in Hx; cbn [fst snd] in Hx.
            destruct (defTrue sigma c); [| destruct (HT Hx)].
            cbn [PF.Reduction.Lookup.negNames PF.Reduction.fnames] in Hx.
            apply PF.Reduction.NSet.singleton_spec in Hx; exists nc; exact Hx.
          + destruct (PF.Reduction.NSet.empty_spec Hx).
          + unfold pindForm in Hx;
              cbn [fst snd PF.Reduction.Lookup.negNames PF.Reduction.fnames]
              in Hx.
            apply PF.Reduction.NSet.singleton_spec in Hx; exists n; exact Hx.
      Qed.

      Lemma dependees_core : forall sigma I Vq q,
          PF.PkgSet.In q (reduceReal sigma I) ->
          (forall m, Vq (TName.Real m) = versions sigma I (TName.Real m)) ->
          PF.Reduction.T.dependees
            (PF.Reduction.reduceDeps (reduceReal sigma I) (reduceDeps sigma I))
            (PF.Reduction.Name.Orig (fst q),
             PF.Reduction.Version.Orig (snd q)) =
          PF.Reduction.T.dependees
            (PF.Reduction.reduceDepsBy Vq (depEdges q (dependees sigma I q)))
            (PF.Reduction.Name.Orig (fst q),
             PF.Reduction.Version.Orig (snd q)).
      Proof.
        intros sigma I Vq [o u] Hq HVq; cbn [fst snd].
        rewrite
          (PF.Reduction.Lookup.dependees_lookupOrigBy _ _ (versions sigma I))
          by (intros n _; symmetry; apply versions_reduceReal).
        rewrite (reduceDeps_tailFibre sigma I (o, u) Hq).
        f_equal; apply PF.Reduction.Lookup.reduceDepsBy_agreeNeg.
        intros p psi x Hpf Hx.
        unfold depEdges in Hpf; apply SOfd.mem_map in Hpf as [psi0 [Hf0 E]].
        mem_destruct.
        destruct (dependees_negNames _ _ _ _ _ _ Hf0 Hx) as [m ->].
        symmetry; apply HVq.
      Qed.

      Theorem dependees_lookupOrigCore : forall sigma I Vq n v,
          PkgSet.In (n, v) (effRepo sigma I) ->
          (forall m, Vq (TName.Real m) = versions sigma I (TName.Real m)) ->
          PF.Reduction.T.dependees
            (PF.Reduction.reduceDeps (reduceReal sigma I) (reduceDeps sigma I))
            (PF.Reduction.embedPkg (embedPkg (n, v))) =
          PF.Reduction.T.dependees
            (PF.Reduction.reduceDepsBy Vq
               (depEdges (embedPkg (n, v))
                  (dependees sigma (pkgSubInst I (n, v)) (embedPkg (n, v)))))
            (PF.Reduction.embedPkg (embedPkg (n, v))).
      Proof.
        intros sigma I Vq n v Hnv HVq; rewrite <- dependees_lookupOrig.
        apply (dependees_core sigma I Vq (embedPkg (n, v))); [| exact HVq].
        apply mem_reduceReal; left; exists (n, v); split;
          [exact Hnv | reflexivity].
      Qed.

      Theorem dependees_lookupRootCore : forall sigma I Vq,
          (forall m, Vq (TName.Real m) = versions sigma I (TName.Real m)) ->
          PF.Reduction.T.dependees
            (PF.Reduction.reduceDeps (reduceReal sigma I) (reduceDeps sigma I))
            (PF.Reduction.embedPkg rootPkg) =
          PF.Reduction.T.dependees
            (PF.Reduction.reduceDepsBy Vq
               (depEdges rootPkg (dependees sigma (rootSubInst I) rootPkg)))
            (PF.Reduction.embedPkg rootPkg).
      Proof.
        intros sigma I Vq HVq; rewrite <- dependees_lookupRoot.
        apply (dependees_core sigma I Vq rootPkg); [| exact HVq].
        apply mem_reduceReal; right; left; reflexivity.
      Qed.

      Theorem dependees_lookupClassCore : forall sigma I k n,
          PF.Reduction.T.dependees
            (PF.Reduction.reduceDeps (reduceReal sigma I) (reduceDeps sigma I))
            (PF.Reduction.Name.Orig (TName.Cls k),
             PF.Reduction.Version.Orig n) =
          PF.Reduction.T.DependeesSet.empty.
      Proof.
        intros sigma I k n; apply PF.Reduction.T.dependees_empty_iff;
          intros h H.
        apply PF.Reduction.mem_reduceDeps in H.
        destruct H as [[pn pv] [psi [Hd He]]].
        assert (E := proj1
                       (PF.Reduction.Lookup.encodeNNF_depender_orig_aux _ psi)
                       _ _ _ _ He).
        unfold PF.Reduction.embedPkg in E; injection E as -> ->.
        apply mem_reduceDeps in Hd; destruct Hd as [_ Hf].
        unfold dependees, dependeesBy in Hf.
        destruct n; destruct (FSet.empty_spec Hf).
      Qed.

      Theorem dependees_lookupDisjunctCore : forall sigma I I' Vq q chis i,
          PF.PkgSet.In q (reduceReal sigma I) ->
          dependees sigma I' q = dependees sigma I q ->
          (forall m, Vq (TName.Real m) = versions sigma I (TName.Real m)) ->
          PF.Reduction.T.PkgSet.In (PF.Reduction.Name.Disjunct chis, i)
            (PF.Reduction.reduceReal (PF.PkgSet.singleton q)
               (depEdges q (dependees sigma I' q))) ->
          PF.Reduction.T.dependees
            (PF.Reduction.reduceDeps (reduceReal sigma I) (reduceDeps sigma I))
            (PF.Reduction.Name.Disjunct chis, i) =
          PF.Reduction.T.dependees
            (PF.Reduction.reduceDepsBy Vq (depEdges q (dependees sigma I' q)))
            (PF.Reduction.Name.Disjunct chis, i).
      Proof.
        intros sigma I I' Vq q chis i Hq HI HVq Hin; rewrite HI in Hin |- *.
        assert (Hsub : PF.DepRel.Subset (depEdges q (dependees sigma I q))
                         (reduceDeps sigma I)).
        { rewrite <- (reduceDeps_tailFibre sigma I q Hq).
          apply PF.Reduction.Lookup.DepRelFibred.tailFibre_subset. }
        apply (PF.Reduction.Lookup.dependees_lookupDisjunctBy
                 _ _ _ _ _ _ _ Hsub Hin).
        intros p psi x Hpf Hx.
        unfold depEdges in Hpf; apply SOfd.mem_map in Hpf as [psi0 [Hf0 E]].
        mem_destruct.
        destruct (dependees_negNames _ _ _ _ _ _ Hf0 Hx) as [m ->].
        rewrite HVq, versions_reduceReal; reflexivity.
      Qed.

      Lemma versions_core : forall sigma I n,
          (exists v, PF.PkgSet.In (n, v) (reduceReal sigma I)) \/
          (exists p h,
              PF.Reduction.T.DepRel.In (p, (PF.Reduction.Name.Orig n, h))
                (PF.Reduction.reduceDeps (reduceReal sigma I)
                   (reduceDeps sigma I))) ->
          PF.Reduction.T.versions
            (PF.Reduction.reduceReal (reduceReal sigma I) (reduceDeps sigma I))
            (PF.Reduction.Name.Orig n) =
          PF.Reduction.T.VSet.add PF.Reduction.Version.Bot
            (PF.Reduction.embedVS (versions sigma I n)).
      Proof.
        intros sigma I n Hreach.
        assert (Hr : PF.PkgSet.In rootPkg (reduceReal sigma I))
          by (apply mem_reduceReal; right; left; reflexivity).
        destruct Hreach as [[v Hv] | Hreach];
          [rewrite (PF.Reduction.Lookup.versions_lookupOrig _ _ n v n Hv
                      (or_intror eq_refl) eq_refl)
          | rewrite (PF.Reduction.Lookup.versions_lookupOrig _ _ _ _ n Hr
                       (or_introl Hreach) eq_refl)];
          do 2 f_equal; rewrite <- versions_reduceReal;
          apply PF.C.versions_ext; intro u;
          rewrite PF.Reduction.Lookup.PkgFibred.mem_tailFibre; tauto.
      Qed.

      Theorem versions_lookupOrigCore : forall sigma I n,
          (exists v, PkgSet.In (n, v) (effRepo sigma I)) \/
          (exists p h,
              PF.Reduction.T.DepRel.In
                (p, (PF.Reduction.Name.Orig (TName.Real n), h))
                (PF.Reduction.reduceDeps (reduceReal sigma I)
                   (reduceDeps sigma I))) ->
          PF.Reduction.T.versions
            (PF.Reduction.reduceReal (reduceReal sigma I) (reduceDeps sigma I))
            (PF.Reduction.Name.Orig (TName.Real n)) =
          PF.Reduction.T.VSet.add PF.Reduction.Version.Bot
            (PF.Reduction.embedVS
               (versions sigma (nameSubInst I n) (TName.Real n))).
      Proof.
        intros sigma I n H; rewrite <- versions_lookupOrig; apply versions_core.
        destruct H as [[v Hv] | H]; [left | right; exact H].
        exists (TVer.RV v); apply mem_reduceReal; left; exists (n, v); split;
          [exact Hv | reflexivity].
      Qed.

      Theorem versions_lookupRootCore : forall sigma I,
          PF.Reduction.T.versions
            (PF.Reduction.reduceReal (reduceReal sigma I) (reduceDeps sigma I))
            (PF.Reduction.Name.Orig TName.Root) =
          PF.Reduction.T.VSet.add PF.Reduction.Version.Bot
            (PF.Reduction.embedVS (versions sigma I TName.Root)).
      Proof.
        intros sigma I; apply versions_core; left; exists TVer.UnitV.
        apply mem_reduceReal; right; left; reflexivity.
      Qed.

      Theorem versions_lookupClassCore : forall sigma I k,
          (exists p h,
              PF.Reduction.T.DepRel.In
                (p, (PF.Reduction.Name.Orig (TName.Cls k), h))
                (PF.Reduction.reduceDeps (reduceReal sigma I)
                   (reduceDeps sigma I))) ->
          PF.Reduction.T.versions
            (PF.Reduction.reduceReal (reduceReal sigma I) (reduceDeps sigma I))
            (PF.Reduction.Name.Orig (TName.Cls k)) =
          PF.Reduction.T.VSet.add PF.Reduction.Version.Bot
            (PF.Reduction.embedVS
               (versions sigma (classSubInst I k) (TName.Cls k))).
      Proof.
        intros sigma I k H; rewrite <- versions_lookupClass; apply versions_core.
        right; exact H.
      Qed.
    End Lookup.
  End Reduction.

End Opam.
