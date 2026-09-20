From Stdlib Require Import MSets Bool.
From PackageCalculus Require Import Prelude Core Semver.

Create HintDb cmp_cargo.
Create Rewrite HintDb cmp_cargo.

(* Cargo: crates resolve with at most one version per semver-compatibility
   class (the granularity g), feature unification per crate version,
   optional dependencies activated by features, and native-library mutual
   exclusion via the links key.  The calculus is a source record over
   honest manifest data plus a verified translation into Core.
   Caret/tilde/wildcard
   requirements, implicit features of optional dependencies, and the
   dep: suppression rule are frontend desugarings into the carried
   range/feature-table data.

   Cargo resolves a project twice, and the difference between the two is
   only which features the root is asked for: the lockfile resolve takes
   every feature the root declares, so that one lock serves every later
   selection, and the build resolve takes the features actually named.
   Both are IsResolution over the same manifest data at different
   rootFeats, so neither needs its own record. *)
Module Cargo (N V L F G CfgS Src : UsualOrderedType) (PM : SemverMatch V).
  Module C := Core N V.
  Module Pkg := C.Pkg.
  Module PkgSet := C.PkgSet.
  Module VSet := C.VSet.

  (* cargo requirements are the shared semver language: a comma-separated
     conjunction is one comparator set, and the prerelease rule the
     semver crate applies over a whole VersionReq is that set's csAdmits.
     Included under their own names rather than qualified. *)
  Module Sv := Semver V VSet PM.
  Include Sv.

  Module FSet := FSetUOT F.
  Module Featured := PairUOT Pkg FSet.AsUOT.
  Module FeaturedSet := FSetUOT Featured.
  Module PkgF := PairUOT Pkg F.
  Module SupportSet := FSetUOT PkgF.

  Module NFPair := PairUOT N F.
  Module NFF := UOTCompareFacts NFPair.
  Module NF := UOTCompareFacts N.
  Module FF := UOTCompareFacts F.
  #[local] Hint Rewrite NFF.compare_eq_iff NF.compare_eq_iff
    FF.compare_eq_iff : cmp_cargo.
  #[local] Hint Extern 1 => cmp_by NFF.compare_antisym : cmp_cargo.
  #[local] Hint Extern 1 => cmp_by NF.compare_antisym : cmp_cargo.
  #[local] Hint Extern 1 => cmp_by FF.compare_antisym : cmp_cargo.
  #[local] Hint Extern 1 => cmp_by NFF.compare_lt_trans : cmp_cargo.
  #[local] Hint Extern 1 => cmp_by NF.compare_lt_trans : cmp_cargo.
  #[local] Hint Extern 1 => cmp_by FF.compare_lt_trans : cmp_cargo.

  (* One entry of a crate feature's enable list: another feature of the
     same crate, activation of an optional dependency slot (dep:a), a
     strong dependency feature (a/feat), or a weak one (a?/feat).  The
     weak form is kept as its own constructor because the manifest
     distinguishes it and a later narrowing pass over a fixed resolution
     would need to; version resolution here reduces it exactly as the
     strong form, which is what cargo's resolver does. *)
  Module FEntry.
    Inductive fentry : Type :=
    | EFeat (f : F.t)
    | EDep (a : N.t)
    | EDepFeat (a : N.t) (feat : F.t)
    | EWeakFeat (a : N.t) (feat : F.t).
    Definition t := fentry.

    Definition rank (e : t) : nat :=
      match e with
      | EFeat _ => 0 | EDep _ => 1 | EDepFeat _ _ => 2 | EWeakFeat _ _ => 3
      end.

    Definition compare (x y : t) : comparison :=
      match Nat.compare (rank x) (rank y) with
      | Eq =>
          match x, y with
          | EFeat f1, EFeat f2 => F.compare f1 f2
          | EDep a1, EDep a2 => N.compare a1 a2
          | EDepFeat a1 f1, EDepFeat a2 f2 =>
              NFPair.compare (a1, f1) (a2, f2)
          | EWeakFeat a1 f1, EWeakFeat a2 f2 =>
              NFPair.compare (a1, f1) (a2, f2)
          | _, _ => Eq
          end
      | c => c
      end.

    Lemma compare_eq_iff : forall x y, compare x y = Eq <-> x = y.
    Proof. cmp_eq_iff cmp_cargo. Qed.

    Lemma compare_antisym : forall x y, compare y x = CompOpp (compare x y).
    Proof. cmp_antisym cmp_cargo. Qed.

    Lemma compare_lt_trans : forall x y z,
        compare x y = Lt -> compare y z = Lt -> compare x z = Lt.
    Proof. cmp_lt_trans cmp_cargo. Qed.
  End FEntry.
  Module FEntryOT := UOTFromCompare FEntry.

  Module FDefElt := PairUOT PkgF FEntryOT.
  Module FDefRel := FSetUOT FDefElt.

  (* Dependency kinds; dev dependencies participate only at the root. *)
  Module Kind.
    Inductive kind : Type := KNormal | KBuild | KDev.
    Definition t := kind.

    Definition rank (k : t) : nat :=
      match k with KNormal => 0 | KBuild => 1 | KDev => 2 end.

    Definition compare (x y : t) : comparison :=
      Nat.compare (rank x) (rank y).

    Lemma compare_eq_iff : forall x y, compare x y = Eq <-> x = y.
    Proof. cmp_eq_iff cmp_cargo. Qed.

    Lemma compare_antisym : forall x y, compare y x = CompOpp (compare x y).
    Proof. cmp_antisym cmp_cargo. Qed.

    Lemma compare_lt_trans : forall x y z,
        compare x y = Lt -> compare y z = Lt -> compare x z = Lt.
    Proof. cmp_lt_trans cmp_cargo. Qed.
  End Kind.
  Module KindOT := UOTFromCompare Kind.

  (* A dependency slot: manifest alias (the identity dep:/a/feat entries
     reference, and the rename key), real target crate, requirement
     formula, kind, optionality, default-features opt-out, requested
     features, and carried cfg predicate and source identity.

     The cfg predicate is never evaluated and the source identity is
     never read at all: cargo's resolver does not match a
     [target.'cfg(...)'] against real cfgs, and a dependency's registry
     only has to agree across the declarations sharing one alias, which
     the manifest reader checks before resolution begins.  The cfg does
     decide identity -- see sKey -- but that is where a declaration was
     written, not what it means. *)
  Module SDCfg := PairUOT CfgS Src.
  Module SDReq := PairUOT FSet.AsUOT SDCfg.
  Module SDDflt := PairUOT BoolOT SDReq.
  Module SDOpt := PairUOT BoolOT SDDflt.
  Module SDKind := PairUOT KindOT SDOpt.
  Module SDForm := PairUOT RangeOT SDKind.
  Module SDTgt := PairUOT N SDForm.
  Module SlotData := PairUOT N SDTgt.
  Module SlotElt := PairUOT Pkg SlotData.
  Module SlotRel := FSetUOT SlotElt.

  Definition sAlias (d : SlotData.t) : N.t := fst d.
  Definition sTarget (d : SlotData.t) : N.t := fst (snd d).
  Definition sReq (d : SlotData.t) : Range := fst (snd (snd d)).
  Definition sKind (d : SlotData.t) : Kind.t := fst (snd (snd (snd d))).
  Definition sOptional (d : SlotData.t) : bool :=
    fst (snd (snd (snd (snd d)))).
  Definition sDefault (d : SlotData.t) : bool :=
    fst (snd (snd (snd (snd (snd d))))).
  Definition sReqFeats (d : SlotData.t) : FSet.t :=
    fst (snd (snd (snd (snd (snd (snd d)))))).
  Definition sCfg (d : SlotData.t) : CfgS.t :=
    fst (snd (snd (snd (snd (snd (snd (snd d))))))).
  Definition sSrc (d : SlotData.t) : Src.t :=
    snd (snd (snd (snd (snd (snd (snd (snd d))))))).

  (* What cargo takes one dependency to be: the manifest site that
     declared it.  A manifest offers one table per (cfg target, kind) and
     each is a map, so the site is the triple (cfg, kind, key), and the
     key is the alias -- cargo's name_in_toml is the table key whether or
     not a rename moved the crate name into "package".  Nothing collapses
     two sites naming one alias: a summary carries a plain list of
     dependencies, the manifest reader's only cross-table check is that
     they agree on a registry, and the resolver walks the list, so a
     crate may ask for libc ^0.2 in [dependencies] and libc ^0.1 in
     [target.'cfg(windows)'.dependencies] and get both versions.  The
     alias alone still governs features -- dep:a and a/feat name a table
     key, and reach every declaration under it. *)
  Module SKTail := PairUOT KindOT CfgS.
  Module SlotKey := PairUOT N SKTail.
  Definition sKey (d : SlotData.t) : SlotKey.t :=
    (sAlias d, (sKind d, sCfg d)).
  Definition kAlias (k : SlotKey.t) : N.t := fst k.

  Lemma kAlias_sKey : forall d, kAlias (sKey d) = sAlias d.
  Proof. reflexivity. Qed.

  Module LinkElt := PairUOT Pkg L.
  Module LinkRel := FSetUOT LinkElt.

  (* The concurrent calculus' parent relation, keyed by declaration site
     rather than by the (child, parent) pair alone.  A cargo rename lets
     one crate depend on a single crate name twice -- foo = { package =
     "bar" } beside baz = { package = "bar" } -- and a repeated alias lets
     it depend on one name twice again; either way the two may land on
     different compatibility classes, so the parent edge has to say which
     declaration received which version, and the requested feature set is
     per declaration too. *)
  Module NAPair := PairUOT Pkg SlotKey.
  Module ParentElt := PairUOT NAPair V.
  Module ParentRel := FSetUOT ParentElt.

  (* Whether a slot participates in resolution: dev dependencies only
     from the root crate.  Build dependencies resolve in the shared graph
     (the resolver-v1 reading; the v2 build/normal feature split is
     carried by sKind but not separated here).

     A slot's cfg does not appear, because cargo's version resolver never
     sees a target: resolve_with_previous takes no RustcTargetData, and
     the one pass that matches a cfg against real cfgs filters an
     already-finished Resolve on its way to the unit graph, never the
     lockfile.  A [target.'cfg(...)'] row is therefore a dependency row
     like any other -- an unsatisfiable windows-only requirement fails a
     linux resolve -- and sCfg says only which row this is, never whether
     the row applies. *)
  Definition slotActive (rc p : Pkg.t) (d : SlotData.t) : bool :=
    match sKind d with
    | Kind.KDev => if Pkg.eq_dec p rc then true else false
    | _ => true
    end.

  (* An optional slot is activated when some enabled feature of its
     owner names it, by dep:a or by either a/feat or a?/feat.  A weak
     entry activating is cargo's resolver behaviour: it activates weak
     entries unconditionally and narrows them only in a later pass over
     an already-fixed resolution, which is what keeps a lockfile
     complete as --features varies. *)
  Definition Activated (FDefs : FDefRel.t) (fs : FSet.t) (p : Pkg.t)
      (a : N.t) : Prop :=
    exists f, FSet.In f fs /\
      (FDefRel.In ((p, f), FEntry.EDep a) FDefs \/
       (exists feat, FDefRel.In ((p, f), FEntry.EDepFeat a feat) FDefs) \/
       (exists feat, FDefRel.In ((p, f), FEntry.EWeakFeat a feat) FDefs)).

  Definition slotRequests (d : SlotData.t) (dflt : F.t) : FSet.t :=
    if sDefault d then FSet.add dflt (sReqFeats d) else sReqFeats d.

  (* The record quantifies feature sets through FeaturedSet membership;
     fs_functional makes the projection well defined.

     rootFeats is a parameter and not a constant because it is the only
     place cargo's two resolves of one project differ.  Instantiated at
     every feature the root's table defines -- the implicit feature of
     each of its optional dependencies included -- res_root_feats forces
     all of them on and the resolutions are the ones cargo writes as
     Cargo.lock.  Instantiated at the features actually asked for, they
     are the builds cargo runs against that lock.  Either way the choice
     reaches the root alone: every other crate's features are whatever
     its declarers requested, which is what keeps an unactivated optional
     of a *dependency* out under sOptional and Activated, in both
     instantiations alike. *)
  Record IsResolution
      (R : PkgSet.t) (support : SupportSet.t) (FDefs : FDefRel.t)
      (Slots : SlotRel.t) (Links : LinkRel.t)
      (g : V.t -> G.t) (dflt : F.t)
      (rc : Pkg.t) (rootFeats : FSet.t)
      (S : PkgSet.t) (FS : FeaturedSet.t) (pi : ParentRel.t) : Prop :=
    { res_subset : PkgSet.Subset S R
    ; res_root_mem : PkgSet.In rc S
    ; res_root_feats :
        forall fs, FeaturedSet.In (rc, fs) FS -> FSet.Subset rootFeats fs
    ; res_fs_dom : forall p fs, FeaturedSet.In (p, fs) FS -> PkgSet.In p S
    ; res_fs_total : forall p, PkgSet.In p S ->
        exists fs, FeaturedSet.In (p, fs) FS
    ; res_fs_functional :
        forall p fs fs', FeaturedSet.In (p, fs) FS ->
        FeaturedSet.In (p, fs') FS -> fs = fs'
    ; res_class_unique :
        forall m v v', PkgSet.In (m, v) S -> PkgSet.In (m, v') S ->
        v <> v' -> g v <> g v'
    ; res_support_mem :
        forall p fs f, FeaturedSet.In (p, fs) FS -> FSet.In f fs ->
        SupportSet.In (p, f) support
    ; res_pi_functional :
        forall p k u u', ParentRel.In ((p, k), u) pi ->
        ParentRel.In ((p, k), u') pi -> u = u'
    ; res_slot_closure :
        forall p fs, PkgSet.In p S -> FeaturedSet.In (p, fs) FS ->
        forall d, SlotRel.In (p, d) Slots ->
        slotActive rc p d = true ->
        (sOptional d = false \/ Activated FDefs fs p (sAlias d)) ->
        exists u, ParentRel.In ((p, sKey d), u) pi /\
          rgHolds (sReq d) u = true /\ PkgSet.In (sTarget d, u) S /\
          forall fs', FeaturedSet.In ((sTarget d, u), fs') FS ->
          FSet.Subset (slotRequests d dflt) fs'
    ; res_feat_closure_same :
        forall p fs f f', FeaturedSet.In (p, fs) FS -> FSet.In f fs ->
        FDefRel.In ((p, f), FEntry.EFeat f') FDefs -> FSet.In f' fs
    ; res_feat_closure_dep :
        forall p fs f a feat, FeaturedSet.In (p, fs) FS -> FSet.In f fs ->
        (FDefRel.In ((p, f), FEntry.EDepFeat a feat) FDefs \/
         FDefRel.In ((p, f), FEntry.EWeakFeat a feat) FDefs) ->
        forall d u, SlotRel.In (p, d) Slots -> sAlias d = a ->
        ParentRel.In ((p, sKey d), u) pi ->
        forall fs', FeaturedSet.In ((sTarget d, u), fs') FS ->
        FSet.In feat fs'
    ; res_links_unique :
        forall p q l, PkgSet.In p S -> PkgSet.In q S ->
        LinkRel.In (p, l) Links -> LinkRel.In (q, l) Links -> p = q }.

  Module LF := UOTCompareFacts L.
  Module GF := UOTCompareFacts G.
  Module VF := UOTCompareFacts V.
  Module PkgFct := UOTCompareFacts Pkg.
  Module SlotName := TripleUOT N V SlotKey.
  Module SlotNameF := UOTCompareFacts SlotName.
  Module FDTail := TripleUOT F SlotKey F.
  Module DecName := TripleUOT N V FDTail.
  Module DecNameF := UOTCompareFacts DecName.
  #[local] Hint Rewrite LF.compare_eq_iff GF.compare_eq_iff
    VF.compare_eq_iff PkgFct.compare_eq_iff SlotNameF.compare_eq_iff
    DecNameF.compare_eq_iff : cmp_cargo.
  #[local] Hint Extern 1 => cmp_by LF.compare_antisym : cmp_cargo.
  #[local] Hint Extern 1 => cmp_by GF.compare_antisym : cmp_cargo.
  #[local] Hint Extern 1 => cmp_by VF.compare_antisym : cmp_cargo.
  #[local] Hint Extern 1 => cmp_by PkgFct.compare_antisym : cmp_cargo.
  #[local] Hint Extern 1 => cmp_by SlotNameF.compare_antisym : cmp_cargo.
  #[local] Hint Extern 1 => cmp_by DecNameF.compare_antisym : cmp_cargo.
  #[local] Hint Extern 1 => cmp_by LF.compare_lt_trans : cmp_cargo.
  #[local] Hint Extern 1 => cmp_by GF.compare_lt_trans : cmp_cargo.
  #[local] Hint Extern 1 => cmp_by VF.compare_lt_trans : cmp_cargo.
  #[local] Hint Extern 1 => cmp_by PkgFct.compare_lt_trans : cmp_cargo.
  #[local] Hint Extern 1 => cmp_by SlotNameF.compare_lt_trans : cmp_cargo.
  #[local] Hint Extern 1 => cmp_by DecNameF.compare_lt_trans : cmp_cargo.

  Module NEqb := UOTEqb N.
  Module LEqb := UOTEqb L.
  Module PkgEqb := UOTEqb Pkg.
  Module SKEqb := UOTEqb SlotKey.

  Module SOpv := SetOps Pkg V PkgSet VSet.
  Definition evalReq (R : PkgSet.t) (m : N.t) (rg : Range) : VSet.t :=
    SOpv.filterMap (fun '(o, u) =>
        if NEqb.eqb o m then if rgHolds rg u then Some u else None
        else None)
      R.

  Lemma mem_evalReq : forall R m rg u,
      VSet.In u (evalReq R m rg) <->
      PkgSet.In (m, u) R /\ rgHolds rg u = true.
  Proof.
    intros R m rg u; unfold evalReq; rewrite SOpv.mem_filterMap.
    split.
    - intros [[o w] [HR He]]; cbn beta iota in He.
      destruct (NEqb.eqb o m) eqn:En; [| discriminate].
      apply NEqb.eqb_true_iff in En; subst o.
      destruct (rgHolds rg w) eqn:Ev; [| discriminate].
      injection He as ->; split; assumption.
    - intros [HR Hv]; exists (m, u); split; [exact HR | cbn beta iota].
      rewrite NEqb.eqb_refl, Hv; reflexivity.
  Qed.

  (* The versions of a crate name in the repository; encoders consult R
     only through an oracle Vq of this shape, so sub-instance reuse below is
     oracle agreement (the lookup lemmas).  This is not evalReq at some
     top range: no range admits a prerelease it does not name, so none
     denotes the whole repository. *)
  Definition srcVersions (R : PkgSet.t) (m : N.t) : VSet.t :=
    SOpv.filterMap (fun '(o, u) => if NEqb.eqb o m then Some u else None) R.

  Lemma mem_srcVersions : forall R m v,
      VSet.In v (srcVersions R m) <-> PkgSet.In (m, v) R.
  Proof.
    intros R m v; unfold srcVersions; rewrite SOpv.mem_filterMap.
    split.
    - intros [[o w] [HR He]]; cbn beta iota in He.
      destruct (NEqb.eqb o m) eqn:En; [| discriminate].
      apply NEqb.eqb_true_iff in En; subst o.
      injection He as ->; exact HR.
    - intro HR; exists (m, v); split; [exact HR | cbn beta iota].
      rewrite NEqb.eqb_refl; reflexivity.
  Qed.

  (* Slots of p under alias a that participate in resolution. *)
  Definition slotsAt (Slots : SlotRel.t)
      (rc : Pkg.t) (p : Pkg.t) (a : N.t) : SlotRel.t :=
    SlotRel.filter (fun '(q, d) =>
        andb (if Pkg.eq_dec q p then true else false)
          (andb (NEqb.eqb (sAlias d) a) (slotActive rc q d)))
      Slots.

  Lemma mem_slotsAt : forall Slots rc p a q d,
      SlotRel.In (q, d) (slotsAt Slots rc p a) <->
      SlotRel.In (q, d) Slots /\ q = p /\ sAlias d = a /\
      slotActive rc q d = true.
  Proof.
    intros Slots rc p a q d; unfold slotsAt.
    rewrite SlotRel.filter_spec'.
    split.
    - intros [Hin Hb].
      apply andb_true_iff in Hb; destruct Hb as [Hq Hb].
      destruct (Pkg.eq_dec q p) as [-> | NE]; [| discriminate].
      apply andb_true_iff in Hb; destruct Hb as [Ha Hact].
      apply NEqb.eqb_true_iff in Ha.
      repeat split; assumption.
    - intros [Hin [-> [Ha Hact]]]; split; [exact Hin |].
      destruct (Pkg.eq_dec p p) as [_ | NE];
        [| contradiction NE; reflexivity].
      subst a; rewrite NEqb.eqb_refl, Hact; reflexivity.
  Qed.

  (* and the same cut by declaration site rather than by alias: what one
     slot node stands for, where slotsAt is what one feature entry
     reaches *)
  Definition slotsAtKey (Slots : SlotRel.t)
      (rc : Pkg.t) (p : Pkg.t) (k : SlotKey.t) : SlotRel.t :=
    SlotRel.filter (fun '(q, d) =>
        andb (if Pkg.eq_dec q p then true else false)
          (andb (SKEqb.eqb (sKey d) k) (slotActive rc q d)))
      Slots.

  Lemma mem_slotsAtKey : forall Slots rc p k q d,
      SlotRel.In (q, d) (slotsAtKey Slots rc p k) <->
      SlotRel.In (q, d) Slots /\ q = p /\ sKey d = k /\
      slotActive rc q d = true.
  Proof.
    intros Slots rc p k q d; unfold slotsAtKey.
    rewrite SlotRel.filter_spec'.
    split.
    - intros [Hin Hb].
      apply andb_true_iff in Hb; destruct Hb as [Hq Hb].
      destruct (Pkg.eq_dec q p) as [-> | NE]; [| discriminate].
      apply andb_true_iff in Hb; destruct Hb as [Ha Hact].
      apply SKEqb.eqb_true_iff in Ha.
      repeat split; assumption.
    - intros [Hin [-> [Ha Hact]]]; split; [exact Hin |].
      destruct (Pkg.eq_dec p p) as [_ | NE];
        [| contradiction NE; reflexivity].
      subst k; rewrite SKEqb.eqb_refl, Hact; reflexivity.
  Qed.

  (* Feature-table entries that create a decision name, with the feat
     they deliver. *)
  Definition entryFeatD (e : FEntry.t) : option (N.t * F.t) :=
    match e with
    | FEntry.EDepFeat a feat => Some (a, feat)
    | FEntry.EWeakFeat a feat => Some (a, feat)
    | _ => None
    end.

  (* Entries that activate an optional slot: dep:a, and both a/feat and
     a?/feat -- the weak form is reduced as the strong one. *)
  Definition entryActivates (e : FEntry.t) : option N.t :=
    match e with
    | FEntry.EDep a => Some a
    | FEntry.EDepFeat a _ => Some a
    | FEntry.EWeakFeat a _ => Some a
    | _ => None
    end.

  (* Whether some feature entry of (p, f) delivers (a, feat); weak and
     strong entries introduce the same decision name. *)
  Definition fdEntryb (FDefs : FDefRel.t) (p : Pkg.t) (f : F.t)
      (a : N.t) (feat : F.t) : bool :=
    orb (FDefRel.mem ((p, f), FEntry.EDepFeat a feat) FDefs)
      (FDefRel.mem ((p, f), FEntry.EWeakFeat a feat) FDefs).

  Lemma fdEntryb_iff : forall FDefs p f a feat,
      fdEntryb FDefs p f a feat = true <->
      exists e, FDefRel.In ((p, f), e) FDefs /\
        entryFeatD e = Some (a, feat).
  Proof.
    intros FDefs p f a feat; unfold fdEntryb; rewrite orb_true_iff.
    rewrite !FDefRel.mem_spec.
    split.
    - intros [H | H]; eexists; split; try exact H; reflexivity.
    - intros [e [He Hd]].
      destruct e; simpl in Hd; try discriminate;
        injection Hd as -> ->; [left | right]; exact He.
  Qed.

  (* One manifest site declares one dependency: the tables a manifest
     offers are maps, so a crate has at most one slot per (cfg, kind,
     alias).  The products assume that well-formedness because the slot
     node is keyed by the site. *)
  Definition SiteFunctional (Slots : SlotRel.t) : Prop :=
    forall p d d', SlotRel.In (p, d) Slots -> SlotRel.In (p, d') Slots ->
    sKey d = sKey d' -> d = d'.

  Definition activatedb (FDefs : FDefRel.t) (fs : FSet.t) (p : Pkg.t)
      (a : N.t) : bool :=
    FDefRel.exists_ (fun '((q, f), e) =>
        andb (PkgEqb.eqb q p)
          (andb (FSet.mem f fs)
             (match entryActivates e with
              | Some a' => NEqb.eqb a' a
              | None => false
              end)))
      FDefs.

  Lemma activatedb_iff : forall FDefs fs p a,
      activatedb FDefs fs p a = true <-> Activated FDefs fs p a.
  Proof.
    intros FDefs fs p a; unfold activatedb, Activated.
    rewrite FDefRel.exists_spec'.
    split.
    - intros [[[q f] e] [He Hb]]; cbn beta iota in Hb.
      apply andb_true_iff in Hb; destruct Hb as [Hq Hb].
      apply andb_true_iff in Hb; destruct Hb as [Hf Ha].
      apply PkgEqb.eqb_true_iff in Hq; subst q.
      apply FSet.mem_spec in Hf.
      destruct e; cbn in Ha; try discriminate;
        apply NEqb.eqb_true_iff in Ha; subst a.
      + exists f; split; [exact Hf | left; exact He].
      + exists f; split; [exact Hf | right; left; eexists; exact He].
      + exists f; split; [exact Hf | right; right; eexists; exact He].
    - intros [f [Hf [He | [[feat He] | [feat He]]]]].
      + exists ((p, f), FEntry.EDep a); split; [exact He |].
        cbn beta iota; rewrite PkgEqb.eqb_refl; cbn.
        apply FSet.mem_spec in Hf; rewrite Hf; cbn.
        rewrite NEqb.eqb_refl; reflexivity.
      + exists ((p, f), FEntry.EDepFeat a feat); split; [exact He |].
        cbn beta iota; rewrite PkgEqb.eqb_refl; cbn.
        apply FSet.mem_spec in Hf; rewrite Hf; cbn.
        rewrite NEqb.eqb_refl; reflexivity.
      + exists ((p, f), FEntry.EWeakFeat a feat); split; [exact He |].
        cbn beta iota; rewrite PkgEqb.eqb_refl; cbn.
        apply FSet.mem_spec in Hf; rewrite Hf; cbn.
        rewrite NEqb.eqb_refl; reflexivity.
  Qed.

  Definition requiredb (FDefs : FDefRel.t) (fs : FSet.t) (p : Pkg.t)
      (d : SlotData.t) : bool :=
    orb (negb (sOptional d)) (activatedb FDefs fs p (sAlias d)).

  Lemma requiredb_iff : forall FDefs fs p d,
      requiredb FDefs fs p d = true <->
      sOptional d = false \/ Activated FDefs fs p (sAlias d).
  Proof.
    intros FDefs fs p d; unfold requiredb.
    rewrite orb_true_iff, negb_true_iff, activatedb_iff; tauto.
  Qed.

  (* The unique feature set FS assigns to p; total via a default so the
     witness stays computable, pinned by fs_functional in proofs. *)
  Definition fsAt (FS : FeaturedSet.t) (p : Pkg.t) : FSet.t :=
    match FeaturedSet.choose
            (FeaturedSet.filter (fun '(q, _) => PkgEqb.eqb q p) FS)
    with
    | Some (_, fs) => fs
    | None => FSet.empty
    end.

  Lemma fsAt_in : forall FS p fs,
      (forall q fs1 fs2, FeaturedSet.In (q, fs1) FS ->
         FeaturedSet.In (q, fs2) FS -> fs1 = fs2) ->
      FeaturedSet.In (p, fs) FS -> fsAt FS p = fs.
  Proof.
    intros FS p fs Hfun Hin; unfold fsAt.
    destruct (FeaturedSet.choose
                (FeaturedSet.filter (fun '(q, _) => PkgEqb.eqb q p) FS))
      as [[q fs'] |] eqn:Hc.
    - apply FeaturedSet.choose_spec1 in Hc.
      apply FeaturedSet.filter_spec' in Hc; destruct Hc as [Hc Hq].
      apply PkgEqb.eqb_true_iff in Hq; subst q.
      exact (Hfun _ _ _ Hc Hin).
    - exfalso; apply FeaturedSet.choose_spec2 in Hc.
      apply (Hc (p, fs)).
      apply FeaturedSet.filter_spec'; split;
        [exact Hin | apply PkgEqb.eqb_refl].
  Qed.

  (* Whether the choice node at (q, a) carries a parent edge: q resolved
     and some active slot under alias a is required (non-optional or
     activated). *)
  Definition parentsb (FDefs : FDefRel.t) (Slots : SlotRel.t)
      (rc : Pkg.t)
      (S : PkgSet.t) (FS : FeaturedSet.t) (q : Pkg.t) (k : SlotKey.t)
    : bool :=
    andb (PkgSet.mem q S)
      (SlotRel.exists_ (fun '(q', d) =>
           andb (PkgEqb.eqb q' q)
             (andb (SKEqb.eqb (sKey d) k)
                (andb (slotActive rc q' d)
                   (requiredb FDefs (fsAt FS q) q d))))
         Slots).

  Lemma parentsb_iff : forall FDefs Slots rc S FS q k,
      parentsb FDefs Slots rc S FS q k = true <->
      PkgSet.In q S /\
      exists d, SlotRel.In (q, d) Slots /\ sKey d = k /\
        slotActive rc q d = true /\
        (sOptional d = false \/
         Activated FDefs (fsAt FS q) q (sAlias d)).
  Proof.
    intros FDefs Slots rc S FS q k; unfold parentsb.
    rewrite andb_true_iff, PkgSet.mem_spec, SlotRel.exists_spec'.
    split.
    - intros [HS [[q' d] [Hd Hb]]]; cbn beta iota in Hb.
      apply andb_true_iff in Hb; destruct Hb as [Hq Hb].
      apply andb_true_iff in Hb; destruct Hb as [Ha Hb].
      apply andb_true_iff in Hb; destruct Hb as [Hact Hreq].
      apply PkgEqb.eqb_true_iff in Hq; subst q'.
      apply SKEqb.eqb_true_iff in Ha.
      apply requiredb_iff in Hreq.
      split; [exact HS |].
      exists d; repeat split; assumption.
    - intros [HS [d [Hd [Ha [Hact Hreq]]]]].
      split; [exact HS |].
      exists (q, d); split; [exact Hd | cbn beta iota].
      rewrite PkgEqb.eqb_refl; cbn.
      subst k; rewrite SKEqb.eqb_refl; cbn.
      rewrite Hact; cbn.
      apply requiredb_iff in Hreq; rewrite Hreq; reflexivity.
  Qed.

  (* ---- Reduction to Core ----------------------------------------------

     Concurrency and features are inlined rather than inherited from the
     functors that supply them on their own: the granularity class sits in
     the name, and a crate feature is its own granular name.

     A per-site node ranges over granularity classes rather than over
     versions, and its edge carries the requirement onto the granular crate
     name, where every depender's range already meets and where version
     uniqueness picks the version.  That is one node per dependency edge
     rather than one keyed by each version the requirement admits, which is
     what a preference over versions would otherwise have to walk.  The
     parent relation is still recoverable -- one version per class is all
     a resolution admits -- so nothing the Cargo resolution asks for is
     lost. *)
  Module NGPair := PairUOT N G.
  Module NFGTrip := TripleUOT N F G.
  Module NGF := UOTCompareFacts NGPair.
  Module NFGF := UOTCompareFacts NFGTrip.
  Module GEqb := UOTEqb G.
  Module FEqb := UOTEqb F.
  Module GFacts := UOTCompareFacts G.
  #[local] Hint Rewrite NGF.compare_eq_iff NFGF.compare_eq_iff
    GFacts.compare_eq_iff : cmp_cargo.
  #[local] Hint Extern 1 => cmp_by NGF.compare_antisym : cmp_cargo.
  #[local] Hint Extern 1 => cmp_by NFGF.compare_antisym : cmp_cargo.
  #[local] Hint Extern 1 => cmp_by GFacts.compare_antisym : cmp_cargo.
  #[local] Hint Extern 1 => cmp_by NGF.compare_lt_trans : cmp_cargo.
  #[local] Hint Extern 1 => cmp_by NFGF.compare_lt_trans : cmp_cargo.
  #[local] Hint Extern 1 => cmp_by GFacts.compare_lt_trans : cmp_cargo.

  Module NPlus.
    Inductive name : Type :=
    | CRoot
    | CCrate (m : N.t) (gr : G.t)
    | CFeatP (m : N.t) (f : F.t) (gr : G.t)
    | CSlot (m : N.t) (v : V.t) (k : SlotKey.t)
    | CDec (m : N.t) (v : V.t) (f : F.t) (k : SlotKey.t) (feat : F.t)
    | CLink (l : L.t).
    Definition t := name.

    Definition rank (x : t) : nat :=
      match x with
      | CRoot => 0 | CCrate _ _ => 1 | CFeatP _ _ _ => 2
      | CSlot _ _ _ => 3 | CDec _ _ _ _ _ => 4 | CLink _ => 5
      end.

    Definition compare (x y : t) : comparison :=
      match Nat.compare (rank x) (rank y) with
      | Eq =>
          match x, y with
          | CCrate n1 g1, CCrate n2 g2 => NGPair.compare (n1, g1) (n2, g2)
          | CFeatP n1 f1 g1, CFeatP n2 f2 g2 =>
              NFGTrip.compare (n1, (f1, g1)) (n2, (f2, g2))
          | CSlot n1 v1 a1, CSlot n2 v2 a2 =>
              SlotName.compare (n1, (v1, a1)) (n2, (v2, a2))
          | CDec n1 v1 f1 a1 t1, CDec n2 v2 f2 a2 t2 =>
              DecName.compare (n1, (v1, (f1, (a1, t1))))
                (n2, (v2, (f2, (a2, t2))))
          | CLink l1, CLink l2 => L.compare l1 l2
          | _, _ => Eq
          end
      | c => c
      end.

    Lemma compare_eq_iff : forall x y, compare x y = Eq <-> x = y.
    Proof. cmp_eq_iff cmp_cargo. Qed.

    Lemma compare_antisym : forall x y, compare y x = CompOpp (compare x y).
    Proof. cmp_antisym cmp_cargo. Qed.

    Lemma compare_lt_trans : forall x y z,
        compare x y = Lt -> compare y z = Lt -> compare x z = Lt.
    Proof. cmp_lt_trans cmp_cargo. Qed.
  End NPlus.
  Module NPOT := UOTFromCompare NPlus.

  Module VPlus.
    Inductive version : Type :=
    | WUnit
    | WOrig (v : V.t)
    | WClass (gr : G.t)
    | WMember (p : Pkg.t).
    Definition t := version.

    Definition rank (x : t) : nat :=
      match x with
      | WUnit => 0 | WOrig _ => 1 | WClass _ => 2 | WMember _ => 3
      end.

    Definition compare (x y : t) : comparison :=
      match Nat.compare (rank x) (rank y) with
      | Eq =>
          match x, y with
          | WOrig v1, WOrig v2 => V.compare v1 v2
          | WClass g1, WClass g2 => G.compare g1 g2
          | WMember p1, WMember p2 => Pkg.compare p1 p2
          | _, _ => Eq
          end
      | c => c
      end.

    Lemma compare_eq_iff : forall x y, compare x y = Eq <-> x = y.
    Proof. cmp_eq_iff cmp_cargo. Qed.

    Lemma compare_antisym : forall x y, compare y x = CompOpp (compare x y).
    Proof. cmp_antisym cmp_cargo. Qed.

    Lemma compare_lt_trans : forall x y z,
        compare x y = Lt -> compare y z = Lt -> compare x z = Lt.
    Proof. cmp_lt_trans cmp_cargo. Qed.
  End VPlus.
  Module VPOT := UOTFromCompare VPlus.

  Module T := Core NPOT VPOT.

  Module SOvp := SetOps V T.Pkg VSet T.PkgSet.
  Module SOpp := SetOps Pkg T.Pkg PkgSet T.PkgSet.
  Module SOsp := SetOps PkgF T.Pkg SupportSet T.PkgSet.
  Module SOslp := SetOps SlotElt T.Pkg SlotRel T.PkgSet.
  Module SOfp := SetOps FDefElt T.Pkg FDefRel T.PkgSet.
  Module SOlp := SetOps LinkElt T.Pkg LinkRel T.PkgSet.
  Module SOvv := SetOps V VPOT VSet T.VSet.

  (* the versions of a name are classes, not versions: one candidate per
     granularity class the requirement meets *)
  Definition classesOf (g : V.t -> G.t) (vs : VSet.t) : T.VSet.t :=
    SOvv.map (fun u => VPlus.WClass (g u)) vs.

  (* and the class's own members, which is what travels to the crate
     name, where version uniqueness then picks exactly one *)
  Definition inClass (g : V.t -> G.t) (gr : G.t) (vs : VSet.t) : T.VSet.t :=
    SOvv.filterMap
      (fun u => if GEqb.eqb (g u) gr then Some (VPlus.WOrig u) else None) vs.

  (* whether a class is one the requirement meets, which is what makes a
     per-site node exist: the guard the lookups test so that they answer
     nowhere else *)
  Definition classMet (g : V.t -> G.t) (gr : G.t) (vs : VSet.t) : bool :=
    VSet.exists_ (fun u => GEqb.eqb (g u) gr) vs.

  Definition transRoot : T.Pkg.t := (NPlus.CRoot, VPlus.WUnit).

  Definition crateReal (g : V.t -> G.t) (R : PkgSet.t) : T.PkgSet.t :=
    SOpp.map (fun '(m, v) => (NPlus.CCrate m (g v), VPlus.WOrig v)) R.

  Definition featReal (g : V.t -> G.t) (support : SupportSet.t)
    : T.PkgSet.t :=
    SOsp.map (fun '((m, v), f) => (NPlus.CFeatP m f (g v), VPlus.WOrig v)) support.

  Definition slotReal (g : V.t -> G.t) (R : PkgSet.t) (Slots : SlotRel.t)
      (rc : Pkg.t) : T.PkgSet.t :=
    SOslp.unionMap (fun '((m, v), d) =>
        if slotActive rc (m, v) d
        then SOvp.map (fun u => (NPlus.CSlot m v (sKey d), VPlus.WClass (g u)))
               (evalReq R (sTarget d) (sReq d))
        else T.PkgSet.empty)
      Slots.

  Definition decReal (g : V.t -> G.t) (R : PkgSet.t) (FDefs : FDefRel.t)
      (Slots : SlotRel.t) (rc : Pkg.t)
    : T.PkgSet.t :=
    SOfp.unionMap (fun '(((m, v), f), e) =>
        match entryFeatD e with
        | Some (a, feat) =>
            SOslp.unionMap (fun '(_, d) =>
                SOvp.map (fun u =>
                    (NPlus.CDec m v f (sKey d) feat, VPlus.WClass (g u)))
                  (evalReq R (sTarget d) (sReq d)))
              (slotsAt Slots rc (m, v) a)
        | None => T.PkgSet.empty
        end)
      FDefs.

  Definition linkReal (R : PkgSet.t) (Links : LinkRel.t) : T.PkgSet.t :=
    SOlp.filterMap (fun '(q, l) =>
        if PkgSet.mem q R then Some (NPlus.CLink l, VPlus.WMember q) else None)
      Links.

  Definition transReal (g : V.t -> G.t) (R : PkgSet.t)
      (support : SupportSet.t) (FDefs : FDefRel.t) (Slots : SlotRel.t)
      (Links : LinkRel.t) (rc : Pkg.t)
    : T.PkgSet.t :=
    T.PkgSet.union (T.PkgSet.singleton transRoot)
      (T.PkgSet.union (crateReal g R)
         (T.PkgSet.union (featReal g support)
            (T.PkgSet.union (slotReal g R Slots rc)
               (T.PkgSet.union (decReal g R FDefs Slots rc)
                  (linkReal R Links))))).

  (* The lookups below say what one name or one package answers, without
     the instance existing.  That is what the driver needs, since a crate
     is parsed the first time a lookup reads its name, so materialising
     transReal to filter it would defeat the laziness the frontend is
     built on.  The edge relation is then built out of the per-package
     lookup rather than beside it, so the two cannot disagree. *)

  Module SOsv := SetOps SlotElt VPOT SlotRel T.VSet.
  Module SOlv := SetOps LinkElt VPOT LinkRel T.VSet.
  Module SOpv2 := SetOps Pkg VPOT PkgSet T.VSet.
  Module SOspv := SetOps PkgF VPOT SupportSet T.VSet.
  Module SOsh := SetOps SlotElt T.Dependees SlotRel T.DependeesSet.
  Module SOfh := SetOps FDefElt T.Dependees FDefRel T.DependeesSet.
  Module SOlh := SetOps LinkElt T.Dependees LinkRel T.DependeesSet.
  Module SOfsh := SetOps F T.Dependees FSet T.DependeesSet.

  (* the versions of one name: a crate's are its repository versions in
     that class, a feature name's are the versions supporting it, and a
     per-site node's are the classes its requirement meets *)
  Definition versions (g : V.t -> G.t) (R : PkgSet.t)
      (support : SupportSet.t) (FDefs : FDefRel.t) (Slots : SlotRel.t)
      (Links : LinkRel.t) (rc : Pkg.t)
      (n : NPlus.t) : T.VSet.t :=
    match n with
    | NPlus.CRoot => T.VSet.singleton VPlus.WUnit
    | NPlus.CCrate m gr =>
        SOpv2.filterMap (fun '(n', v) =>
            if andb (NEqb.eqb n' m) (GEqb.eqb (g v) gr)
            then Some (VPlus.WOrig v) else None)
          R
    | NPlus.CFeatP m f gr =>
        SOspv.filterMap (fun '((n', v), f') =>
            if andb (andb (NEqb.eqb n' m) (FEqb.eqb f' f))
                 (GEqb.eqb (g v) gr)
            then Some (VPlus.WOrig v) else None)
          support
    | NPlus.CSlot m v k =>
        SOsv.unionMap (fun '(_, d) =>
            classesOf g (evalReq R (sTarget d) (sReq d)))
          (slotsAtKey Slots rc (m, v) k)
    | NPlus.CDec m v f k feat =>
        if fdEntryb FDefs (m, v) f (kAlias k) feat
        then SOsv.unionMap (fun '(_, d) =>
               classesOf g (evalReq R (sTarget d) (sReq d)))
             (slotsAtKey Slots rc (m, v) k)
        else T.VSet.empty
    | NPlus.CLink l =>
        SOlv.filterMap (fun '(q, l') =>
            if andb (LEqb.eqb l' l) (PkgSet.mem q R)
            then Some (VPlus.WMember q) else None)
          Links
    end.

  (* and the edges out of one package, by the shape of its name.  Every
     branch is empty where the package is not real, so the relation built
     from it below and the lookup answer the same thing at every p. *)
  Definition dependees (g : V.t -> G.t) (R : PkgSet.t)
      (support : SupportSet.t) (FDefs : FDefRel.t) (Slots : SlotRel.t)
      (Links : LinkRel.t) (dflt : F.t)
      (rc : Pkg.t) (rootFeats : FSet.t) (p : T.Pkg.t)
    : T.DependeesSet.t :=
    match p with
    | (NPlus.CRoot, VPlus.WUnit) =>
        let '(m, v) := rc in
        T.DependeesSet.add
          (NPlus.CCrate m (g v), T.VSet.singleton (VPlus.WOrig v))
          (SOfsh.map (fun f =>
               (NPlus.CFeatP m f (g v), T.VSet.singleton (VPlus.WOrig v)))
             rootFeats)
    | (NPlus.CCrate m gr, VPlus.WOrig v) =>
        if negb (andb (GEqb.eqb (g v) gr) (PkgSet.mem (m, v) R))
        then T.DependeesSet.empty else
        T.DependeesSet.union
          (SOsh.filterMap (fun '(q, d) =>
               if andb (PkgEqb.eqb q (m, v))
                    (andb (slotActive rc (m, v) d)
                       (negb (sOptional d)))
               then Some (NPlus.CSlot m v (sKey d),
                          classesOf g (evalReq R (sTarget d) (sReq d)))
               else None)
             Slots)
          (SOlh.filterMap (fun '(q, l) =>
               if PkgEqb.eqb q (m, v)
               then Some (NPlus.CLink l,
                          T.VSet.singleton (VPlus.WMember (m, v)))
               else None)
             Links)
    | (NPlus.CFeatP m f gr, VPlus.WOrig v) =>
        if negb (GEqb.eqb (g v) gr) then T.DependeesSet.empty else
        if negb (SupportSet.mem ((m, v), f) support)
        then T.DependeesSet.empty else
        T.DependeesSet.add
          (NPlus.CCrate m (g v), T.VSet.singleton (VPlus.WOrig v))
          (SOfh.unionMap (fun '(((n', v'), f'), e) =>
               if negb (andb (PkgEqb.eqb (n', v') (m, v)) (FEqb.eqb f' f))
               then T.DependeesSet.empty
               else
                 T.DependeesSet.union
                   (match e with
                    | FEntry.EFeat f2 =>
                        T.DependeesSet.singleton
                          (NPlus.CFeatP m f2 (g v),
                           T.VSet.singleton (VPlus.WOrig v))
                    | _ => T.DependeesSet.empty
                    end)
                   (T.DependeesSet.union
                      (match entryActivates e with
                       | Some a =>
                           SOsh.map (fun '(_, d) =>
                               (NPlus.CSlot m v (sKey d),
                                classesOf g
                                  (evalReq R (sTarget d) (sReq d))))
                             (slotsAt Slots rc (m, v) a)
                       | None => T.DependeesSet.empty
                       end)
                      (match entryFeatD e with
                       | Some (a, feat) =>
                           SOsh.map (fun '(_, d) =>
                               (NPlus.CDec m v f (sKey d) feat,
                                classesOf g
                                  (evalReq R (sTarget d) (sReq d))))
                             (slotsAt Slots rc (m, v) a)
                       | None => T.DependeesSet.empty
                       end)))
             FDefs)
    | (NPlus.CSlot m v k, VPlus.WClass gr) =>
        SOsh.unionMap (fun '(_, d) =>
            if negb (classMet g gr (evalReq R (sTarget d) (sReq d)))
            then T.DependeesSet.empty else
            T.DependeesSet.add
              (NPlus.CCrate (sTarget d) gr,
               inClass g gr (evalReq R (sTarget d) (sReq d)))
              (SOfsh.map (fun f =>
                   (NPlus.CFeatP (sTarget d) f gr,
                    inClass g gr (evalReq R (sTarget d) (sReq d))))
                 (slotRequests d dflt)))
          (slotsAtKey Slots rc (m, v) k)
    | (NPlus.CDec m v f k feat, VPlus.WClass gr) =>
        if negb (fdEntryb FDefs (m, v) f (kAlias k) feat)
        then T.DependeesSet.empty else
        SOsh.unionMap (fun '(_, d) =>
            if negb (classMet g gr (evalReq R (sTarget d) (sReq d)))
            then T.DependeesSet.empty else
            T.DependeesSet.add
              (NPlus.CSlot m v k, T.VSet.singleton (VPlus.WClass gr))
              (T.DependeesSet.singleton
                 (NPlus.CFeatP (sTarget d) feat gr,
                  inClass g gr (evalReq R (sTarget d) (sReq d)))))
          (slotsAtKey Slots rc (m, v) k)
    | _ => T.DependeesSet.empty
    end.

  Module SOhe := SetOps T.Dependees T.DepElt T.DependeesSet T.DepRel.
  Definition depEdges (p : T.Pkg.t) (hs : T.DependeesSet.t) : T.DepRel.t :=
    SOhe.map (fun h => (p, h)) hs.

  Module SOpe := SetOps T.Pkg T.DepElt T.PkgSet T.DepRel.
  (* the instance is the lookup iterated over the real packages: the
     edges out of a package are what that package answers, and a package
     that is not real has none *)
  Definition transDeps (g : V.t -> G.t) (R : PkgSet.t)
      (support : SupportSet.t) (FDefs : FDefRel.t) (Slots : SlotRel.t)
      (Links : LinkRel.t) (dflt : F.t)
      (rc : Pkg.t) (rootFeats : FSet.t) : T.DepRel.t :=
    SOpe.unionMap (fun p =>
        depEdges p
          (dependees g R support FDefs Slots Links dflt rc
             rootFeats p))
      (transReal g R support FDefs Slots Links rc).

  Lemma mem_classesOf : forall g vs w,
      T.VSet.In w (classesOf g vs) <->
      exists u, VSet.In u vs /\ w = VPlus.WClass (g u).
  Proof.
    intros g vs w; unfold classesOf; rewrite SOvv.mem_map; reflexivity.
  Qed.

  Lemma mem_inClass : forall g gr vs w,
      T.VSet.In w (inClass g gr vs) <->
      exists u, VSet.In u vs /\ g u = gr /\ w = VPlus.WOrig u.
  Proof.
    intros g gr vs w; unfold inClass; rewrite SOvv.mem_filterMap.
    split.
    - intros [u [Hu He]].
      destruct (GEqb.eqb (g u) gr) eqn:Eg; [| discriminate].
      apply GEqb.eqb_true_iff in Eg.
      injection He as <-; exists u; repeat split; assumption.
    - intros [u [Hu [Hg ->]]]; exists u; split; [exact Hu |].
      rewrite (proj2 (GEqb.eqb_true_iff _ _) Hg); reflexivity.
  Qed.

  Lemma classMet_iff : forall g gr vs,
      classMet g gr vs = true <-> exists u, VSet.In u vs /\ g u = gr.
  Proof.
    intros g gr vs; unfold classMet; rewrite VSet.exists_spec'; split.
    - intros [u [Hu Hb]]; exists u; split;
        [exact Hu | exact (proj1 (GEqb.eqb_true_iff _ _) Hb)].
    - intros [u [Hu Hg]]; exists u; split;
        [exact Hu | exact (proj2 (GEqb.eqb_true_iff _ _) Hg)].
  Qed.

  Lemma mem_crateReal : forall g R x,
      T.PkgSet.In x (crateReal g R) <->
      exists m v, PkgSet.In (m, v) R /\
        x = (NPlus.CCrate m (g v), VPlus.WOrig v).
  Proof.
    intros g R x; unfold crateReal; rewrite SOpp.mem_map; split.
    - intros [[m v] [HR He]]; cbn beta iota in He.
      exists m, v; split; assumption.
    - intros [m [v [HR ->]]]; exists (m, v); split;
        [exact HR | reflexivity].
  Qed.

  Lemma mem_featReal : forall g support x,
      T.PkgSet.In x (featReal g support) <->
      exists m v f, SupportSet.In ((m, v), f) support /\
        x = (NPlus.CFeatP m f (g v), VPlus.WOrig v).
  Proof.
    intros g support x; unfold featReal; rewrite SOsp.mem_map; split.
    - intros [[[m v] f] [HR He]]; cbn beta iota in He.
      exists m, v, f; split; assumption.
    - intros [m [v [f [HR ->]]]]; exists ((m, v), f); split;
        [exact HR | reflexivity].
  Qed.

  Lemma mem_slotReal : forall g R Slots rc x,
      T.PkgSet.In x (slotReal g R Slots rc) <->
      exists m v d u, SlotRel.In ((m, v), d) Slots /\
        slotActive rc (m, v) d = true /\
        VSet.In u (evalReq R (sTarget d) (sReq d)) /\
        x = (NPlus.CSlot m v (sKey d), VPlus.WClass (g u)).
  Proof.
    intros g R Slots rc x; unfold slotReal.
    rewrite SOslp.mem_unionMap; split.
    - intros [[[m v] d] [Hs Hx]]; cbn beta iota in Hx.
      destruct (slotActive rc (m, v) d) eqn:Ea;
        [| exfalso; exact (SOvp.empty_in _ Hx)].
      apply SOvp.mem_map in Hx; destruct Hx as [u [Hu ->]].
      exists m, v, d, u; repeat split; assumption.
    - intros [m [v [d [u [Hs [Ha [Hu ->]]]]]]].
      exists ((m, v), d); split; [exact Hs | cbn beta iota].
      rewrite Ha; apply SOvp.mem_map; exists u; split;
        [exact Hu | reflexivity].
  Qed.

  Lemma mem_decReal : forall g R FDefs Slots rc x,
      T.PkgSet.In x (decReal g R FDefs Slots rc) <->
      exists m v f e a feat d u,
        FDefRel.In (((m, v), f), e) FDefs /\
        entryFeatD e = Some (a, feat) /\
        SlotRel.In ((m, v), d) Slots /\ sAlias d = a /\
        slotActive rc (m, v) d = true /\
        VSet.In u (evalReq R (sTarget d) (sReq d)) /\
        x = (NPlus.CDec m v f (sKey d) feat, VPlus.WClass (g u)).
  Proof.
    intros g R FDefs Slots rc x; unfold decReal.
    rewrite SOfp.mem_unionMap; split.
    - intros [[[[m v] f] e] [Hf Hx]]; cbn beta iota in Hx.
      destruct (entryFeatD e) as [[a feat] |] eqn:Ee;
        [| exfalso; exact (SOslp.empty_in _ Hx)].
      apply SOslp.mem_unionMap in Hx; destruct Hx as [[q d] [Hq Hx]];
        cbn beta iota in Hx.
      apply mem_slotsAt in Hq; destruct Hq as [Hs [-> [Ha Hact]]].
      apply SOvp.mem_map in Hx; destruct Hx as [u [Hu ->]].
      exists m, v, f, e, a, feat, d, u; repeat split; assumption.
    - intros [m [v [f [e [a [feat [d [u
        [Hf [Ee [Hs [Ha [Hact [Hu ->]]]]]]]]]]]]]].
      exists (((m, v), f), e); split; [exact Hf | cbn beta iota].
      rewrite Ee; apply SOslp.mem_unionMap; exists ((m, v), d); split.
      { apply mem_slotsAt; repeat split; assumption. }
      cbn beta iota; apply SOvp.mem_map; exists u; split;
        [exact Hu | reflexivity].
  Qed.

  Lemma mem_linkReal : forall R Links x,
      T.PkgSet.In x (linkReal R Links) <->
      exists q l, LinkRel.In (q, l) Links /\ PkgSet.In q R /\
        x = (NPlus.CLink l, VPlus.WMember q).
  Proof.
    intros R Links x; unfold linkReal; rewrite SOlp.mem_filterMap; split.
    - intros [[q l] [Hl He]]; cbn beta iota in He.
      destruct (PkgSet.mem q R) eqn:Em; [| discriminate].
      apply PkgSet.mem_spec in Em.
      injection He as <-; exists q, l; repeat split; assumption.
    - intros [q [l [Hl [HR ->]]]]; exists (q, l); split;
        [exact Hl | cbn beta iota].
      rewrite (proj2 (PkgSet.mem_spec _ _) HR); reflexivity.
  Qed.

  Lemma mem_transReal :
    forall g R support FDefs Slots Links rc x,
      T.PkgSet.In x
        (transReal g R support FDefs Slots Links rc) <->
      x = transRoot \/ T.PkgSet.In x (crateReal g R) \/
      T.PkgSet.In x (featReal g support) \/
      T.PkgSet.In x (slotReal g R Slots rc) \/
      T.PkgSet.In x (decReal g R FDefs Slots rc) \/
      T.PkgSet.In x (linkReal R Links).
  Proof.
    intros; unfold transReal; rewrite !T.PkgSet.union_spec.
    rewrite T.PkgSet.singleton_spec; reflexivity.
  Qed.

  Lemma mem_transDeps :
    forall g R support FDefs Slots Links dflt rc rootFeats
           (p : T.Pkg.t) (h : T.Dependees.t),
      T.DepRel.In (p, h)
        (transDeps g R support FDefs Slots Links dflt rc
           rootFeats) <->
      T.PkgSet.In p
        (transReal g R support FDefs Slots Links rc) /\
      T.DependeesSet.In h
        (dependees g R support FDefs Slots Links dflt rc
           rootFeats p).
  Proof.
    intros g R support FDefs Slots Links dflt rc rootFeats p
      [n vs]; unfold transDeps; rewrite SOpe.mem_unionMap.
    split.
    - intros [q [Hq Hy]]; cbn beta iota in Hy.
      unfold depEdges in Hy; apply SOhe.mem_map in Hy.
      destruct Hy as [e [He Hy]].
      injection Hy as -> He2.
      rewrite <- He2 in He.
      split; assumption.
    - intros [Hp Hh].
      exists p; split; [exact Hp | cbn beta iota].
      unfold depEdges; apply SOhe.mem_map.
      exists (n, vs); split; [exact Hh | reflexivity].
  Qed.

  (* Link edges run only into CLink, never out, and every other name
     answers at one version shape; the catch-all is those packages. *)
  Definition Inert (p : T.Pkg.t) : Prop :=
    match p with
    | (NPlus.CRoot, VPlus.WUnit) => False
    | (NPlus.CCrate _ _, VPlus.WOrig _) => False
    | (NPlus.CFeatP _ _ _, VPlus.WOrig _) => False
    | (NPlus.CSlot _ _ _, VPlus.WClass _) => False
    | (NPlus.CDec _ _ _ _ _, VPlus.WClass _) => False
    | _ => True
    end.

  Lemma dep_inert :
    forall g R support FDefs Slots Links dflt rc rootFeats p,
      Inert p ->
      dependees g R support FDefs Slots Links dflt rc
        rootFeats p = T.DependeesSet.empty.
  Proof.
    intros g R support FDefs Slots Links dflt rc rootFeats
      [n w] Hi; destruct n; destruct w; try (exfalso; exact Hi);
      reflexivity.
  Qed.

  Lemma mem_dep_root :
    forall g R support FDefs Slots Links dflt rn rv rootFeats h,
      T.DependeesSet.In h
        (dependees g R support FDefs Slots Links dflt (rn, rv)
           rootFeats transRoot) <->
      h = (NPlus.CCrate rn (g rv), T.VSet.singleton (VPlus.WOrig rv)) \/
      exists f, FSet.In f rootFeats /\
        h = (NPlus.CFeatP rn f (g rv), T.VSet.singleton (VPlus.WOrig rv)).
  Proof.
    intros; cbn [dependees transRoot].
    rewrite T.DependeesSet.add_spec, SOfsh.mem_map.
    split; (intros [Hx | [f [Hf Hx]]];
            [left; exact Hx
             | right; exists f; split; [exact Hf | exact Hx]]).
  Qed.

  Lemma mem_dep_crate :
    forall g R support FDefs Slots Links dflt rc rootFeats
           m gr v h,
      T.DependeesSet.In h
        (dependees g R support FDefs Slots Links dflt rc
           rootFeats (NPlus.CCrate m gr, VPlus.WOrig v)) <->
      g v = gr /\ PkgSet.In (m, v) R /\
      ((exists d, SlotRel.In ((m, v), d) Slots /\
          slotActive rc (m, v) d = true /\
          sOptional d = false /\
          h = (NPlus.CSlot m v (sKey d),
               classesOf g (evalReq R (sTarget d) (sReq d)))) \/
       (exists l, LinkRel.In ((m, v), l) Links /\
          h = (NPlus.CLink l, T.VSet.singleton (VPlus.WMember (m, v))))).
  Proof.
    intros; cbn [dependees].
    destruct (andb (GEqb.eqb (g v) gr) (PkgSet.mem (m, v) R)) eqn:Eb;
      cbn [negb].
    - apply andb_true_iff in Eb; destruct Eb as [Eg Em].
      apply GEqb.eqb_true_iff in Eg; apply PkgSet.mem_spec in Em.
      rewrite T.DependeesSet.union_spec, SOsh.mem_filterMap,
        SOlh.mem_filterMap.
      split.
      + intros [[[q d] [Hs He]] | [[q l] [Hl He]]]; cbn beta iota in He.
        * destruct (andb (PkgEqb.eqb q (m, v))
                      (andb (slotActive rc (m, v) d)
                         (negb (sOptional d)))) eqn:Ec; [| discriminate].
          apply andb_true_iff in Ec; destruct Ec as [Eq Ec].
          apply PkgEqb.eqb_true_iff in Eq; subst q.
          apply andb_true_iff in Ec; destruct Ec as [Ha Ho].
          apply negb_true_iff in Ho.
          injection He as <-.
          split; [exact Eg | split; [exact Em |]].
          left; exists d; repeat split; assumption.
        * destruct (PkgEqb.eqb q (m, v)) eqn:Eq; [| discriminate].
          apply PkgEqb.eqb_true_iff in Eq; subst q.
          injection He as <-.
          split; [exact Eg | split; [exact Em |]].
          right; exists l; split; [exact Hl | reflexivity].
      + intros [_ [_ [[d [Hs [Ha [Ho ->]]]] | [l [Hl ->]]]]].
        * left; exists ((m, v), d); split; [exact Hs | cbn beta iota].
          rewrite PkgEqb.eqb_refl, Ha, Ho; reflexivity.
        * right; exists ((m, v), l); split; [exact Hl | cbn beta iota].
          rewrite PkgEqb.eqb_refl; reflexivity.
    - split; [intro Hc; exfalso; exact (T.DependeesSet.empty_spec Hc) |].
      intros [Eg [Em _]]; exfalso.
      rewrite (proj2 (GEqb.eqb_true_iff _ _) Eg),
        (proj2 (PkgSet.mem_spec _ _) Em) in Eb; discriminate Eb.
  Qed.

  Lemma mem_dep_featP :
    forall g R support FDefs Slots Links dflt rc rootFeats
           m f gr v h,
      T.DependeesSet.In h
        (dependees g R support FDefs Slots Links dflt rc
           rootFeats (NPlus.CFeatP m f gr, VPlus.WOrig v)) <->
      g v = gr /\ SupportSet.In ((m, v), f) support /\
      (h = (NPlus.CCrate m (g v), T.VSet.singleton (VPlus.WOrig v)) \/
       exists e0, FDefRel.In (((m, v), f), e0) FDefs /\
         ((exists f', e0 = FEntry.EFeat f' /\
             h = (NPlus.CFeatP m f' (g v),
                  T.VSet.singleton (VPlus.WOrig v))) \/
          (exists a d, entryActivates e0 = Some a /\
             SlotRel.In ((m, v), d) Slots /\ sAlias d = a /\
             slotActive rc (m, v) d = true /\
             h = (NPlus.CSlot m v (sKey d),
                  classesOf g (evalReq R (sTarget d) (sReq d)))) \/
          (exists a feat d, entryFeatD e0 = Some (a, feat) /\
             SlotRel.In ((m, v), d) Slots /\ sAlias d = a /\
             slotActive rc (m, v) d = true /\
             h = (NPlus.CDec m v f (sKey d) feat,
                  classesOf g (evalReq R (sTarget d) (sReq d)))))).
  Proof.
    intros; cbn [dependees].
    destruct (GEqb.eqb (g v) gr) eqn:Eg; cbn [negb].
    2:{ split; [intro Hc; exfalso; exact (T.DependeesSet.empty_spec Hc) |].
        intros [Hg _]; exfalso;
          rewrite (proj2 (GEqb.eqb_true_iff _ _) Hg) in Eg;
          discriminate Eg. }
    apply GEqb.eqb_true_iff in Eg.
    destruct (SupportSet.mem ((m, v), f) support) eqn:Em; cbn [negb].
    2:{ split; [intro Hc; exfalso; exact (T.DependeesSet.empty_spec Hc) |].
        intros [_ [Hsp _]]; exfalso;
          rewrite (proj2 (SupportSet.mem_spec _ _) Hsp) in Em;
          discriminate Em. }
    apply SupportSet.mem_spec in Em.
    rewrite T.DependeesSet.add_spec, SOfh.mem_unionMap.
    split.
    - intros [Hh | [[[[n' v'] f'] e0] [Hfd Hh]]].
      + split; [exact Eg | split; [exact Em | left; exact Hh]].
      + cbn beta iota in Hh.
        destruct (negb (andb (PkgEqb.eqb (n', v') (m, v))
                         (FEqb.eqb f' f))) eqn:Ek;
          [exfalso; exact (T.DependeesSet.empty_spec Hh) |].
        apply negb_false_iff, andb_true_iff in Ek; destruct Ek as [Ep Ef].
        apply PkgEqb.eqb_true_iff in Ep; injection Ep as -> ->.
        apply FEqb.eqb_true_iff in Ef; subst f'.
        rewrite !T.DependeesSet.union_spec in Hh.
        split; [exact Eg | split; [exact Em | right]].
        exists e0; split; [exact Hfd |].
        destruct Hh as [Hh | [Hh | Hh]].
        * destruct e0 as [f2 | a0 | a0 feat0 | a0 feat0];
            try (exfalso; exact (T.DependeesSet.empty_spec Hh)).
          apply T.DependeesSet.singleton_spec in Hh; subst h.
          left; exists f2; split; reflexivity.
        * destruct (entryActivates e0) as [a |] eqn:Ea;
            [| exfalso; exact (T.DependeesSet.empty_spec Hh)].
          apply SOsh.mem_map in Hh; destruct Hh as [[q d] [Hq ->]].
          apply mem_slotsAt in Hq; destruct Hq as [Hs [-> [Ha Hact]]].
          right; left; exists a, d; repeat split; assumption.
        * destruct (entryFeatD e0) as [[a feat] |] eqn:Ea;
            [| exfalso; exact (T.DependeesSet.empty_spec Hh)].
          apply SOsh.mem_map in Hh; destruct Hh as [[q d] [Hq ->]].
          apply mem_slotsAt in Hq; destruct Hq as [Hs [-> [Ha Hact]]].
          right; right; exists a, feat, d; repeat split; assumption.
    - intros [_ [_ [Hh | [e0 [Hfd Hcase]]]]]; [left; exact Hh | right].
      exists (((m, v), f), e0); split; [exact Hfd | cbn beta iota].
      rewrite PkgEqb.eqb_refl, FEqb.eqb_refl; cbn [andb negb].
      rewrite !T.DependeesSet.union_spec.
      destruct Hcase as [[f2 [-> ->]] | [Hc | Hc]].
      + left; cbn [entryActivates entryFeatD].
        apply T.DependeesSet.singleton_spec; reflexivity.
      + destruct Hc as [a [d [Ea [Hs [Ha [Hact ->]]]]]].
        right; left; rewrite Ea; apply SOsh.mem_map.
        exists ((m, v), d); split; [| reflexivity].
        apply mem_slotsAt; repeat split; assumption.
      + destruct Hc as [a [feat [d [Ea [Hs [Ha [Hact ->]]]]]]].
        right; right; rewrite Ea; apply SOsh.mem_map.
        exists ((m, v), d); split; [| reflexivity].
        apply mem_slotsAt; repeat split; assumption.
  Qed.

  Lemma mem_dep_slot :
    forall g R support FDefs Slots Links dflt rc rootFeats
           m v k gr h,
      T.DependeesSet.In h
        (dependees g R support FDefs Slots Links dflt rc
           rootFeats (NPlus.CSlot m v k, VPlus.WClass gr)) <->
      exists d u, SlotRel.In ((m, v), d) Slots /\ sKey d = k /\
        slotActive rc (m, v) d = true /\
        VSet.In u (evalReq R (sTarget d) (sReq d)) /\ g u = gr /\
        (h = (NPlus.CCrate (sTarget d) gr,
              inClass g gr (evalReq R (sTarget d) (sReq d))) \/
         exists f, FSet.In f (slotRequests d dflt) /\
           h = (NPlus.CFeatP (sTarget d) f gr,
                inClass g gr (evalReq R (sTarget d) (sReq d)))).
  Proof.
    intros; cbn [dependees]; rewrite SOsh.mem_unionMap; split.
    - intros [[q d] [Hq Hh]]; cbn beta iota in Hh.
      apply mem_slotsAtKey in Hq; destruct Hq as [Hs [-> [Ha Hact]]].
      destruct (classMet g gr (evalReq R (sTarget d) (sReq d))) eqn:Ec;
        cbn [negb] in Hh;
        [| exfalso; exact (T.DependeesSet.empty_spec Hh)].
      apply classMet_iff in Ec; destruct Ec as [u [Hu Hgu]].
      exists d, u; repeat split; try assumption.
      rewrite T.DependeesSet.add_spec, SOfsh.mem_map in Hh.
      destruct Hh as [Hh | [f [Hf Hh]]];
        [left; exact Hh | right; exists f; split; [exact Hf | exact Hh]].
    - intros [d [u [Hs [Ha [Hact [Hu [Hgu Hh]]]]]]].
      exists ((m, v), d); split;
        [apply mem_slotsAtKey; repeat split; assumption | cbn beta iota].
      rewrite (proj2 (classMet_iff _ _ _) (ex_intro _ u (conj Hu Hgu)));
        cbn [negb].
      rewrite T.DependeesSet.add_spec, SOfsh.mem_map.
      destruct Hh as [Hh | [f [Hf Hh]]];
        [left; exact Hh | right; exists f; split; [exact Hf | exact Hh]].
  Qed.

  Lemma mem_dep_dec :
    forall g R support FDefs Slots Links dflt rc rootFeats
           m v f k feat gr h,
      T.DependeesSet.In h
        (dependees g R support FDefs Slots Links dflt rc
           rootFeats (NPlus.CDec m v f k feat, VPlus.WClass gr)) <->
      (exists e0, FDefRel.In (((m, v), f), e0) FDefs /\
         entryFeatD e0 = Some (kAlias k, feat)) /\
      exists d u, SlotRel.In ((m, v), d) Slots /\ sKey d = k /\
        slotActive rc (m, v) d = true /\
        VSet.In u (evalReq R (sTarget d) (sReq d)) /\ g u = gr /\
        (h = (NPlus.CSlot m v k, T.VSet.singleton (VPlus.WClass gr)) \/
         h = (NPlus.CFeatP (sTarget d) feat gr,
              inClass g gr (evalReq R (sTarget d) (sReq d)))).
  Proof.
    intros; cbn [dependees].
    destruct (fdEntryb FDefs (m, v) f (kAlias k) feat) eqn:Eb; cbn [negb].
    2:{ split; [intro Hc; exfalso; exact (T.DependeesSet.empty_spec Hc) |].
        intros [He _]; exfalso;
          rewrite (proj2 (fdEntryb_iff _ _ _ _ _) He) in Eb;
          discriminate Eb. }
    apply fdEntryb_iff in Eb.
    rewrite SOsh.mem_unionMap; split.
    - intros [[q d] [Hq Hh]]; cbn beta iota in Hh.
      apply mem_slotsAtKey in Hq; destruct Hq as [Hs [-> [Ha Hact]]].
      destruct (classMet g gr (evalReq R (sTarget d) (sReq d))) eqn:Ec;
        cbn [negb] in Hh;
        [| exfalso; exact (T.DependeesSet.empty_spec Hh)].
      apply classMet_iff in Ec; destruct Ec as [u [Hu Hgu]].
      split; [exact Eb |].
      exists d, u; repeat split; try assumption.
      rewrite T.DependeesSet.add_spec, T.DependeesSet.singleton_spec
        in Hh; exact Hh.
    - intros [_ [d [u [Hs [Ha [Hact [Hu [Hgu Hh]]]]]]]].
      exists ((m, v), d); split;
        [apply mem_slotsAtKey; repeat split; assumption | cbn beta iota].
      rewrite (proj2 (classMet_iff _ _ _) (ex_intro _ u (conj Hu Hgu)));
        cbn [negb].
      rewrite T.DependeesSet.add_spec, T.DependeesSet.singleton_spec.
      exact Hh.
  Qed.

  (* Every answer has a real package to come out of: this is what makes
     the relation built from the lookup agree with the lookup at every
     package, real or not. *)
  Lemma dep_real :
    forall g R support FDefs Slots Links dflt rc rootFeats p h,
      T.DependeesSet.In h
        (dependees g R support FDefs Slots Links dflt rc
           rootFeats p) ->
      T.PkgSet.In p
        (transReal g R support FDefs Slots Links rc).
  Proof.
    intros g R support FDefs Slots Links dflt rc rootFeats
      [n w] h Hh.
    destruct n as [ | m gr | m f gr | m v k | m v f k feat | l ];
      destruct w as [ | u | gr' | q ];
      try (rewrite dep_inert in Hh by exact I;
           exfalso; exact (T.DependeesSet.empty_spec Hh));
      apply mem_transReal.
    - left; reflexivity.
    - apply mem_dep_crate in Hh; destruct Hh as [Hg [HR _]].
      right; left; apply mem_crateReal; exists m, u; split;
        [exact HR | rewrite Hg; reflexivity].
    - apply mem_dep_featP in Hh; destruct Hh as [Hg [Hsp _]].
      right; right; left; apply mem_featReal; exists m, u, f; split;
        [exact Hsp | rewrite Hg; reflexivity].
    - apply mem_dep_slot in Hh;
        destruct Hh as [d [u [Hs [Ha [Hact [Hu [Hgu _]]]]]]].
      right; right; right; left; apply mem_slotReal.
      exists m, v, d, u; repeat split; try assumption.
      rewrite Ha, Hgu; reflexivity.
    - apply mem_dep_dec in Hh;
        destruct Hh as [[e0 [Hfd Hee]]
                        [d [u [Hs [Ha [Hact [Hu [Hgu _]]]]]]]].
      right; right; right; right; left; apply mem_decReal.
      exists m, v, f, e0, (kAlias k), feat, d, u; repeat split;
        try assumption.
      + rewrite <- Ha; reflexivity.
      + rewrite Ha, Hgu; reflexivity.
  Qed.

  Module SOtp := SetOps T.Pkg Pkg T.PkgSet PkgSet.
  Definition decodeS (S : T.PkgSet.t) : PkgSet.t :=
    SOtp.filterMap (fun '(n, w) =>
        match n, w with
        | NPlus.CCrate m _, VPlus.WOrig v => Some (m, v)
        | _, _ => None
        end)
      S.

  Lemma mem_decodeS : forall S m v,
      PkgSet.In (m, v) (decodeS S) <->
      exists gr, T.PkgSet.In (NPlus.CCrate m gr, VPlus.WOrig v) S.
  Proof.
    intros S m v; unfold decodeS; rewrite SOtp.mem_filterMap; split.
    - intros [[n w] [Hin He]]; cbn beta iota in He.
      destruct n; try discriminate; destruct w; try discriminate.
      injection He as -> ->; exists gr; exact Hin.
    - intros [gr Hin]; exists (NPlus.CCrate m gr, VPlus.WOrig v); split;
        [exact Hin | reflexivity].
  Qed.

  Module SOtf := SetOps T.Pkg F T.PkgSet FSet.
  (* the class the feature node carries is the crate version's own, so
     the decode reads the version off the node and ignores the class *)
  Definition featsAt (S : T.PkgSet.t) (p : Pkg.t) : FSet.t :=
    SOtf.filterMap (fun '(n, w) =>
        match n, w with
        | NPlus.CFeatP m f _, VPlus.WOrig v =>
            if PkgEqb.eqb (m, v) p then Some f else None
        | _, _ => None
        end)
      S.

  Lemma mem_featsAt : forall S m v f,
      FSet.In f (featsAt S (m, v)) <->
      exists gr, T.PkgSet.In (NPlus.CFeatP m f gr, VPlus.WOrig v) S.
  Proof.
    intros S m v f; unfold featsAt; rewrite SOtf.mem_filterMap; split.
    - intros [[n w] [Hin He]]; cbn beta iota in He.
      destruct n; try discriminate; destruct w; try discriminate.
      destruct (PkgEqb.eqb (m0, v0) (m, v)) eqn:Ep; [| discriminate].
      apply PkgEqb.eqb_true_iff in Ep; injection Ep as -> ->.
      injection He as ->; exists gr; exact Hin.
    - intros [gr Hin]; exists (NPlus.CFeatP m f gr, VPlus.WOrig v); split;
        [exact Hin | cbn beta iota].
      rewrite PkgEqb.eqb_refl; reflexivity.
  Qed.

  Module SOpf := SetOps Pkg Featured PkgSet FeaturedSet.
  Definition decodeFS (S : T.PkgSet.t) : FeaturedSet.t :=
    SOpf.map (fun p => (p, featsAt S p)) (decodeS S).

  Lemma mem_decodeFS : forall S p fs,
      FeaturedSet.In (p, fs) (decodeFS S) <->
      PkgSet.In p (decodeS S) /\ fs = featsAt S p.
  Proof.
    intros S p fs; unfold decodeFS; rewrite SOpf.mem_map; split.
    - intros [q [Hq He]]; injection He as -> ->; split;
        [exact Hq | reflexivity].
    - intros [Hp ->]; exists p; split; [exact Hp | reflexivity].
  Qed.

  Module SOtv2 := SetOps T.Pkg V T.PkgSet VSet.
  (* a slot node holds a class, not a version, so the parent edge's
     version is not readable off the node: it is the member of that class
     the target crate name carries, which Core's version uniqueness makes
     unique *)
  Definition targets (S : T.PkgSet.t) (m : N.t) (gr : G.t) : VSet.t :=
    SOtv2.filterMap (fun '(n, w) =>
        match n, w with
        | NPlus.CCrate m' gr', VPlus.WOrig u =>
            if andb (NEqb.eqb m' m) (GEqb.eqb gr' gr) then Some u else None
        | _, _ => None
        end)
      S.

  Lemma mem_targets : forall S m gr u,
      VSet.In u (targets S m gr) <->
      T.PkgSet.In (NPlus.CCrate m gr, VPlus.WOrig u) S.
  Proof.
    intros S m gr u; unfold targets; rewrite SOtv2.mem_filterMap; split.
    - intros [[n w] [Hin He]]; cbn beta iota in He.
      destruct n; try discriminate; destruct w; try discriminate.
      destruct (andb (NEqb.eqb m0 m) (GEqb.eqb gr0 gr)) eqn:Eb;
        [| discriminate].
      apply andb_true_iff in Eb; destruct Eb as [En Eg].
      apply NEqb.eqb_true_iff in En; apply GEqb.eqb_true_iff in Eg.
      subst m0 gr0; injection He as ->; exact Hin.
    - intro Hin; exists (NPlus.CCrate m gr, VPlus.WOrig u); split;
        [exact Hin | cbn beta iota].
      rewrite NEqb.eqb_refl, GEqb.eqb_refl; reflexivity.
  Qed.

  Module SOtpar := SetOps T.Pkg ParentElt T.PkgSet ParentRel.
  Module SOslpar := SetOps SlotElt ParentElt SlotRel ParentRel.
  Module SOvpar := SetOps V ParentElt VSet ParentRel.
  Definition decodeParents (Slots : SlotRel.t)
      (rc : Pkg.t) (S : T.PkgSet.t) : ParentRel.t :=
    SOtpar.unionMap (fun '(n, w) =>
        match n, w with
        | NPlus.CSlot m v k, VPlus.WClass gr =>
            SOslpar.unionMap (fun '(_, d) =>
                SOvpar.map (fun u => (((m, v), k), u))
                  (targets S (sTarget d) gr))
              (slotsAtKey Slots rc (m, v) k)
        | _, _ => ParentRel.empty
        end)
      S.

  Lemma mem_decodeParents : forall Slots rc S m v k u,
      ParentRel.In (((m, v), k), u) (decodeParents Slots rc S) <->
      exists gr d, T.PkgSet.In (NPlus.CSlot m v k, VPlus.WClass gr) S /\
        SlotRel.In ((m, v), d) Slots /\ sKey d = k /\
        slotActive rc (m, v) d = true /\
        T.PkgSet.In (NPlus.CCrate (sTarget d) gr, VPlus.WOrig u) S.
  Proof.
    intros Slots rc S m v k u; unfold decodeParents.
    rewrite SOtpar.mem_unionMap; split.
    - intros [[n w] [Hin Hy]]; cbn beta iota in Hy.
      destruct n; try (exfalso; exact (SOslpar.empty_in _ Hy));
        destruct w; try (exfalso; exact (SOslpar.empty_in _ Hy)).
      apply SOslpar.mem_unionMap in Hy; destruct Hy as [[q d] [Hq Hy]];
        cbn beta iota in Hy.
      apply SOvpar.mem_map in Hy; destruct Hy as [u' [Hu' He]].
      injection He as -> -> -> ->.
      apply mem_slotsAtKey in Hq; destruct Hq as [Hs [-> [Ha Hact]]].
      exists gr, d; repeat split; try assumption.
      apply mem_targets; exact Hu'.
    - intros [gr [d [Hslot [Hs [Ha [Hact Hcr]]]]]].
      exists (NPlus.CSlot m v k, VPlus.WClass gr); split;
        [exact Hslot | cbn beta iota].
      apply SOslpar.mem_unionMap; exists ((m, v), d); split.
      { apply mem_slotsAtKey; repeat split; assumption. }
      cbn beta iota; apply SOvpar.mem_map; exists u; split;
        [apply mem_targets; exact Hcr | reflexivity].
  Qed.

  Module Lookup.
    Theorem versions_lookupRoot :
      forall g R support FDefs Slots Links rc w,
        T.PkgSet.In (NPlus.CRoot, w)
          (transReal g R support FDefs Slots Links rc) <->
        T.VSet.In w
          (versions g R support FDefs Slots Links rc NPlus.CRoot).
    Proof.
      intros; rewrite mem_transReal; cbn [versions].
      rewrite T.VSet.singleton_spec; split.
      - intros [He | [He | [He | [He | [He | He]]]]].
        + unfold transRoot in He; injection He as ->; reflexivity.
        + apply mem_crateReal in He;
            destruct He as [? [? [_ He]]]; discriminate He.
        + apply mem_featReal in He;
            destruct He as [? [? [? [_ He]]]]; discriminate He.
        + apply mem_slotReal in He;
            destruct He as [? [? [? [? [_ [_ [_ He]]]]]]];
            discriminate He.
        + apply mem_decReal in He;
            destruct He as [? [? [? [? [? [? [? [?
              [_ [_ [_ [_ [_ [_ He]]]]]]]]]]]]]]; discriminate He.
        + apply mem_linkReal in He;
            destruct He as [? [? [_ [_ He]]]]; discriminate He.
      - intros ->; left; reflexivity.
    Qed.

    Theorem versions_lookupCrate :
      forall g R support FDefs Slots Links rc m gr w,
        T.PkgSet.In (NPlus.CCrate m gr, w)
          (transReal g R support FDefs Slots Links rc) <->
        T.VSet.In w
          (versions g R support FDefs Slots Links rc
             (NPlus.CCrate m gr)).
    Proof.
      intros; rewrite mem_transReal; cbn [versions].
      rewrite SOpv2.mem_filterMap; split.
      - intros [He | [He | [He | [He | [He | He]]]]].
        + unfold transRoot in He; discriminate He.
        + apply mem_crateReal in He; destruct He as [n' [v [HR He]]].
          injection He as E1 E2 E3.
          exists (n', v); split; [exact HR | cbn beta iota].
          rewrite <- E1, <- E2, E3, NEqb.eqb_refl, GEqb.eqb_refl;
            reflexivity.
        + apply mem_featReal in He;
            destruct He as [? [? [? [_ He]]]]; discriminate He.
        + apply mem_slotReal in He;
            destruct He as [? [? [? [? [_ [_ [_ He]]]]]]];
            discriminate He.
        + apply mem_decReal in He;
            destruct He as [? [? [? [? [? [? [? [?
              [_ [_ [_ [_ [_ [_ He]]]]]]]]]]]]]]; discriminate He.
        + apply mem_linkReal in He;
            destruct He as [? [? [_ [_ He]]]]; discriminate He.
      - intros [[n' v] [HR He]]; cbn beta iota in He.
        destruct (andb (NEqb.eqb n' m) (GEqb.eqb (g v) gr)) eqn:Eb;
          [| discriminate].
        apply andb_true_iff in Eb; destruct Eb as [En Eg].
        apply NEqb.eqb_true_iff in En; apply GEqb.eqb_true_iff in Eg.
        subst n'; injection He as <-.
        right; left; apply mem_crateReal; exists m, v; split;
          [exact HR | rewrite Eg; reflexivity].
    Qed.

    Theorem versions_lookupFeatP :
      forall g R support FDefs Slots Links rc m f gr w,
        T.PkgSet.In (NPlus.CFeatP m f gr, w)
          (transReal g R support FDefs Slots Links rc) <->
        T.VSet.In w
          (versions g R support FDefs Slots Links rc
             (NPlus.CFeatP m f gr)).
    Proof.
      intros; rewrite mem_transReal; cbn [versions].
      rewrite SOspv.mem_filterMap; split.
      - intros [He | [He | [He | [He | [He | He]]]]].
        + unfold transRoot in He; discriminate He.
        + apply mem_crateReal in He;
            destruct He as [? [? [_ He]]]; discriminate He.
        + apply mem_featReal in He; destruct He as [n' [v [f' [Hsp He]]]].
          injection He as E1 E2 E3 E4.
          exists ((n', v), f'); split; [exact Hsp | cbn beta iota].
          rewrite <- E1, <- E2, <- E3, E4, NEqb.eqb_refl, FEqb.eqb_refl,
            GEqb.eqb_refl; reflexivity.
        + apply mem_slotReal in He;
            destruct He as [? [? [? [? [_ [_ [_ He]]]]]]];
            discriminate He.
        + apply mem_decReal in He;
            destruct He as [? [? [? [? [? [? [? [?
              [_ [_ [_ [_ [_ [_ He]]]]]]]]]]]]]]; discriminate He.
        + apply mem_linkReal in He;
            destruct He as [? [? [_ [_ He]]]]; discriminate He.
      - intros [[[n' v] f'] [Hsp He]]; cbn beta iota in He.
        destruct (andb (andb (NEqb.eqb n' m) (FEqb.eqb f' f))
                    (GEqb.eqb (g v) gr)) eqn:Eb; [| discriminate].
        apply andb_true_iff in Eb; destruct Eb as [Enf Eg].
        apply andb_true_iff in Enf; destruct Enf as [En Ef].
        apply NEqb.eqb_true_iff in En; apply FEqb.eqb_true_iff in Ef.
        apply GEqb.eqb_true_iff in Eg.
        subst n' f'; injection He as <-.
        right; right; left; apply mem_featReal; exists m, v, f; split;
          [exact Hsp | rewrite Eg; reflexivity].
    Qed.

    Theorem versions_lookupSlot :
      forall g R support FDefs Slots Links rc m v k w,
        T.PkgSet.In (NPlus.CSlot m v k, w)
          (transReal g R support FDefs Slots Links rc) <->
        T.VSet.In w
          (versions g R support FDefs Slots Links rc
             (NPlus.CSlot m v k)).
    Proof.
      intros; rewrite mem_transReal; cbn [versions].
      rewrite SOsv.mem_unionMap; split.
      - intros [He | [He | [He | [He | [He | He]]]]].
        + unfold transRoot in He; discriminate He.
        + apply mem_crateReal in He;
            destruct He as [? [? [_ He]]]; discriminate He.
        + apply mem_featReal in He;
            destruct He as [? [? [? [_ He]]]]; discriminate He.
        + apply mem_slotReal in He;
            destruct He as [n' [v' [d [u [Hs [Hact [Hu He]]]]]]].
          injection He as E1 E2 E3 E4; subst n' v' k w.
          exists ((m, v), d); split.
          { apply mem_slotsAtKey; repeat split; assumption. }
          cbn beta iota; apply mem_classesOf; exists u; split;
            [exact Hu | reflexivity].
        + apply mem_decReal in He;
            destruct He as [? [? [? [? [? [? [? [?
              [_ [_ [_ [_ [_ [_ He]]]]]]]]]]]]]]; discriminate He.
        + apply mem_linkReal in He;
            destruct He as [? [? [_ [_ He]]]]; discriminate He.
      - intros [[q d] [Hq Hw]]; cbn beta iota in Hw.
        apply mem_slotsAtKey in Hq; destruct Hq as [Hs [-> [Ha Hact]]].
        apply mem_classesOf in Hw; destruct Hw as [u [Hu ->]].
        right; right; right; left; apply mem_slotReal.
        exists m, v, d, u; repeat split; try assumption.
        rewrite Ha; reflexivity.
    Qed.

    Theorem versions_lookupDecision :
      forall g R support FDefs Slots Links rc m v f k feat w,
        T.PkgSet.In (NPlus.CDec m v f k feat, w)
          (transReal g R support FDefs Slots Links rc) <->
        T.VSet.In w
          (versions g R support FDefs Slots Links rc
             (NPlus.CDec m v f k feat)).
    Proof.
      intros; rewrite mem_transReal; cbn [versions]; split.
      - intros [He | [He | [He | [He | [He | He]]]]].
        + unfold transRoot in He; discriminate He.
        + apply mem_crateReal in He;
            destruct He as [? [? [_ He]]]; discriminate He.
        + apply mem_featReal in He;
            destruct He as [? [? [? [_ He]]]]; discriminate He.
        + apply mem_slotReal in He;
            destruct He as [? [? [? [? [_ [_ [_ He]]]]]]];
            discriminate He.
        + apply mem_decReal in He;
            destruct He as [n' [v' [f' [e0 [a' [feat' [d [u
              [Hf [Ee [Hs [Ha [Hact [Hu He]]]]]]]]]]]]]].
          injection He as E1 E2 E3 E4 E5 E6;
            subst n' v' f' feat' w k.
          assert (Hb : fdEntryb FDefs (m, v) f (kAlias (sKey d)) feat
              = true)
            by (apply fdEntryb_iff; exists e0; split;
                [exact Hf | rewrite kAlias_sKey, Ha; exact Ee]).
          rewrite Hb.
          apply SOsv.mem_unionMap; exists ((m, v), d); split.
          { apply mem_slotsAtKey; repeat split; assumption. }
          cbn beta iota; apply mem_classesOf; exists u; split;
            [exact Hu | reflexivity].
        + apply mem_linkReal in He;
            destruct He as [? [? [_ [_ He]]]]; discriminate He.
      - destruct (fdEntryb FDefs (m, v) f (kAlias k) feat) eqn:Eb;
          [| intro Hw; exfalso; exact (T.VSet.empty_spec Hw)].
        apply fdEntryb_iff in Eb; destruct Eb as [e0 [Hf Ee]].
        intro Hw; apply SOsv.mem_unionMap in Hw;
          destruct Hw as [[q d] [Hq Hw]]; cbn beta iota in Hw.
        apply mem_slotsAtKey in Hq; destruct Hq as [Hs [-> [Ha Hact]]].
        apply mem_classesOf in Hw; destruct Hw as [u [Hu ->]].
        right; right; right; right; left; apply mem_decReal.
        exists m, v, f, e0, (kAlias k), feat, d, u; repeat split;
          try assumption.
        + rewrite <- Ha; reflexivity.
        + rewrite Ha; reflexivity.
    Qed.

    Theorem versions_lookupLink :
      forall g R support FDefs Slots Links rc l w,
        T.PkgSet.In (NPlus.CLink l, w)
          (transReal g R support FDefs Slots Links rc) <->
        T.VSet.In w
          (versions g R support FDefs Slots Links rc
             (NPlus.CLink l)).
    Proof.
      intros; rewrite mem_transReal; cbn [versions].
      rewrite SOlv.mem_filterMap; split.
      - intros [He | [He | [He | [He | [He | He]]]]].
        + unfold transRoot in He; discriminate He.
        + apply mem_crateReal in He;
            destruct He as [? [? [_ He]]]; discriminate He.
        + apply mem_featReal in He;
            destruct He as [? [? [? [_ He]]]]; discriminate He.
        + apply mem_slotReal in He;
            destruct He as [? [? [? [? [_ [_ [_ He]]]]]]];
            discriminate He.
        + apply mem_decReal in He;
            destruct He as [? [? [? [? [? [? [? [?
              [_ [_ [_ [_ [_ [_ He]]]]]]]]]]]]]]; discriminate He.
        + apply mem_linkReal in He;
            destruct He as [q [l' [Hl [HR He]]]].
          injection He as E1 E2; subst l' w.
          exists (q, l); split; [exact Hl | cbn beta iota].
          rewrite LEqb.eqb_refl, (proj2 (PkgSet.mem_spec _ _) HR);
            reflexivity.
      - intros [[q l'] [Hl He]]; cbn beta iota in He.
        destruct (andb (LEqb.eqb l' l) (PkgSet.mem q R)) eqn:Eb;
          [| discriminate].
        apply andb_true_iff in Eb; destruct Eb as [El Em].
        apply LEqb.eqb_true_iff in El; apply PkgSet.mem_spec in Em.
        subst l'; injection He as <-.
        right; right; right; right; right; apply mem_linkReal.
        exists q, l; repeat split; assumption.
    Qed.

    (* The instance is built from the lookup, so the lookup is exactly
       what it answers -- at a package that is not real both sides are
       empty, since no branch answers off a real package. *)
    Theorem dependees_lookup :
      forall g R support FDefs Slots Links dflt rc rootFeats p,
        dependees g R support FDefs Slots Links dflt rc
          rootFeats p =
        T.dependees
          (transDeps g R support FDefs Slots Links dflt rc
             rootFeats) p.
    Proof.
      intros; apply T.DependeesSet.ext; intro h.
      rewrite T.mem_dependees, mem_transDeps; split.
      - intro Hh; split; [| exact Hh]; eapply dep_real; exact Hh.
      - intros [_ Hh]; exact Hh.
    Qed.

    Theorem dependees_lookupRoot :
      forall g R support FDefs Slots Links dflt rc rootFeats,
        dependees g R support FDefs Slots Links dflt rc
          rootFeats transRoot =
        T.dependees
          (transDeps g R support FDefs Slots Links dflt rc
             rootFeats) transRoot.
    Proof. intros; apply dependees_lookup. Qed.

    Theorem dependees_lookupCrate :
      forall g R support FDefs Slots Links dflt rc rootFeats
             m gr v,
        dependees g R support FDefs Slots Links dflt rc
          rootFeats (NPlus.CCrate m gr, VPlus.WOrig v) =
        T.dependees
          (transDeps g R support FDefs Slots Links dflt rc
             rootFeats) (NPlus.CCrate m gr, VPlus.WOrig v).
    Proof. intros; apply dependees_lookup. Qed.

    Theorem dependees_lookupFeatP :
      forall g R support FDefs Slots Links dflt rc rootFeats
             m f gr v,
        dependees g R support FDefs Slots Links dflt rc
          rootFeats (NPlus.CFeatP m f gr, VPlus.WOrig v) =
        T.dependees
          (transDeps g R support FDefs Slots Links dflt rc
             rootFeats) (NPlus.CFeatP m f gr, VPlus.WOrig v).
    Proof. intros; apply dependees_lookup. Qed.

    Theorem dependees_lookupSlot :
      forall g R support FDefs Slots Links dflt rc rootFeats
             m v a gr,
        dependees g R support FDefs Slots Links dflt rc
          rootFeats (NPlus.CSlot m v a, VPlus.WClass gr) =
        T.dependees
          (transDeps g R support FDefs Slots Links dflt rc
             rootFeats) (NPlus.CSlot m v a, VPlus.WClass gr).
    Proof. intros; apply dependees_lookup. Qed.

    Theorem dependees_lookupDecision :
      forall g R support FDefs Slots Links dflt rc rootFeats
             m v f a feat gr,
        dependees g R support FDefs Slots Links dflt rc
          rootFeats (NPlus.CDec m v f a feat, VPlus.WClass gr) =
        T.dependees
          (transDeps g R support FDefs Slots Links dflt rc
             rootFeats) (NPlus.CDec m v f a feat, VPlus.WClass gr).
    Proof. intros; apply dependees_lookup. Qed.

    Theorem dependees_lookupInert :
      forall g R support FDefs Slots Links dflt rc rootFeats p,
        Inert p ->
        dependees g R support FDefs Slots Links dflt rc
          rootFeats p =
        T.dependees
          (transDeps g R support FDefs Slots Links dflt rc
             rootFeats) p.
    Proof. intros; apply dependees_lookup. Qed.
  End Lookup.

  Theorem cargo_soundness :
    forall R support FDefs Slots Links g dflt rc rootFeats
           (S : T.PkgSet.t),
      SiteFunctional Slots ->
      T.IsResolution
        (transReal g R support FDefs Slots Links rc)
        (transDeps g R support FDefs Slots Links dflt rc
           rootFeats) transRoot S ->
      IsResolution R support FDefs Slots Links g dflt rc
        rootFeats (decodeS S) (decodeFS S)
        (decodeParents Slots rc S).
  Proof.
    intros R support FDefs Slots Links g dflt rc rootFeats S
      Hsite Hres.
    destruct rc as [rn rv].
    destruct Hres as [Hsub Hroot Hdep Huniq].
    assert (A1 : forall m gr v,
        T.PkgSet.In (NPlus.CCrate m gr, VPlus.WOrig v) S ->
        PkgSet.In (m, v) R /\ gr = g v).
    { intros m gr v Hin; specialize (Hsub _ Hin).
      apply mem_transReal in Hsub.
      destruct Hsub as [He | [He | [He | [He | [He | He]]]]].
      - unfold transRoot in He; discriminate He.
      - apply mem_crateReal in He; destruct He as [n' [v' [HR He]]].
        injection He as E1 E2 E3; subst n' v'; split;
          [exact HR | exact E2].
      - apply mem_featReal in He;
          destruct He as [? [? [? [_ He]]]]; discriminate He.
      - apply mem_slotReal in He;
          destruct He as [? [? [? [? [_ [_ [_ He]]]]]]]; discriminate He.
      - apply mem_decReal in He;
          destruct He as [? [? [? [? [? [? [? [?
            [_ [_ [_ [_ [_ [_ He]]]]]]]]]]]]]]; discriminate He.
      - apply mem_linkReal in He;
          destruct He as [? [? [_ [_ He]]]]; discriminate He. }
    assert (A2 : forall m f gr v,
        T.PkgSet.In (NPlus.CFeatP m f gr, VPlus.WOrig v) S ->
        SupportSet.In ((m, v), f) support /\ gr = g v).
    { intros m f gr v Hin; specialize (Hsub _ Hin).
      apply mem_transReal in Hsub.
      destruct Hsub as [He | [He | [He | [He | [He | He]]]]].
      - unfold transRoot in He; discriminate He.
      - apply mem_crateReal in He;
          destruct He as [? [? [_ He]]]; discriminate He.
      - apply mem_featReal in He; destruct He as [n' [v' [f' [Hsp He]]]].
        injection He as E1 E2 E3 E4; subst n' f' v'; split;
          [exact Hsp | exact E3].
      - apply mem_slotReal in He;
          destruct He as [? [? [? [? [_ [_ [_ He]]]]]]]; discriminate He.
      - apply mem_decReal in He;
          destruct He as [? [? [? [? [? [? [? [?
            [_ [_ [_ [_ [_ [_ He]]]]]]]]]]]]]]; discriminate He.
      - apply mem_linkReal in He;
          destruct He as [? [? [_ [_ He]]]]; discriminate He. }
    assert (A3 : forall m v k gr,
        T.PkgSet.In (NPlus.CSlot m v k, VPlus.WClass gr) S ->
        exists d u, SlotRel.In ((m, v), d) Slots /\ sKey d = k /\
          slotActive (rn, rv) (m, v) d = true /\
          VSet.In u (evalReq R (sTarget d) (sReq d)) /\ g u = gr).
    { intros m v k gr Hin; specialize (Hsub _ Hin).
      apply mem_transReal in Hsub.
      destruct Hsub as [He | [He | [He | [He | [He | He]]]]].
      - unfold transRoot in He; discriminate He.
      - apply mem_crateReal in He;
          destruct He as [? [? [_ He]]]; discriminate He.
      - apply mem_featReal in He;
          destruct He as [? [? [? [_ He]]]]; discriminate He.
      - apply mem_slotReal in He;
          destruct He as [n' [v' [d [u [Hs [Hact [Hu He]]]]]]].
        injection He as E1 E2 E3 E4; subst n' v'.
        exists d, u; repeat split; try assumption;
          [symmetry; exact E3 | symmetry; exact E4].
      - apply mem_decReal in He;
          destruct He as [? [? [? [? [? [? [? [?
            [_ [_ [_ [_ [_ [_ He]]]]]]]]]]]]]]; discriminate He.
      - apply mem_linkReal in He;
          destruct He as [? [? [_ [_ He]]]]; discriminate He. }
    (* a feature name commits its own crate version, so the member of a
       class a feature node carries is the one the crate name carries *)
    assert (A5 : forall m f gr u u',
        T.PkgSet.In (NPlus.CFeatP m f gr, VPlus.WOrig u') S ->
        T.PkgSet.In (NPlus.CCrate m gr, VPlus.WOrig u) S -> u' = u).
    { intros m f gr u u' Hf Hc.
      destruct (A2 _ _ _ _ Hf) as [Hsp Egr]; subst gr.
      assert (Hed : T.DepRel.In
          ((NPlus.CFeatP m f (g u'), VPlus.WOrig u'),
           (NPlus.CCrate m (g u'), T.VSet.singleton (VPlus.WOrig u')))
          (transDeps g R support FDefs Slots Links dflt
             (rn, rv) rootFeats)).
      { apply mem_transDeps; split; [exact (Hsub _ Hf) |].
        apply mem_dep_featP; split; [reflexivity |].
        split; [exact Hsp | left; reflexivity]. }
      destruct (Hdep _ Hf _ _ Hed) as [w [Hw HwS]].
      apply T.VSet.singleton_spec in Hw; subst w.
      assert (E := Huniq _ _ _ HwS Hc); injection E as E; exact E. }
    constructor.
    - intros [m v] Hp; apply mem_decodeS in Hp; destruct Hp as [gr Hp].
      exact (proj1 (A1 _ _ _ Hp)).
    - assert (Hed : T.DepRel.In
          (transRoot, (NPlus.CCrate rn (g rv), T.VSet.singleton (VPlus.WOrig rv)))
          (transDeps g R support FDefs Slots Links dflt
             (rn, rv) rootFeats)).
      { apply mem_transDeps; split; [exact (Hsub _ Hroot) |].
        apply mem_dep_root; left; reflexivity. }
      destruct (Hdep _ Hroot _ _ Hed) as [w [Hw HwS]].
      apply T.VSet.singleton_spec in Hw; subst w.
      apply mem_decodeS; exists (g rv); exact HwS.
    - intros fs Hfs; apply mem_decodeFS in Hfs;
        destruct Hfs as [_ ->]; intros f Hf.
      assert (Hed : T.DepRel.In
          (transRoot, (NPlus.CFeatP rn f (g rv),
                   T.VSet.singleton (VPlus.WOrig rv)))
          (transDeps g R support FDefs Slots Links dflt
             (rn, rv) rootFeats)).
      { apply mem_transDeps; split; [exact (Hsub _ Hroot) |].
        apply mem_dep_root; right; exists f; split;
          [exact Hf | reflexivity]. }
      destruct (Hdep _ Hroot _ _ Hed) as [w [Hw HwS]].
      apply T.VSet.singleton_spec in Hw; subst w.
      apply mem_featsAt; exists (g rv); exact HwS.
    - intros p fs Hfs; apply mem_decodeFS in Hfs; exact (proj1 Hfs).
    - intros p Hp; exists (featsAt S p); apply mem_decodeFS; split;
        [exact Hp | reflexivity].
    - intros p fs fs' Hfs Hfs'.
      apply mem_decodeFS in Hfs; destruct Hfs as [_ ->].
      apply mem_decodeFS in Hfs'; destruct Hfs' as [_ ->]; reflexivity.
    - intros m v v' Hv Hv' NE Hg.
      apply mem_decodeS in Hv; destruct Hv as [gr Hv].
      apply mem_decodeS in Hv'; destruct Hv' as [gr' Hv'].
      destruct (A1 _ _ _ Hv) as [_ Egr]; subst gr.
      destruct (A1 _ _ _ Hv') as [_ Egr']; subst gr'.
      rewrite <- Hg in Hv'.
      assert (E := Huniq _ _ _ Hv Hv'); injection E as E.
      contradiction NE.
    - intros [m v] fs f Hfs Hf.
      apply mem_decodeFS in Hfs; destruct Hfs as [_ ->].
      apply mem_featsAt in Hf; destruct Hf as [gr Hf].
      exact (proj1 (A2 _ _ _ _ Hf)).
    - intros [m v] a u u' Hu Hu'.
      apply mem_decodeParents in Hu;
        destruct Hu as [gr [d [Hslot [Hs [Ha [Hact Hcr]]]]]].
      apply mem_decodeParents in Hu';
        destruct Hu' as [gr' [d' [Hslot' [Hs' [Ha' [Hact' Hcr']]]]]].
      assert (d' = d)
        by exact (Hsite (m, v) d' d Hs' Hs (eq_trans Ha' (eq_sym Ha))).
      subst d'.
      assert (E := Huniq _ _ _ Hslot Hslot'); injection E as E; subst gr'.
      assert (E2 := Huniq _ _ _ Hcr Hcr'); injection E2 as E2; exact E2.
    - intros [m v] fs Hp Hfs d Hd Hact Hopt.
      apply mem_decodeFS in Hfs; destruct Hfs as [_ ->].
      apply mem_decodeS in Hp; destruct Hp as [gr0 Hp].
      destruct (A1 _ _ _ Hp) as [_ Egr0]; subst gr0.
      assert (Achain : forall gr,
          T.PkgSet.In (NPlus.CSlot m v (sKey d), VPlus.WClass gr) S ->
          exists u, ParentRel.In (((m, v), sKey d), u)
                      (decodeParents Slots (rn, rv) S) /\
            rgHolds (sReq d) u = true /\
            PkgSet.In (sTarget d, u) (decodeS S) /\
            forall fs', FeaturedSet.In ((sTarget d, u), fs')
              (decodeFS S) ->
            FSet.Subset (slotRequests d dflt) fs').
      { intros gr Hslot.
        destruct (A3 _ _ _ _ Hslot)
          as [d0 [u0 [Hs0 [Ha0 [Hact0 [Hu0 Egr]]]]]].
        assert (d0 = d) by exact (Hsite (m, v) d0 d Hs0 Hd Ha0); subst d0.
        subst gr.
        assert (Hed : T.DepRel.In
            ((NPlus.CSlot m v (sKey d), VPlus.WClass (g u0)),
             (NPlus.CCrate (sTarget d) (g u0),
              inClass g (g u0) (evalReq R (sTarget d) (sReq d))))
            (transDeps g R support FDefs Slots Links dflt
               (rn, rv) rootFeats)).
        { apply mem_transDeps; split; [exact (Hsub _ Hslot) |].
          apply mem_dep_slot; exists d, u0; repeat split;
            try assumption; left; reflexivity. }
        destruct (Hdep _ Hslot _ _ Hed) as [w [Hw HwS]].
        apply mem_inClass in Hw; destruct Hw as [u [Hu [Hgu ->]]].
        exists u; repeat split.
        - apply mem_decodeParents; exists (g u0), d; repeat split;
            assumption.
        - apply mem_evalReq in Hu; exact (proj2 Hu).
        - apply mem_decodeS; exists (g u0); exact HwS.
        - intros fs' Hfs'; apply mem_decodeFS in Hfs';
            destruct Hfs' as [_ ->]; intros f Hf.
          assert (Hef : T.DepRel.In
              ((NPlus.CSlot m v (sKey d), VPlus.WClass (g u0)),
               (NPlus.CFeatP (sTarget d) f (g u0),
                inClass g (g u0) (evalReq R (sTarget d) (sReq d))))
              (transDeps g R support FDefs Slots Links dflt
                 (rn, rv) rootFeats)).
          { apply mem_transDeps; split; [exact (Hsub _ Hslot) |].
            apply mem_dep_slot; exists d, u0; repeat split;
              try assumption.
            right; exists f; split; [exact Hf | reflexivity]. }
          destruct (Hdep _ Hslot _ _ Hef) as [w' [Hw' Hw'S]].
          apply mem_inClass in Hw'; destruct Hw' as [u' [Hu' [Hgu' ->]]].
          assert (u' = u) by (apply (A5 (sTarget d) f (g u0));
                              assumption).
          subst u'.
          apply mem_featsAt; exists (g u0); exact Hw'S. }
      destruct Hopt as [Hno | Hacted].
      + assert (Hed : T.DepRel.In
            ((NPlus.CCrate m (g v), VPlus.WOrig v),
             (NPlus.CSlot m v (sKey d),
              classesOf g (evalReq R (sTarget d) (sReq d))))
            (transDeps g R support FDefs Slots Links dflt
               (rn, rv) rootFeats)).
        { apply mem_transDeps; split; [exact (Hsub _ Hp) |].
          apply mem_dep_crate; split; [reflexivity |].
          split; [exact (proj1 (A1 _ _ _ Hp)) |].
          left; exists d; repeat split; assumption. }
        destruct (Hdep _ Hp _ _ Hed) as [w [Hw HwS]].
        apply mem_classesOf in Hw; destruct Hw as [u1 [Hu1 ->]].
        exact (Achain _ HwS).
      + destruct Hacted as [f [Hffs Hent]].
        apply mem_featsAt in Hffs; destruct Hffs as [gr1 Hffs].
        destruct (A2 _ _ _ _ Hffs) as [_ Egr1]; subst gr1.
        assert (Hea : exists e', FDefRel.In (((m, v), f), e') FDefs /\
            entryActivates e' = Some (sAlias d)).
        { destruct Hent as [He | [[feat He] | [feat He]]].
          - exists (FEntry.EDep (sAlias d)); split;
              [exact He | reflexivity].
          - exists (FEntry.EDepFeat (sAlias d) feat); split;
              [exact He | reflexivity].
          - exists (FEntry.EWeakFeat (sAlias d) feat); split;
              [exact He | reflexivity]. }
        destruct Hea as [e' [He' Ea]].
        assert (Hed : T.DepRel.In
            ((NPlus.CFeatP m f (g v), VPlus.WOrig v),
             (NPlus.CSlot m v (sKey d),
              classesOf g (evalReq R (sTarget d) (sReq d))))
            (transDeps g R support FDefs Slots Links dflt
               (rn, rv) rootFeats)).
        { apply mem_transDeps; split; [exact (Hsub _ Hffs) |].
          apply mem_dep_featP; split; [reflexivity |].
          split; [exact (proj1 (A2 _ _ _ _ Hffs)) |].
          right; exists e'; split; [exact He' |].
          right; left; exists (sAlias d), d; repeat split; assumption. }
        destruct (Hdep _ Hffs _ _ Hed) as [w [Hw HwS]].
        apply mem_classesOf in Hw; destruct Hw as [u1 [Hu1 ->]].
        exact (Achain _ HwS).
    - intros [m v] fs f f' Hfs Hf He.
      apply mem_decodeFS in Hfs; destruct Hfs as [_ ->].
      apply mem_featsAt in Hf; destruct Hf as [gr Hf].
      destruct (A2 _ _ _ _ Hf) as [_ Egr]; subst gr.
      assert (Hed : T.DepRel.In
          ((NPlus.CFeatP m f (g v), VPlus.WOrig v),
           (NPlus.CFeatP m f' (g v), T.VSet.singleton (VPlus.WOrig v)))
          (transDeps g R support FDefs Slots Links dflt
             (rn, rv) rootFeats)).
      { apply mem_transDeps; split; [exact (Hsub _ Hf) |].
        apply mem_dep_featP; split; [reflexivity |].
        split; [exact (proj1 (A2 _ _ _ _ Hf)) |].
        right; exists (FEntry.EFeat f'); split; [exact He |].
        left; exists f'; split; reflexivity. }
      destruct (Hdep _ Hf _ _ Hed) as [w [Hw HwS]].
      apply T.VSet.singleton_spec in Hw; subst w.
      apply mem_featsAt; exists (g v); exact HwS.
    - intros [m v] fs f a feat Hfs Hf Hent d u Hd Halias Hpi fs' Hfs'.
      apply mem_decodeFS in Hfs; destruct Hfs as [_ ->].
      apply mem_featsAt in Hf; destruct Hf as [gr Hf].
      destruct (A2 _ _ _ _ Hf) as [_ Egr]; subst gr.
      subst a.
      assert (He' : exists e', FDefRel.In (((m, v), f), e') FDefs /\
          entryFeatD e' = Some (sAlias d, feat)).
      { destruct Hent as [He | He].
        - exists (FEntry.EDepFeat (sAlias d) feat); split;
            [exact He | reflexivity].
        - exists (FEntry.EWeakFeat (sAlias d) feat); split;
            [exact He | reflexivity]. }
      destruct He' as [e' [He' Ee]].
      apply mem_decodeParents in Hpi;
        destruct Hpi as [gr2 [d2 [Hslot2 [Hs2 [Ha2 [Hact2 Hcr2]]]]]].
      assert (d2 = d) by exact (Hsite (m, v) d2 d Hs2 Hd Ha2); subst d2.
      assert (Hed : T.DepRel.In
          ((NPlus.CFeatP m f (g v), VPlus.WOrig v),
           (NPlus.CDec m v f (sKey d) feat,
            classesOf g (evalReq R (sTarget d) (sReq d))))
          (transDeps g R support FDefs Slots Links dflt
             (rn, rv) rootFeats)).
      { apply mem_transDeps; split; [exact (Hsub _ Hf) |].
        apply mem_dep_featP; split; [reflexivity |].
        split; [exact (proj1 (A2 _ _ _ _ Hf)) |].
        right; exists e'; split; [exact He' |].
        right; right; exists (sAlias d), feat, d; repeat split;
          assumption. }
      destruct (Hdep _ Hf _ _ Hed) as [w [Hw HwS]].
      apply mem_classesOf in Hw; destruct Hw as [u1 [Hu1 ->]].
      assert (Hpin : T.DepRel.In
          ((NPlus.CDec m v f (sKey d) feat, VPlus.WClass (g u1)),
           (NPlus.CSlot m v (sKey d),
            T.VSet.singleton (VPlus.WClass (g u1))))
          (transDeps g R support FDefs Slots Links dflt
             (rn, rv) rootFeats)).
      { apply mem_transDeps; split; [exact (Hsub _ HwS) |].
        apply mem_dep_dec; split;
          [exists e'; split; [exact He' | exact Ee] |].
        exists d, u1; repeat split; try assumption; left; reflexivity. }
      destruct (Hdep _ HwS _ _ Hpin) as [x [Hx HxS]].
      apply T.VSet.singleton_spec in Hx; subst x.
      assert (Hdel : T.DepRel.In
          ((NPlus.CDec m v f (sKey d) feat, VPlus.WClass (g u1)),
           (NPlus.CFeatP (sTarget d) feat (g u1),
            inClass g (g u1) (evalReq R (sTarget d) (sReq d))))
          (transDeps g R support FDefs Slots Links dflt
             (rn, rv) rootFeats)).
      { apply mem_transDeps; split; [exact (Hsub _ HwS) |].
        apply mem_dep_dec; split;
          [exists e'; split; [exact He' | exact Ee] |].
        exists d, u1; repeat split; try assumption; right; reflexivity. }
      destruct (Hdep _ HwS _ _ Hdel) as [y [Hy HyS]].
      apply mem_inClass in Hy; destruct Hy as [u2 [Hu2 [Hgu2 ->]]].
      assert (Egr : VPlus.WClass gr2 = VPlus.WClass (g u1))
        by exact (Huniq _ _ _ Hslot2 HxS).
      injection Egr as Egr; subst gr2.
      assert (u2 = u) by (apply (A5 (sTarget d) feat (g u1)); assumption).
      subst u2.
      apply mem_decodeFS in Hfs'; destruct Hfs' as [_ ->].
      apply mem_featsAt; exists (g u1); exact HyS.
    - intros p q l Hp Hq Hlp Hlq.
      destruct p as [pn pv]; destruct q as [qn qv].
      apply mem_decodeS in Hp; destruct Hp as [grp Hp].
      apply mem_decodeS in Hq; destruct Hq as [grq Hq].
      destruct (A1 _ _ _ Hp) as [HpR Egp]; subst grp.
      destruct (A1 _ _ _ Hq) as [HqR Egq]; subst grq.
      assert (Hep : T.DepRel.In
          ((NPlus.CCrate pn (g pv), VPlus.WOrig pv),
           (NPlus.CLink l, T.VSet.singleton (VPlus.WMember (pn, pv))))
          (transDeps g R support FDefs Slots Links dflt
             (rn, rv) rootFeats)).
      { apply mem_transDeps; split; [exact (Hsub _ Hp) |].
        apply mem_dep_crate; split; [reflexivity |].
        split; [exact HpR | right; exists l; split;
                            [exact Hlp | reflexivity]]. }
      assert (Heq : T.DepRel.In
          ((NPlus.CCrate qn (g qv), VPlus.WOrig qv),
           (NPlus.CLink l, T.VSet.singleton (VPlus.WMember (qn, qv))))
          (transDeps g R support FDefs Slots Links dflt
             (rn, rv) rootFeats)).
      { apply mem_transDeps; split; [exact (Hsub _ Hq) |].
        apply mem_dep_crate; split; [reflexivity |].
        split; [exact HqR | right; exists l; split;
                            [exact Hlq | reflexivity]]. }
      destruct (Hdep _ Hp _ _ Hep) as [x [Hx HxS]].
      destruct (Hdep _ Hq _ _ Heq) as [y [Hy HyS]].
      apply T.VSet.singleton_spec in Hx; subst x.
      apply T.VSet.singleton_spec in Hy; subst y.
      assert (E := Huniq _ _ _ HxS HyS); injection E as E1 E2.
      rewrite E1, E2; reflexivity.
  Qed.

  Module SOfw2 := SetOps Featured T.Pkg FeaturedSet T.PkgSet.
  Module SOfsp := SetOps F T.Pkg FSet T.PkgSet.
  Module SOparp := SetOps ParentElt T.Pkg ParentRel T.PkgSet.

  Definition wFeats (g : V.t -> G.t) (FS : FeaturedSet.t) : T.PkgSet.t :=
    SOfw2.unionMap (fun '((m, v), fs) =>
        SOfsp.map (fun f => (NPlus.CFeatP m f (g v), VPlus.WOrig v)) fs)
      FS.

  Lemma mem_wFeats : forall g FS x,
      T.PkgSet.In x (wFeats g FS) <->
      exists m v fs f, FeaturedSet.In ((m, v), fs) FS /\ FSet.In f fs /\
        x = (NPlus.CFeatP m f (g v), VPlus.WOrig v).
  Proof.
    intros g FS x; unfold wFeats; rewrite SOfw2.mem_unionMap; split.
    - intros [[[m v] fs] [Hin Hx]]; cbn beta iota in Hx.
      apply SOfsp.mem_map in Hx; destruct Hx as [f [Hf ->]].
      exists m, v, fs, f; repeat split; assumption.
    - intros [m [v [fs [f [Hin [Hf ->]]]]]].
      exists ((m, v), fs); split; [exact Hin | cbn beta iota].
      apply SOfsp.mem_map; exists f; split; [exact Hf | reflexivity].
  Qed.

  Definition wSlots (g : V.t -> G.t) (FDefs : FDefRel.t)
      (Slots : SlotRel.t) (rc : Pkg.t)
      (S : PkgSet.t) (FS : FeaturedSet.t) (pi : ParentRel.t) : T.PkgSet.t :=
    SOparp.filterMap (fun '(((m, v), k), u) =>
        if parentsb FDefs Slots rc S FS (m, v) k
        then Some (NPlus.CSlot m v k, VPlus.WClass (g u))
        else None)
      pi.

  Lemma mem_wSlots : forall g FDefs Slots rc S FS pi x,
      T.PkgSet.In x (wSlots g FDefs Slots rc S FS pi) <->
      exists m v k u, ParentRel.In (((m, v), k), u) pi /\
        parentsb FDefs Slots rc S FS (m, v) k = true /\
        x = (NPlus.CSlot m v k, VPlus.WClass (g u)).
  Proof.
    intros g FDefs Slots rc S FS pi x; unfold wSlots.
    rewrite SOparp.mem_filterMap; split.
    - intros [[[[m v] k] u] [Hin He]]; cbn beta iota in He.
      destruct (parentsb FDefs Slots rc S FS (m, v) k) eqn:Eb;
        [| discriminate].
      injection He as <-; exists m, v, k, u; repeat split; assumption.
    - intros [m [v [k [u [Hin [Eb ->]]]]]].
      exists (((m, v), k), u); split; [exact Hin | cbn beta iota].
      rewrite Eb; reflexivity.
  Qed.

  (* A decision name is introduced only for an enabled feature, so its edge
     into the target feature name is unconditional rather than gated on a
     witness the owner has to enable. *)
  Definition wDecs (g : V.t -> G.t) (FDefs : FDefRel.t)
      (Slots : SlotRel.t) (rc : Pkg.t)
      (S : PkgSet.t) (FS : FeaturedSet.t) (pi : ParentRel.t) : T.PkgSet.t :=
    SOparp.unionMap (fun '(((m, v), k), u) =>
        if parentsb FDefs Slots rc S FS (m, v) k
        then SOfp.filterMap (fun '((q, f), e) =>
               match entryFeatD e with
               | Some (a', feat) =>
                   if andb (andb (PkgEqb.eqb q (m, v))
                              (NEqb.eqb a' (kAlias k)))
                        (FSet.mem f (fsAt FS (m, v)))
                   then Some (NPlus.CDec m v f k feat, VPlus.WClass (g u))
                   else None
               | None => None
               end)
             FDefs
        else T.PkgSet.empty)
      pi.

  Lemma mem_wDecs : forall g FDefs Slots rc S FS pi x,
      T.PkgSet.In x (wDecs g FDefs Slots rc S FS pi) <->
      exists m v k u f e feat, ParentRel.In (((m, v), k), u) pi /\
        parentsb FDefs Slots rc S FS (m, v) k = true /\
        FDefRel.In (((m, v), f), e) FDefs /\
        entryFeatD e = Some (kAlias k, feat) /\
        FSet.In f (fsAt FS (m, v)) /\
        x = (NPlus.CDec m v f k feat, VPlus.WClass (g u)).
  Proof.
    intros g FDefs Slots rc S FS pi x; unfold wDecs.
    rewrite SOparp.mem_unionMap; split.
    - intros [[[[m v] k] u] [Hin Hx]]; cbn beta iota in Hx.
      destruct (parentsb FDefs Slots rc S FS (m, v) k) eqn:Eb;
        [| exfalso; exact (SOfp.empty_in _ Hx)].
      apply SOfp.mem_filterMap in Hx; destruct Hx as [[[q f] e] [Hf He]].
      cbn beta iota in He.
      destruct (entryFeatD e) as [[a' feat] |] eqn:Ee; [| discriminate].
      destruct (andb (andb (PkgEqb.eqb q (m, v))
                       (NEqb.eqb a' (kAlias k)))
                  (FSet.mem f (fsAt FS (m, v)))) eqn:Eg; [| discriminate].
      apply andb_true_iff in Eg; destruct Eg as [Eq Em].
      apply andb_true_iff in Eq; destruct Eq as [Eq Ea].
      apply PkgEqb.eqb_true_iff in Eq; subst q.
      apply NEqb.eqb_true_iff in Ea; subst a'.
      apply FSet.mem_spec in Em.
      injection He as <-.
      exists m, v, k, u, f, e, feat; repeat split; assumption.
    - intros [m [v [k [u [f [e [feat
        [Hin [Eb [Hf [Ee [Em ->]]]]]]]]]]]].
      exists (((m, v), k), u); split; [exact Hin | cbn beta iota].
      rewrite Eb; apply SOfp.mem_filterMap.
      exists (((m, v), f), e); split; [exact Hf | cbn beta iota].
      rewrite Ee, PkgEqb.eqb_refl, NEqb.eqb_refl,
        (proj2 (FSet.mem_spec _ _) Em); reflexivity.
  Qed.

  Definition coreRes (g : V.t -> G.t) (FDefs : FDefRel.t)
      (Slots : SlotRel.t) (Links : LinkRel.t)
      (rc : Pkg.t) (S : PkgSet.t)
      (FS : FeaturedSet.t) (pi : ParentRel.t) : T.PkgSet.t :=
    T.PkgSet.add transRoot
      (T.PkgSet.union (crateReal g S)
         (T.PkgSet.union (wFeats g FS)
            (T.PkgSet.union
               (wSlots g FDefs Slots rc S FS pi)
               (T.PkgSet.union
                  (wDecs g FDefs Slots rc S FS pi)
                  (linkReal S Links))))).

  Lemma mem_coreRes :
    forall g FDefs Slots Links rc S FS pi x,
      T.PkgSet.In x
        (coreRes g FDefs Slots Links rc S FS pi) <->
      x = transRoot \/ T.PkgSet.In x (crateReal g S) \/
      T.PkgSet.In x (wFeats g FS) \/
      T.PkgSet.In x (wSlots g FDefs Slots rc S FS pi) \/
      T.PkgSet.In x (wDecs g FDefs Slots rc S FS pi) \/
      T.PkgSet.In x (linkReal S Links).
  Proof.
    intros; unfold coreRes.
    rewrite T.PkgSet.add_spec, !T.PkgSet.union_spec; reflexivity.
  Qed.

  Lemma core_shape :
    forall g FDefs Slots Links rc S FS pi n w,
      T.PkgSet.In (n, w)
        (coreRes g FDefs Slots Links rc S FS pi) ->
      match n with
      | NPlus.CRoot => w = VPlus.WUnit
      | NPlus.CCrate m gr =>
          exists v, w = VPlus.WOrig v /\ PkgSet.In (m, v) S /\ gr = g v
      | NPlus.CFeatP m f gr =>
          exists v fs, w = VPlus.WOrig v /\ FeaturedSet.In ((m, v), fs) FS /\
            FSet.In f fs /\ gr = g v
      | NPlus.CSlot m v k =>
          exists u, w = VPlus.WClass (g u) /\
            ParentRel.In (((m, v), k), u) pi /\
            parentsb FDefs Slots rc S FS (m, v) k = true
      | NPlus.CDec m v f k feat =>
          exists u e, w = VPlus.WClass (g u) /\
            ParentRel.In (((m, v), k), u) pi /\
            parentsb FDefs Slots rc S FS (m, v) k = true /\
            FDefRel.In (((m, v), f), e) FDefs /\
            entryFeatD e = Some (kAlias k, feat) /\
            FSet.In f (fsAt FS (m, v))
      | NPlus.CLink l =>
          exists q, w = VPlus.WMember q /\ LinkRel.In (q, l) Links /\
            PkgSet.In q S
      end.
  Proof.
    intros g FDefs Slots Links rc S FS pi n w Hin.
    apply mem_coreRes in Hin.
    destruct Hin as [He | [He | [He | [He | [He | He]]]]].
    - unfold transRoot in He; injection He as E1 E2; subst n w; reflexivity.
    - apply mem_crateReal in He; destruct He as [m [v [HS He]]].
      injection He as E1 E2; subst n w; cbn beta iota.
      exists v; repeat split; exact HS.
    - apply mem_wFeats in He; destruct He as [m [v [fs [f [Hfs [Hf He]]]]]].
      injection He as E1 E2; subst n w; cbn beta iota.
      exists v, fs; repeat split; assumption.
    - apply mem_wSlots in He;
        destruct He as [m [v [k [u [Hpi [Eb He]]]]]].
      injection He as E1 E2; subst n w; cbn beta iota.
      exists u; repeat split; assumption.
    - apply mem_wDecs in He;
        destruct He as [m [v [k [u [f [e [feat
          [Hpi [Eb [Hf [Ee [Em He]]]]]]]]]]]].
      injection He as E1 E2; subst n w; cbn beta iota.
      exists u, e; repeat split; assumption.
    - apply mem_linkReal in He; destruct He as [q [l [Hl [HS He]]]].
      injection He as E1 E2; subst n w; cbn beta iota.
      exists q; repeat split; assumption.
  Qed.

  Lemma fsAt_mem :
    forall R support FDefs Slots Links g dflt rc rootFeats
           S FS pi,
      IsResolution R support FDefs Slots Links g dflt rc
        rootFeats S FS pi ->
      forall p, PkgSet.In p S -> FeaturedSet.In (p, fsAt FS p) FS.
  Proof.
    intros R support FDefs Slots Links g dflt rc rootFeats
      S FS pi Hres p Hp.
    destruct (res_fs_total _ _ _ _ _ _ _ _ _ _ _ _ Hres p Hp)
      as [fs Hfs].
    rewrite (fsAt_in FS p fs
               (fun q fs1 fs2 => res_fs_functional _ _ _ _ _ _ _ _ _ _
                                   _ _ Hres q fs1 fs2) Hfs).
    exact Hfs.
  Qed.

  (* From a required active slot of a resolved crate: the parent edge, its
     gate, and everything the core instance asks of it. *)
  Lemma parent_pick :
    forall R support FDefs Slots Links g dflt rc rootFeats
           S FS pi,
      IsResolution R support FDefs Slots Links g dflt rc
        rootFeats S FS pi ->
      forall m v d, PkgSet.In (m, v) S ->
      SlotRel.In ((m, v), d) Slots ->
      slotActive rc (m, v) d = true ->
      (sOptional d = false \/
       Activated FDefs (fsAt FS (m, v)) (m, v) (sAlias d)) ->
      exists u, ParentRel.In (((m, v), sKey d), u) pi /\
        parentsb FDefs Slots rc S FS (m, v) (sKey d) = true /\
        VSet.In u (evalReq R (sTarget d) (sReq d)) /\
        PkgSet.In (sTarget d, u) S /\
        FSet.Subset (slotRequests d dflt) (fsAt FS (sTarget d, u)).
  Proof.
    intros R support FDefs Slots Links g dflt rc rootFeats
      S FS pi Hres m v d HS Hd Hact Hopt.
    assert (HfsAt := fsAt_mem _ _ _ _ _ _ _ _ _ _ _ _ Hres).
    destruct (res_slot_closure _ _ _ _ _ _ _ _ _ _ _ _ Hres
                (m, v) (fsAt FS (m, v)) HS (HfsAt _ HS) d Hd Hact Hopt)
      as [u [Hpi [Hrg [Htgt Hsub]]]].
    exists u; repeat split; try assumption.
    - apply parentsb_iff; split; [exact HS |].
      exists d; repeat split; assumption.
    - apply mem_evalReq; split;
        [exact (res_subset _ _ _ _ _ _ _ _ _ _ _ _ Hres _ Htgt)
        | exact Hrg].
    - exact (Hsub _ (HfsAt _ Htgt)).
  Qed.

  Lemma parent_slot :
    forall R support FDefs Slots Links g dflt rc rootFeats
           S FS pi,
      SiteFunctional Slots ->
      IsResolution R support FDefs Slots Links g dflt rc
        rootFeats S FS pi ->
      forall m v k u, ParentRel.In (((m, v), k), u) pi ->
      parentsb FDefs Slots rc S FS (m, v) k = true ->
      exists d, SlotRel.In ((m, v), d) Slots /\ sKey d = k /\
        slotActive rc (m, v) d = true /\
        VSet.In u (evalReq R (sTarget d) (sReq d)) /\
        PkgSet.In (sTarget d, u) S /\
        FSet.Subset (slotRequests d dflt) (fsAt FS (sTarget d, u)).
  Proof.
    intros R support FDefs Slots Links g dflt rc rootFeats
      S FS pi Hsite Hres m v k u Hpi Eb.
    apply parentsb_iff in Eb; destruct Eb as [HS [d [Hd [Ha [Hact Hreq]]]]].
    rewrite <- Ha in Hpi.
    destruct (parent_pick R support FDefs Slots Links g dflt rc
                rootFeats S FS pi Hres m v d HS Hd Hact Hreq)
      as [u0 [Hpi0 [_ [Hu0 [Htgt Hsub]]]]].
    assert (u = u0)
      by exact (res_pi_functional _ _ _ _ _ _ _ _ _ _ _ _ Hres
                  (m, v) (sKey d) u u0 Hpi Hpi0).
    subst u0.
    exists d; repeat split; assumption.
  Qed.

  Theorem cargo_completeness :
    forall R support FDefs Slots Links g dflt rc rootFeats
           S FS pi,
      SiteFunctional Slots ->
      IsResolution R support FDefs Slots Links g dflt rc
        rootFeats S FS pi ->
      T.IsResolution
        (transReal g R support FDefs Slots Links rc)
        (transDeps g R support FDefs Slots Links dflt rc
           rootFeats) transRoot
        (coreRes g FDefs Slots Links rc S FS pi).
  Proof.
    intros R support FDefs Slots Links g dflt rc rootFeats
      S FS pi Hsite Hres.
    assert (HfsAt := fsAt_mem _ _ _ _ _ _ _ _ _ _ _ _ Hres).
    assert (Hpick := parent_pick _ _ _ _ _ _ _ _ _ _ _ _ Hres).
    assert (Hslot := parent_slot _ _ _ _ _ _ _ _ _ _ _ _ Hsite Hres).
    destruct rc as [rn rv].
    destruct Hres as [Hsub Hroot Hrootf Hdom Htot Hfun Hclass Hsupp
      Hpifun Hslotc Hfsame Hfdep Hlinks].
    constructor.
    - (* res_subset *)
      intros x Hx; apply mem_coreRes in Hx.
      apply mem_transReal.
      destruct Hx as [-> | [Hx | [Hx | [Hx | [Hx | Hx]]]]].
      + left; reflexivity.
      + right; left; apply mem_crateReal in Hx.
        destruct Hx as [m [v [HS ->]]]; apply mem_crateReal.
        exists m, v; split; [exact (Hsub _ HS) | reflexivity].
      + right; right; left; apply mem_wFeats in Hx.
        destruct Hx as [m [v [fs [f [Hfs [Hf ->]]]]]].
        apply mem_featReal; exists m, v, f; split;
          [exact (Hsupp _ _ _ Hfs Hf) | reflexivity].
      + right; right; right; left; apply mem_wSlots in Hx.
        destruct Hx as [m [v [k [u [Hpi [Eb ->]]]]]].
        destruct (Hslot _ _ _ _ Hpi Eb)
          as [d [Hd [Ha [Hact [Hu [Htgt Hss]]]]]].
        apply mem_slotReal; exists m, v, d, u; repeat split;
          try assumption.
        rewrite Ha; reflexivity.
      + right; right; right; right; left; apply mem_wDecs in Hx.
        destruct Hx as [m [v [k [u [f [e [feat
          [Hpi [Eb [Hf [Ee [Em ->]]]]]]]]]]]].
        destruct (Hslot _ _ _ _ Hpi Eb)
          as [d [Hd [Ha [Hact [Hu [Htgt Hss]]]]]].
        apply mem_decReal; exists m, v, f, e, (kAlias k), feat, d, u;
          repeat split; try assumption.
        * rewrite <- Ha; reflexivity.
        * rewrite Ha; reflexivity.
      + right; right; right; right; right; apply mem_linkReal in Hx.
        destruct Hx as [q [l [Hl [HS ->]]]].
        apply mem_linkReal; exists q, l; repeat split;
          [exact Hl | exact (Hsub _ HS)].
    - (* res_root_mem *)
      apply mem_coreRes; left; reflexivity.
    - (* res_dep_closure *)
      intros p Hp n vs Hed.
      apply mem_transDeps in Hed; destruct Hed as [_ Hh].
      destruct p as [[| m gr | m f gr | m v k | m v f k feat | l]
                     [| v0 | gr0 | q]];
        try (rewrite dep_inert in Hh by exact I;
             exfalso; exact (T.DependeesSet.empty_spec Hh)).
      + apply mem_dep_root in Hh.
        destruct Hh as [He | [f [Hf He]]]; injection He as E1 E2;
          subst n vs.
        * exists (VPlus.WOrig rv); split;
            [apply T.VSet.singleton_spec; reflexivity |].
          apply mem_coreRes; right; left; apply mem_crateReal.
          exists rn, rv; split; [exact Hroot | reflexivity].
        * exists (VPlus.WOrig rv); split;
            [apply T.VSet.singleton_spec; reflexivity |].
          apply mem_coreRes; right; right; left; apply mem_wFeats.
          exists rn, rv, (fsAt FS (rn, rv)), f.
          split; [exact (HfsAt _ Hroot) |].
          split; [exact (Hrootf _ (HfsAt _ Hroot) f Hf) | reflexivity].
      + apply mem_dep_crate in Hh.
        apply core_shape in Hp; cbn beta iota in Hp.
        destruct Hp as [v1 [Ev [HS _]]]; injection Ev as Ev; subst v1.
        destruct Hh
          as [_ [_ [[d [Hd [Hact [Hopt He]]]] | [l [Hl He]]]]];
          injection He as E1 E2; subst n vs.
        * destruct (Hpick _ _ _ HS Hd Hact (or_introl Hopt))
            as [u [Hpi [Eb [Hu [Htgt Hss]]]]].
          exists (VPlus.WClass (g u)); split.
          { apply mem_classesOf; exists u; split;
              [exact Hu | reflexivity]. }
          apply mem_coreRes; right; right; right; left;
            apply mem_wSlots.
          exists m, v0, (sKey d), u; repeat split; assumption.
        * exists (VPlus.WMember (m, v0)); split;
            [apply T.VSet.singleton_spec; reflexivity |].
          apply mem_coreRes; right; right; right; right; right;
            apply mem_linkReal.
          exists (m, v0), l; repeat split; assumption.
      + apply mem_dep_featP in Hh.
        apply core_shape in Hp; cbn beta iota in Hp.
        destruct Hp as [v1 [fs [Ev [Hfs [Hf _]]]]].
        injection Ev as Ev; subst v1.
        assert (Efs : fsAt FS (m, v0) = fs)
          by exact (fsAt_in FS (m, v0) fs Hfun Hfs).
        assert (HS : PkgSet.In (m, v0) S) by exact (Hdom _ _ Hfs).
        destruct Hh as [_ [_ [He | [e0 [Hfd Hcase]]]]].
        * injection He as E1 E2; subst n vs.
          exists (VPlus.WOrig v0); split;
            [apply T.VSet.singleton_spec; reflexivity |].
          apply mem_coreRes; right; left; apply mem_crateReal.
          exists m, v0; split; [exact HS | reflexivity].
        * destruct Hcase as [[f' [Ee He]] | [Hcase | Hcase]].
          -- injection He as E1 E2; subst n vs e0.
             exists (VPlus.WOrig v0); split;
               [apply T.VSet.singleton_spec; reflexivity |].
             apply mem_coreRes; right; right; left; apply mem_wFeats.
             exists m, v0, fs, f'; split; [exact Hfs |].
             split; [exact (Hfsame _ _ _ _ Hfs Hf Hfd) | reflexivity].
          -- destruct Hcase as [a [d [Ea [Hd [Ha [Hact He]]]]]]; subst a.
             injection He as E1 E2; subst n vs.
             assert (Hactd : Activated FDefs (fsAt FS (m, v0)) (m, v0)
                 (sAlias d)).
             { rewrite Efs; exists f; split; [exact Hf |].
               destruct e0 as [f0 | a0 | a0 feat0 | a0 feat0];
                 cbn [entryActivates] in Ea; try discriminate;
                 injection Ea as Ea; subst a0;
                 [left; exact Hfd
                 | right; left; exists feat0; exact Hfd
                 | right; right; exists feat0; exact Hfd]. }
             destruct (Hpick _ _ _ HS Hd Hact (or_intror Hactd))
               as [u [Hpi [Eb [Hu [Htgt Hss]]]]].
             exists (VPlus.WClass (g u)); split.
             { apply mem_classesOf; exists u; split;
                 [exact Hu | reflexivity]. }
             apply mem_coreRes; right; right; right; left;
               apply mem_wSlots.
             exists m, v0, (sKey d), u; repeat split; assumption.
          -- destruct Hcase as [a [feat [d [Ea [Hd [Ha [Hact He]]]]]]];
               subst a.
             injection He as E1 E2; subst n vs.
             assert (Hactd : Activated FDefs (fsAt FS (m, v0)) (m, v0)
                 (sAlias d)).
             { rewrite Efs; exists f; split; [exact Hf |].
               destruct e0 as [f0 | a0 | a0 feat0 | a0 feat0];
                 cbn [entryFeatD] in Ea; try discriminate;
                 injection Ea as Ea1 Ea2; subst a0 feat0;
                 [right; left | right; right]; exists feat; exact Hfd. }
             destruct (Hpick _ _ _ HS Hd Hact (or_intror Hactd))
               as [u [Hpi [Eb [Hu [Htgt Hss]]]]].
             exists (VPlus.WClass (g u)); split.
             { apply mem_classesOf; exists u; split;
                 [exact Hu | reflexivity]. }
             apply mem_coreRes; right; right; right; right; left;
               apply mem_wDecs.
             exists m, v0, (sKey d), u, f, e0, feat; repeat split;
               try assumption.
             rewrite Efs; exact Hf.
      + apply mem_dep_slot in Hh.
        destruct Hh as [d [u0 [Hd [Ha [Hact [Hu0 [Hgu Hcase]]]]]]];
          subst k.
        apply core_shape in Hp; cbn beta iota in Hp.
        destruct Hp as [u [Eu [Hpi Eb]]]; injection Eu as Eu.
        destruct (Hslot _ _ _ _ Hpi Eb)
          as [d' [Hd' [Ha' [Hact' [Hu' [Htgt Hss]]]]]].
        assert (Ed : d' = d) by exact (Hsite (m, v) d' d Hd' Hd Ha').
        subst d'.
        destruct Hcase as [He | [f0 [Hf0 He]]]; injection He as E1 E2;
          subst n vs.
        * exists (VPlus.WOrig u); split.
          { apply mem_inClass; exists u; repeat split;
              [exact Hu' | exact (eq_sym Eu)]. }
          apply mem_coreRes; right; left; apply mem_crateReal.
          exists (sTarget d), u; split;
            [exact Htgt | rewrite Eu; reflexivity].
        * exists (VPlus.WOrig u); split.
          { apply mem_inClass; exists u; repeat split;
              [exact Hu' | exact (eq_sym Eu)]. }
          apply mem_coreRes; right; right; left; apply mem_wFeats.
          exists (sTarget d), u, (fsAt FS (sTarget d, u)), f0.
          split; [exact (HfsAt _ Htgt) |].
          split; [exact (Hss _ Hf0) | rewrite Eu; reflexivity].
      + apply mem_dep_dec in Hh.
        destruct Hh as [_ [d [u0 [Hd [Ha [Hact [Hu0 [Hgu Hcase]]]]]]]].
        apply core_shape in Hp; cbn beta iota in Hp.
        destruct Hp as [u [e [Eu [Hpi [Eb [Hfd2 [Ee2 Hf]]]]]]].
        injection Eu as Eu.
        assert (HSnv : PkgSet.In (m, v) S)
          by (apply parentsb_iff in Eb; exact (proj1 Eb)).
        destruct (Hslot _ _ _ _ Hpi Eb)
          as [d' [Hd' [Ha' [Hact' [Hu' [Htgt Hss]]]]]].
        assert (Ed : d' = d)
          by exact (Hsite (m, v) d' d Hd' Hd (eq_trans Ha' (eq_sym Ha))).
        subst d'.
        destruct Hcase as [He | He]; injection He as E1 E2; subst n vs.
        * exists (VPlus.WClass gr0); split;
            [apply T.VSet.singleton_spec; reflexivity |].
          apply mem_coreRes; right; right; right; left;
            apply mem_wSlots.
          exists m, v, k, u; repeat split; try assumption.
          rewrite Eu; reflexivity.
        * exists (VPlus.WOrig u); split.
          { apply mem_inClass; exists u; repeat split;
              [exact Hu' | exact (eq_sym Eu)]. }
          apply mem_coreRes; right; right; left; apply mem_wFeats.
          exists (sTarget d), u, (fsAt FS (sTarget d, u)), feat.
          split; [exact (HfsAt _ Htgt) |].
          split; [| rewrite Eu; reflexivity].
          assert (Hor :
              FDefRel.In (((m, v), f), FEntry.EDepFeat (kAlias k) feat)
                FDefs \/
              FDefRel.In (((m, v), f), FEntry.EWeakFeat (kAlias k) feat)
                FDefs).
          { destruct e as [f0 | a0 | a0 feat0 | a0 feat0];
              cbn [entryFeatD] in Ee2; try discriminate;
              injection Ee2 as Ee1 Ee3; subst a0 feat0;
              [left | right]; exact Hfd2. }
          assert (Hal : sAlias d = kAlias k) by (rewrite <- Ha; reflexivity).
          rewrite <- Ha in Hpi.
          exact (Hfdep (m, v) (fsAt FS (m, v)) f (kAlias k) feat
                   (HfsAt _ HSnv) Hf Hor d u Hd Hal Hpi
                   (fsAt FS (sTarget d, u)) (HfsAt _ Htgt)).
    - (* res_version_unique *)
      intros n w w' Hw Hw'.
      apply core_shape in Hw; apply core_shape in Hw'.
      destruct n; cbn beta iota in Hw, Hw'.
      + subst w w'; reflexivity.
      + destruct Hw as [v [-> [HS Eg]]];
          destruct Hw' as [v' [-> [HS' Eg']]].
        destruct (V.eq_dec v v') as [E | NE];
          [rewrite E; reflexivity |].
        exfalso; apply (Hclass m v v' HS HS' NE); congruence.
      + destruct Hw as [v [fs [-> [Hfs [Hf Eg]]]]];
          destruct Hw' as [v' [fs' [-> [Hfs' [Hf' Eg']]]]].
        destruct (V.eq_dec v v') as [E | NE];
          [rewrite E; reflexivity |].
        exfalso; apply (Hclass m v v' (Hdom _ _ Hfs) (Hdom _ _ Hfs') NE);
          congruence.
      + destruct Hw as [u [-> [Hpi _]]];
          destruct Hw' as [u' [-> [Hpi' _]]].
        rewrite (Hpifun (m, v) k u u' Hpi Hpi'); reflexivity.
      + destruct Hw as [u [e [-> [Hpi _]]]];
          destruct Hw' as [u' [e' [-> [Hpi' _]]]].
        rewrite (Hpifun (m, v) k u u' Hpi Hpi'); reflexivity.
      + destruct Hw as [q [-> [Hl HS]]];
          destruct Hw' as [q' [-> [Hl' HS']]].
        rewrite (Hlinks q q' l HS HS' Hl Hl'); reflexivity.
  Qed.
End Cargo.
