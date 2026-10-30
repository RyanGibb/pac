module type SEARCH = sig
  module T : Tables.S

  module PVersion : sig
    type t = {
      pos : int;
      v : T.DMA.Deb.Reduction.Version.t;
      tgt : (string * T.DMA.coq_NameArch) option;
    }

    val compare : t -> t -> int
  end

  module PG : sig
    module Ranges : sig
      type t

      val contains : PVersion.t -> t -> bool
    end

    type selection = Unselected | Entailed of Ranges.t | Decided of PVersion.t
  end

  val tables : T.tables

  val tag :
    T.DMA.Deb.Reduction.Name.t -> T.DMA.Deb.Reduction.Version.t -> PVersion.t

  val cands_of : T.DMA.Deb.Reduction.Name.t -> PVersion.t list

  val dependees_of :
    T.DMA.Deb.Reduction.Name.t ->
    T.DMA.Deb.Reduction.Version.t ->
    (T.DMA.Deb.Reduction.Name.t * PVersion.t list) list

  val has_ref : T.DMA.Deb.Reduction.Name.t -> bool

  val free_of :
    assigned:(T.DMA.Deb.Reduction.Name.t -> PG.selection) ->
    T.DMA.Deb.Reduction.Name.t ->
    PVersion.t list ->
    PVersion.t list

  val greatest : PVersion.t list -> PVersion.t
end

module Make (S : SEARCH) = struct
  open S
  open T

  type name = DMA.Deb.Reduction.Name.t
  type assigned = name -> PG.selection

  type state = {
    (* version vars and package vars assigned false *)
    vdead : (DMA.Pkg.t, unit) Hashtbl.t;
    pdead : (string * string, unit) Hashtbl.t;
    (* the solutions of a clause apt folded a later one into are the
       intersection, and Solve takes the first undecided of those: the
       narrower atom, for the choice among the name's own candidates.  The
       fold is of the depender's own clause, so it holds only while the
       depender is installed; the name, which another depender may share,
       is keyed by that depender too. *)
    narrowed : (name, DMA.Pkg.t * DMA.Deb.Atom.t) Hashtbl.t;
    (* whether apt's cache has a Provides entry for a name at an arch *)
    provided : (string * string, bool) Hashtbl.t;
  }

  let create_state () =
    {
      vdead = Hashtbl.create 256;
      pdead = Hashtbl.create 256;
      narrowed = Hashtbl.create 64;
      provided = Hashtbl.create 64;
    }

  let forget_rejections st =
    Hashtbl.reset st.vdead;
    Hashtbl.reset st.pdead

  let narrowings st n = Hashtbl.find_all st.narrowed n
  let stanza p = T.stanza tables p

  let provides_matching (stz : nstanza) n f =
    List.filter
      (fun (pn, vt) -> String.equal pn n && DMA.Deb.vtMatchb vt f)
      stz.nprovs

  (* the alternative's own name in the encoding: its selector where a
     provider matches it, its dependee otherwise *)
  let alt_name a =
    if has_ref (DMA.Deb.Reduction.Name.Selector a) then
      DMA.Deb.Reduction.Name.Selector a
    else DMA.Deb.Reduction.Name.Orig (fst a)

  (* the real versions among a name's candidates *)
  let orig_versions n =
    List.filter_map
      (fun (pv : PVersion.t) ->
        match pv.PVersion.v with
        | DMA.Deb.Reduction.Version.Orig w -> Some (pv, w)
        | _ -> None)
      (cands_of n)

  (* the cache generator keeps no Provides of a package's own name at its
     own version (ListParser::NewProvides, pkgcachegen.cc), except through
     the every-architecture path a Multi-Arch: foreign package's Provides
     take, which has no such check: luit provides luit *)
  let self_dropped (((m, _), w) as q : DMA.Pkg.t) n vt =
    String.equal m n
    && (match stanza q with
      | Some stz -> stz.ncls <> DMA.MAForeign
      | None -> true)
    &&
    match vt with
    | DMA.Deb.DTTop -> true
    | DMA.Deb.DTVal u -> Version.Debian.compare u w = 0

  (* the entry a Multi-Arch: foreign foo gives foo at each other
     architecture (NewProvidesAllArch, pkgcachegen.cc), which skips its own *)
  let sibling_provides (((m, b), _) : DMA.Pkg.t) (stz : nstanza)
      (a : DMA.Deb.Atom.t) =
    String.equal m (fst (fst a))
    && stz.ncls = DMA.MAForeign
    &&
    match snd (fst a) with
    | DMA.QAArch c -> not (String.equal b c)
    | _ -> false

  (* apt's solution counts: an alternative's solutions are its dependee's
     versions that satisfy it and, one per entry, the dependee's ProvidesList
     entries that do (AllTargets, pkgcache.cc), so a package providing its
     own name is two solutions.  A provided name resolves through its
     selector, whose Ref candidates are keyed by provider package; the
     entries apt holds for one are its declared Provides of the name, plus
     the foo:any of a Multi-Arch: allowed package and the foo:b
     pseudo-package's entry for each version of b's own foo (ParseProvides,
     deblistparser.cc), and a sibling's (sibling_provides). *)
  let provides_count ((m, y) : string * DMA.coq_NameArch) w (a : DMA.Deb.Atom.t)
      =
    let n = fst (fst a) in
    match y with
    | DMA.QAArch b -> (
        match stanza ((m, b), w) with
        | None -> 0
        | Some stz ->
            let declared =
              List.length
                (List.filter
                   (fun (_, vt) -> not (self_dropped ((m, b), w) n vt))
                   (provides_matching stz n (snd a)))
            in
            let implicit =
              match snd (fst a) with
              | (DMA.QAAny | DMA.QAExact _) when String.equal m n -> 1
              | _ when sibling_provides ((m, b), w) stz a -> 1
              | _ -> 0
            in
            declared + implicit)
    | _ -> 1

  let allowed_of ~(assigned : assigned) n =
    match assigned n with
    | PG.Unselected -> fun _ -> true
    | PG.Decided u -> fun (pv : PVersion.t) -> PVersion.compare u pv = 0
    | PG.Entailed r -> fun pv -> PG.Ranges.contains pv r

  let is_bot (pv : PVersion.t) = pv.PVersion.v = DMA.Deb.Reduction.Version.Bot

  (* n at b has an entry from a declared Provides that reaches b, or from a
     Multi-Arch: foreign n at another architecture, as provides_count counts
     them *)
  let apt_provided st ((n, b) as k) =
    match Hashtbl.find_opt st.provided k with
    | Some p -> p
    | None ->
        let foreign q =
          match stanza q with
          | Some stz -> stz.ncls = DMA.MAForeign
          | None -> false
        in
        let p =
          List.exists
            (fun ((((_, c), _) as q), vt) ->
              (not (self_dropped q n vt)) && (String.equal b c || foreign q))
            (providers tables n)
          || List.exists
               (fun (c, w) -> (not (String.equal b c)) && foreign ((n, c), w))
               (group_members tables n)
        in
        Hashtbl.add st.provided k p;
        p

  (* Defer-Version-Selection (TranslateOrGroup): an atom whose dependee has no
     Provides entry and every version of which satisfies it is one solution,
     the dependee's package var; any other atom's solutions are version vars.
     apt tests every version in its cache, those Strict-Pinning rejected
     included; this tests the candidates only. *)
  let deferred st (a : DMA.Deb.Atom.t) =
    match fst a with
    | n, DMA.QAArch b ->
        (not (apt_provided st (n, b)))
        &&
        let vs = versions_of tables (n, b) in
        vs <> [] && List.for_all (sat (snd a)) vs
    | _ -> false

  (* the literal a solution reads is still unassigned *)
  let live_at st ~pkgvar ((n, y) : string * DMA.coq_NameArch) w =
    match y with
    | DMA.QAArch b ->
        if pkgvar then not (Hashtbl.mem st.pdead (n, b))
        else not (Hashtbl.mem st.vdead ((n, b), w))
    | _ -> true

  (* PubGrub's partial solution excludes a version the moment a standing
     decision's conflict or range does, which is when apt assigns the
     version var false; the package var lags until that rejection
     propagates, so a solution reading it stays live until then whatever
     the partial solution says of the versions.  With no partial solution,
     the count is over the whole instance, where nothing is rejected yet. *)
  let solutions st (assigned : assigned option) a =
    let pkgvar = deferred st a in
    let live ~pkgvar m w =
      match assigned with None -> true | Some _ -> live_at st ~pkgvar m w
    in
    let allowed ~pkgvar n =
      match assigned with
      | Some assigned when not pkgvar -> allowed_of ~assigned n
      | _ -> fun _ -> true
    in
    match cands_of (DMA.Deb.Reduction.Name.Selector a) with
    | [] ->
        let tn = DMA.Deb.Reduction.Name.Orig (fst a) in
        let ok = allowed ~pkgvar tn in
        let sols =
          List.filter
            (fun (pv, w) -> sat (snd a) w && ok pv && live ~pkgvar (fst a) w)
            (orig_versions tn)
        in
        if sols = [] then 0 else if pkgvar then 1 else List.length sols
    | cs ->
        (* apt's solutions are packages, and a solution is out only when its
           package is false: the selector's own state says nothing about
           that, since deciding it to one provider leaves the others
           installable *)
        let ok ~pkgvar m w =
          let on = DMA.Deb.Reduction.Name.Orig m in
          allowed ~pkgvar on (tag on (DMA.Deb.Reduction.Version.Orig w))
          && live ~pkgvar m w
        in
        let reals, provs =
          List.fold_left
            (fun (r, p) (pv : PVersion.t) ->
              match pv.PVersion.v with
              | DMA.Deb.Reduction.Version.RefReal w ->
                  ((if ok ~pkgvar (fst a) w then r + 1 else r), p)
              | DMA.Deb.Reduction.Version.Ref (m, w) ->
                  ( r,
                    if ok ~pkgvar:false m w then p + provides_count m w a else p
                  )
              | _ -> (r, p))
            (0, 0) cs
        in
        (* a deferred atom's real versions are one solution, the package var,
           whatever the version count *)
        (if pkgvar then min reals 1 else reals) + provs

  (* the clause's name in this encoding: its synthetic name, or for a
     one-alternative Depends the alternative's selector where a provider
     matches it, and its dependee otherwise *)
  let clause_name opt g = function [ a ] when not opt -> alt_name a | _ -> g

  let pkg_names (((n, _), _) as p : DMA.Pkg.t) =
    n
    :: (match stanza p with Some stz -> List.map fst stz.nprovs | None -> [])

  let orig_of (((n, b), _) : DMA.Pkg.t) =
    DMA.Deb.Reduction.Name.Orig (n, DMA.QAArch b)

  let installed_at ~(assigned : assigned) (((_, _), v) as p : DMA.Pkg.t) =
    match assigned (orig_of p) with
    | PG.Decided u -> u.PVersion.v = DMA.Deb.Reduction.Version.Orig v
    | _ -> false

  type rejection = [ `Ver of DMA.Pkg.t | `Pkg of string * string ]

  let reject_ver st ~assigned out (x : DMA.Pkg.t) =
    if (not (Hashtbl.mem st.vdead x)) && not (installed_at ~assigned x) then (
      Hashtbl.replace st.vdead x ();
      out := `Ver x :: !out)

  let reject_pkg st ~assigned out ((n, b) as k) =
    if
      (not (Hashtbl.mem st.pdead k))
      && not
           (List.exists
              (fun w -> installed_at ~assigned ((n, b), w))
              (versions_of tables k))
    then (
      Hashtbl.replace st.pdead k ();
      out := `Pkg k :: !out)

  let assign st ~assigned (rs : rejection list) =
    let out = ref [] in
    List.iter
      (function
        | `Ver x -> reject_ver st ~assigned out x
        | `Pkg k -> reject_pkg st ~assigned out k)
      rs;
    List.rev !out

  (* what installing p assigns at once through its own Conflicts and Breaks:
     the versions its negatives exclude (the negative clause's solutions,
     rejected as its reason comes true) *)
  let conflicts st ~assigned (((pkgname, _), v) as p : DMA.Pkg.t) =
    let out = ref [] in
    List.iter
      (fun (tn, tvs) ->
        if List.exists is_bot tvs then
          match tn with
          | DMA.Deb.Reduction.Name.Orig (m, DMA.QAArch mb)
            when not (String.equal m pkgname) ->
              List.iter
                (fun ((c : PVersion.t), w) ->
                  if not (List.exists (fun t -> PVersion.compare c t = 0) tvs)
                  then reject_ver st ~assigned out ((m, mb), w))
                (orig_versions tn)
          | _ -> ())
      (dependees_of (orig_of p) (DMA.Deb.Reduction.Version.Orig v));
    List.rev !out

  (* apt's implicit Multi-Arch negatives (AddImplicitDepends,
     apt-pkg/pkgcachegen.cc:812-880): a version of foo:b conflicts with every
     other architecture's foo that has a version, or, if it is Multi-Arch:
     same, breaks those versions but its own *)
  let group_reaches (((_, b), v) as p : DMA.Pkg.t) c w =
    (not (String.equal b c))
    && ((match stanza p with
          | Some stz -> stz.ncls <> DMA.MASame
          | None -> true)
       || Version.Debian.compare v w <> 0)

  (* what installing p assigns through its implicit negatives, which the
     cache appends to its dependencies after the Recommends *)
  let group_conflicts st ~assigned (((n, _), _) as p : DMA.Pkg.t) =
    let out = ref [] in
    List.iter
      (fun (c, w) ->
        if group_reaches p c w then reject_ver st ~assigned out ((n, c), w))
      (group_members tables n);
    List.rev !out

  (* The declarer's atom names p, or a name p provides, at p's architecture
     -- an explicit :arch elsewhere is another package, one apt's cache holds
     as an empty pseudo-package -- and its version formula holds of p's
     version, or of the version p provides the name at (IsSatisfied over a
     PrvIterator: an unversioned Provides never meets a versioned
     negative). *)
  let reaches (((pkgname, pb), v) as p : DMA.Pkg.t) (a : DMA.Atom.t) n =
    String.equal (DMA.aname a) n
    && (match DMA.aqual a with
      | DMA.QUnq | DMA.QAny -> true
      | DMA.QNative -> String.equal APx.native pb
      | DMA.QExact c -> String.equal c pb)
    &&
    if String.equal n pkgname then sat (DMA.aform a) v
    else
      match stanza p with
      | Some stz -> provides_matching stz n (DMA.aform a) <> []
      | None -> false

  (* what p's version var assigns as it propagates: the declarers of a
     conflict it matches lose their package var, the reason of their
     negative clause.  A declarer in p's own group is skipped: apt ignores a
     conflict on the declarer itself, on a provider in its group, and on its
     group from an MA:same declarer (IsIgnorable,
     apt-pkg/pkgcache.cc:757-790), and a declarer that is not MA:same
     already conflicts with its whole group implicitly: those implicit
     negatives, group_reaches, are what reaches p from its own group. *)
  let conflicted_by st ~assigned (((pkgname, pb), v) as p : DMA.Pkg.t) =
    (* by package, not version: under Strict-Pinning a package has one,
       and with it off the replay judges the first it meets, which moves
       the order and never an answer's validity *)
    let seen = Hashtbl.create 16 in
    let out = ref [] in
    let names = pkg_names p in
    List.iter
      (fun n ->
        List.iter
          (fun (q : DMA.Pkg.t) ->
            let qk = fst q in
            if
              (not (Hashtbl.mem seen qk))
              && (not (String.equal (fst qk) pkgname))
              && not (Hashtbl.mem st.pdead qk)
            then (
              Hashtbl.replace seen qk ();
              match stanza q with
              | None -> ()
              | Some stz ->
                  (* a declarer met under one of p's names is judged on all
                     of them: a conflict on the real name that misses p's
                     version says nothing of one on a name p provides *)
                  if
                    List.exists
                      (fun a -> List.exists (reaches p a) names)
                      stz.nconfs
                  then reject_pkg st ~assigned out qk))
          (conflicters tables n))
      names;
    List.iter
      (fun (c, w) ->
        let q = ((pkgname, c), w) in
        if (not (Hashtbl.mem st.pdead (pkgname, c))) && group_reaches q pb v
        then reject_pkg st ~assigned out (pkgname, c))
      (group_members tables pkgname);
    List.rev !out

  (* the clauses a rejected literal is watched by, and what they assign: a
     hard clause of an undecided depender that has lost its last solution
     rejects the depender's package var, the reason of every clause of a
     single-version package, and a hard clause of an installed depender down
     to one is unit, its solution apt's next Enqueue.  A clause reads the
     literal apt made its solution, so a version var reaches versioned and
     provided atoms, a package var the deferred ones; a clause with no
     solution at all never fires, having nothing to watch. *)
  let cascade st ~assigned ~pkgvar names out units =
    (* by package, as in conflicted_by *)
    let seen = Hashtbl.create 16 in
    let watched (opt, _, atoms) =
      (not opt)
      && List.exists
           (fun (a : DMA.Deb.Atom.t) ->
             List.mem (fst (fst a)) names && deferred st a = pkgvar)
           atoms
      && List.exists (fun a -> solutions st None a > 0) atoms
    in
    let fire rk inst ((opt, g, atoms) as c) =
      if watched c then
        let live =
          List.fold_left
            (fun acc a -> acc + solutions st (Some assigned) a)
            0 atoms
        in
        if live = 0 then (if not inst then reject_pkg st ~assigned out rk)
        else if live = 1 && inst then units := clause_name opt g atoms :: !units
    in
    List.iter
      (fun nm ->
        List.iter
          (fun (r : DMA.Pkg.t) ->
            let rk = fst r in
            if (not (Hashtbl.mem seen rk)) && not (Hashtbl.mem st.pdead rk) then (
              Hashtbl.replace seen rk ();
              let inst = installed_at ~assigned r in
              List.iter (fire rk inst) (ordered_clauses tables r)))
          (dependers tables nm))
      names

  let propagate st ~assigned r =
    let out = ref [] and units = ref [] in
    (match r with
    | `Ver (((n, b), _) as x) ->
        (* the package's SelectVersion clause: every version false *)
        if
          List.for_all
            (fun w -> Hashtbl.mem st.vdead ((n, b), w))
            (versions_of tables (n, b))
        then reject_pkg st ~assigned out (n, b);
        cascade st ~assigned ~pkgvar:false (pkg_names x) out units
    | `Pkg (n, b) ->
        (* each version's own clause, version -> package *)
        List.iter
          (fun w -> reject_ver st ~assigned out ((n, b), w))
          (versions_of tables (n, b));
        cascade st ~assigned ~pkgvar:true [ n ] out units);
    (List.rev !out, List.rev !units)

  (* RegisterClause's merge (solver3.cc): a single-atom clause on a name an
     earlier one of the same optionality names, with a solution in common, is
     folded into it, keeping the intersection; a Recommends on a Depends'
     name keeps the Depends' solutions.  Discover registers the folded
     clause's second half again on the version var, with its own solutions,
     so it propagates right after the package's own wave. *)
  let conj ((n, f) : DMA.Deb.Atom.t) ((_, f') : DMA.Deb.Atom.t) : DMA.Deb.Atom.t
      =
    (n, DMA.Deb.Ver.FConj (f, f'))

  let overlap st a a' =
    match (deferred st a, deferred st a') with
    | true, true -> true
    | false, false -> solutions st None (conj a a') > 0
    | _ -> false

  let register st p =
    let earlier = Hashtbl.create 8 in
    let again = ref [] in
    let fold opt g a =
      let a =
        if not opt then a
        else
          match Hashtbl.find_opt earlier (false, fst a) with
          | Some (_, ea) when overlap st !ea a -> conj a !ea
          | _ -> a
      in
      match Hashtbl.find_opt earlier (opt, fst a) with
      | Some (eg, ea) when overlap st !ea a ->
          if not (DMA.Deb.Atom.eq_dec !ea a) then (
            ea := conj !ea a;
            Hashtbl.add st.narrowed eg (p, !ea));
          again := (opt, Some g, fun () -> [ a ]) :: !again;
          (opt, None, fun () -> [])
      | _ ->
          let r = ref a in
          Hashtbl.replace earlier (opt, fst a) (g, r);
          (opt, Some g, fun () -> [ !r ])
    in
    let out =
      List.map
        (fun (opt, g, atoms) ->
          let g = clause_name opt g atoms in
          match atoms with
          | [ a ] -> fold opt g a
          | _ -> (opt, Some g, fun () -> atoms))
        (ordered_clauses tables p)
    in
    (* a later fold has narrowed the earlier's atom in place *)
    let live l =
      List.filter_map
        (fun (optional, g, atoms) ->
          match g with
          | None -> None
          | Some _ -> Some { Work_heap.optional; name = g; atoms = atoms () })
        l
    in
    (live out, live (List.rev !again))

  (* A clause found unit is one Enqueue for apt: the alternative left, and
     where that alternative is deferred -- unversioned, unprovided in apt's
     cache, which sees none of the calculus's implicit provides with one
     architecture configured -- the package var itself, processed at the
     clause's own queue slot.  Any other solution is a version var, and the
     package var then joins the queue at the back as the version pops. *)
  let head st ~assigned atoms =
    let one a =
      let h = clause_name false (DMA.Deb.Reduction.Name.Disjunct atoms) [ a ] in
      match h with
      | DMA.Deb.Reduction.Name.Orig ((m, DMA.QAArch b) as mn)
        when not (deferred st a) ->
          (* the newest live version, which apt's sort of one package's
             versions puts first (CompareProviders3) *)
          let on = DMA.Deb.Reduction.Name.Orig mn in
          let live =
            List.filter_map
              (fun (pv, w) ->
                if sat (snd a) w && not (Hashtbl.mem st.vdead ((m, b), w)) then
                  Some pv
                else None)
              (orig_versions on)
          in
          {
            Work_heap.solution = h;
            version_var =
              (match live with [] -> None | _ -> Some (on, greatest live));
          }
      | _ -> { Work_heap.solution = h; version_var = None }
    in
    match atoms with
    | [] -> None
    | [ a ] -> Some (one a)
    | _ -> (
        match
          List.filter (fun a -> solutions st (Some assigned) a > 0) atoms
        with
        | [ a ] -> Some (one a)
        | _ -> None)

  let negation st ~assigned n (pv : PVersion.t) : rejection list =
    let ver ((m, y) : string * DMA.coq_NameArch) w =
      match y with DMA.QAArch b -> [ `Ver ((m, b), w) ] | _ -> []
    in
    let of_atom a =
      match head st ~assigned [ a ] with
      | Some
          {
            Work_heap.solution = DMA.Deb.Reduction.Name.Orig (m, DMA.QAArch b);
            version_var = None;
          } ->
          [ `Pkg (m, b) ]
      | Some { version_var = Some (_, (ov : PVersion.t)); _ } -> (
          match ov.PVersion.v with
          | DMA.Deb.Reduction.Version.Orig w -> ver (fst a) w
          | _ -> [])
      | _ -> []
    in
    match (n, pv.PVersion.v) with
    | DMA.Deb.Reduction.Name.Orig m, DMA.Deb.Reduction.Version.Orig w -> ver m w
    | DMA.Deb.Reduction.Name.Selector a, DMA.Deb.Reduction.Version.RefReal w ->
        if deferred st a then
          match fst a with m, DMA.QAArch b -> [ `Pkg (m, b) ] | _ -> []
        else ver (fst a) w
    | DMA.Deb.Reduction.Name.Selector _, DMA.Deb.Reduction.Version.Ref (m, w) ->
        ver m w
    | ( (DMA.Deb.Reduction.Name.Disjunct _ | DMA.Deb.Reduction.Name.Soft _),
        DMA.Deb.Reduction.Version.Atom a ) ->
        of_atom a
    | _ -> []
end
