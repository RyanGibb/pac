
(* Nothing is an element whose named version apt finds no match for; it
   refuses the whole request, which an empty range says. *)
type accepts = Any | Only of string | Nothing

(* whose order the search decides in: apt's, replayed, or PubGrub's own *)
type order = Order.t

module E = Pac
module DF = Debian_frontend.Deb_packages

module Make (AP : Tables.ARCH) = struct
  module T = Tables.Make (AP)
  include T

  let ma_real_at idx (n, b) =
    DMA.PkgSet.ofList
      (List.map (fun v -> ((n, b), v)) (find_list idx.versions_of (n, b)))

  (* Every group member at any arch: foreign provides and group provides
     come from any member, so name preimages must span the whole group. *)
  let ma_group_of_names idx ns =
    DMA.PkgSet.ofList
      (List.concat_map
         (fun n ->
           List.map (fun (b, v) -> ((n, b), v)) (find_list idx.group_of n))
         ns)

  let ma_prov_of_names idx ns =
    DMA.Prov.ofList
      (List.concat_map
         (fun n ->
           List.map (fun (q, vt) -> (q, (n, vt))) (find_list idx.providers_of n))
         ns)

  let ma_prov_of_pkg idx p =
    match Hashtbl.find_opt idx.stanza_of p with
    | None -> DMA.Prov.empty
    | Some stz ->
        DMA.Prov.ofList (List.map (fun (m, vt) -> (p, (m, vt))) stz.nprovs)

  let ma_deps_of_pkg idx p =
    match Hashtbl.find_opt idx.stanza_of p with
    | None -> DMA.Deps.empty
    | Some stz ->
        DMA.Deps.ofList (List.map (fun alts -> (p, alts)) (deps_of idx stz))

  let ma_recs_of_pkg idx p =
    match Hashtbl.find_opt idx.stanza_of p with
    | None -> DMA.Deps.empty
    | Some stz ->
        DMA.Deps.ofList (List.map (fun alts -> (p, alts)) (recs_of idx stz))

  let ma_conf_of_pkg idx p =
    match Hashtbl.find_opt idx.stanza_of p with
    | None -> DMA.Conf.empty
    | Some stz -> DMA.Conf.ofList (List.map (fun ma -> (p, ma)) stz.nconfs)

  (* classOf defaults to MANo, so unindexed packages need no entry. *)
  let classes_of idx pkgs =
    DMA.Cls.ofList
      (List.filter_map
         (fun p ->
           Option.map (fun c -> (p, c)) (Hashtbl.find_opt idx.class_of p))
         pkgs)

  let atom_names_of idx p =
    match Hashtbl.find_opt idx.stanza_of p with
    | None -> []
    | Some stz -> List.concat_map (List.map DMA.aname) (deps_of idx stz)

  (* The base names p's conflicts can land on: its own, carrying the implicit
     group exclusion, each negative's, and the names of their declared
     providers. *)
  let conf_read idx p =
    let names =
      fst (fst p)
      ::
      (match Hashtbl.find_opt idx.stanza_of p with
      | None -> []
      | Some stz -> List.map DMA.aname stz.nconfs)
    in
    List.concat_map
      (fun m ->
        m :: List.map (fun (q, _) -> fst (fst q)) (find_list idx.providers_of m))
      names

  (* R/Pi preimages for a mangled name (m, x): whichever x is, every
     provider of (m, x) is either a group member of m (reals, implicit group
     / explicit-qualifier / foreign / :any provides) or a declared provider
     of m. *)
  let sel_preimages idx (mn : string * DMA.coq_NameArch) =
    let m = fst mn in
    let r_ma = ma_group_of_names idx [ m ] in
    let pi_decl = ma_prov_of_names idx [ m ] in
    let cls =
      classes_of idx
        (DMA.PkgSet.elements r_ma @ List.map fst (DMA.Prov.elements pi_decl))
    in
    (DMA.reduceReal r_ma, DMA.reduceProv r_ma pi_decl cls)

  (* the preimages depend on the name alone, and every atom on a name --
     each version constraint a depender writes is another selector -- asks
     for the same pair *)
  let sel_preimages idx mn =
    match Hashtbl.find_opt idx.sel_cache mn with
    | Some r -> r
    | None ->
        let r = sel_preimages idx mn in
        Hashtbl.add idx.sel_cache mn r;
        r

  let vers_sparse idx (n' : DMA.Deb.Name.t) =
    match n' with
    | DMA.Deb.Name.Orig (n, DMA.QAArch b) ->
        DMA.Deb.T.VSet.add DMA.Deb.Version.Bot
          (DMA.Deb.embedVS
             (DMA.Deb.Ver.realVersions
                (DMA.reduceReal (ma_real_at idx (n, b)))
                (n, DMA.QAArch b)))
    | DMA.Deb.Name.Orig _ ->
        (* embedPkg introduces only QAArch names, so an explicit-qualifier,
           :any or group pseudo-name carries absence alone *)
        DMA.Deb.T.VSet.singleton DMA.Deb.Version.Bot
    | DMA.Deb.Name.Disjunct aset -> DMA.Deb.versionsDisj aset
    | DMA.Deb.Name.Soft aset -> DMA.Deb.versionsSoft aset
    | DMA.Deb.Name.Selector a ->
        let r, pi = sel_preimages idx (fst a) in
        DMA.Deb.us r pi a

  let dependees_sparse idx (s : DMA.Deb.T.Pkg.t) =
    match s with
    | DMA.Deb.Name.Orig (n, DMA.QAArch b), DMA.Deb.Version.Orig v ->
        let p = ((n, b), v) in
        let m = atom_names_of idx p @ conf_read idx p in
        let r_ma = ma_group_of_names idx m in
        (* p itself joins the reduceProv carrier so its implicit provides
           (group pseudo-name, foreign/:any names) are visible to matchb *)
        let r_pi = DMA.PkgSet.add p r_ma in
        let pi_decl =
          DMA.Prov.union (ma_prov_of_names idx m) (ma_prov_of_pkg idx p)
        in
        let pi_cls =
          classes_of idx
            (DMA.PkgSet.elements r_pi @ List.map fst (DMA.Prov.elements pi_decl))
        in
        DMA.Deb.dependees (DMA.reduceReal r_ma)
          (DMA.reduceDeps (ma_deps_of_pkg idx p))
          (DMA.reduceRec (ma_recs_of_pkg idx p))
          (DMA.reduceProv r_pi pi_decl pi_cls)
          (DMA.reduceConf (DMA.PkgSet.singleton p) (ma_conf_of_pkg idx p) pi_cls)
          s
    | DMA.Deb.Name.Disjunct _, DMA.Deb.Version.Atom a ->
        let r, pi = sel_preimages idx (fst a) in
        DMA.Deb.T.DependeesSet.singleton (DMA.Deb.tgt r pi a)
    | DMA.Deb.Name.Soft _, DMA.Deb.Version.Atom a ->
        let r, pi = sel_preimages idx (fst a) in
        DMA.Deb.T.DependeesSet.singleton (DMA.Deb.tgt r pi a)
    | DMA.Deb.Name.Selector _, DMA.Deb.Version.Ref (m, w) ->
        DMA.Deb.T.DependeesSet.singleton
          ( DMA.Deb.Name.Orig m,
            DMA.Deb.T.VSet.singleton (DMA.Deb.Version.Orig w) )
    | DMA.Deb.Name.Selector a, DMA.Deb.Version.RefReal w ->
        DMA.Deb.T.DependeesSet.singleton
          ( DMA.Deb.Name.Orig (DMA.Deb.aname a),
            DMA.Deb.T.VSet.singleton (DMA.Deb.Version.Orig w) )
    | _ ->
        (* every other shape is empty by dependees' catch-all, or, at a
           pseudo-name, because no reduced clause hangs there *)
        DMA.Deb.T.DependeesSet.empty


  let is_native = function
    | DMA.QAArch a -> String.equal a AP.native
    | _ -> false

  (* apt's CompareProviders3 (apt-pkg/solver3.cc) sorts the candidates of one
     alternative and takes the first undecided one.  Resolving from an empty
     system with no pins leaves it these keys, in this order: the Essential
     flag, the Important flag (which Protected also sets), the native
     architecture, the Priority field, and the package name.  Its earlier keys
     are a pin, the upgrade candidate, the installed version, obsoleteness and
     a Multi-Arch:same package with another arch installed, none of which an
     empty system can distinguish; the one live key above these is "same group
     as the target", which is the real-before-provided split PVersion.compare
     already makes. *)
  type pref = {
    pess : bool;
    pimp : bool;
    pnat : bool;
    pprio : int; (* apt's VerPriority enum: the smaller rank is preferred *)
    pname : string;
  }

  (* apt sorts the preferred candidate first and PubGrub decides the greatest,
     so the two rank-ordered keys are read backwards here. *)
  let pref_compare a b =
    let c = Bool.compare a.pess b.pess in
    if c <> 0 then c
    else
      let c = Bool.compare a.pimp b.pimp in
      if c <> 0 then c
      else
        let c = Bool.compare a.pnat b.pnat in
        if c <> 0 then c
        else
          let c = Int.compare b.pprio a.pprio in
          if c <> 0 then c else String.compare b.pname a.pname

  let pref_of_pkg idx (p : DMA.Pkg.t) =
    let (n, b), _ = p in
    let nat = String.equal b AP.native in
    match Hashtbl.find_opt idx.stanza_of p with
    | Some stz ->
        {
          pess = stz.ness;
          pimp = stz.nimp;
          pnat = nat;
          pprio = stz.nprio;
          pname = n;
        }
    | None ->
        {
          pess = false;
          pimp = false;
          pnat = nat;
          pprio = DF.priority_lowest;
          pname = n;
        }

  (* A Ref names the provider package it came from, so its keys are that
     package's own.  embedPkg introduces only QAArch names, so the other
     cases are unreachable and rank as an unindexed package would. *)
  let ref_pref idx ((n, x) : string * DMA.coq_NameArch) w =
    match x with
    | DMA.QAArch b -> pref_of_pkg idx ((n, b), w)
    | _ ->
        {
          pess = false;
          pimp = false;
          pnat = is_native x;
          pprio = DF.priority_lowest;
          pname = n;
        }

  (* The candidate order reads the index the candidates were introduced
     from, so the comparator and the PubGrub instance over it are built per
     solve. *)
  module Search (I : sig
    val idx : index
    val versions : DMA.Deb.Name.t -> DMA.Deb.T.VSet.t
    val dependencies : DMA.Deb.T.Pkg.t -> DMA.Deb.T.DependeesSet.t
  end) =
  struct
    module PVersion = struct
      (* pos is the candidate's position in the clause whose name is being
         decided -- supplied by tag, where that name is known -- and is a
         constant for every candidate that is not an alternative of one. *)
      type t = { pos : int; v : DMA.Deb.Version.t }

      (* PubGrub decides the V.compare-maximum candidate, so preference lives
         here: dpkg-newest for real versions, leftmost alternative by clause
         position, a real package above any provider claiming its name, and apt's
         candidate order among the providers.  The calculus only makes the
         real/provided split legible -- RefReal carries no name, so it is the
         one candidate that cannot be a provider -- and says nothing about which
         to try first.

         Position is the whole of the alternative order because apt's sort is
         per alternative: TranslateOrGroup (apt-pkg/solver3.cc) sorts each
         alternative's targets among themselves and leaves the alternatives in
         the field's order, and Solve takes the first solution not already
         decided.  So pref only ever separates the providers of one atom.

         The escape is likewise a preference and not a constraint: the calculus
         tags it above Version.Atom, but we want the soft disjunct to try
         every real alternative before giving up on the clause, so it is ranked
         below them here.  Only candidates of one name are ever compared
         (PubGrub ranges are per name), and Version.Zero shares a name with
         Version.Atom in the soft disjunct and nowhere else, so the escape
         case cannot disturb any other pair.  Absence is the greatest version
         of a real name (VersionOT.compare), so a name nothing comes to
         require is decided absent. *)
      let compare (a : t) (b : t) =
        let fallback () = Tables.r2c (DMA.Deb.VersionOT.compare a.v b.v) in
        match (a.v, b.v) with
        | DMA.Deb.Version.Orig x, DMA.Deb.Version.Orig y ->
            Debian_frontend.Deb_version.compare x y
        | DMA.Deb.Version.Atom _, DMA.Deb.Version.Atom _ ->
            (* leftmost alternative first: lower position = greater version *)
            let c = Stdlib.compare b.pos a.pos in
            if c <> 0 then c else fallback ()
        | DMA.Deb.Version.Zero, DMA.Deb.Version.Atom _ -> -1
        | DMA.Deb.Version.Atom _, DMA.Deb.Version.Zero -> 1
        | DMA.Deb.Version.RefReal w, DMA.Deb.Version.RefReal w' ->
            (* one selector's real candidates all share its name, hence its
               arch: only the version separates them *)
            let c = Debian_frontend.Deb_version.compare w w' in
            if c <> 0 then c else fallback ()
        | DMA.Deb.Version.RefReal _, DMA.Deb.Version.Ref (_, _) -> 1
        | DMA.Deb.Version.Ref (_, _), DMA.Deb.Version.RefReal _ -> -1
        | DMA.Deb.Version.Ref (m, w), DMA.Deb.Version.Ref (m', w') ->
            let c = pref_compare (ref_pref I.idx m w) (ref_pref I.idx m' w') in
            if c <> 0 then c
            else
              (* two versions of one provider are apt's same-package case,
                 which the version alone settles *)
              let c = Debian_frontend.Deb_version.compare w w' in
              if c <> 0 then c else fallback ()
        | _ -> fallback ()

      let pp fmt ({ v; _ } : t) =
        match v with
        | DMA.Deb.Version.Orig v -> Format.fprintf fmt "%s" v
        | DMA.Deb.Version.Atom a -> Format.fprintf fmt "alt:%a" pp_atom a
        | DMA.Deb.Version.Ref (m, w) ->
            Format.fprintf fmt "ref:%a=%s" pp_mname m w
        | DMA.Deb.Version.RefReal w -> Format.fprintf fmt "real:%s" w
        | DMA.Deb.Version.Zero -> Format.fprintf fmt "0"
        | DMA.Deb.Version.Bot -> Format.fprintf fmt "⊥"
    end

    (* The clause position is known only where the name is: a Disjunct or Soft
       name carries the clause its candidates are alternatives of, and no other
       name has Version.Atom candidates at all. *)
    let tag (n' : DMA.Deb.Name.t) (v : DMA.Deb.Version.t) : PVersion.t =
      match (n', v) with
      | ( (DMA.Deb.Name.Disjunct aset | DMA.Deb.Name.Soft aset),
          DMA.Deb.Version.Atom a ) ->
          { PVersion.pos = atom_pos aset a; v }
      | _ -> { PVersion.pos = 0; v }

    module PG = Pubgrub.Make (PName) (PVersion)

    let greatest = function
      | [] -> invalid_arg "greatest"
      | c :: cs ->
          List.fold_left
            (fun a b -> if PVersion.compare b a > 0 then b else a)
            c cs

    (* Does the partial solution already carry [tn] at one of [tvs]?  An
       entailed selector does not: it says only that some provider will be
       chosen, and apt, whose item for it is still pending, installs a
       clause's leftmost alternative rather than wait for it.  Nor does a
       range that still admits ⊥, which is what a conflict leaves a name,
       not a need for it. *)
    let carried_at ~assigned tn tvs =
      match assigned tn with
      | PG.Unselected -> false
      | PG.Decided u -> List.exists (fun v -> PVersion.compare u v = 0) tvs
      | PG.Entailed r -> (
          match tn with
          | DMA.Deb.Name.Selector _ -> false
          | _ ->
              (not (PG.Ranges.contains (tag tn DMA.Deb.Version.Bot) r))
              && List.exists (fun v -> PG.Ranges.contains v r) tvs)

    (* The back edge a selector candidate would add: dependees sends Ref m w
       to (Orig m, Orig w) and RefReal w to (Orig (aname a), Orig w). *)
    let sel_carried ~assigned a (pv : PVersion.t) =
      let at m w =
        carried_at ~assigned (DMA.Deb.Name.Orig m)
          [ tag (DMA.Deb.Name.Orig m) (DMA.Deb.Version.Orig w) ]
      in
      match pv.PVersion.v with
      | DMA.Deb.Version.Ref (m, w) -> at m w
      | DMA.Deb.Version.RefReal w -> at (fst a) w
      | _ -> false

    let cands_tbl = Hashtbl.create 4096

    let cands_of n =
      match Hashtbl.find_opt cands_tbl n with
      | Some l -> l
      | None ->
          let l = List.map (tag n) (DMA.Deb.T.VSet.elements (I.versions n)) in
          Hashtbl.add cands_tbl n l;
          l

    let targets n (v : DMA.Deb.Version.t) =
      DMA.Deb.T.DependeesSet.elements (I.dependencies (n, v))
      |> List.map (fun (tn, tvs) ->
          (tn, List.map (tag tn) (DMA.Deb.T.VSet.elements tvs)))

    let has_ref n =
      List.exists
        (fun (pv : PVersion.t) ->
          match pv.PVersion.v with DMA.Deb.Version.Ref _ -> true | _ -> false)
        (cands_of n)

    (* the candidates of a clause name the partial solution already
       discharges: an alternative whose target is carried, or which resolves
       through a selector one of whose providers is.  Non-empty is apt's
       ELIDED, a popped clause some solution of which is true. *)
    let free_of ~assigned n cands =
      let alt_carried (pv : PVersion.t) =
        List.exists
          (fun (tn, tvs) ->
            carried_at ~assigned tn tvs
            ||
            match tn with
            | DMA.Deb.Name.Selector a -> List.exists (sel_carried ~assigned a) tvs
            | _ -> false)
          (targets n pv.PVersion.v)
      in
      match n with
      | DMA.Deb.Name.Selector a -> List.filter (sel_carried ~assigned a) cands
      | DMA.Deb.Name.Disjunct _ | DMA.Deb.Name.Soft _ ->
          List.filter alt_carried cands
      | _ -> []

    module Replay = Order.Make (struct
      module T = T
      module PVersion = PVersion
      module PG = PG

      let idx = I.idx
      let tag = tag
      let cands_of = cands_of
      let targets = targets
      let has_ref = has_ref
      let free_of = free_of
      let greatest = greatest
    end)

    let dependencies n (pv : PVersion.t) =
      List.map
        (fun (tn, tvs) -> (tn, PG.Ranges.of_list tvs))
        (targets n pv.PVersion.v)

    (* apt never resolves a clause one of whose alternatives is already
       satisfied: it leaves the clause alone and installs nothing for it.
       PubGrub has to decide the disjunct either way, so the nearest thing is
       to decide it at no cost -- an alternative, or a provider of one, the
       solution already carries.  Where nothing is carried, and for every
       other name, PVersion.compare's answer stands unchanged; the tool order
       first narrows the candidates to those apt would consider. *)
    let choose ~filter ~assigned n cands =
      let cands = filter ~assigned n cands in
      match free_of ~assigned n cands with
      | [] -> greatest cands
      | free -> greatest free

    (* A name only conflicts have reached admits absence, its greatest
       version, and is decided last: deciding it earlier would forbid a
       dependency that later comes to require it.  apt has no work item for
       such a name, so the shadow heap never sees it. *)
    let admits_bot ~assigned tn =
      match tn with
      | DMA.Deb.Name.Orig _ -> (
          match assigned tn with
          | PG.Entailed r -> PG.Ranges.contains (tag tn DMA.Deb.Version.Bot) r
          | _ -> false)
      (* only a real name has the absent version; asking the partial solution
         about a clause name would compare its atom set *)
      | _ -> false

    let required ~assigned open_names =
      List.filter (fun (tn, _) -> not (admits_bot ~assigned tn)) open_names

    let next ~order ~assigned open_names =
      match (required ~assigned open_names, order) with
      | [], _ -> fst (List.hd open_names)
      | (tn, _) :: _, `Pubgrub -> tn
      | req, `Tool t -> Replay.next t ~assigned req

    (* Ranges.full would admit ⊥, which PubGrub then picks, so a bare query
       would answer nothing; the query asks for the name, so it excludes
       absence. *)
    let root (n, acc) =
      let accepted (pv : PVersion.t) =
        match (pv.PVersion.v, acc) with
        | DMA.Deb.Version.Orig _, Any -> true
        | DMA.Deb.Version.Orig w, Only x ->
            Debian_frontend.Deb_version.compare w x = 0
        | _ -> false
      in
      ( DMA.Deb.Name.Orig n,
        PG.Ranges.of_list
          (List.filter accepted (cands_of (DMA.Deb.Name.Orig n))) )

    let decode sol =
      let s' =
        DMA.Deb.T.PkgSet.ofList
          (List.map (fun (n, (pv : PVersion.t)) -> (n, pv.PVersion.v)) sol)
      in
      List.map
        (fun ((n, b), v) -> (n, b, v))
        (DMA.PkgSet.elements
           (DMA.multiarchResolution (DMA.Deb.debianResolution s')))

    let run ~debug ~order query =
      let order =
        match order with
        | `Tool -> `Tool (Replay.create ())
        | `Pubgrub -> `Pubgrub
      in
      let filter =
        match order with
        | `Tool t -> Replay.filter t
        | `Pubgrub -> fun ~assigned:_ _ cands -> cands
      in
      let r =
        PG.solve ~next:(next ~order) ~choose:(choose ~filter) ~vers:cands_of
          ~deps:dependencies (List.map root query)
      in
      (match order with `Tool t -> Replay.report t | `Pubgrub -> ());
      match r with
      | Error inc ->
          Format.printf "unsatisfiable:@.%a@." PG.explain_incompatibility inc;
          None
      | Ok sol ->
          if debug then (
            Format.printf "raw solution (%d):@." (List.length sol);
            List.iter
              (fun (n, v) -> Format.printf "  %a = %a@." PName.pp n PVersion.pp v)
              sol);
          Some (decode sol)
  end

  let solve ~debug ~order (idx : index) (query : ((string * string) * accepts) list)
      =
    (* PACPROF's lookup buckets: calls and CPU time per name kind *)
    let buckets : (string, int ref * float ref) Hashtbl.t = Hashtbl.create 8 in
    let timed name f x =
      let c, t =
        match Hashtbl.find_opt buckets name with
        | Some ct -> ct
        | None ->
            let ct = (ref 0, ref 0.) in
            Hashtbl.replace buckets name ct;
            ct
      in
      incr c;
      let t0 = Sys.time () in
      let r = f x in
      t := !t +. (Sys.time () -. t0);
      r
    in
    let vname : DMA.Deb.Name.t -> string = function
      | DMA.Deb.Name.Orig _ -> "versions/orig"
      | DMA.Deb.Name.Disjunct _ -> "versions/disj"
      | DMA.Deb.Name.Soft _ -> "versions/soft"
      | DMA.Deb.Name.Selector _ -> "versions/sel"
    in
    let module S = Search (struct
      let idx = idx
      let versions n' = timed (vname n') (vers_sparse idx) n'
      let dependencies = timed "dependees" (dependees_sparse idx)
    end) in
    let r =
      S.run ~debug ~order
        (List.map (fun ((n, b), acc) -> ((n, DMA.QAArch b), acc)) query)
    in
    if Sys.getenv_opt "PACPROF" <> None then (
      Hashtbl.iter
        (fun name (c, t) ->
          Printf.eprintf "PACPROF %s: %d calls %.2fs\n%!" name !c !t)
        buckets;
      Printf.eprintf "PACPROF clauses parsed: %d of %d stanzas\n%!"
        idx.n_clauses_parsed
        (Hashtbl.length idx.stanza_of));
    r
end

(* apt's solver rejects every version but the candidate before it starts
   (APT::Solver::Strict-Pinning, on by default: FromDepCache, solver3.cc),
   so its answer holds only candidates, though its cache still lists the
   rest, rejected.  The cut is made on the stanzas, before any table is built, so that the lookups
   answer over the instance their theorems are stated over.  The candidate
   is the version of highest pin priority, the newest among equals
   (pkgPolicy::GetCandidateVer), and an arch:all stanza belongs to the
   native architecture's package (pkgCacheGenerator::NewPackage).  What
   sets one version's priority apart is a pin (a preferences file,
   APT::Default-Release) or a Release file's NotAutomatic or
   ButAutomaticUpgrades; pac reads Packages files alone, which carry none
   of them, so they are out of scope and every version ties.
   A query naming a version (apt-get install pkg=ver) makes it pkg's
   candidate (TryToInstall, apt-private/private-install.cc), so [named]
   overrides the newest.  Of two stanzas at one version the first read is
   kept: apt files the later one behind it in the package's version list,
   and the candidate is the first to reach the top priority. *)
let stanza_key ~native (st : DF.stanza) =
  (st.package, if st.architecture = "all" then native else st.architecture)

let candidates ~native ~named (stanzas : DF.stanza list) =
  let key = stanza_key ~native in
  let best = Hashtbl.create 65536 in
  let better (st : DF.stanza) (b : DF.stanza) =
    match Hashtbl.find_opt named (key st) with
    | Some v ->
        Debian_frontend.Deb_version.compare st.version v = 0
        && Debian_frontend.Deb_version.compare b.version v <> 0
    | None -> Debian_frontend.Deb_version.compare st.version b.version > 0
  in
  List.iter
    (fun (st : DF.stanza) ->
      match Hashtbl.find_opt best (key st) with
      | Some b when not (better st b) -> ()
      | _ -> Hashtbl.replace best (key st) st)
    stanzas;
  List.filter (fun st -> Hashtbl.find best (key st) == st) stanzas

(* fnmatch(3) with FNM_CASEFOLD, which pkgVersionMatch::ExpressionMatches
   calls on a version pattern *)
let fnmatch p s =
  let p = String.lowercase_ascii p and s = String.lowercase_ascii s in
  let np = String.length p and ns = String.length s in
  let bracket i =
    let neg, i =
      if i < np && (p.[i] = '!' || p.[i] = '^') then (true, i + 1)
      else (false, i)
    in
    let rec scan k acc first =
      if k >= np then None
      else if p.[k] = ']' && not first then Some (k + 1, acc)
      else if k + 2 < np && p.[k + 1] = '-' && p.[k + 2] <> ']' then
        scan (k + 3) ((p.[k], p.[k + 2]) :: acc) false
      else scan (k + 1) ((p.[k], p.[k]) :: acc) false
    in
    Option.map
      (fun (e, rs) ->
        (e, fun c -> neg <> List.exists (fun (a, b) -> a <= c && c <= b) rs))
      (scan i [] true)
  in
  let rec go i j =
    if i = np then j = ns
    else
      match p.[i] with
      | '*' -> go (i + 1) j || (j < ns && go i (j + 1))
      | '?' -> j < ns && go (i + 1) (j + 1)
      | '\\' when i + 1 < np -> j < ns && p.[i + 1] = s.[j] && go (i + 2) (j + 1)
      | '[' -> (
          match bracket (i + 1) with
          | Some (e, test) -> j < ns && test s.[j] && go e (j + 1)
          | None -> j < ns && s.[j] = '[' && go (i + 1) (j + 1))
      | c -> j < ns && c = s.[j] && go (i + 1) (j + 1)
  in
  go 0 0

(* pkgVersionMatch::VersionMatches for a Version matcher
   (apt-pkg/versionmatch.cc): the whole string, case-insensitively, or a
   prefix of it where the pattern ends in '*', or a glob of the pattern less
   that '*', so 1.*2* matches 1.2 and not 1.23.  apt would read /regex/ as a
   regex, but its argument splits at the last '/', so no argument reaches
   that branch. *)
let version_matches pat v =
  let n = String.length pat in
  let pre = n > 0 && pat.[n - 1] = '*' in
  let b = if pre then String.sub pat 0 (n - 1) else pat in
  let lb = String.length b and lv = String.length v in
  (lv = lb || (pre && lv > lb))
  && String.lowercase_ascii (String.sub v 0 lb) = String.lowercase_ascii b
  || fnmatch b v

(* One argument of apt-get install, as VersionContainerInterface::FromString
   (apt-pkg/cacheset.cc) reads it: whatever follows the last '/' or '='
   selects a version, by release or by version string, and what precedes it
   names the package, NAME[:ARCH] (PackageFromPackageName). *)
let query_element ~native ~arches (stanzas : DF.stanza list) arg =
  let tag =
    match (String.rindex_opt arg '=', String.rindex_opt arg '/') with
    | Some i, Some j -> Some (max i j)
    | t, None | None, t -> t
  in
  let pkg, sel =
    match tag with
    | Some i ->
        ( String.sub arg 0 i,
          Some (arg.[i], String.sub arg (i + 1) (String.length arg - i - 1)) )
    | None -> (arg, None)
  in
  let has (n, b) =
    List.exists (fun st -> stanza_key ~native st = (n, b)) stanzas
  in
  (* an unqualified name is apt's preferred package of the group
     (GrpIterator::FindPreferredPkg): the native one if it has a version,
     else the first architecture that does.  apt tries them in
     APT::Architectures order, which pac cannot read, and takes the
     index's architectures in sorted order instead. *)
  let key =
    match String.rindex_opt pkg ':' with
    | Some i ->
        let b = String.sub pkg (i + 1) (String.length pkg - i - 1) in
        ( String.sub pkg 0 i,
          if b = "all" || b = "native" then native else b )
    | None -> (
        match
          List.find_opt
            (fun b -> has (pkg, b))
            (native :: List.filter (( <> ) native) arches)
        with
        | Some b -> (pkg, b)
        | None -> (pkg, native))
  in
  (* the package's version list, newest first and the first read ahead of
     a later stanza at the same version *)
  let vlist =
    List.stable_sort
      (fun (a : DF.stanza) (b : DF.stanza) ->
        Debian_frontend.Deb_version.compare b.version a.version)
      (List.filter (fun st -> stanza_key ~native st = key) stanzas)
  in
  let first p =
    match List.find_opt (fun (st : DF.stanza) -> p st.version) vlist with
    | Some st -> Only st.version
    | None -> Nothing
  in
  (* failing every version, pkgVersionMatch::Find takes a version whose
     package provides itself at a matching version *)
  let self_provided v =
    List.find_map
      (fun (st : DF.stanza) ->
        if
          List.exists
            (fun (p : DF.provide) ->
              p.pname = fst key
              && Option.fold ~none:false ~some:(version_matches v) p.pversion)
            st.provides
        then Some (Only st.version)
        else None)
      vlist
  in
  let acc =
    match sel with
    | None -> Any
    (* apt tests these keywords before the tag, so they read the same after
       '/'; nothing is installed, as pac reads no dpkg status *)
    | Some (_, "installed") -> Nothing
    (* without pins the candidate is the newest, which heads the list *)
    | Some (_, ("candidate" | "newest")) -> first (fun _ -> true)
    | Some ('=', v) -> (
        match first (version_matches v) with
        | Nothing -> Option.value (self_provided v) ~default:Nothing
        | a -> a)
    (* a release is matched against Release files, which pac does not
       read; "*" matches every file (pkgVersionMatch::FileMatch) *)
    | Some (_, "*") -> first (fun _ -> true)
    | Some _ -> Nothing
  in
  (key, acc)

(* Parsing and index construction are reported apart from solving because
   they scale differently: the archive is read whole, while the solve
   touches only the sub-instances the lookup theorems bound.  Which of the
   two dominates is the frontend's headline number, so it is printed rather
   than inferred. *)
let solve_files ~debug ~order ~recommends ~strict_pinning ~native ~paths ~query
    :
    ((string * string * string) list * float * float) option =
  let t0 = Unix.gettimeofday () in
  let stanzas = List.concat_map DF.parse_file paths in
  let arches =
    List.sort_uniq String.compare
      (native
      :: List.filter_map
           (fun (st : DF.stanza) ->
             if st.architecture = "all" then None else Some st.architecture)
           stanzas)
  in
  (* apt installs each element's version in argument order, setting it as
     the candidate, so of two naming one package the later wins *)
  let query =
    List.fold_left
      (fun acc arg ->
        let k, a = query_element ~native ~arches stanzas arg in
        List.remove_assoc k acc @ [ (k, a) ])
      [] query
  in
  let named = Hashtbl.create 8 in
  List.iter
    (function k, Only v -> Hashtbl.replace named k v | _ -> ())
    query;
  let stanzas =
    if strict_pinning then candidates ~native ~named stanzas else stanzas
  in
  let module AP = struct
    let arches = arches
    let native = native
  end in
  let module M = Make (AP) in
  let idx = M.build_index ~recommends stanzas in
  let t1 = Unix.gettimeofday () in
  match M.solve ~debug ~order idx query with
  | None -> None
  | Some pkgs -> Some (pkgs, t1 -. t0, Unix.gettimeofday () -. t1)
