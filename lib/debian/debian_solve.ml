module E = Pac
module DF = Deb_packages
module Args = Apt_args

type answer = {
  pkgs : (string * string * string) list;
  nodes : int;
  lookups : int;
}

module Make (AP : Tables.ARCH) = struct
  module T = Tables.Make (AP)
  include T

  let ma_real_at tables (n, b) =
    DMA.PkgSet.ofList
      (List.map (fun v -> ((n, b), v)) (find_list tables.versions_table (n, b)))

  (* Every group member at any arch: foreign provides and group provides
     come from any member, so name preimages must span the whole group. *)
  let ma_group_of_names tables ns =
    DMA.PkgSet.ofList
      (List.concat_map
         (fun n ->
           List.map (fun (b, v) -> ((n, b), v)) (find_list tables.group_table n))
         ns)

  let ma_prov_of_names tables ns =
    DMA.Prov.ofList
      (List.concat_map
         (fun n ->
           List.map
             (fun (q, vt) -> (q, (n, vt)))
             (find_list tables.providers_table n))
         ns)

  (* p's own fibre of a component; a package with no stanza has none *)
  let fibre tables p ~none f = Option.fold ~none ~some:f (stanza tables p)

  let ma_prov_of_pkg tables p =
    fibre tables p ~none:DMA.Prov.empty (fun stz ->
        DMA.Prov.ofList (List.map (fun (m, vt) -> (p, (m, vt))) stz.nprovs))

  let ma_deps_of_pkg tables p =
    fibre tables p ~none:DMA.Deps.empty (fun stz ->
        DMA.Deps.ofList (List.map (fun alts -> (p, alts)) (deps_of tables stz)))

  let ma_recs_of_pkg tables p =
    fibre tables p ~none:DMA.Deps.empty (fun stz ->
        DMA.Deps.ofList (List.map (fun alts -> (p, alts)) (recs_of tables stz)))

  let ma_conf_of_pkg tables p =
    fibre tables p ~none:DMA.Conf.empty (fun stz ->
        DMA.Conf.ofList (List.map (fun ma -> (p, ma)) stz.nconfs))

  (* classOf defaults to MANo, so a package with no stanza needs no entry. *)
  let classes_of tables pkgs =
    DMA.Cls.ofList
      (List.filter_map
         (fun p ->
           Option.map (fun (stz : nstanza) -> (p, stz.ncls)) (stanza tables p))
         pkgs)

  let atom_names_of tables p =
    fibre tables p ~none:[] (fun stz ->
        List.concat_map (List.map DMA.aname) (deps_of tables stz))

  (* The base names p's conflicts can land on: its own, bearing the implicit
     group exclusion, each negative's, and the names of their declared
     providers. *)
  let conflict_names tables p =
    let names =
      fst (fst p)
      :: fibre tables p ~none:[] (fun stz -> List.map DMA.aname stz.nconfs)
    in
    List.concat_map
      (fun m ->
        m
        :: List.map
             (fun (q, _) -> fst (fst q))
             (find_list tables.providers_table m))
      names

  (* R/Pi preimages for a mangled name (m, x): whichever x is, every
     provider of (m, x) is either a group member of m (reals, implicit group
     / explicit-qualifier / foreign / :any provides) or a declared provider
     of m. *)
  let sel_preimages_uncached tables (mn : string * DMA.coq_NameArch) =
    let m = fst mn in
    let r_ma = ma_group_of_names tables [ m ] in
    let pi_decl = ma_prov_of_names tables [ m ] in
    let cls =
      classes_of tables
        (DMA.PkgSet.elements r_ma @ List.map fst (DMA.Prov.elements pi_decl))
    in
    (DMA.reduceReal r_ma, DMA.reduceProv r_ma pi_decl cls)

  (* the preimages depend on the name alone, and every atom on a name --
     each version constraint a depender writes is another selector -- asks
     for the same pair *)
  let sel_preimages tables mn =
    Pac_common.Tbl.memo tables.sel_cache mn (fun () ->
        sel_preimages_uncached tables mn)

  let versions tables (n' : DMA.Deb.Name.t) =
    match n' with
    | DMA.Deb.Name.Orig (n, DMA.QAArch b) ->
        DMA.Deb.T.VSet.add DMA.Deb.Version.Bot
          (DMA.Deb.embedVS
             (DMA.Deb.Ver.realVersions
                (DMA.reduceReal (ma_real_at tables (n, b)))
                (n, DMA.QAArch b)))
    | DMA.Deb.Name.Orig _ ->
        (* embedPkg introduces only QAArch names, so an explicit-qualifier,
           :any or group pseudo-name has absence alone *)
        DMA.Deb.T.VSet.singleton DMA.Deb.Version.Bot
    | DMA.Deb.Name.Disjunct aset -> DMA.Deb.versionsDisj aset
    | DMA.Deb.Name.Soft aset -> DMA.Deb.versionsSoft aset
    | DMA.Deb.Name.Selector a ->
        let r, pi = sel_preimages tables (fst a) in
        DMA.Deb.us r pi a

  let dependees tables (s : DMA.Deb.T.Pkg.t) =
    match s with
    | DMA.Deb.Name.Orig (n, DMA.QAArch b), DMA.Deb.Version.Orig v ->
        let p = ((n, b), v) in
        let m = atom_names_of tables p @ conflict_names tables p in
        let r_ma = ma_group_of_names tables m in
        (* p itself joins the reduceProv carrier so its implicit provides
           (group pseudo-name, foreign/:any names) are visible to matchb *)
        let r_pi = DMA.PkgSet.add p r_ma in
        let pi_decl =
          DMA.Prov.union (ma_prov_of_names tables m) (ma_prov_of_pkg tables p)
        in
        let pi_cls =
          classes_of tables
            (DMA.PkgSet.elements r_pi @ List.map fst (DMA.Prov.elements pi_decl))
        in
        DMA.Deb.dependees
          {
            DMA.Deb.inst_repo = DMA.reduceReal r_ma;
            inst_deps = DMA.reduceDeps (ma_deps_of_pkg tables p);
            inst_rec = DMA.reduceRec (ma_recs_of_pkg tables p);
            inst_prov = DMA.reduceProv r_pi pi_decl pi_cls;
            inst_conf =
              DMA.reduceConf (DMA.PkgSet.singleton p) (ma_conf_of_pkg tables p)
                pi_cls;
            (* dependees never reads the root, and a query has several *)
            inst_root = DMA.embedPkg p;
          }
          s
    | (DMA.Deb.Name.Disjunct _ | DMA.Deb.Name.Soft _), DMA.Deb.Version.Atom a ->
        let r, pi = sel_preimages tables (fst a) in
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
    pkgname : string;
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
          if c <> 0 then c else String.compare b.pkgname a.pkgname

  let pref_of_pkg tables (p : DMA.Pkg.t) =
    let (n, b), _ = p in
    let nat = String.equal b AP.native in
    match stanza tables p with
    | Some stz ->
        {
          pess = stz.ness;
          pimp = stz.nimp;
          pnat = nat;
          pprio = stz.nprio;
          pkgname = n;
        }
    | None ->
        {
          pess = false;
          pimp = false;
          pnat = nat;
          pprio = DF.priority_lowest;
          pkgname = n;
        }

  (* A Ref names the provider package it came from, so its keys are that
     package's own.  embedPkg introduces only QAArch names, so the other
     cases are unreachable and rank as a package with no stanza would. *)
  let ref_pref tables ((n, x) : string * DMA.coq_NameArch) w =
    match x with
    | DMA.QAArch b -> pref_of_pkg tables ((n, b), w)
    | _ ->
        {
          pess = false;
          pimp = false;
          pnat = is_native x;
          pprio = DF.priority_lowest;
          pkgname = n;
        }

  (* The candidate order reads the tables the candidates were introduced
     from, so the comparator and the PubGrub instance over it are built per
     solve. *)
  module Search (I : sig
    val tables : tables
    val versions : DMA.Deb.Name.t -> DMA.Deb.T.VSet.t
    val dependencies : DMA.Deb.T.Pkg.t -> DMA.Deb.T.DependeesSet.t
  end) =
  struct
    module PVersion = struct
      (* pos is the candidate's position in the clause whose name is being
         decided -- supplied by tag, where that name is known -- and is a
         constant for every candidate that is not an alternative of one. *)
      type t = { pos : int; v : DMA.Deb.Version.t }

      (* PubGrub decides the greatest candidate under compare, so preference
         lives here: dpkg-newest for real versions, leftmost alternative by
         clause position, a real package above any provider claiming its
         name, and apt's candidate order among the providers.  The calculus
         only makes the real/provided split legible -- RefReal has no name,
         so it is the one candidate that cannot be a provider -- and says
         nothing about which to try first.

         Position is the whole of the alternative order because apt's sort is
         per alternative: TranslateOrGroup (apt-pkg/solver3.cc) sorts each
         alternative's solutions among themselves and leaves the alternatives in
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
        let fallback () =
          Pac_common.Ot.r2c (DMA.Deb.VersionOT.compare a.v b.v)
        in
        match (a.v, b.v) with
        | DMA.Deb.Version.Orig x, DMA.Deb.Version.Orig y ->
            Version.Debian.compare x y
        | DMA.Deb.Version.Atom _, DMA.Deb.Version.Atom _ ->
            (* leftmost alternative first: lower position = greater version *)
            let c = Stdlib.compare b.pos a.pos in
            if c <> 0 then c else fallback ()
        | DMA.Deb.Version.Zero, DMA.Deb.Version.Atom _ -> -1
        | DMA.Deb.Version.Atom _, DMA.Deb.Version.Zero -> 1
        | DMA.Deb.Version.RefReal w, DMA.Deb.Version.RefReal w' ->
            (* one selector's real candidates all share its name, hence its
               arch: only the version separates them *)
            let c = Version.Debian.compare w w' in
            if c <> 0 then c else fallback ()
        | DMA.Deb.Version.RefReal _, DMA.Deb.Version.Ref (_, _) -> 1
        | DMA.Deb.Version.Ref (_, _), DMA.Deb.Version.RefReal _ -> -1
        | DMA.Deb.Version.Ref (m, w), DMA.Deb.Version.Ref (m', w') ->
            let c =
              pref_compare (ref_pref I.tables m w) (ref_pref I.tables m' w')
            in
            if c <> 0 then c
            else
              (* two versions of one provider are apt's same-package case,
                 which the version alone settles *)
              let c = Version.Debian.compare w w' in
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
       name holds the clause its candidates are alternatives of, and no other
       name has Version.Atom candidates at all. *)
    let tag (n' : DMA.Deb.Name.t) (v : DMA.Deb.Version.t) : PVersion.t =
      match (n', v) with
      | ( (DMA.Deb.Name.Disjunct aset | DMA.Deb.Name.Soft aset),
          DMA.Deb.Version.Atom a ) ->
          { PVersion.pos = atom_pos aset a; v }
      | _ -> { PVersion.pos = 0; v }

    module PG = Pubgrub.Make (PName) (PVersion)

    let greatest = Pac_common.Order.greatest PVersion.compare

    (* Has the partial solution already assigned [tn] one of [tvs]?  An
       entailed selector does not: it says only that some provider will be
       chosen, and apt, whose item for it is still pending, installs a
       clause's leftmost alternative rather than wait for it.  Nor does a
       range that still admits ⊥, which is what a conflict leaves a name,
       not a need for it. *)
    let assigned_among ~assigned tn tvs =
      match assigned tn with
      | PG.Unselected -> false
      | PG.Decided u -> List.exists (fun v -> PVersion.compare u v = 0) tvs
      | PG.Entailed r -> (
          match tn with
          | DMA.Deb.Name.Selector _ -> false
          | _ ->
              (not (PG.Ranges.contains (tag tn DMA.Deb.Version.Bot) r))
              && List.exists (fun v -> PG.Ranges.contains v r) tvs)

    (* The back edge a selector candidate would add, already assigned:
       dependees sends Ref m w to (Orig m, Orig w) and RefReal w to
       (Orig (aname a), Orig w). *)
    let sel_assigned ~assigned a (pv : PVersion.t) =
      let at m w =
        assigned_among ~assigned (DMA.Deb.Name.Orig m)
          [ tag (DMA.Deb.Name.Orig m) (DMA.Deb.Version.Orig w) ]
      in
      match pv.PVersion.v with
      | DMA.Deb.Version.Ref (m, w) -> at m w
      | DMA.Deb.Version.RefReal w -> at (fst a) w
      | _ -> false

    let cands_tbl = Hashtbl.create 4096

    let cands_of n =
      Pac_common.Tbl.memo cands_tbl n (fun () ->
          List.map (tag n) (DMA.Deb.T.VSet.elements (I.versions n)))

    let dependees_of n (v : DMA.Deb.Version.t) =
      DMA.Deb.T.DependeesSet.elements (I.dependencies (n, v))
      |> List.map (fun (tn, tvs) ->
          (tn, List.map (tag tn) (DMA.Deb.T.VSet.elements tvs)))

    let has_ref n =
      List.exists
        (fun (pv : PVersion.t) ->
          match pv.PVersion.v with DMA.Deb.Version.Ref _ -> true | _ -> false)
        (cands_of n)

    (* the candidates of a clause name the partial solution already
       discharges: an alternative whose target it holds, or which resolves
       through a selector one of whose providers it holds.  Non-empty is apt's
       ELIDED, a popped clause some solution of which is true. *)
    let free_of ~assigned n cands =
      let alt_assigned (pv : PVersion.t) =
        List.exists
          (fun (tn, tvs) ->
            assigned_among ~assigned tn tvs
            ||
            match tn with
            | DMA.Deb.Name.Selector a ->
                List.exists (sel_assigned ~assigned a) tvs
            | _ -> false)
          (dependees_of n pv.PVersion.v)
      in
      match n with
      | DMA.Deb.Name.Selector a -> List.filter (sel_assigned ~assigned a) cands
      | DMA.Deb.Name.Disjunct _ | DMA.Deb.Name.Soft _ ->
          List.filter alt_assigned cands
      | _ -> []

    module Replay = Order.Make (struct
      module T = T
      module PVersion = PVersion
      module PG = PG

      let tables = I.tables
      let tag = tag
      let cands_of = cands_of
      let dependees_of = dependees_of
      let has_ref = has_ref
      let free_of = free_of
      let greatest = greatest
    end)

    let dependencies n (pv : PVersion.t) =
      List.map
        (fun (tn, tvs) -> (tn, PG.Ranges.of_list tvs))
        (dependees_of n pv.PVersion.v)

    (* Ranges.full would admit ⊥, which PubGrub then picks, so a bare query
       would answer nothing; the query asks for the name, so it excludes
       absence.  A named version is the string apt matched. *)
    let root (n, acc) =
      let accepted (pv : PVersion.t) =
        match (pv.PVersion.v, acc) with
        | DMA.Deb.Version.Orig _, Args.Any -> true
        | DMA.Deb.Version.Orig w, Args.Only x -> String.equal w x
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
      let h = Replay.hooks order () in
      let r =
        PG.solve ?next:h.Pac_common.Order.next ?choose:h.Pac_common.Order.choose
          ~vers:cands_of ~deps:dependencies (List.map root query)
      in
      h.Pac_common.Order.finish ();
      match r with
      | Error inc -> Error (fun ppf -> PG.explain_incompatibility ppf inc)
      | Ok sol ->
          if debug then (
            Format.printf "raw solution (%d):@." (List.length sol);
            List.iter
              (fun (n, v) ->
                Format.printf "  %a = %a@." PName.pp n PVersion.pp v)
              sol);
          Ok (decode sol, List.length sol)
  end

  let solve ~debug ~order (tables : tables)
      (query : ((string * string) * Args.accepts) list) =
    let looked_up = Hashtbl.create 4096 in
    let module S = Search (struct
      let tables = tables
      let versions = versions tables

      let dependencies p =
        Hashtbl.replace looked_up p ();
        dependees tables p
    end) in
    let r =
      S.run ~debug ~order
        (List.map (fun ((n, b), acc) -> ((n, DMA.QAArch b), acc)) query)
    in
    let lookups = Hashtbl.length looked_up in
    Result.map (fun (pkgs, nodes) -> { pkgs; nodes; lookups }) r
end

type result = {
  answer : (answer, Pac_common.Report.explanation) Stdlib.result;
  names : int;
  versions : int;
  dropped : int;
  t_parse : float;
}

(* Parsing and table construction are reported apart from solving because
   they scale differently: the archive is read whole, while the solve
   touches only the sub-instances the lookup theorems bound. *)
let solve_files ~debug ~order ~recommends ~strict_pinning ~native ~paths ~query
    : (result, string) Stdlib.result =
  Pubgrub.set_debug debug;
  let t0 = Unix.gettimeofday () in
  let dropped = ref 0 in
  let index =
    List.concat_map (DF.parse_file ~reject:(fun () -> incr dropped)) paths
  in
  let arches =
    List.sort_uniq String.compare
      (native
      :: List.filter_map
           (fun (st : DF.stanza) ->
             if st.architecture = "all" then None else Some st.architecture)
           index)
  in
  Result.map
    (fun (query, named) ->
      let index =
        if strict_pinning then Args.pin_candidates ~native ~named index
        else index
      in
      let module AP = struct
        let arches = arches
        let native = native
      end in
      let module M = Make (AP) in
      let tables = M.build_tables ~recommends index in
      let t_parse = Unix.gettimeofday () -. t0 in
      {
        answer = M.solve ~debug ~order tables query;
        names = Hashtbl.length tables.M.group_table;
        versions = Hashtbl.length tables.M.stanza_table;
        dropped = !dropped;
        t_parse;
      })
    (Args.parse_query ~native ~arches index query)
