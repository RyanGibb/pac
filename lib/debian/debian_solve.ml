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
      (List.map (fun v -> ((n, b), v)) (versions_of tables (n, b)))

  (* Every group member at any arch: foreign provides and group provides
     come from any member, so name preimages must span the whole group. *)
  let ma_group_of_names tables ns =
    DMA.PkgSet.ofList
      (List.concat_map
         (fun n ->
           List.map (fun (b, v) -> ((n, b), v)) (group_members tables n))
         ns)

  let ma_prov_of_names tables ns =
    DMA.Prov.ofList
      (List.concat_map
         (fun n -> List.map (fun (q, vt) -> (q, (n, vt))) (providers tables n))
         ns)

  (* p's own fibre of a component; a package with no stanza has none *)
  let fibre tables p ~none f = Option.fold ~none ~some:f (stanza tables p)

  let ma_prov_of_pkg tables p =
    fibre tables p ~none:DMA.Prov.empty (fun stz ->
        DMA.Prov.ofList (List.map (fun (m, vt) -> (p, (m, vt))) stz.nprovs))

  let ma_deps_of_pkg tables p =
    fibre tables p ~none:DMA.Deps.empty (fun stz ->
        DMA.Deps.ofList (List.map (fun alts -> (p, alts)) (deps_of stz)))

  let ma_recs_of_pkg tables p =
    fibre tables p ~none:DMA.Deps.empty (fun stz ->
        DMA.Deps.ofList (List.map (fun alts -> (p, alts)) (recs_of stz)))

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
        List.concat_map (List.map DMA.aname) (deps_of stz))

  (* The base names p's conflicts can land on: its own, bearing the implicit
     group exclusion, each negative's, and the names of their declared
     providers. *)
  let conflict_names tables p =
    let names =
      fst (fst p)
      :: fibre tables p ~none:[] (fun stz -> List.map DMA.aname stz.nconfs)
    in
    List.concat_map
      (fun m -> m :: List.map (fun (q, _) -> fst (fst q)) (providers tables m))
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
    (DMA.Reduction.reduceReal r_ma, DMA.Reduction.reduceProv r_ma pi_decl cls)

  (* the preimages depend on the name alone, and every atom on a name --
     each version constraint a depender writes is another selector -- asks
     for the same pair *)
  let sel_preimages sel_cache tables mn =
    Pac_common.Tbl.memo sel_cache mn (fun () ->
        sel_preimages_uncached tables mn)

  let versions sel_cache tables (n' : DMA.Deb.Reduction.Name.t) =
    match n' with
    | DMA.Deb.Reduction.Name.Orig (n, DMA.QAArch b) ->
        let vs =
          DMA.Deb.C.versions
            (DMA.Reduction.reduceReal (ma_real_at tables (n, b)))
            (n, DMA.QAArch b)
        in
        if DMA.Deb.VSet.is_empty vs then DMA.Deb.Reduction.T.VSet.empty
        else
          DMA.Deb.Reduction.T.VSet.add DMA.Deb.Reduction.Version.Bot
            (DMA.Deb.Reduction.embedVS vs)
    | DMA.Deb.Reduction.Name.Orig _ ->
        (* embedPkg introduces only QAArch names, so an explicit-qualifier,
           :any or group pseudo-name has no real package *)
        DMA.Deb.Reduction.T.VSet.empty
    | DMA.Deb.Reduction.Name.Disjunct aset ->
        DMA.Deb.Reduction.versionsDisj aset
    | DMA.Deb.Reduction.Name.Soft aset -> DMA.Deb.Reduction.versionsSoft aset
    | DMA.Deb.Reduction.Name.Selector a ->
        let r, pi = sel_preimages sel_cache tables (fst a) in
        DMA.Deb.Reduction.us r pi a

  let dependees sel_cache tables (s : DMA.Deb.Reduction.T.Pkg.t) =
    match s with
    | ( DMA.Deb.Reduction.Name.Orig (n, DMA.QAArch b),
        DMA.Deb.Reduction.Version.Orig v ) ->
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
        DMA.Deb.Reduction.dependees
          {
            DMA.Deb.inst_repo = DMA.Reduction.reduceReal r_ma;
            inst_deps = DMA.Reduction.reduceDeps (ma_deps_of_pkg tables p);
            inst_rec = DMA.Reduction.reduceRec (ma_recs_of_pkg tables p);
            inst_prov = DMA.Reduction.reduceProv r_pi pi_decl pi_cls;
            inst_conf =
              DMA.Reduction.reduceConf (DMA.PkgSet.singleton p)
                (ma_conf_of_pkg tables p) pi_cls;
            (* dependees never reads the root, so any package fills it *)
            inst_root = DMA.Reduction.embedPkg p;
          }
          s
    | ( (DMA.Deb.Reduction.Name.Disjunct _ | DMA.Deb.Reduction.Name.Soft _),
        DMA.Deb.Reduction.Version.Atom a ) ->
        let r, pi = sel_preimages sel_cache tables (fst a) in
        DMA.Deb.Reduction.T.DependeesSet.singleton
          (DMA.Deb.Reduction.dependee r pi a)
    | DMA.Deb.Reduction.Name.Selector _, DMA.Deb.Reduction.Version.Ref (m, w) ->
        DMA.Deb.Reduction.T.DependeesSet.singleton
          ( DMA.Deb.Reduction.Name.Orig m,
            DMA.Deb.Reduction.T.VSet.singleton
              (DMA.Deb.Reduction.Version.Orig w) )
    | DMA.Deb.Reduction.Name.Selector a, DMA.Deb.Reduction.Version.RefReal w ->
        DMA.Deb.Reduction.T.DependeesSet.singleton
          ( DMA.Deb.Reduction.Name.Orig (DMA.Deb.aname a),
            DMA.Deb.Reduction.T.VSet.singleton
              (DMA.Deb.Reduction.Version.Orig w) )
    | _ ->
        (* every other shape is empty by dependees' catch-all, or, at a
           pseudo-name, because no reduced clause hangs there *)
        DMA.Deb.Reduction.T.DependeesSet.empty

  (* apt's CompareProviders3 (apt-pkg/solver3.cc) sorts the candidates of one
     alternative and takes the first undecided one.  Resolving from an empty
     system with no pins leaves it these keys, in this order: the Essential
     flag, the Important flag (which Protected also sets), the native
     architecture, the Priority field, and the package name.  Its earlier keys
     are a pin, the upgrade candidate, the installed version, obsoleteness and
     a Multi-Arch:same package with another arch installed, none of which an
     empty system can distinguish; the one live key above these is "same group
     as the target", which provider_compare reads. *)
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

  (* apt's order of two candidates for the name n, as the packages they
     install: one package's versions by the version alone, and two packages
     first by whether each is in n's group, where foo:amd64 and foo:i386 tie
     whichever architecture asks for foo, and then by pref, which takes the
     native one. *)
  let provider_compare tables n ((pk, _) as p : DMA.Pkg.t) ((qk, _) as q) =
    if pk = qk then Version.Debian.compare (snd p) (snd q)
    else
      let c =
        Bool.compare (String.equal (fst pk) n) (String.equal (fst qk) n)
      in
      if c <> 0 then c
      else
        let c = pref_compare (pref_of_pkg tables p) (pref_of_pkg tables q) in
        if c <> 0 then c else Version.Debian.compare (snd p) (snd q)

  (* The candidate order reads the tables the candidates were introduced
     from, so the comparator and the PubGrub instance over it are built per
     solve. *)
  module Search (I : sig
    val tables : tables
    val versions : DMA.Deb.Reduction.Name.t -> DMA.Deb.Reduction.T.VSet.t

    val dependencies :
      DMA.Deb.Reduction.T.Pkg.t -> DMA.Deb.Reduction.T.DependeesSet.t
  end) =
  struct
    module PVersion = struct
      (* pos is the candidate's position in the clause whose name is being
         decided, and tgt the name a selector's candidates provide -- both
         supplied by tag, where that name is known.  pos is a constant for
         every candidate that is not an alternative of a clause, and tgt is
         None for every one that is not a selector's. *)
      type t = {
        pos : int;
        v : DMA.Deb.Reduction.Version.t;
        tgt : (string * DMA.coq_NameArch) option;
      }

      (* A selector candidate as the package it installs: RefReal names no
         package, so it is a version of the dependee itself. *)
      let sel_pkg (pv : t) =
        match (pv.tgt, pv.v) with
        | Some (n, DMA.QAArch b), DMA.Deb.Reduction.Version.RefReal w ->
            Some ((n, b), w)
        | Some _, DMA.Deb.Reduction.Version.Ref ((m, DMA.QAArch c), w) ->
            Some ((m, c), w)
        | _ -> None

      (* PubGrub decides the greatest candidate, so preference lives here:
         dpkg order for real versions; the leftmost alternative, as apt sorts
         solutions within an alternative and keeps the field's order between
         them (TranslateOrGroup, apt-pkg/solver3.cc); apt's provider order among
         a selector's candidates; the escape below every alternative, so a soft
         disjunct tries them all; and absence greatest, so a name nothing
         requires is decided absent.  The escape's rank contradicts
         VersionOT's safely: only one name's candidates are compared, and
         Version.Zero shares a name with Version.Atom only in the soft
         disjunct. *)
      let compare (a : t) (b : t) =
        let fallback () =
          Pac_common.Ot.r2c (DMA.Deb.Reduction.VersionOT.compare a.v b.v)
        in
        match (a.v, b.v) with
        | DMA.Deb.Reduction.Version.Orig x, DMA.Deb.Reduction.Version.Orig y ->
            Version.Debian.compare x y
        | DMA.Deb.Reduction.Version.Atom _, DMA.Deb.Reduction.Version.Atom _ ->
            (* leftmost alternative first: lower position = greater version *)
            let c = Stdlib.compare b.pos a.pos in
            if c <> 0 then c else fallback ()
        | DMA.Deb.Reduction.Version.Zero, DMA.Deb.Reduction.Version.Atom _ -> -1
        | DMA.Deb.Reduction.Version.Atom _, DMA.Deb.Reduction.Version.Zero -> 1
        | ( ( DMA.Deb.Reduction.Version.RefReal _
            | DMA.Deb.Reduction.Version.Ref _ ),
            ( DMA.Deb.Reduction.Version.RefReal _
            | DMA.Deb.Reduction.Version.Ref _ ) ) -> (
            (* a RefReal and its package's own provide are one version to
               apt, and the fallback puts the RefReal first *)
            match (a.tgt, sel_pkg a, sel_pkg b) with
            | Some (n, _), Some p, Some q ->
                let c = provider_compare I.tables n p q in
                if c <> 0 then c else fallback ()
            | _ -> fallback ())
        | _ -> fallback ()

      let pp fmt ({ v; _ } : t) =
        match v with
        | DMA.Deb.Reduction.Version.Orig v -> Format.fprintf fmt "%s" v
        | DMA.Deb.Reduction.Version.Atom a ->
            Format.fprintf fmt "alt:%a" pp_atom a
        | DMA.Deb.Reduction.Version.Ref (m, w) ->
            Format.fprintf fmt "ref:%a=%s" pp_mname m w
        | DMA.Deb.Reduction.Version.RefReal w -> Format.fprintf fmt "real:%s" w
        | DMA.Deb.Reduction.Version.Zero -> Format.fprintf fmt "0"
        | DMA.Deb.Reduction.Version.Bot -> Format.fprintf fmt "⊥"
    end

    (* The clause position and the dependee are known only where the name is:
       a Disjunct or Soft name holds the clause its candidates are
       alternatives of, and no other name has Version.Atom candidates at all;
       a Selector holds the atom its candidates provide. *)
    let tag (n' : DMA.Deb.Reduction.Name.t) (v : DMA.Deb.Reduction.Version.t) :
        PVersion.t =
      match (n', v) with
      | ( ( DMA.Deb.Reduction.Name.Disjunct aset
          | DMA.Deb.Reduction.Name.Soft aset ),
          DMA.Deb.Reduction.Version.Atom a ) ->
          { PVersion.pos = atom_pos aset a; v; tgt = None }
      | DMA.Deb.Reduction.Name.Selector a, _ ->
          { PVersion.pos = 0; v; tgt = Some (fst a) }
      | _ -> { PVersion.pos = 0; v; tgt = None }

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
          | DMA.Deb.Reduction.Name.Selector _ -> false
          | _ ->
              (not
                 (PG.Ranges.contains (tag tn DMA.Deb.Reduction.Version.Bot) r))
              && List.exists (fun v -> PG.Ranges.contains v r) tvs)

    (* The back edge a selector candidate would add, already assigned:
       dependees sends Ref m w to (Orig m, Orig w) and RefReal w to
       (Orig (aname a), Orig w). *)
    let sel_assigned ~assigned a (pv : PVersion.t) =
      let at m w =
        assigned_among ~assigned (DMA.Deb.Reduction.Name.Orig m)
          [
            tag (DMA.Deb.Reduction.Name.Orig m)
              (DMA.Deb.Reduction.Version.Orig w);
          ]
      in
      match pv.PVersion.v with
      | DMA.Deb.Reduction.Version.Ref (m, w) -> at m w
      | DMA.Deb.Reduction.Version.RefReal w -> at (fst a) w
      | _ -> false

    let cands_tbl = Hashtbl.create 4096

    let cands_of n =
      Pac_common.Tbl.memo cands_tbl n (fun () ->
          List.map (tag n) (DMA.Deb.Reduction.T.VSet.elements (I.versions n)))

    let dependees_of n (v : DMA.Deb.Reduction.Version.t) =
      DMA.Deb.Reduction.T.DependeesSet.elements (I.dependencies (n, v))
      |> List.map (fun (tn, tvs) ->
          (tn, List.map (tag tn) (DMA.Deb.Reduction.T.VSet.elements tvs)))

    let has_ref n =
      List.exists
        (fun (pv : PVersion.t) ->
          match pv.PVersion.v with
          | DMA.Deb.Reduction.Version.Ref _ -> true
          | _ -> false)
        (cands_of n)

    (* the candidates of a clause name the partial solution already
       discharges: an alternative whose dependee it holds, or which resolves
       through a selector one of whose providers it holds.  Non-empty is apt's
       ELIDED, a popped clause some solution of which is true. *)
    let free_of ~assigned n cands =
      let alt_assigned (pv : PVersion.t) =
        List.exists
          (fun (tn, tvs) ->
            assigned_among ~assigned tn tvs
            ||
            match tn with
            | DMA.Deb.Reduction.Name.Selector a ->
                List.exists (sel_assigned ~assigned a) tvs
            | _ -> false)
          (dependees_of n pv.PVersion.v)
      in
      match n with
      | DMA.Deb.Reduction.Name.Selector a ->
          List.filter (sel_assigned ~assigned a) cands
      | DMA.Deb.Reduction.Name.Disjunct _ | DMA.Deb.Reduction.Name.Soft _ ->
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
    let root_cands (n, acc) =
      let accepted (pv : PVersion.t) =
        match (pv.PVersion.v, acc) with
        | DMA.Deb.Reduction.Version.Orig _, Args.Any -> true
        | DMA.Deb.Reduction.Version.Orig w, Args.Only x -> String.equal w x
        | _ -> false
      in
      ( DMA.Deb.Reduction.Name.Orig n,
        List.filter accepted (cands_of (DMA.Deb.Reduction.Name.Orig n)) )

    let root q =
      let n, cs = root_cands q in
      (n, PG.Ranges.of_list cs)

    module CT = DMA.Deb.Reduction.T

    (* the query has no root package: its names are the roots PubGrub is
       handed, each at the versions its range lists *)
    let check query sol =
      let s =
        CT.PkgSet.ofList
          (List.map (fun (n, (pv : PVersion.t)) -> (n, pv.PVersion.v)) sol)
      in
      let q =
        CT.DependeesSet.ofList
          (List.map
             (fun x ->
               let n, cs = root_cands x in
               (n, CT.VSet.ofList (List.map (fun pv -> pv.PVersion.v) cs)))
             query)
      in
      match CT.check I.versions I.dependencies q s with
      | None -> ()
      | Some f ->
          Pac_common.Check.fail ~pp_name:PName.pp
            ~pp_version:(fun n fmt v -> PVersion.pp fmt (tag n v))
            ~elements:CT.VSet.elements f

    let decode sol =
      let s' =
        DMA.Deb.Reduction.T.PkgSet.ofList
          (List.map (fun (n, (pv : PVersion.t)) -> (n, pv.PVersion.v)) sol)
      in
      List.map
        (fun ((n, b), v) -> (n, b, v))
        (DMA.PkgSet.elements
           (DMA.Reduction.debianMAResolution
              (DMA.Deb.Reduction.debianResolution s')))

    (* apt enqueues the requested packages as it walks its package table
       (FromDepCache, apt-pkg/solver3.cc): bucket by bucket of sHash, the
       djb2 hash of the lower-cased name modulo APT::Cache-HashTableSize,
       196613 by default; a bucket's groups by name length, then name
       (StringViewCompareFast); and a group's packages as they were
       created, the native one first (pkgcache.cc, pkgcachegen.cc) *)
    let request query =
      let bucket n =
        let h = ref 5381 in
        String.iter
          (fun c ->
            h :=
              ((33 * !h) + Char.code (Char.lowercase_ascii c)) land 0xffffffff)
          n;
        !h mod 196613
      in
      let key ((n, x), _) =
        let b = match x with DMA.QAArch b -> b | _ -> "" in
        (bucket n, String.length n, n, not (String.equal b AP.native), b)
      in
      List.map (fun ((m, _) as q) -> (DMA.Deb.Reduction.Name.Orig m, q)) query
      |> List.stable_sort (fun (_, a) (_, b) -> compare (key a) (key b))
      |> List.map fst

    let run ~debug ~check:checked ~order query =
      let h = Replay.hooks order (request query) in
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
          if checked then check query sol;
          Ok (decode sol, List.length sol)
  end

  let solve ~debug ~check ~order (tables : tables)
      (query : ((string * string) * Args.accepts) list) =
    (* each package's dependees, which the rejection cascade and every check
       of a clause's candidates ask for again *)
    let looked_up = Hashtbl.create 4096 in
    (* selector preimages by name, asked for again by every depender and by
       the rejection cascade *)
    let sel_cache = Hashtbl.create 4096 in
    let module S = Search (struct
      let tables = tables
      let versions = versions sel_cache tables

      let dependencies p =
        Pac_common.Tbl.memo looked_up p (fun () -> dependees sel_cache tables p)
    end) in
    let query =
      List.map (fun ((n, b), acc) -> ((n, DMA.QAArch b), acc)) query
    in
    let r = S.run ~debug ~check ~order query in
    let lookups = Hashtbl.length looked_up in
    let r = Result.map (fun (pkgs, nodes) -> { pkgs; nodes; lookups }) r in
    let core () =
      Pac_common.Core.print ~pp_name:PName.pp_core ~pp_version:S.PVersion.pp
        (Pac_common.Core.walk ~versions:S.cands_of
           ~dependees:(fun (n, (pv : S.PVersion.t)) ->
             S.dependees_of n pv.S.PVersion.v)
           (List.map (fun (n, _) -> DMA.Deb.Reduction.Name.Orig n) query))
    in
    (r, core)
end

type result = {
  answer : (answer, Pac_common.Report.explanation) Stdlib.result;
  core : unit -> unit;
  names : int;
  versions : int;
  dropped : int;
  cached : bool;
  t_parse : float;
}

(* a parse the entry may be written from carries its bytes' digests *)
type source =
  | Entry of in_channel
  | Parsed of DF.stanza list * int * string list option

(* A cache entry holds the parsed index, its drop count and the tables
   built with no version named; a query naming a version cuts the other
   candidates under Strict-Pinning, so it builds its own tables and writes
   no entry.  An entry is keyed by each file's device, inode, size and
   times, so a hit reads none of it; a file changed under two seconds before
   the run is parsed but not cached, since a write within the previous
   change's clock tick leaves the ctime where it was.  The entry keeps its
   source's digests, which --debug checks on a hit. *)
let solve_files ~debug ~check ~order ~recommends ~strict_pinning ~native ~cache
    ~paths ~query : (result, string) Stdlib.result =
  Pubgrub.set_debug debug;
  let t0 = Unix.gettimeofday () in
  let entry, settled =
    match cache with
    | None -> (None, false)
    | Some dir ->
        let ss =
          List.map
            (fun p ->
              In_channel.with_open_bin p (fun ic ->
                  Unix.fstat (Unix.descr_of_in_channel ic)))
            paths
        in
        ( Some
            (Pac_common.Cache.entry dir ~format:Index_format.digest
               (Digest.to_hex
                  (Digest.string
                     (String.concat "\000"
                        (List.map
                           (fun (s : Unix.stats) ->
                             Printf.sprintf "%d %d %d %h %h" s.st_dev s.st_ino
                               s.st_size s.st_mtime s.st_ctime)
                           ss
                        @ [
                            native;
                            string_of_bool recommends;
                            string_of_bool strict_pinning;
                          ]))))),
          List.for_all (fun (s : Unix.stats) -> s.st_ctime < t0 -. 2.) ss )
  in
  let ic = Option.bind entry Pac_common.Cache.open_entry in
  Fun.protect ~finally:(fun () -> Option.iter close_in_noerr ic) @@ fun () ->
  let parse () =
    let dropped = ref 0 in
    let reject () = incr dropped in
    let index, digests =
      if not settled then (List.concat_map (DF.parse_file ~reject) paths, None)
      else
        let bytes =
          List.map
            (fun p -> In_channel.with_open_bin p In_channel.input_all)
            paths
        in
        ( List.concat_map (DF.parse_string ~reject) bytes,
          Some (List.map Digest.string bytes) )
    in
    Parsed (index, !dropped, digests)
  in
  let arches_of index =
    List.sort_uniq String.compare
      (native
      :: List.filter_map
           (fun (st : DF.stanza) ->
             if st.architecture = "all" then None else Some st.architecture)
           index)
  in
  let rec at arches source =
    let module AP = struct
      let arches = arches
      let native = native
    end in
    let module M = Make (AP) in
    match
      match source with
      | Entry ic ->
          Option.map
            (fun (index, dropped, e) ->
              (index, dropped, Some (e : M.eager), None))
            (Pac_common.Cache.value ic)
      | Parsed (index, dropped, digests) -> Some (index, dropped, None, digests)
    with
    | None -> start (parse ())
    | Some (index, dropped, eager, digests) ->
        Result.map
          (fun (query, named) ->
            let unnamed = (not strict_pinning) || Hashtbl.length named = 0 in
            let tables =
              match eager with
              | Some e when unnamed -> M.of_eager e
              | _ ->
                  let tables =
                    M.build_tables ~recommends
                      (if strict_pinning then
                         Args.pin_candidates ~native ~named index
                       else index)
                  in
                  (match (entry, digests) with
                  | Some f, Some ds when unnamed ->
                      Pac_common.Cache.store f (fun oc ->
                          Marshal.to_channel oc (ds, arches) [];
                          Marshal.to_channel oc
                            (index, dropped, M.eager tables)
                            [])
                  | _ -> ());
                  tables
            in
            let t_parse = Unix.gettimeofday () -. t0 in
            let answer, core = M.solve ~debug ~check ~order tables query in
            let { Tables.names; versions } = M.stats tables in
            {
              answer;
              core;
              names;
              versions;
              dropped;
              cached = Option.is_some eager;
              t_parse;
            })
          (Args.parse_query ~native ~arches index query)
  and start = function
    | Parsed (index, _, _) as p -> at (arches_of index) p
    | Entry ic as e -> (
        match Pac_common.Cache.value ic with
        | Some (ds, _) when debug && List.map Digest.file paths <> ds ->
            prerr_endline "the cache entry was built from other bytes";
            start (parse ())
        | Some (_, arches) -> at arches e
        | None -> start (parse ()))
  in
  start (match ic with Some ic -> Entry ic | None -> parse ())
