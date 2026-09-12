(* PubGrub over the extracted multiarch reduction: stanzas are normalized
   to (name, arch, version) packages with Multi-Arch classes, and every
   query slice is a small MA-side restriction pushed through the verified
   translation (reduceReal/reduceDeps/reduceProv/reduceConf in DebianMA.v), so
   the translation itself computes the mangled Debian-side sets.  Queries
   then go through per-name slice instances — the Debian.v lookup lemmas
   applied at mangled names (N * NameArch) — and
   solutions come back through the two verified decoders (Deb.multiarchResolution,
   then DebianMA.multiarchResolution). *)

module E = Pac
module DF = Debian_frontend.Deb_packages

let c2r c = if c < 0 then E.Lt else if c > 0 then E.Gt else E.Eq
let r2c = function E.Lt -> -1 | E.Eq -> 0 | E.Gt -> 1

module StringOT = struct
  type t = string

  let compare a b = c2r (String.compare a b)
  let eq_dec (a : string) b = String.equal a b
end

module DebVersionOT = struct
  type t = string

  let compare a b = c2r (Debian_frontend.Deb_version.compare a b)
  let eq_dec a b = Debian_frontend.Deb_version.compare a b = 0
end

module Make (AP : sig
  val arches : string list
  val native : string
end) =
struct
  module APx = struct
    module A = struct
      type t = string

      let compare a b = c2r (String.compare a b)
      let eq_dec (a : string) b = String.equal a b
      let enum = AP.arches
    end

    let native = AP.native
  end

  module DMA = E.DebianMA (StringOT) (DebVersionOT) (APx)

  let formula_of_constr = function
    | None -> DMA.Deb.Ver.FTop
    | Some (DF.Ge, v) -> DMA.Deb.Ver.FCmp (E.OpGe, v)
    | Some (DF.Gt, v) -> DMA.Deb.Ver.FCmp (E.OpGt, v)
    | Some (DF.Le, v) -> DMA.Deb.Ver.FCmp (E.OpLe, v)
    | Some (DF.Lt, v) -> DMA.Deb.Ver.FCmp (E.OpLt, v)
    | Some (DF.Eq, v) -> DMA.Deb.Ver.FCmp (E.OpEq, v)

  let qual_of = function
    | DF.Unqual -> DMA.QUnq
    | DF.AnyArch -> DMA.QAny
    | DF.NativeArch -> DMA.QNative
    | DF.ExplicitArch a -> DMA.QArch a

  let matom_of (a : DF.atom) : DMA.Atom.t =
    (a.name, (qual_of a.aqual, formula_of_constr a.constr))

  let dtop_of = function Some v -> DMA.Deb.DTVal v | None -> DMA.Deb.DTTop
  let maset_of = DMA.AtomSet.ofList

  (* Normalized stanza: apt rewrites arch:all packages to the native arch
     and downgrades all+same to no (arch:all content is arch-invariant). *)
  type nstanza = {
    npkg : DMA.Pkg.t;
    ncls : DMA.coq_MAClass;
    ndeps : DMA.Atom.t list list;
    nprovs : (string * DMA.Deb.coq_DTop) list;
    nconfs : DMA.Atom.t list;
  }

  let normalize (st : DF.stanza) : nstanza =
    let arch = if st.architecture = "all" then AP.native else st.architecture in
    let ncls =
      match st.multi_arch with
      | Some "same" when st.architecture = "all" -> DMA.MANo
      | Some "same" -> DMA.MASame
      | Some "foreign" -> DMA.MAForeign
      | Some "allowed" -> DMA.MAAllowed
      | _ -> DMA.MANo
    in
    {
      npkg = ((st.package, arch), st.version);
      ncls;
      ndeps = List.map (List.map matom_of) st.depends;
      nprovs =
        List.map
          (fun (pr : DF.provide) -> (pr.pname, dtop_of pr.pversion))
          st.provides;
      nconfs = List.map matom_of st.conflicts;
    }

  (* Debian prefers the leftmost alternative in a Depends clause; ranks
     are keyed by the mangled atom
     (reduceAtom of the depending stanza's arch), which is what appears in
     encoded DVAtom versions. *)
  let atom_rank : (DMA.Deb.Atom.t, int) Hashtbl.t = Hashtbl.create 65536

  let rank a =
    match Hashtbl.find_opt atom_rank a with Some i -> i | None -> max_int

  (* Untrusted whole-archive index; faithfulness to the parsed instance is
     this module's only trusted-computing-base beyond the parser itself. *)
  type index = {
    versions_of : (string * string, string list) Hashtbl.t;
    stanza_of : (DMA.Pkg.t, nstanza) Hashtbl.t;
    group_of : (string, (string * string) list) Hashtbl.t;
    providers_of : (string, (DMA.Pkg.t * DMA.Deb.coq_DTop) list) Hashtbl.t;
    conflicts_on : (string, (DMA.Pkg.t * DMA.Atom.t) list) Hashtbl.t;
    clause_of_aset : (DMA.Deb.AtomSet.t, DMA.Pkg.t * DMA.AtomSet.t) Hashtbl.t;
    clause_of_atom : (DMA.Deb.Atom.t, DMA.Pkg.t * DMA.AtomSet.t) Hashtbl.t;
    class_of : (DMA.Pkg.t, DMA.coq_MAClass) Hashtbl.t;
  }

  let push tbl k v =
    Hashtbl.replace tbl k
      (v :: (match Hashtbl.find_opt tbl k with Some l -> l | None -> []))

  let build_index (stanzas : DF.stanza list) : index =
    let idx =
      {
        versions_of = Hashtbl.create 65536;
        stanza_of = Hashtbl.create 65536;
        group_of = Hashtbl.create 65536;
        providers_of = Hashtbl.create 4096;
        conflicts_on = Hashtbl.create 4096;
        clause_of_aset = Hashtbl.create 65536;
        clause_of_atom = Hashtbl.create 65536;
        class_of = Hashtbl.create 65536;
      }
    in
    List.iter
      (fun st ->
        let ns = normalize st in
        let (n, b), v = ns.npkg in
        push idx.versions_of (n, b) v;
        Hashtbl.replace idx.stanza_of ns.npkg ns;
        push idx.group_of n (b, v);
        Hashtbl.replace idx.class_of ns.npkg ns.ncls;
        List.iter
          (fun (m, vt) -> push idx.providers_of m (ns.npkg, vt))
          ns.nprovs;
        List.iter
          (fun ma -> push idx.conflicts_on (DMA.aname ma) (ns.npkg, ma))
          ns.nconfs;
        List.iter
          (fun alts ->
            let aset = maset_of alts in
            Hashtbl.replace idx.clause_of_aset (DMA.reduceClause b aset)
              (ns.npkg, aset);
            List.iteri
              (fun i ma ->
                let ea = DMA.reduceAtom b ma in
                if not (Hashtbl.mem atom_rank ea) then
                  Hashtbl.replace atom_rank ea i;
                Hashtbl.replace idx.clause_of_atom ea (ns.npkg, aset))
              alts)
          ns.ndeps)
      stanzas;
    idx

  (* MA-side slice builders, in the shapes DebianMA.Lookup proves
     sufficient (versions_lookup*MA / dependees_lookup*MA). *)

  let find_list tbl k =
    match Hashtbl.find_opt tbl k with Some l -> l | None -> []

  let ma_real_at idx (n, b) =
    DMA.PkgSet.ofList
      (List.map (fun v -> ((n, b), v)) (find_list idx.versions_of (n, b)))

  (* Every group member at any arch: foreign provides and group provides
     come from any member, so name slices must span the whole group. *)
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
    | Some ns ->
        DMA.Prov.ofList (List.map (fun (m, vt) -> (p, (m, vt))) ns.nprovs)

  let ma_deps_of_pkg idx p =
    match Hashtbl.find_opt idx.stanza_of p with
    | None -> DMA.Deps.empty
    | Some ns ->
        DMA.Deps.ofList (List.map (fun alts -> (p, maset_of alts)) ns.ndeps)

  let ma_conf_of_pkg idx p =
    match Hashtbl.find_opt idx.stanza_of p with
    | None -> DMA.Conf.empty
    | Some ns -> DMA.Conf.ofList (List.map (fun ma -> (p, ma)) ns.nconfs)

  let ma_conf_on_names idx ns =
    DMA.Conf.ofList (List.concat_map (find_list idx.conflicts_on) ns)

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
    | Some ns -> List.concat_map (List.map DMA.aname) ns.ndeps

  let prov_names_of idx p =
    match Hashtbl.find_opt idx.stanza_of p with
    | None -> []
    | Some ns -> List.map fst ns.nprovs

  (* Singleton clause slices as in deb_solve.ml, except the stored clause is
     MA-side and the mangled clause is recomputed by reduceDeps, so the
     translated slice is the translation of a sub-instance by construction. *)
  let clause_by_aset idx aset =
    match Hashtbl.find_opt idx.clause_of_aset aset with
    | None -> DMA.Deb.Deps.empty
    | Some (p, mal) -> DMA.reduceDeps (DMA.Deps.add (p, mal) DMA.Deps.empty)

  let clause_by_atom idx a =
    match Hashtbl.find_opt idx.clause_of_atom a with
    | None -> DMA.Deb.Deps.empty
    | Some (p, mal) -> DMA.reduceDeps (DMA.Deps.add (p, mal) DMA.Deps.empty)

  (* R/Pi slices for a mangled name (m, x): whichever x is, every provider
     of (m, x) is either a group member of m (reals, implicit group /
     foreign / :any provides) or a declared provider of m. *)
  let sel_slices idx (mn : string * DMA.coq_NameArch) =
    let m = fst mn in
    let r_ma = ma_group_of_names idx [ m ] in
    let pi_decl = ma_prov_of_names idx [ m ] in
    let cls =
      classes_of idx
        (DMA.PkgSet.elements r_ma @ List.map fst (DMA.Prov.elements pi_decl))
    in
    (DMA.reduceReal r_ma, DMA.reduceProv r_ma pi_decl cls)

  (* Conflict entries owned by one mangled package: its hand-written
     negatives plus its implicit group exclusion.  PubGrub re-queries each
     guard name many times during propagation, so memoize per owner. *)
  let guard_memo : (DMA.Deb.Ver.C.Pkg.t, DMA.Deb.Conf.t) Hashtbl.t =
    Hashtbl.create 1024

  let guard_conf idx (pm : DMA.Deb.Ver.C.Pkg.t) =
    match Hashtbl.find_opt guard_memo pm with
    | Some g -> g
    | None ->
        let g =
          match pm with
          | (n, DMA.QAArch b), v ->
              let p = ((n, b), v) in
              DMA.reduceConf
                (DMA.PkgSet.add p DMA.PkgSet.empty)
                (ma_conf_of_pkg idx p) (classes_of idx [ p ])
          | _ -> DMA.Deb.Conf.empty
        in
        Hashtbl.replace guard_memo pm g;
        g

  let vers_sparse idx (n' : DMA.Deb.Name.t) =
    match n' with
    | DMA.Deb.Name.Orig (n, DMA.QAArch b) ->
        (* Lookup.versions_lookupOrig *)
        DMA.Deb.versions
          (DMA.reduceReal (ma_real_at idx (n, b)))
          DMA.Deb.Deps.empty DMA.Deb.Prov.empty DMA.Deb.Conf.empty n'
    | DMA.Deb.Name.Orig _ ->
        (* embedPkg mints only QAArch names: no reals at :any/group names *)
        DMA.Deb.versions DMA.Deb.Ver.C.PkgSet.empty DMA.Deb.Deps.empty
          DMA.Deb.Prov.empty DMA.Deb.Conf.empty n'
    | DMA.Deb.Name.Disjunct aset ->
        (* Lookup.versions_lookupDisjunct *)
        DMA.Deb.versions DMA.Deb.Ver.C.PkgSet.empty (clause_by_aset idx aset)
          DMA.Deb.Prov.empty DMA.Deb.Conf.empty n'
    | DMA.Deb.Name.Selector a ->
        (* Lookup.versions_lookupSelector *)
        let r, pi = sel_slices idx (fst a) in
        DMA.Deb.versions r (clause_by_atom idx a) pi DMA.Deb.Conf.empty n'
    | DMA.Deb.Name.Guard (p, _, _) ->
        (* Lookup.versions_lookupGuard *)
        DMA.Deb.versions DMA.Deb.Ver.C.PkgSet.empty DMA.Deb.Deps.empty
          DMA.Deb.Prov.empty (guard_conf idx p) n'

  let dependees_sparse idx (s : DMA.Deb.T.Pkg.t) =
    match s with
    | DMA.Deb.Name.Orig (n, DMA.QAArch b), DMA.Deb.Version.Orig v ->
        (* Lookup.dependees_lookupOrig *)
        let p = ((n, b), v) in
        let m = atom_names_of idx p in
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
        (* group members of n carry the implicit conflicts that can target
           p through (n, group); hand-written negatives reach p only via
           its name or a name it provides *)
        let g_r =
          DMA.PkgSet.ofList
            (p
            :: List.map
                 (fun (b', v') -> ((n, b'), v'))
                 (find_list idx.group_of n))
        in
        let g_conf =
          DMA.Conf.union (ma_conf_of_pkg idx p)
            (ma_conf_on_names idx (n :: prov_names_of idx p))
        in
        let g_cls =
          classes_of idx
            (DMA.PkgSet.elements g_r @ List.map fst (DMA.Conf.elements g_conf))
        in
        DMA.Deb.dependees (DMA.reduceReal r_ma)
          (DMA.reduceDeps (ma_deps_of_pkg idx p))
          (DMA.reduceProv r_pi pi_decl pi_cls)
          (DMA.reduceConf g_r g_conf g_cls)
          s
    | DMA.Deb.Name.Disjunct aset, DMA.Deb.Version.Atom a ->
        (* Lookup.dependees_lookupDisjunct *)
        let r, pi = sel_slices idx (fst a) in
        DMA.Deb.dependees r (clause_by_aset idx aset) pi DMA.Deb.Conf.empty s
    | ( DMA.Deb.Name.Selector a,
        (DMA.Deb.Version.Ref (_, _) | DMA.Deb.Version.RefReal _) ) ->
        (* Lookup.dependees_lookupSelector *)
        let r, pi = sel_slices idx (fst a) in
        DMA.Deb.dependees r (clause_by_atom idx a) pi DMA.Deb.Conf.empty s
    | _ ->
        (* Lookup.dependees_lookupGuard; other shape mismatches are empty
           by definition of dependees *)
        DMA.Deb.T.DependeesSet.empty

  (* PubGrub instantiation over the encoded mangled names/versions. *)

  let pp_formula fmt (f : DMA.Deb.Ver.coq_Formula) =
    let rec go fmt = function
      | DMA.Deb.Ver.FTop -> Format.fprintf fmt "T"
      | DMA.Deb.Ver.FBot -> Format.fprintf fmt "F"
      | DMA.Deb.Ver.FConj (a, b) -> Format.fprintf fmt "(%a & %a)" go a go b
      | DMA.Deb.Ver.FDisj (a, b) -> Format.fprintf fmt "(%a | %a)" go a go b
      | DMA.Deb.Ver.FCmp (op, v) ->
          let ops =
            match op with
            | E.OpGe -> ">="
            | E.OpGt -> ">>"
            | E.OpLe -> "<="
            | E.OpLt -> "<<"
            | E.OpEq -> "="
            | E.OpNe -> "!="
          in
          Format.fprintf fmt "%s %s" ops v
    in
    go fmt f

  let pp_qarch fmt = function
    | DMA.QAArch a -> Format.fprintf fmt "%s" a
    | DMA.QAAny -> Format.fprintf fmt "any"
    | DMA.QAGroup -> Format.fprintf fmt "<group>"

  let pp_mname fmt (n, x) = Format.fprintf fmt "%s:%a" n pp_qarch x
  let pp_atom fmt (m, f) = Format.fprintf fmt "%a (%a)" pp_mname m pp_formula f

  module PName = struct
    type t = DMA.Deb.Name.t

    let compare a b = r2c (DMA.Deb.NameOT.compare a b)

    let pp fmt = function
      | DMA.Deb.Name.Orig m -> pp_mname fmt m
      | DMA.Deb.Name.Disjunct _ -> Format.fprintf fmt "<alts>"
      | DMA.Deb.Name.Selector a -> Format.fprintf fmt "<sel %a>" pp_atom a
      | DMA.Deb.Name.Guard ((m, v), a, _) ->
          Format.fprintf fmt "<guard %a=%s vs %a>" pp_mname m v pp_atom a
  end

  let is_native = function
    | DMA.QAArch a -> String.equal a AP.native
    | _ -> false

  module PVersion = struct
    type t = DMA.Deb.Version.t

    (* PubGrub decides the V.compare-maximum candidate, so preference lives
       here: dpkg-newest for real versions, leftmost alternative via atom
       rank, a real package above any alias claiming its name, native-arch
       referents first within each, encoded order otherwise.  The calculus
       only makes the real/provided split legible -- RefReal carries no name,
       so it is the one candidate that cannot be an alias -- and says nothing
       about which to try first. *)
    let compare a b =
      match (a, b) with
      | DMA.Deb.Version.Orig x, DMA.Deb.Version.Orig y ->
          Debian_frontend.Deb_version.compare x y
      | DMA.Deb.Version.Atom x, DMA.Deb.Version.Atom y ->
          (* leftmost alternative first: lower rank = greater version *)
          let c = Stdlib.compare (rank y) (rank x) in
          if c <> 0 then c else r2c (DMA.Deb.VersionOT.compare a b)
      | DMA.Deb.Version.RefReal w, DMA.Deb.Version.RefReal w' ->
          (* one selector's real candidates all share its name, hence its
             arch: only the version separates them *)
          let c = Debian_frontend.Deb_version.compare w w' in
          if c <> 0 then c else r2c (DMA.Deb.VersionOT.compare a b)
      | DMA.Deb.Version.RefReal _, DMA.Deb.Version.Ref (_, _) -> 1
      | DMA.Deb.Version.Ref (_, _), DMA.Deb.Version.RefReal _ -> -1
      | DMA.Deb.Version.Ref ((_, x), w), DMA.Deb.Version.Ref ((_, x'), w') ->
          let c = Stdlib.compare (is_native x) (is_native x') in
          if c <> 0 then c
          else
            let c = Debian_frontend.Deb_version.compare w w' in
            if c <> 0 then c else r2c (DMA.Deb.VersionOT.compare a b)
      | _ -> r2c (DMA.Deb.VersionOT.compare a b)

    let pp fmt = function
      | DMA.Deb.Version.Orig v -> Format.fprintf fmt "%s" v
      | DMA.Deb.Version.Atom a -> Format.fprintf fmt "alt:%a" pp_atom a
      | DMA.Deb.Version.Ref (m, w) ->
          Format.fprintf fmt "ref:%a=%s" pp_mname m w
      | DMA.Deb.Version.RefReal w -> Format.fprintf fmt "real:%s" w
      | DMA.Deb.Version.Zero -> Format.fprintf fmt "0"
      | DMA.Deb.Version.One -> Format.fprintf fmt "1"
  end

  module PG = Pubgrub.Make (PName) (PVersion)

  let run_pubgrub ?(debug = false) ~versions ~dependencies goal =
    let dependencies n v =
      DMA.Deb.T.DependeesSet.elements (dependencies (n, v))
      |> List.map (fun (tn, tvs) ->
          (tn, PG.Ranges.of_list (DMA.Deb.T.VSet.elements tvs)))
    in
    let versions n = DMA.Deb.T.VSet.elements (versions n) in
    (* Ranges.full here trips an upstream pubgrub edge case (initial
       Neg-term status); the goal's available versions are what we mean
       anyway. *)
    let goal_range = PG.Ranges.of_list (versions (DMA.Deb.Name.Orig goal)) in
    match
      PG.solve ~versions ~dependencies [ (DMA.Deb.Name.Orig goal, goal_range) ]
    with
    | Error inc ->
        Format.printf "unsatisfiable:@.%a@." PG.explain_incompatibility inc;
        None
    | Ok sol ->
        if debug then (
          Format.printf "raw solution (%d):@." (List.length sol);
          List.iter
            (fun (n, v) -> Format.printf "  %a = %a@." PName.pp n PVersion.pp v)
            sol);
        let s' = DMA.Deb.T.PkgSet.ofList sol in
        Some
          (List.map
             (fun ((n, b), v) -> (n, b, v))
             (DMA.PkgSet.elements
                (DMA.multiarchResolution (DMA.Deb.debianResolution s'))))

  let prof_vc = ref 0
  let prof_vt = ref 0.
  let prof_oc = ref 0
  let prof_ot = ref 0.

  let timed c t f x =
    incr c;
    let t0 = Sys.time () in
    let r = f x in
    t := !t +. (Sys.time () -. t0);
    r

  let solve ?debug (idx : index) (goal_name : string) (goal_arch : string) =
    let buckets : (string, int ref * float ref) Hashtbl.t = Hashtbl.create 8 in
    let bucket name f x =
      let c, t =
        match Hashtbl.find_opt buckets name with
        | Some ct -> ct
        | None ->
            let ct = (ref 0, ref 0.) in
            Hashtbl.replace buckets name ct;
            ct
      in
      timed c t f x
    in
    let vname : DMA.Deb.Name.t -> string = function
      | DMA.Deb.Name.Orig _ -> "orig"
      | DMA.Deb.Name.Disjunct _ -> "disj"
      | DMA.Deb.Name.Selector _ -> "sel"
      | DMA.Deb.Name.Guard _ -> "guard"
    in
    let r =
      run_pubgrub ?debug
        ~versions:(fun n' -> bucket (vname n') (vers_sparse idx) n')
        ~dependencies:(timed prof_oc prof_ot (dependees_sparse idx))
        (goal_name, DMA.QAArch goal_arch)
    in
    if Sys.getenv_opt "PACPROF" <> None then (
      Hashtbl.iter
        (fun name (c, t) ->
          Printf.eprintf "PACPROF versions/%s: %d calls %.2fs\n%!" name !c !t)
        buckets;
      Printf.eprintf "PACPROF dependees: %d calls %.2fs\n%!" !prof_oc !prof_ot);
    r

  (* Fixture-scale oracle: the whole instance through the translation in
     one shot, no slicing -- use for cross-checks, not archives. *)
  let solve_monolithic ?debug (idx : index) (goal_name : string)
      (goal_arch : string) =
    let stz = Hashtbl.fold (fun _ ns acc -> ns :: acc) idx.stanza_of [] in
    let r_ma = DMA.PkgSet.ofList (List.map (fun ns -> ns.npkg) stz) in
    let d_ma =
      DMA.Deps.ofList
        (List.concat_map
           (fun ns -> List.map (fun alts -> (ns.npkg, maset_of alts)) ns.ndeps)
           stz)
    in
    let pi_ma =
      DMA.Prov.ofList
        (List.concat_map
           (fun ns -> List.map (fun (m, vt) -> (ns.npkg, (m, vt))) ns.nprovs)
           stz)
    in
    let g_ma =
      DMA.Conf.ofList
        (List.concat_map
           (fun ns -> List.map (fun ma -> (ns.npkg, ma)) ns.nconfs)
           stz)
    in
    let cls = DMA.Cls.ofList (List.map (fun ns -> (ns.npkg, ns.ncls)) stz) in
    let r = DMA.reduceReal r_ma in
    let d = DMA.reduceDeps d_ma in
    let pi = DMA.reduceProv r_ma pi_ma cls in
    let g = DMA.reduceConf r_ma g_ma cls in
    run_pubgrub ?debug
      ~versions:(DMA.Deb.versions r d pi g)
      ~dependencies:(DMA.Deb.dependees r d pi g)
      (goal_name, DMA.QAArch goal_arch)
end

let solve_files ?debug ?(monolithic = false) ~native ~paths ~goal :
    (string * string * string) list option =
  let stanzas = List.concat_map DF.parse_file paths in
  let arches =
    List.sort_uniq String.compare
      (native
      :: List.filter_map
           (fun (st : DF.stanza) ->
             if st.architecture = "all" then None else Some st.architecture)
           stanzas)
  in
  let module M = Make (struct
    let arches = arches
    let native = native
  end) in
  let goal_name, goal_arch =
    match String.index_opt goal ':' with
    | Some i ->
        ( String.sub goal 0 i,
          String.sub goal (i + 1) (String.length goal - i - 1) )
    | None -> (goal, native)
  in
  let idx = M.build_index stanzas in
  if monolithic then M.solve_monolithic ?debug idx goal_name goal_arch
  else M.solve ?debug idx goal_name goal_arch
