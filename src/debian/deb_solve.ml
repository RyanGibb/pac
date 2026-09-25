(* PubGrub over the extracted multiarch reduction: stanzas are normalized
   to (name, arch, version) packages with Multi-Arch classes, and every
   lookup's sub-instance is a small MA-side restriction pushed through the
   verified translation (reduceReal/reduceDeps/reduceProv/reduceConf in
   DebianMA.v), so the translation itself computes the mangled Debian-side
   sets.  Lookups then go through per-name sub-instances — the Debian.v
   lookup lemmas
   applied at mangled names (N * NameArch) — and
   solutions come back through the two verified decoders (Deb.multiarchResolution,
   then DebianMA.multiarchResolution). *)

module E = Pac
module DF = Debian_frontend.Deb_packages

let c2r c = if c < 0 then E.Lt else if c > 0 then E.Gt else E.Eq
let r2c = function E.Lt -> -1 | E.Eq -> 0 | E.Gt -> 1

(* Nothing is an element whose named version apt finds no match for; it
   refuses the whole request, which an empty range says. *)
type accepts = Any | Only of string | Nothing

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

  (* Normalized stanza: apt rewrites arch:all packages to the native arch
     and downgrades all+same to no (arch:all content is arch-invariant).
     Its Depends and Recommends clauses are still the raw field text, and
     are mangled once, on the first sub-instance that reads them. *)
  type nstanza = {
    npkg : DMA.Pkg.t;
    ncls : DMA.coq_MAClass;
    raw_deps : string list;
    raw_recs : string list;
    mutable nclauses : (DMA.Atom.t list list * DMA.Atom.t list list) option;
    nprovs : (string * DMA.Deb.coq_DTop) list;
    nconfs : DMA.Atom.t list;
    (* apt ranks the providers claiming a name by these; see pref below *)
    ness : bool;
    nimp : bool;
    nprio : int;
    nsrc : string * string;
    (* apt keys an arch:all version apart from its native twin
       (Version::All), whatever package arch it was filed under *)
    nall : bool;
  }

  (* ~recommends false is the --no-install-recommends reading: the Rec
     instance is empty, so every soft disjunct is empty and unreachable. *)
  let normalize ~recommends (st : DF.stanza) : nstanza =
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
      raw_deps = st.depends_raw;
      raw_recs = (if recommends then st.recommends_raw else []);
      nclauses = None;
      nprovs =
        List.map
          (fun (pr : DF.provide) -> (pr.pname, dtop_of pr.pversion))
          st.provides;
      nconfs = List.map matom_of st.conflicts;
      (* apt's cache generator marks the package named apt Essential and
         Important whatever its stanza says (deblistparser.cc, UsePackage:
         pkgCacheGen::ForceEssential defaults to "apt"), and the solver
         ranks providers on the flags in the cache, not in the stanza *)
      ness = st.essential || st.package = "apt";
      nimp = st.important || st.package = "apt";
      nprio = st.priority;
      nsrc = st.source;
      nall = st.architecture = "all";
    }

  (* Untrusted whole-archive index; faithfulness to the parsed instance is
     this module's only trusted-computing-base beyond the parser itself. *)
  type index = {
    versions_of : (string * string, string list) Hashtbl.t;
    stanza_of : (DMA.Pkg.t, nstanza) Hashtbl.t;
    group_of : (string, (string * string) list) Hashtbl.t;
    providers_of : (string, (DMA.Pkg.t * DMA.Deb.coq_DTop) list) Hashtbl.t;
    class_of : (DMA.Pkg.t, DMA.coq_MAClass) Hashtbl.t;
    (* stanzas whose clauses a sub-instance has asked for, reported under
       PACPROF:
       the whole point of deferring them is that this stays small *)
    mutable n_clauses_parsed : int;
    (* who names a package in a Depends or Pre-Depends, and who in a
       Conflicts or Breaks, by the bare name as written: the watch lists
       apt's Reject propagation walks, built on first use from the field
       text alone, so no clause is parsed for them; only the --apt-heap
       search asks *)
    mutable rev_dep : (string, DMA.Pkg.t list) Hashtbl.t option;
    mutable rev_conf : (string, DMA.Pkg.t list) Hashtbl.t option;
    (* the binaries each source name builds, for apt's obsolescence test;
       likewise built on first use, and only by --apt-heap *)
    mutable by_src : (string, nstanza list) Hashtbl.t option;
    (* selector preimages by name, and a package's clauses in field order,
       both asked for again by every depender and by the rejection cascade *)
    sel_cache :
      (string * DMA.coq_NameArch, DMA.Deb.PkgSet.t * DMA.Deb.Prov.t) Hashtbl.t;
    oc_cache :
      (DMA.Pkg.t, (bool * DMA.Deb.Name.t * DMA.Deb.Atom.t list) list) Hashtbl.t;
  }

  let push tbl k v =
    Hashtbl.replace tbl k
      (v :: (match Hashtbl.find_opt tbl k with Some l -> l | None -> []))

  let mangle fields =
    List.map (List.map matom_of) (DF.parse_depends_fields fields)

  (* the alternative's position in the clause being decided, which is what
     PVersion.compare ranks on; max_int for an atom the clause does not list,
     which cannot arise for a name introduced from that clause *)
  let atom_pos (alts : DMA.Deb.Clause.t) a =
    let rec go i = function
      | [] -> max_int
      | b :: bs -> if DMA.Deb.Atom.eq_dec b a then i else go (i + 1) bs
    in
    go 0 alts

  (* the bare names a relationship field mentions, one per alternative: the
     token before any version or architecture qualifier, in one pass *)
  let field_names fields =
    List.concat_map
      (fun f ->
        let n = String.length f in
        let acc = ref [] in
        let i = ref 0 in
        while !i < n do
          while !i < n && f.[!i] = ' ' do
            incr i
          done;
          let s = !i in
          while
            !i < n
            &&
            match f.[!i] with
            | ' ' | '(' | ':' | ',' | '|' | '\n' -> false
            | _ -> true
          do
            incr i
          done;
          if !i > s then acc := String.sub f s (!i - s) :: !acc;
          while !i < n && f.[!i] <> ',' && f.[!i] <> '|' do
            incr i
          done;
          if !i < n then incr i
        done;
        !acc)
      fields

  let build_index ?(recommends = true) (stanzas : DF.stanza list) : index =
    let idx =
      {
        versions_of = Hashtbl.create 65536;
        stanza_of = Hashtbl.create 65536;
        group_of = Hashtbl.create 65536;
        providers_of = Hashtbl.create 4096;
        class_of = Hashtbl.create 65536;
        n_clauses_parsed = 0;
        rev_dep = None;
        rev_conf = None;
        by_src = None;
        sel_cache = Hashtbl.create 4096;
        oc_cache = Hashtbl.create 4096;
      }
    in
    List.iter
      (fun st ->
        let stz = normalize ~recommends st in
        let (n, b), v = stz.npkg in
        push idx.versions_of (n, b) v;
        Hashtbl.replace idx.stanza_of stz.npkg stz;
        push idx.group_of n (b, v);
        Hashtbl.replace idx.class_of stz.npkg stz.ncls;
        List.iter
          (fun (m, vt) -> push idx.providers_of m (stz.npkg, vt))
          stz.nprovs)
      stanzas;
    idx

  let reverse_index idx =
    match (idx.rev_dep, idx.rev_conf) with
    | Some d, Some c -> (d, c)
    | _ ->
        let d = Hashtbl.create 65536 and c = Hashtbl.create 4096 in
        Hashtbl.iter
          (fun p (stz : nstanza) ->
            List.iter (fun n -> push d n p) (field_names stz.raw_deps);
            List.iter (fun a -> push c (DMA.aname a) p) stz.nconfs)
          idx.stanza_of;
        idx.rev_dep <- Some d;
        idx.rev_conf <- Some c;
        (d, c)

  (* apt's ObsoletedByNewerSourceVersion (solver3.cc:863-888): another
     binary of the same source, on the same architecture and equally arch:all
     or not, comes from a newer source version.  apt also asks that binary's
     pin priority to be no lower, which with no pins every version meets. *)
  let obsolete idx (stz : nstanza) =
    let by_src =
      match idx.by_src with
      | Some t -> t
      | None ->
          let t = Hashtbl.create 65536 in
          Hashtbl.iter (fun _ (s : nstanza) -> push t (fst s.nsrc) s) idx.stanza_of;
          idx.by_src <- Some t;
          t
    in
    let (_, b), _ = stz.npkg in
    List.exists
      (fun (s : nstanza) ->
        let (_, b'), _ = s.npkg in
        fst s.npkg <> fst stz.npkg
        && String.equal b b' && s.nall = stz.nall
        && Debian_frontend.Deb_version.compare (snd s.nsrc) (snd stz.nsrc) > 0)
      (match Hashtbl.find_opt by_src (fst stz.nsrc) with
      | Some l -> l
      | None -> [])

  (* Only a lookup at a stanza's own package reads its clauses, so they can
     wait until one does.  providers_of cannot: it is a preimage -- who
     provides the name I want -- that no clause of the asking package can
     reach, so Provides stays eager. *)
  let clauses_of idx (stz : nstanza) =
    match stz.nclauses with
    | Some c -> c
    | None ->
        let c = (mangle stz.raw_deps, mangle stz.raw_recs) in
        stz.nclauses <- Some c;
        idx.n_clauses_parsed <- idx.n_clauses_parsed + 1;
        c

  let deps_of idx stz = fst (clauses_of idx stz)
  let recs_of idx stz = snd (clauses_of idx stz)

  (* One package's clauses in control-file order, Depends before Recommends,
     each with its mangled alternatives and the synthetic name a multi-way
     clause would carry: the order apt's Propagate walks the watches of a
     package that just became true, which is the order its work items enter
     the heap.  A one-alternative Depends has no disjunct package (Debian.v
     introduces one only at cardinality >= 2): its work item, when it has
     one, is
     the alternative's selector, which the caller resolves because a
     selector in turn exists only for a provided name (tgt, Debian.v). *)
  let ordered_clauses idx (p : DMA.Pkg.t) :
      (bool * DMA.Deb.Name.t * DMA.Deb.Atom.t list) list =
    match Hashtbl.find_opt idx.oc_cache p with
    | Some r -> r
    | None ->
        let r =
          match Hashtbl.find_opt idx.stanza_of p with
          | None -> []
          | Some stz ->
              let b = snd (fst p) in
              let mk opt synth alts =
                let ma = DMA.reduceClause b alts in
                let eatoms =
                  List.sort_uniq Stdlib.compare
                    (List.map (DMA.reduceAtom b) alts)
                in
                (opt, synth ma, eatoms)
              in
              List.map
                (fun alts -> mk false (fun s -> DMA.Deb.Name.Disjunct s) alts)
                (deps_of idx stz)
              @ List.map
                  (fun alts -> mk true (fun s -> DMA.Deb.Name.Soft s) alts)
                  (recs_of idx stz)
        in
        Hashtbl.add idx.oc_cache p r;
        r

  (* Does version [w] satisfy the atom's formula?  Mangled formulas compare
     raw Debian versions, so dpkg's comparison decides. *)
  let rec sat f w =
    match f with
    | DMA.Deb.Ver.FTop -> true
    | DMA.Deb.Ver.FBot -> false
    | DMA.Deb.Ver.FConj (p, q) -> sat p w && sat q w
    | DMA.Deb.Ver.FDisj (p, q) -> sat p w || sat q w
    | DMA.Deb.Ver.FCmp (op, u) -> (
        let c = Debian_frontend.Deb_version.compare w u in
        match op with
        | E.OpGe -> c >= 0
        | E.OpGt -> c > 0
        | E.OpLe -> c <= 0
        | E.OpLt -> c < 0
        | E.OpEq -> c = 0
        | E.OpNe -> c <> 0)

  (* MA-side sub-instance builders, in the shapes DebianMA.Lookup proves
     sufficient (versions_lookup*MA / dependees_lookup*MA). *)

  let find_list tbl k =
    match Hashtbl.find_opt tbl k with Some l -> l | None -> []

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
        (* Lookup.versions_lookupOrigMA *)
        DMA.Deb.T.VSet.add DMA.Deb.Version.Bot
          (DMA.Deb.embedVS
             (DMA.Deb.Ver.realVersions
                (DMA.reduceReal (ma_real_at idx (n, b)))
                (n, DMA.QAArch b)))
    | DMA.Deb.Name.Orig _ ->
        (* Lookup.versions_lookupOrigMA_pseudo: embedPkg introduces only
           QAArch names, so an explicit-qualifier, :any or group
           pseudo-name carries absence alone *)
        DMA.Deb.T.VSet.singleton DMA.Deb.Version.Bot
    | DMA.Deb.Name.Disjunct aset ->
        (* Lookup.versions_lookupDisjunct *)
        DMA.Deb.versionsDisj aset
    | DMA.Deb.Name.Soft aset ->
        (* Lookup.versions_lookupSoft *)
        DMA.Deb.versionsSoft aset
    | DMA.Deb.Name.Selector a ->
        (* Lookup.versions_lookupSelector *)
        let r, pi = sel_preimages idx (fst a) in
        DMA.Deb.us r pi a

  let dependees_sparse idx (s : DMA.Deb.T.Pkg.t) =
    match s with
    | DMA.Deb.Name.Orig (n, DMA.QAArch b), DMA.Deb.Version.Orig v ->
        (* Lookup.dependees_lookupOrigMA *)
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
        (* Lookup.dependees_lookupDisjunct *)
        let r, pi = sel_preimages idx (fst a) in
        DMA.Deb.T.DependeesSet.singleton (DMA.Deb.tgt r pi a)
    | DMA.Deb.Name.Soft _, DMA.Deb.Version.Atom a ->
        (* Lookup.dependees_lookupSoft *)
        let r, pi = sel_preimages idx (fst a) in
        DMA.Deb.T.DependeesSet.singleton (DMA.Deb.tgt r pi a)
    | DMA.Deb.Name.Selector _, DMA.Deb.Version.Ref (m, w) ->
        (* Lookup.dependees_lookupSelector *)
        DMA.Deb.T.DependeesSet.singleton
          ( DMA.Deb.Name.Orig m,
            DMA.Deb.T.VSet.singleton (DMA.Deb.Version.Orig w) )
    | DMA.Deb.Name.Selector a, DMA.Deb.Version.RefReal w ->
        DMA.Deb.T.DependeesSet.singleton
          ( DMA.Deb.Name.Orig (DMA.Deb.aname a),
            DMA.Deb.T.VSet.singleton (DMA.Deb.Version.Orig w) )
    | _ ->
        (* Lookup.dependees_lookupAbsent; other shape mismatches are empty
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
    | DMA.QAExact a -> Format.fprintf fmt "<%s>" a
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
      | DMA.Deb.Name.Soft _ -> Format.fprintf fmt "<rec>"
      | DMA.Deb.Name.Selector a -> Format.fprintf fmt "<sel %a>" pp_atom a
  end

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
     cases are
     unreachable and rank as an unindexed package would. *)
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
     from, so
     the comparator and the PubGrub instance over it are built per solve. *)
  module Search (I : sig
    val idx : index
  end) =
  struct
    module PVersion = struct
      (* pos is the candidate's position in the clause whose name is being
         decided -- supplied by tag, where that name is known -- and is a
         constant for every candidate that is not an alternative of one. *)
      type t = { pos : int; v : DMA.Deb.Version.t }

      (* PubGrub decides the V.compare-maximum candidate, so preference lives
         here: dpkg-newest for real versions, leftmost alternative by clause
         position, a real package above any alias claiming its name, and apt's
         candidate order among the aliases.  The calculus only makes the
         real/provided split legible -- RefReal carries no name, so it is the
         one candidate that cannot be an alias -- and says nothing about which
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
        let fallback () = r2c (DMA.Deb.VersionOT.compare a.v b.v) in
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

    (* ~apt_heap replays apt's work-heap scheduling through Apt_heap: the
       hooks below then stand in for apt's propagation queue (which name is
       first sighted when) and its Solver::Work pushes.  Off, none of them
       fires and the search is the plain PubGrub one. *)
    let run_pubgrub ?(debug = false) ?(apt_heap = false) ~versions ~dependencies
        query =
      let cands_tbl = Hashtbl.create 4096 in
      let cands_of n =
        match Hashtbl.find_opt cands_tbl n with
        | Some l -> l
        | None ->
            let l = List.map (tag n) (DMA.Deb.T.VSet.elements (versions n)) in
            Hashtbl.add cands_tbl n l;
            l
      in
      (* apt's solution counts: an alternative's solutions are its target's
         versions that satisfy it and, one per entry, the target's
         ProvidesList entries that do (AllTargets, pkgcache.cc), so a
         package providing its own name is two solutions.  A provided name
         resolves through its selector, whose Ref candidates are keyed by
         provider package; the entries apt holds for one are its declared
         Provides of the name, plus the foo:any of a Multi-Arch: allowed
         package and the foo:b pseudo-package's entry for each version of
         b's own foo (ParseProvides, deblistparser.cc), and none of the
         calculus's other implicit provides, which apt's cache has only
         with a second architecture configured.  An
         unprovided name has no selector (tgt, Debian.v): apt defers its
         version selection to one package var when every version satisfies
         the atom, and lists the satisfying versions otherwise. *)
      (* the cache generator keeps no Provides of a package's own name at its
         own version (ListParser::NewProvides, pkgcachegen.cc), except
         through the every-architecture path a Multi-Arch: foreign package's
         Provides take, which has no such check: luit provides luit *)
      let self_dropped (((m, _), w) as q : DMA.Pkg.t) n vt =
        String.equal m n
        && (match Hashtbl.find_opt I.idx.stanza_of q with
          | Some stz -> stz.ncls <> DMA.MAForeign
          | None -> true)
        &&
        match vt with
        | DMA.Deb.DTTop -> true
        | DMA.Deb.DTVal u -> Debian_frontend.Deb_version.compare u w = 0
      in
      let provides_count ((m, x) : string * DMA.coq_NameArch) w
          (a : DMA.Deb.Atom.t) =
        let n = fst (fst a) in
        match x with
        | DMA.QAArch b -> (
            match Hashtbl.find_opt I.idx.stanza_of ((m, b), w) with
            | None -> 0
            | Some stz ->
                let declared =
                  List.length
                    (List.filter
                       (fun (pn, vt) ->
                         String.equal pn n
                         && DMA.Deb.vtMatchb vt (snd a)
                         && not (self_dropped ((m, b), w) n vt))
                       stz.nprovs)
                in
                let implicit =
                  match snd (fst a) with
                  | (DMA.QAAny | DMA.QAExact _) when String.equal m n -> 1
                  | _ -> 0
                in
                declared + implicit)
        | _ -> 1
      in
      let targets n (v : DMA.Deb.Version.t) =
        DMA.Deb.T.DependeesSet.elements (dependencies (n, v))
        |> List.map (fun (tn, tvs) ->
            (tn, List.map (tag tn) (DMA.Deb.T.VSet.elements tvs)))
      in
      let allowed_of ~assigned n =
        match assigned n with
        | PG.Unselected -> fun _ -> true
        | PG.Decided u -> fun (pv : PVersion.t) -> PVersion.compare u pv = 0
        | PG.Entailed r -> fun pv -> PG.Ranges.contains pv r
      in
      (* the static count asks about the whole instance, where nothing is
         rejected yet: one closure, so it can be told apart *)
      let unselected _ = PG.Unselected in
      let is_bot (pv : PVersion.t) = pv.PVersion.v = DMA.Deb.Version.Bot in
      (* apt's Reject propagation (Solver::Propagate, solver3.cc): a package
         is rejected the moment a hard clause of its loses its last solution,
         or a package it conflicts with is installed, and the rejection
         cascades through the discovered closure along the watch lists.
         PubGrub learns the same only when it decides the package, so without
         this the live solution counts and the choice among alternatives
         would see alternatives apt has already crossed off.  apt assigns a
         rejection the moment it is derived and propagates it only when the
         queue reaches it, so each step of the cascade is one queue entry,
         which the shadow heap holds; and a package is two literals, whose
         order the cascade alternates: the installed package's own Conflicts
         reject the other's version var (its solutions are versions) and its
         package var follows through the SelectVersion clause, while a
         conflict declared against something installed rejects the
         declarer's package var, the reason of its clauses, and its version
         var follows through the version's own clause.  A solution reads the
         literal apt made it: the package var for an unversioned atom on a
         name nothing provides (Defer-Version-Selection), a version var
         otherwise. *)
      let vdead : (DMA.Pkg.t, unit) Hashtbl.t = Hashtbl.create 256 in
      let pdead : (string * string, unit) Hashtbl.t = Hashtbl.create 256 in
      let apt_provided_tbl = Hashtbl.create 64 in
      let apt_provided n =
        match Hashtbl.find_opt apt_provided_tbl n with
        | Some b -> b
        | None ->
            let b =
              List.exists
                (fun (q, vt) -> not (self_dropped q n vt))
                (find_list I.idx.providers_of n)
            in
            Hashtbl.add apt_provided_tbl n b;
            b
      in
      (* Defer-Version-Selection (TranslateOrGroup): an atom whose target
         has no Provides entry and every version of which satisfies it is
         one solution, the target's package var; any other atom's solutions
         are version vars *)
      let deferred (a : DMA.Deb.Atom.t) =
        match fst a with
        | n, DMA.QAArch b ->
            (not (apt_provided n))
            &&
            let vs = find_list I.idx.versions_of (n, b) in
            vs <> [] && List.for_all (sat (snd a)) vs
        | _ -> false
      in
      (* PubGrub's partial solution excludes a version the moment a standing
         decision's conflict or range does, which is when apt assigns the
         version var false; the package var lags until that rejection
         propagates, so a solution reading it stays live until then whatever
         the partial solution says of the versions *)
      let rec atom_pkgs ~assigned a =
        let pkgvar = deferred a in
        let live_at ~pkgvar ((n, x) : string * DMA.coq_NameArch) w =
          assigned == unselected
          ||
          match x with
          | DMA.QAArch b ->
              if pkgvar then not (Hashtbl.mem pdead (n, b))
              else not (Hashtbl.mem vdead ((n, b), w))
          | _ -> true
        in
        let allowed_of ~pkgvar ~assigned n =
          if pkgvar then fun _ -> true else allowed_of ~assigned n
        in
        match cands_of (DMA.Deb.Name.Selector a) with
        | [] ->
            let tn = DMA.Deb.Name.Orig (fst a) in
            let allowed = allowed_of ~pkgvar ~assigned tn in
            let vs =
              List.filter_map
                (fun (pv : PVersion.t) ->
                  match pv.PVersion.v with
                  | DMA.Deb.Version.Orig w -> Some (pv, w)
                  | _ -> None)
                (cands_of tn)
            in
            let live =
              List.filter
                (fun (pv, w) ->
                  sat (snd a) w && allowed pv && live_at ~pkgvar (fst a) w)
                vs
            in
            if live = [] then 0 else if pkgvar then 1 else List.length live
        | cs ->
            (* apt's solutions are packages, and a solution is out only when
               its package is false: the selector's own state says nothing
               about that, since deciding it to one provider leaves the
               others installable *)
            let ok ~pkgvar m w =
              let on = DMA.Deb.Name.Orig m in
              allowed_of ~pkgvar ~assigned on (tag on (DMA.Deb.Version.Orig w))
              && live_at ~pkgvar m w
            in
            let reals, provs =
              List.fold_left
                (fun (r, p) (pv : PVersion.t) ->
                  match pv.PVersion.v with
                  | DMA.Deb.Version.RefReal w ->
                      ((if ok ~pkgvar (fst a) w then r + 1 else r), p)
                  | DMA.Deb.Version.Ref (m, w) ->
                      ( r,
                        if ok ~pkgvar:false m w then p + provides_count m w a
                        else p )
                  | _ -> (r, p))
                (0, 0) cs
            in
            (* a deferred atom's real versions are one solution, the package
               var, whatever the version count *)
            (if pkgvar then min reals 1 else reals) + provs
      and atom_static a = atom_pkgs ~assigned:unselected a in
      let has_ref n =
        List.exists
          (fun (pv : PVersion.t) ->
            match pv.PVersion.v with
            | DMA.Deb.Version.Ref _ -> true
            | _ -> false)
          (cands_of n)
      in
      (* the clause's name in this encoding: its synthetic name, or for a
         one-alternative Depends what tgt (Debian.v) sends it to -- the
         alternative's selector where a provider matches it (provb, which is
         where us gives the selector a Ref candidate), and the target itself
         otherwise *)
      let clause_name opt g = function
        | [ a ] when not opt ->
            if has_ref (DMA.Deb.Name.Selector a) then DMA.Deb.Name.Selector a
            else DMA.Deb.Name.Orig (fst a)
        | _ -> g
      in
      let pkg_names (((n, _), _) as p : DMA.Pkg.t) =
        n
        ::
        (match Hashtbl.find_opt I.idx.stanza_of p with
        | Some stz -> List.map fst stz.nprovs
        | None -> [])
      in
      let orig_of (((n, b), _) : DMA.Pkg.t) =
        DMA.Deb.Name.Orig (n, DMA.QAArch b)
      in
      let installed_at ~assigned (((_, _), v) as p : DMA.Pkg.t) =
        match assigned (orig_of p) with
        | PG.Decided u -> u.PVersion.v = DMA.Deb.Version.Orig v
        | _ -> false
      in
      let pp_pkg fmt (((n, b), v) : DMA.Pkg.t) =
        Format.fprintf fmt "%s:%s=%s" n b v
      in
      (* one queue entry of the cascade: a version var or a package var
         assigned false, whose propagation waits for its turn *)
      let pp_rejection fmt = function
        | `Ver x -> Format.fprintf fmt "ver %a" pp_pkg x
        | `Pkg (n, b) -> Format.fprintf fmt "pkg %s:%s" n b
      in
      let reject_ver ~assigned out (x : DMA.Pkg.t) =
        if (not (Hashtbl.mem vdead x)) && not (installed_at ~assigned x) then (
          Hashtbl.replace vdead x ();
          out := `Ver x :: !out)
      in
      let reject_pkg ~assigned out ((n, b) as k) =
        if
          (not (Hashtbl.mem pdead k))
          && not
               (List.exists
                  (fun w -> installed_at ~assigned ((n, b), w))
                  (find_list I.idx.versions_of k))
        then (
          Hashtbl.replace pdead k ();
          out := `Pkg k :: !out)
      in
      (* what installing p assigns at once through its own Conflicts and
         Breaks: the versions its negatives exclude (the negative clause's
         solutions, rejected as its reason comes true) *)
      let conflicts ~assigned (((pname, _), v) as p : DMA.Pkg.t) =
        let out = ref [] in
        List.iter
          (fun (tn, tvs) ->
            if List.exists is_bot tvs then
              match tn with
              | DMA.Deb.Name.Orig (m, DMA.QAArch mb)
                when not (String.equal m pname) ->
                  List.iter
                    (fun (c : PVersion.t) ->
                      match c.PVersion.v with
                      | DMA.Deb.Version.Orig w
                        when not
                               (List.exists
                                  (fun t -> PVersion.compare c t = 0)
                                  tvs) ->
                          reject_ver ~assigned out ((m, mb), w)
                      | _ -> ())
                    (cands_of tn)
              | _ -> ())
          (targets (orig_of p) (DMA.Deb.Version.Orig v));
        List.rev !out
      in
      (* what p's version var assigns as it propagates: the declarers of a
         conflict it matches lose their package var, the reason of their
         negative clause.  The declarer's atom names p, or a name p provides,
         at p's architecture -- an explicit :arch elsewhere is another
         package, one apt's cache holds as an empty pseudo-package -- and its
         version formula holds of p's version, or of the version p provides
         the name at (IsSatisfied over a PrvIterator: an unversioned Provides
         never meets a versioned negative).  A conflict never reaches the
         declarer's own group (IsIgnorable). *)
      let conflicted_by ~assigned (((pname, pb), v) as p : DMA.Pkg.t) =
        let _, rev_conf = reverse_index I.idx in
        let seen = Hashtbl.create 16 in
        let out = ref [] in
        let reaches (a : DMA.Atom.t) n =
          String.equal (DMA.aname a) n
          && (match DMA.aqual a with
            | DMA.QUnq | DMA.QAny -> true
            | DMA.QNative -> String.equal AP.native pb
            | DMA.QArch c -> String.equal c pb)
          &&
          if String.equal n pname then sat (DMA.aform a) v
          else
            match Hashtbl.find_opt I.idx.stanza_of p with
            | Some stz ->
                List.exists
                  (fun (pn, vt) ->
                    String.equal pn n && DMA.Deb.vtMatchb vt (DMA.aform a))
                  stz.nprovs
            | None -> false
        in
        let names = pkg_names p in
        List.iter
          (fun n ->
            List.iter
              (fun (q : DMA.Pkg.t) ->
                let qk = fst q in
                if
                  (not (Hashtbl.mem seen qk))
                  && (not (String.equal (fst qk) pname))
                  && not (Hashtbl.mem pdead qk)
                then (
                  Hashtbl.replace seen qk ();
                  match Hashtbl.find_opt I.idx.stanza_of q with
                  | None -> ()
                  | Some stz ->
                      (* a declarer met under one of p's names is judged on
                         all of them: a conflict on the real name that
                         misses p's version says nothing of one on a name p
                         provides *)
                      if
                        List.exists
                          (fun a -> List.exists (reaches a) names)
                          stz.nconfs
                      then reject_pkg ~assigned out qk))
              (find_list rev_conf n))
          names;
        List.rev !out
      in
      (* the clauses a rejected literal is watched by, and what they assign:
         a hard clause of an undecided depender that has lost its last
         solution rejects the depender's package var, the reason of every
         clause of a single-version package, and a hard clause of an
         installed depender down to one is unit, its solution apt's next
         Enqueue.  A clause reads the literal apt made its solution, so a
         version var reaches versioned and provided atoms, a package var the
         deferred ones; a clause with no solution at all never fires, having
         nothing to watch. *)
      let cascade ~assigned ~pkgvar names out units =
        let rev_dep, _ = reverse_index I.idx in
        let seen = Hashtbl.create 16 in
        List.iter
          (fun nm ->
            List.iter
              (fun (r : DMA.Pkg.t) ->
                let rk = fst r in
                if (not (Hashtbl.mem seen rk)) && not (Hashtbl.mem pdead rk)
                then (
                  Hashtbl.replace seen rk ();
                  let inst = installed_at ~assigned r in
                  List.iter
                    (fun (opt, g, atoms) ->
                      if
                        (not opt)
                        && List.exists
                             (fun (a : DMA.Deb.Atom.t) ->
                               List.mem (fst (fst a)) names
                               && deferred a = pkgvar)
                             atoms
                        && List.exists (fun a -> atom_static a > 0) atoms
                      then
                        let live =
                          List.fold_left
                            (fun acc a -> acc + atom_pkgs ~assigned a)
                            0 atoms
                        in
                        if live = 0 then (
                          if not inst then reject_pkg ~assigned out rk)
                        else if live = 1 && inst then
                          units := clause_name opt g atoms :: !units)
                    (ordered_clauses I.idx r)))
              (find_list rev_dep nm))
          names
      in
      let propagate ~assigned r =
        let out = ref [] and units = ref [] in
        (match r with
        | `Ver (((n, b), _) as x) ->
            (* the package's SelectVersion clause: every version false *)
            if
              List.for_all
                (fun w -> Hashtbl.mem vdead ((n, b), w))
                (find_list I.idx.versions_of (n, b))
            then reject_pkg ~assigned out (n, b);
            cascade ~assigned ~pkgvar:false (pkg_names x) out units
        | `Pkg (n, b) ->
            (* each version's own clause, version -> package *)
            List.iter
              (fun w -> reject_ver ~assigned out ((n, b), w))
              (find_list I.idx.versions_of (n, b));
            cascade ~assigned ~pkgvar:true [ n ] out units);
        (List.rev !out, List.rev !units)
      in
      (* the candidates of a clause name the partial solution already
         discharges: an alternative whose target is carried, or which
         resolves through a selector one of whose providers is.  Non-empty is
         apt's ELIDED, a popped clause some solution of which is true. *)
      let free_of ~assigned n cands =
        let alt_carried (pv : PVersion.t) =
          List.exists
            (fun (tn, tvs) ->
              carried_at ~assigned tn tvs
              ||
              match tn with
              | DMA.Deb.Name.Selector a ->
                  List.exists (sel_carried ~assigned a) tvs
              | _ -> false)
            (targets n pv.PVersion.v)
        in
        match n with
        | DMA.Deb.Name.Selector a -> List.filter (sel_carried ~assigned a) cands
        | DMA.Deb.Name.Disjunct _ | DMA.Deb.Name.Soft _ ->
            List.filter alt_carried cands
        | _ -> []
      in
      (* the solutions of a clause apt folded a later one into are the
         intersection, and Solve takes the first undecided of those: the
         narrower atom, for the choice among the name's own candidates *)
      let narrowed : (DMA.Deb.Name.t, DMA.Deb.Atom.t) Hashtbl.t =
        Hashtbl.create 64
      in
      let module D = struct
        type name = DMA.Deb.Name.t
        type version = PVersion.t
        type atom = DMA.Deb.Atom.t
        type assigned = name -> PG.selection

        let pp_name = PName.pp
        let pp_atom = pp_atom

        let kind = function
          | DMA.Deb.Name.Orig _ -> Apt_heap.Package
          | DMA.Deb.Name.Disjunct _ -> Apt_heap.Hard
          | DMA.Deb.Name.Soft _ -> Apt_heap.Soft
          | DMA.Deb.Name.Selector _ -> Apt_heap.Alternative

        let clause_atoms = function
          | DMA.Deb.Name.Disjunct aset | DMA.Deb.Name.Soft aset -> Some aset
          | DMA.Deb.Name.Selector a ->
              (* a one-alternative Depends has no disjunct package: the
                 selector itself is the work item *)
              Some [ a ]
          | _ -> None

        let atom_count assigned a = atom_pkgs ~assigned a
        let atom_static = atom_static

        (* apt tests each solution's package, not the version the solution
           names; under Strict-Pinning the one is the other's only version *)
        let obsolete (a : atom) =
          let at (n, x) w =
            match x with
            | DMA.QAArch b -> (
                match Hashtbl.find_opt I.idx.stanza_of ((n, b), w) with
                | Some stz -> obsolete I.idx stz
                | None -> false)
            | _ -> false
          in
          match cands_of (DMA.Deb.Name.Selector a) with
          | [] ->
              List.exists
                (fun (pv : PVersion.t) ->
                  match pv.PVersion.v with
                  | DMA.Deb.Version.Orig w -> sat (snd a) w && at (fst a) w
                  | _ -> false)
                (cands_of (DMA.Deb.Name.Orig (fst a)))
          | cs ->
              List.exists
                (fun (pv : PVersion.t) ->
                  match pv.PVersion.v with
                  | DMA.Deb.Version.RefReal w -> at (fst a) w
                  | DMA.Deb.Version.Ref (m, w) -> at m w
                  | _ -> false)
                cs

        let decided assigned n =
          match assigned n with PG.Decided pv -> Some pv | _ -> None

        let satisfied assigned n = free_of ~assigned n (cands_of n) <> []

        type rejection = [ `Ver of DMA.Pkg.t | `Pkg of string * string ]

        let pp_rejection = pp_rejection

        let at_pkg f n (pv : PVersion.t) =
          match (n, pv.PVersion.v) with
          | DMA.Deb.Name.Orig (m, DMA.QAArch b), DMA.Deb.Version.Orig v ->
              f ((m, b), v)
          | _ -> []

        let conflicts assigned n pv = at_pkg (conflicts ~assigned) n pv
        let conflicted_by assigned n pv = at_pkg (conflicted_by ~assigned) n pv

        let propagate assigned r : rejection list * name list =
          propagate ~assigned r

        let reset () =
          Hashtbl.reset vdead;
          Hashtbl.reset pdead

        let version_equal a b = PVersion.compare a b = 0

        (* RegisterClause's merge (solver3.cc): a single-atom clause on a
           target an earlier single-atom clause of the same optionality
           already names, with a solution in common, is folded into the
           earlier one, whose solutions become the intersection -- the
           `(>= v), (<< v')` pairs of 2076 stanzas -- and a Recommends on a
           Depends' target keeps the Depends' solutions only.  Solutions are
           apt's vars, so two deferred atoms share their one package var and
           a deferred atom shares nothing with a versioned one.  The folded
           clause is not gone: Discover registers a version's dependencies
           afresh unless a clause of the package carries the same one, and
           the folded clause carries the earlier's, so the second half comes
           back on the version var with its own solutions, propagated as the
           version pops, right after the package's own wave. *)
        let conj ((n, f) : DMA.Deb.Atom.t) ((_, f') : DMA.Deb.Atom.t) :
            DMA.Deb.Atom.t =
          (n, DMA.Deb.Ver.FConj (f, f'))

        let overlap a a' =
          match (deferred a, deferred a') with
          | true, true -> true
          | false, false -> atom_static (conj a a') > 0
          | _ -> false

        let wave n (pv : PVersion.t) =
          match (n, pv.PVersion.v) with
          | DMA.Deb.Name.Orig (m, DMA.QAArch b), DMA.Deb.Version.Orig v ->
              let earlier = Hashtbl.create 8 in
              let again = ref [] in
              let out =
                List.map
                  (fun (opt, g, atoms) ->
                    let g = clause_name opt g atoms in
                    match atoms with
                    | [ a ] -> (
                        let a =
                          if not opt then a
                          else
                            match Hashtbl.find_opt earlier (false, fst a) with
                            | Some (_, ea) when overlap !ea a -> conj a !ea
                            | _ -> a
                        in
                        match Hashtbl.find_opt earlier (opt, fst a) with
                        | Some (eg, ea) when overlap !ea a ->
                            if not (DMA.Deb.Atom.eq_dec !ea a) then (
                              ea := conj !ea a;
                              Hashtbl.replace narrowed eg !ea);
                            again := (opt, Some g, fun () -> [ a ]) :: !again;
                            (opt, None, fun () -> [])
                        | _ ->
                            let r = ref a in
                            Hashtbl.replace earlier (opt, fst a) (g, r);
                            (opt, Some g, fun () -> [ !r ]))
                    | _ -> (opt, Some g, fun () -> atoms))
                  (ordered_clauses I.idx ((m, b), v))
              in
              (* a later fold has narrowed the earlier's atom in place *)
              let live l =
                List.filter_map
                  (fun (opt, g, atoms) ->
                    match g with
                    | None -> None
                    | Some _ -> Some (opt, g, atoms ()))
                  l
              in
              (live out, live (List.rev !again))
          | _ -> ([], [])

        (* apt's Assume of the alternative's solution: a version var, or the
           package var of a deferred alternative *)
        let continuation n (pv : PVersion.t) =
          match (n, pv.PVersion.v) with
          | ( (DMA.Deb.Name.Disjunct _ | DMA.Deb.Name.Soft _),
              DMA.Deb.Version.Atom a ) ->
              [
                (if has_ref (DMA.Deb.Name.Selector a) then
                   DMA.Deb.Name.Selector a
                 else DMA.Deb.Name.Orig (fst a));
              ]
          | _ -> []

        (* A clause found unit is one Enqueue for apt: the alternative left,
           and where that alternative is deferred -- unversioned, unprovided
           in apt's cache, which sees none of the calculus's implicit
           provides with one architecture configured -- the package var
           itself, processed at the clause's own queue slot.  Any other
           solution is a version var, and the package var then joins the
           queue at the back as the version pops. *)
        let forced_to n (pv : PVersion.t) =
          match (n, pv.PVersion.v) with
          | DMA.Deb.Name.Disjunct _, DMA.Deb.Version.Atom a ->
              Some
                (if has_ref (DMA.Deb.Name.Selector a) then
                   DMA.Deb.Name.Selector a
                 else DMA.Deb.Name.Orig (fst a))
          | DMA.Deb.Name.Selector a, DMA.Deb.Version.RefReal _
          | DMA.Deb.Name.Selector a, DMA.Deb.Version.Ref _ ->
              if deferred a then
                Some
                  (match pv.PVersion.v with
                  | DMA.Deb.Version.Ref (m, _) -> DMA.Deb.Name.Orig m
                  | _ -> DMA.Deb.Name.Orig (fst a))
              else None
          | _ -> None

        let same_name a b = PName.compare a b = 0

        let head assigned atoms =
          let one a =
            let h = clause_name false (DMA.Deb.Name.Disjunct atoms) [ a ] in
            match h with
            | DMA.Deb.Name.Orig ((m, DMA.QAArch b) as mn) when not (deferred a)
              -> (
                (* the newest live version, which apt's sort of one
                   package's versions puts first (CompareProviders3) *)
                let on = DMA.Deb.Name.Orig mn in
                let live =
                  List.filter
                    (fun (pv : PVersion.t) ->
                      match pv.PVersion.v with
                      | DMA.Deb.Version.Orig w ->
                          sat (snd a) w && not (Hashtbl.mem vdead ((m, b), w))
                      | _ -> false)
                    (cands_of on)
                in
                (h, match live with [] -> None | _ -> Some (on, greatest live)))
            | _ -> (h, None)
          in
          match atoms with
          | [] -> None
          | [ a ] -> Some (one a)
          | _ -> (
              match List.filter (fun a -> atom_pkgs ~assigned a > 0) atoms with
              | [ a ] -> Some (one a)
              | _ -> None)

        let negation assigned n (pv : PVersion.t) : rejection list =
          let ver ((m, x) : string * DMA.coq_NameArch) w =
            match x with DMA.QAArch b -> [ `Ver ((m, b), w) ] | _ -> []
          in
          let of_atom a =
            match head assigned [ a ] with
            | Some (DMA.Deb.Name.Orig (m, DMA.QAArch b), None) ->
                [ `Pkg (m, b) ]
            | Some (_, Some (_, (ov : PVersion.t))) -> (
                match ov.PVersion.v with
                | DMA.Deb.Version.Orig w -> ver (fst a) w
                | _ -> [])
            | _ -> []
          in
          match (n, pv.PVersion.v) with
          | DMA.Deb.Name.Orig m, DMA.Deb.Version.Orig w -> ver m w
          | DMA.Deb.Name.Selector a, DMA.Deb.Version.RefReal w ->
              if deferred a then
                match fst a with m, DMA.QAArch b -> [ `Pkg (m, b) ] | _ -> []
              else ver (fst a) w
          | DMA.Deb.Name.Selector _, DMA.Deb.Version.Ref (m, w) -> ver m w
          | ( (DMA.Deb.Name.Disjunct _ | DMA.Deb.Name.Soft _),
              DMA.Deb.Version.Atom a ) ->
              of_atom a
          | _ -> []

        (* a selector decided to a provider or real version is apt's version
           var popping, unless the atom is deferred and the var was the
           package's all along *)
        let version_of n (pv : PVersion.t) =
          match (n, pv.PVersion.v) with
          | DMA.Deb.Name.Selector a, DMA.Deb.Version.RefReal w
            when not (deferred a) ->
              let on = DMA.Deb.Name.Orig (fst a) in
              Some (on, tag on (DMA.Deb.Version.Orig w))
          | DMA.Deb.Name.Selector a, DMA.Deb.Version.Ref (m, w)
            when not (deferred a) ->
              let on = DMA.Deb.Name.Orig m in
              Some (on, tag on (DMA.Deb.Version.Orig w))
          | _ -> None
      end in
      let module Shadow = Apt_heap.Make (D) in
      let sh = Shadow.create () in
      let dependencies n (pv : PVersion.t) =
        List.map
          (fun (tn, tvs) -> (tn, PG.Ranges.of_list tvs))
          (targets n pv.PVersion.v)
      in
      (* apt never resolves a clause one of whose alternatives is already
         satisfied: it leaves the clause alone and installs nothing for it.
         PubGrub has to decide the disjunct either way, so the nearest thing
         is
         to decide it at no cost -- an alternative, or a provider of one, the
         solution already carries.  Where nothing is carried, and for every
         other name, PVersion.compare's answer stands unchanged. *)
      let choose ~assigned n cands =
        (* an alternative nothing satisfies is not among apt's solutions
           (AllTargets skips it) or is one it has rejected (Solve takes the
           first undecided), and so is a rejected provider or version of a
           selector's name: trying either would burn a backtrack and permute
           the shadow heap where apt's never moves, so rank it out whenever
           a live alternative, or the escape, remains *)
        let keep f cands =
          match List.filter f cands with [] -> cands | live -> live
        in
        let cands =
          if not apt_heap then cands
          else
            let live_pkg ((m, x) : string * DMA.coq_NameArch) w =
              match x with
              | DMA.QAArch b ->
                  (not (Hashtbl.mem pdead (m, b)))
                  && not (Hashtbl.mem vdead ((m, b), w))
              | _ -> true
            in
            keep
              (fun (pv : PVersion.t) ->
                match (n, pv.PVersion.v) with
                | _, DMA.Deb.Version.Atom a -> atom_pkgs ~assigned a > 0
                | DMA.Deb.Name.Selector a, DMA.Deb.Version.RefReal w ->
                    live_pkg (fst a) w
                | _, DMA.Deb.Version.Ref (m, w) -> live_pkg m w
                | _ -> true)
              cands
        in
        let cands =
          (* a decision apt kept across a Pop that PubGrub undid is made
             again, to the same version *)
          match Shadow.kept sh n with
          | Some v when List.exists (fun c -> PVersion.compare c v = 0) cands ->
              [ v ]
          | _ -> cands
        in
        let cands =
          match Hashtbl.find_opt narrowed n with
          | None -> cands
          | Some na ->
              keep
                (fun (pv : PVersion.t) ->
                  match pv.PVersion.v with
                  | DMA.Deb.Version.RefReal w -> sat (snd na) w
                  (* an explicit :b has no real candidate: b's own package
                     is a Ref, providing the name at its version *)
                  | DMA.Deb.Version.Ref ((m, DMA.QAArch _), w)
                    when String.equal m (fst (fst na))
                         &&
                         match snd (fst na) with
                         | DMA.QAExact _ -> true
                         | _ -> false ->
                      sat (snd na) w
                  | DMA.Deb.Version.Ref ((m, DMA.QAArch b), w) -> (
                      match Hashtbl.find_opt I.idx.stanza_of ((m, b), w) with
                      | Some stz ->
                          List.exists
                            (fun (pn, vt) ->
                              String.equal pn (fst (fst na))
                              && DMA.Deb.vtMatchb vt (snd na))
                            stz.nprovs
                      | None -> false)
                  | _ -> true)
                cands
        in
        match free_of ~assigned n cands with
        | [] -> greatest cands
        | free -> greatest free
      in
      let versions n =
        if apt_heap then cands_of n
        else List.map (tag n) (DMA.Deb.T.VSet.elements (versions n))
      in
      (* A name only conflicts have reached admits absence, its greatest
         version, and is decided last: deciding it earlier would forbid a
         dependency that later comes to require it.  apt has no work item
         for such a name, so the shadow heap never sees it. *)
      let admits_bot ~assigned tn =
        match tn with
        | DMA.Deb.Name.Orig _ -> (
            match assigned tn with
            | PG.Entailed r -> PG.Ranges.contains (tag tn DMA.Deb.Version.Bot) r
            | _ -> false)
        (* only a real name has the absent version; asking the partial
           solution about a clause name would compare its atom set *)
        | _ -> false
      in
      let required ~assigned open_names =
        List.filter (fun (tn, _) -> not (admits_bot ~assigned tn)) open_names
      in
      let defer_bot ~assigned open_names =
        match required ~assigned open_names with
        | (tn, _) :: _ -> tn
        | [] -> fst (List.hd open_names)
      in
      let heap_next ~assigned open_names =
        match required ~assigned open_names with
        | [] -> fst (List.hd open_names)
        | req -> Shadow.next sh ~assigned req
      in
      let next = Some (if apt_heap then heap_next else defer_bot) in
      (* Ranges.full here trips an upstream pubgrub edge case (initial
         Neg-term status); real versions are what we mean anyway: the query
         asks for the name, so it excludes absence. *)
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
            (List.filter accepted (versions (DMA.Deb.Name.Orig n))) )
      in
      let r =
        PG.solve ?next ~choose ~vers:versions ~deps:dependencies
          (List.map root query)
      in
      if apt_heap then Shadow.report sh;
      match r with
      | Error inc ->
          Format.printf "unsatisfiable:@.%a@." PG.explain_incompatibility inc;
          None
      | Ok sol ->
          if debug then (
            Format.printf "raw solution (%d):@." (List.length sol);
            List.iter
              (fun (n, v) ->
                Format.printf "  %a = %a@." PName.pp n PVersion.pp v)
              sol);
          let s' =
            DMA.Deb.T.PkgSet.ofList
              (List.map (fun (n, (pv : PVersion.t)) -> (n, pv.PVersion.v)) sol)
          in
          Some
            (List.map
               (fun ((n, b), v) -> (n, b, v))
               (DMA.PkgSet.elements
                  (DMA.multiarchResolution (DMA.Deb.debianResolution s'))))
  end

  let prof_oc = ref 0
  let prof_ot = ref 0.

  let timed c t f x =
    incr c;
    let t0 = Sys.time () in
    let r = f x in
    t := !t +. (Sys.time () -. t0);
    r

  let solve ?debug ?apt_heap (idx : index)
      (query : ((string * string) * accepts) list) =
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
      | DMA.Deb.Name.Soft _ -> "soft"
      | DMA.Deb.Name.Selector _ -> "sel"
    in
    let module S = Search (struct
      let idx = idx
    end) in
    let r =
      S.run_pubgrub ?debug ?apt_heap
        ~versions:(fun n' -> bucket (vname n') (vers_sparse idx) n')
        ~dependencies:(timed prof_oc prof_ot (dependees_sparse idx))
        (List.map (fun ((n, b), acc) -> ((n, DMA.QAArch b), acc)) query)
    in
    if Sys.getenv_opt "PACPROF" <> None then (
      Hashtbl.iter
        (fun name (c, t) ->
          Printf.eprintf "PACPROF versions/%s: %d calls %.2fs\n%!" name !c !t)
        buckets;
      Printf.eprintf "PACPROF dependees: %d calls %.2fs\n%!" !prof_oc !prof_ot;
      Printf.eprintf "PACPROF clauses parsed: %d of %d stanzas\n%!"
        idx.n_clauses_parsed
        (Hashtbl.length idx.stanza_of));
    r
end

(* apt's solver rejects every version but the candidate before it starts
   (APT::Solver::Strict-Pinning, on by default: FromDepCache, solver3.cc),
   so the instance it answers over holds one version per package.  The cut
   is made on the stanzas, before any table is built, so that the lookups
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
   prefix of it where the pattern ends in '*', or the pattern as a glob *)
let version_matches pat v =
  let n = String.length pat in
  let pre = n > 0 && pat.[n - 1] = '*' in
  let b = if pre then String.sub pat 0 (n - 1) else pat in
  let lb = String.length b and lv = String.length v in
  (lv = lb || (pre && lv > lb))
  && String.lowercase_ascii (String.sub v 0 lb) = String.lowercase_ascii b
  || fnmatch pat v

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
  let acc =
    match sel with
    | None -> Any
    (* nothing is installed: pac reads no dpkg status *)
    | Some ('=', "installed") -> Nothing
    (* without pins the candidate is the newest, which heads the list *)
    | Some ('=', ("candidate" | "newest")) -> first (fun _ -> true)
    | Some ('=', v) -> first (version_matches v)
    (* a release is matched against Release files, which pac does not
       read; "*" matches every file (pkgVersionMatch::FileMatch) *)
    | Some (_, "*") -> first (fun _ -> true)
    | Some _ -> Nothing
  in
  (key, acc)

(* Parsing and index construction are reported apart from solving because
   they scale differently: the archive is read whole, while the solve
   touches only the sub-instances the lookup theorems bound.  Which of the
   two
   dominates is the frontend's headline number, so it is printed rather
   than inferred. *)
let solve_files ?debug ?apt_heap ?(recommends = true) ?(strict_pinning = true)
    ~native ~paths ~query :
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
  let module M = Make (struct
    let arches = arches
    let native = native
  end) in
  let idx = M.build_index ~recommends stanzas in
  let t1 = Unix.gettimeofday () in
  match M.solve ?debug ?apt_heap idx query with
  | None -> None
  | Some pkgs -> Some (pkgs, t1 -. t0, Unix.gettimeofday () -. t1)
