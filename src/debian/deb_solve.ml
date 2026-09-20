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
      ness = st.essential;
      nimp = st.important;
      nprio = st.priority;
    }

  (* Untrusted whole-archive index; faithfulness to the parsed instance is
     this module's only trusted-computing-base beyond the parser itself. *)
  type index = {
    versions_of : (string * string, string list) Hashtbl.t;
    stanza_of : (DMA.Pkg.t, nstanza) Hashtbl.t;
    group_of : (string, (string * string) list) Hashtbl.t;
    providers_of : (string, (DMA.Pkg.t * DMA.Deb.coq_DTop) list) Hashtbl.t;
    conflicts_on : (string, (DMA.Pkg.t * DMA.Atom.t) list) Hashtbl.t;
    (* Debian prefers the leftmost alternative of a clause, and a mangled
       clause is an atom *set*, so the field's left-to-right order has to be
       carried beside it.  Keyed by the mangled clause, and shared between
       Depends and Recommends because Disjunct A and Soft A range over the
       same A. *)
    clause_order : (DMA.Deb.AtomSet.t, DMA.Deb.Atom.t array) Hashtbl.t;
    class_of : (DMA.Pkg.t, DMA.coq_MAClass) Hashtbl.t;
    (* stanzas whose clauses a sub-instance has asked for, reported under
       PACPROF:
       the whole point of deferring them is that this stays small *)
    mutable n_clauses_parsed : int;
  }

  let push tbl k v =
    Hashtbl.replace tbl k
      (v :: (match Hashtbl.find_opt tbl k with Some l -> l | None -> []))

  let mangle fields =
    List.map (List.map matom_of) (DF.parse_depends_fields fields)

  let index_clauses idx (p : DMA.Pkg.t) alts_list =
    let b = snd (fst p) in
    List.iter
      (fun alts ->
        let ma_set = DMA.reduceClause b (maset_of alts) in
        (* Two clauses may list the same alternatives in different orders;
           whichever is recorded first wins.  Both packages already reduce to
           one synthetic name, hence to one PubGrub decision, so there was
           never
           room for the two to be ordered apart.  The order is a preference
           and nothing more, but not because every alternative is a live
           candidate -- a good few of the clause sets written both ways
           round list an
           alternative no version satisfies, such as fuse (<< 3) against
           fuse3, or makedev against udev.  Recording such an order first puts
           a dead alternative at the head and costs a backtrack; it cannot
           change the answer, because an alternative nothing satisfies is one
           PubGrub can never decide the disjunct to. *)
        if not (Hashtbl.mem idx.clause_order ma_set) then
          Hashtbl.replace idx.clause_order ma_set
            (Array.of_list (List.map (DMA.reduceAtom b) alts)))
      alts_list

  (* the alternative's position in the clause being decided, which is what
     PVersion.compare ranks on; max_int for an atom the clause does not list,
     which cannot arise for a name introduced from that clause *)
  let atom_pos idx aset a =
    match Hashtbl.find_opt idx.clause_order aset with
    | None -> max_int
    | Some alts ->
        let n = Array.length alts in
        let rec go i =
          if i >= n then max_int
          else if DMA.Deb.Atom.eq_dec alts.(i) a then i
          else go (i + 1)
        in
        go 0

  let build_index ?(recommends = true) (stanzas : DF.stanza list) : index =
    let idx =
      {
        versions_of = Hashtbl.create 65536;
        stanza_of = Hashtbl.create 65536;
        group_of = Hashtbl.create 65536;
        providers_of = Hashtbl.create 4096;
        conflicts_on = Hashtbl.create 4096;
        clause_order = Hashtbl.create 65536;
        class_of = Hashtbl.create 65536;
        n_clauses_parsed = 0;
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
          stz.nprovs;
        List.iter
          (fun ma -> push idx.conflicts_on (DMA.aname ma) (stz.npkg, ma))
          stz.nconfs)
      stanzas;
    idx

  (* A Disjunct, Soft or Selector name is introduced only by reducing a
     stanza
     that carries the clause, so clause_order can be filled as stanzas are
     read: nothing can ask about a mangled clause, or an atom of one, before
     the owner it came from has been through here.  That is not true of
     conflicts_on or providers_of, which are preimages -- who conflicts with
     me, and who provides the name I want -- that no clause of the asking
     package can reach, so Conflicts, Breaks and Provides stay eager. *)
  let clauses_of idx (stz : nstanza) =
    match stz.nclauses with
    | Some c -> c
    | None ->
        let c = (mangle stz.raw_deps, mangle stz.raw_recs) in
        stz.nclauses <- Some c;
        idx.n_clauses_parsed <- idx.n_clauses_parsed + 1;
        index_clauses idx stz.npkg (fst c);
        index_clauses idx stz.npkg (snd c);
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
    match Hashtbl.find_opt idx.stanza_of p with
    | None -> []
    | Some stz ->
        let b = snd (fst p) in
        let mk opt synth alts =
          let ma = DMA.reduceClause b (maset_of alts) in
          let eatoms =
            List.sort_uniq Stdlib.compare (List.map (DMA.reduceAtom b) alts)
          in
          (opt, synth ma, eatoms)
        in
        List.map
          (fun alts -> mk false (fun s -> DMA.Deb.Name.Disjunct s) alts)
          (deps_of idx stz)
        @ List.map
            (fun alts -> mk true (fun s -> DMA.Deb.Name.Soft s) alts)
            (recs_of idx stz)

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
        DMA.Deps.ofList
          (List.map (fun alts -> (p, maset_of alts)) (deps_of idx stz))

  let ma_recs_of_pkg idx p =
    match Hashtbl.find_opt idx.stanza_of p with
    | None -> DMA.Deps.empty
    | Some stz ->
        DMA.Deps.ofList
          (List.map (fun alts -> (p, maset_of alts)) (recs_of idx stz))

  let ma_conf_of_pkg idx p =
    match Hashtbl.find_opt idx.stanza_of p with
    | None -> DMA.Conf.empty
    | Some stz -> DMA.Conf.ofList (List.map (fun ma -> (p, ma)) stz.nconfs)

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
    | Some stz -> List.concat_map (List.map DMA.aname) (deps_of idx stz)

  let prov_names_of idx p =
    match Hashtbl.find_opt idx.stanza_of p with
    | None -> []
    | Some stz -> List.map fst stz.nprovs

  (* R/Pi preimages for a mangled name (m, x): whichever x is, every
     provider of (m, x) is either a group member of m (reals, implicit group
     / foreign / :any provides) or a declared provider of m. *)
  let sel_preimages idx (mn : string * DMA.coq_NameArch) =
    let m = fst mn in
    let r_ma = ma_group_of_names idx [ m ] in
    let pi_decl = ma_prov_of_names idx [ m ] in
    let cls =
      classes_of idx
        (DMA.PkgSet.elements r_ma @ List.map fst (DMA.Prov.elements pi_decl))
    in
    (DMA.reduceReal r_ma, DMA.reduceProv r_ma pi_decl cls)

  let vers_sparse idx (n' : DMA.Deb.Name.t) =
    match n' with
    | DMA.Deb.Name.Orig (n, DMA.QAArch b) ->
        (* Lookup.versions_lookupOrig *)
        DMA.Deb.versions
          (DMA.reduceReal (ma_real_at idx (n, b)))
          DMA.Deb.Deps.empty DMA.Deb.Deps.empty DMA.Deb.Prov.empty
          DMA.Deb.Conf.empty n'
    | DMA.Deb.Name.Orig _ ->
        (* embedPkg introduces only QAArch names: no reals at :any/group
           names *)
        DMA.Deb.versions DMA.Deb.Ver.C.PkgSet.empty DMA.Deb.Deps.empty
          DMA.Deb.Deps.empty DMA.Deb.Prov.empty DMA.Deb.Conf.empty n'
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
    | DMA.Deb.Name.Guard (_, _, _) ->
        (* Lookup.versions_lookupGuard *)
        DMA.Deb.zeroOne

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
          (DMA.reduceRec (ma_recs_of_pkg idx p))
          (DMA.reduceProv r_pi pi_decl pi_cls)
          (DMA.reduceConf g_r g_conf g_cls)
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
      | DMA.Deb.Name.Soft _ -> Format.fprintf fmt "<rec>"
      | DMA.Deb.Name.Selector a -> Format.fprintf fmt "<sel %a>" pp_atom a
      | DMA.Deb.Name.Guard ((m, v), a, _) ->
          Format.fprintf fmt "<guard %a=%s vs %a>" pp_mname m v pp_atom a
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
         Version.Atom in the soft disjunct and with Version.One in a guard
         and
         nowhere else, so the two escape cases cannot disturb any other pair. *)
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
        | DMA.Deb.Version.One -> Format.fprintf fmt "1"
    end

    (* The clause position is known only where the name is: a Disjunct or Soft
       name carries the clause its candidates are alternatives of, and no other
       name has Version.Atom candidates at all. *)
    let tag (n' : DMA.Deb.Name.t) (v : DMA.Deb.Version.t) : PVersion.t =
      match (n', v) with
      | ( (DMA.Deb.Name.Disjunct aset | DMA.Deb.Name.Soft aset),
          DMA.Deb.Version.Atom a ) ->
          { PVersion.pos = atom_pos I.idx aset a; v }
      | _ -> { PVersion.pos = 0; v }

    module PG = Pubgrub.Make (PName) (PVersion)

    let greatest = function
      | [] -> invalid_arg "greatest"
      | c :: cs ->
          List.fold_left
            (fun a b -> if PVersion.compare b a > 0 then b else a)
            c cs

    (* Does the partial solution already carry [tn] at one of [tvs]? *)
    let carried_at ~assigned tn tvs =
      match assigned tn with
      | PG.Unselected -> false
      | PG.Decided u -> List.exists (fun v -> PVersion.compare u v = 0) tvs
      | PG.Entailed r -> List.exists (fun v -> PG.Ranges.contains v r) tvs

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
        goal =
      let cands_tbl = Hashtbl.create 4096 in
      let cands_of n =
        match Hashtbl.find_opt cands_tbl n with
        | Some l -> l
        | None ->
            let l = List.map (tag n) (DMA.Deb.T.VSet.elements (versions n)) in
            Hashtbl.add cands_tbl n l;
            l
      in
      let reals = Hashtbl.create 4096 in
      let has_real n =
        match Hashtbl.find_opt reals n with
        | Some b -> b
        | None ->
            let b =
              List.exists
                (fun (pv : PVersion.t) ->
                  match pv.PVersion.v with
                  | DMA.Deb.Version.RefReal _ -> true
                  | _ -> false)
                (cands_of n)
            in
            Hashtbl.add reals n b;
            b
      in
      (* A clause every alternative of which is a provider is a role to be
         discharged rather than a choice to be made, so it goes last of all,
         behind the Recommends that are what usually discharge it: a
         selector candidate is RefReal where the selector's own name is
         satisfiable by a real package, and Ref where only a provider can. *)
      let group n =
        match n with
        | DMA.Deb.Name.Guard _ -> 0
        | DMA.Deb.Name.Disjunct _ -> 1
        | DMA.Deb.Name.Selector _ -> if has_real n then 1 else 4
        | DMA.Deb.Name.Orig _ -> 2
        | DMA.Deb.Name.Soft _ -> 3
      in
      (* apt's solution counts: an alternative contributes its target
         packages -- the target itself and its providers.  A provided name
         resolves through its selector; an unprovided one has no selector
         (tgt, Debian.v) and is the target package alone.  Distinct name
         strings stand in for packages, so a group alias or a second version
         of one package counts once, as it does for apt, where pins have
         already rejected non-candidate versions and Defer-Version-Selection
         (the default) collapses an unprovided name to one package var. *)
      let atom_pkgs ~assigned a =
        let allowed_of n =
          match assigned n with
          | PG.Unselected -> fun _ -> true
          | PG.Decided u -> fun pv -> PVersion.compare u pv = 0
          | PG.Entailed r -> fun pv -> PG.Ranges.contains pv r
        in
        match cands_of (DMA.Deb.Name.Selector a) with
        | [] ->
            let tn = DMA.Deb.Name.Orig (fst a) in
            let allowed = allowed_of tn in
            if
              List.exists
                (fun (pv : PVersion.t) ->
                  allowed pv
                  &&
                  match pv.PVersion.v with
                  | DMA.Deb.Version.Orig w -> sat (snd a) w
                  | _ -> false)
                (cands_of tn)
            then 1
            else 0
        | cs ->
            let allowed = allowed_of (DMA.Deb.Name.Selector a) in
            let ns = ref [] in
            let add n =
              if not (List.exists (String.equal n) !ns) then ns := n :: !ns
            in
            List.iter
              (fun (pv : PVersion.t) ->
                if allowed pv then
                  match pv.PVersion.v with
                  | DMA.Deb.Version.RefReal _ -> add (fst (fst a))
                  | DMA.Deb.Version.Ref (m, _) -> add (fst m)
                  | _ -> ())
              cs;
            List.length !ns
      in
      let atom_static a = atom_pkgs ~assigned:(fun _ -> PG.Unselected) a in
      let module D = struct
        type name = DMA.Deb.Name.t
        type version = PVersion.t
        type atom = DMA.Deb.Atom.t
        type assigned = name -> PG.selection

        let pp_name = PName.pp
        let pp_atom = pp_atom

        let kind = function
          | DMA.Deb.Name.Guard _ -> Apt_heap.Forced
          | DMA.Deb.Name.Orig _ -> Apt_heap.Package
          | DMA.Deb.Name.Disjunct _ -> Apt_heap.Hard
          | DMA.Deb.Name.Soft _ -> Apt_heap.Soft
          | DMA.Deb.Name.Selector _ -> Apt_heap.Alternative

        let clause_atoms = function
          | DMA.Deb.Name.Disjunct aset | DMA.Deb.Name.Soft aset ->
              Option.map Array.to_list
                (Hashtbl.find_opt I.idx.clause_order aset)
          | DMA.Deb.Name.Selector a ->
              (* a one-alternative Depends has no disjunct package: the
                 selector itself is the work item *)
              Some [ a ]
          | _ -> None

        let atom_count assigned a = atom_pkgs ~assigned a
        let atom_static = atom_static

        let decided assigned n =
          match assigned n with PG.Decided pv -> Some pv | _ -> None

        let version_equal a b = PVersion.compare a b = 0

        let wave n (pv : PVersion.t) =
          match (n, pv.PVersion.v) with
          | DMA.Deb.Name.Orig (m, DMA.QAArch b), DMA.Deb.Version.Orig v ->
              List.map
                (fun (opt, g, atoms) ->
                  (* the item's name in this encoding: the clause's synthetic
                     name, or
                     for a one-alternative Depends the alternative's selector
                     -- and no item at all where the selector does not exist,
                     because the whole chain is then forced (apt's Enqueue) *)
                  let g =
                    match (opt, atoms) with
                    | false, [ a ] ->
                        if cands_of (DMA.Deb.Name.Selector a) <> [] then
                          Some (DMA.Deb.Name.Selector a)
                        else None
                    | _ -> Some g
                  in
                  (opt, g, atoms))
                (ordered_clauses I.idx ((m, b), v))
          | _ -> []

        let continuation n (pv : PVersion.t) =
          match (n, pv.PVersion.v) with
          | ( (DMA.Deb.Name.Disjunct _ | DMA.Deb.Name.Soft _),
              DMA.Deb.Version.Atom a ) ->
              Some (DMA.Deb.Name.Selector a)
          | _ -> None

        let fallback_key n = (group n, List.length (cands_of n))
      end in
      let module Shadow = Apt_heap.Make (D) in
      let sh = Shadow.create () in
      let discover n = if apt_heap then Shadow.discover sh n in
      let targets n (v : DMA.Deb.Version.t) =
        DMA.Deb.T.DependeesSet.elements (dependencies (n, v))
        |> List.map (fun (tn, tvs) ->
            discover tn;
            (tn, List.map (tag tn) (DMA.Deb.T.VSet.elements tvs)))
      in
      let dependencies n (pv : PVersion.t) =
        List.map
          (fun (tn, tvs) -> (tn, PG.Ranges.of_list tvs))
          (targets n pv.PVersion.v)
      in
      (* Stamp a package's clause targets in field order, clause by clause
         and alternative by alternative: the tier-0 drain follows this
         clock, standing in for apt's FIFO propagation queue, whose enqueues
         are in field order.  Called from [choose] the moment the package's
         version is picked, which beats the solver's set-ordered dependee
         walk to the first sighting. *)
      let stamp_pkg p =
        List.iter
          (fun (_, g, atoms) ->
            discover g;
            List.iter
              (fun a ->
                discover (DMA.Deb.Name.Selector a);
                discover (DMA.Deb.Name.Orig (fst a)))
              atoms)
          (ordered_clauses I.idx p)
      in
      (* apt never resolves a clause one of whose alternatives is already
         satisfied: it leaves the clause alone and installs nothing for it.
         PubGrub has to decide the disjunct either way, so the nearest thing
         is
         to decide it at no cost -- an alternative, or a provider of one, the
         solution already carries.  Where nothing is carried, and for every
         other name, PVersion.compare's answer stands unchanged. *)
      let choose ~assigned n cands =
        (if apt_heap then
           match n with
           | DMA.Deb.Name.Orig (m, DMA.QAArch b) -> (
               match (greatest cands).PVersion.v with
               | DMA.Deb.Version.Orig v -> stamp_pkg ((m, b), v)
               | _ -> ())
           | _ -> ());
        (* an alternative nothing satisfies never enters apt's solutions at
           all (AllTargets skips it), so trying it would burn a backtrack and
           permute the shadow heap where apt's never moves: rank it out
           whenever a live alternative remains *)
        let cands =
          if not apt_heap then cands
          else
            match
              List.filter
                (fun (pv : PVersion.t) ->
                  match pv.PVersion.v with
                  | DMA.Deb.Version.Atom a -> atom_static a > 0
                  | _ -> true)
                cands
            with
            | [] -> cands
            | live -> live
        in
        (* an alternative is discharged if its target is already carried, or
           if it resolves through a selector one of whose providers is *)
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
        let free =
          match n with
          | DMA.Deb.Name.Selector a -> List.filter (sel_carried ~assigned a) cands
          | DMA.Deb.Name.Disjunct _ | DMA.Deb.Name.Soft _ ->
              List.filter alt_carried cands
          | _ -> []
        in
        match free with [] -> greatest cands | free -> greatest free
      in
      let versions n =
        if apt_heap then cands_of n
        else List.map (tag n) (DMA.Deb.T.VSet.elements (versions n))
      in
      let next = if apt_heap then Some (Shadow.next sh) else None in
      (* Ranges.full here trips an upstream pubgrub edge case (initial
         Neg-term status); the goal's available versions are what we mean
         anyway. *)
      let goal_range = PG.Ranges.of_list (versions (DMA.Deb.Name.Orig goal)) in
      let r =
        PG.solve ?next ~choose ~vers:versions ~deps:dependencies
          [ (DMA.Deb.Name.Orig goal, goal_range) ]
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

  let solve ?debug ?apt_heap (idx : index) (goal_name : string)
      (goal_arch : string) =
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
      | DMA.Deb.Name.Guard _ -> "guard"
    in
    let module S = Search (struct
      let idx = idx
    end) in
    let r =
      S.run_pubgrub ?debug ?apt_heap
        ~versions:(fun n' -> bucket (vname n') (vers_sparse idx) n')
        ~dependencies:(timed prof_oc prof_ot (dependees_sparse idx))
        (goal_name, DMA.QAArch goal_arch)
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

(* Parsing and index construction are reported apart from solving because
   they scale differently: the archive is read whole, while the solve
   touches only the sub-instances the lookup theorems bound.  Which of the
   two
   dominates is the frontend's headline number, so it is printed rather
   than inferred. *)
let solve_files ?debug ?apt_heap ?(recommends = true) ~native ~paths ~goal :
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
  let idx = M.build_index ~recommends stanzas in
  let t1 = Unix.gettimeofday () in
  match M.solve ?debug ?apt_heap idx goal_name goal_arch with
  | None -> None
  | Some pkgs -> Some (pkgs, t1 -. t0, Unix.gettimeofday () -. t1)
