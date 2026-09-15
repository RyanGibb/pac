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
     and downgrades all+same to no (arch:all content is arch-invariant).
     Its Depends and Recommends clauses are still the raw field text, and
     are mangled once, on the first slice that reads them. *)
  type nstanza = {
    npkg : DMA.Pkg.t;
    ncls : DMA.coq_MAClass;
    raw_deps : string list;
    raw_recs : string list;
    mutable nclauses : (DMA.Atom.t list list * DMA.Atom.t list list) option;
    nprovs : (string * DMA.Deb.coq_DTop) list;
    nconfs : DMA.Atom.t list;
  }

  (* ~recommends false is the --no-install-recommends reading: the Rec
     instance is empty, so every Soft gadget is empty and unreachable. *)
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
    }

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
    (* Recommends clauses are keyed separately from Depends: Soft A and
       Disjunct A are distinct names over the same atom set, and one clause
       may be a Depends of one package and a Recommends of another. *)
    rclause_of_aset : (DMA.Deb.AtomSet.t, DMA.Pkg.t * DMA.AtomSet.t) Hashtbl.t;
    rclause_of_atom : (DMA.Deb.Atom.t, DMA.Pkg.t * DMA.AtomSet.t) Hashtbl.t;
    (* Debian prefers the leftmost alternative of a clause, and a mangled
       clause is an atom *set*, so the field's left-to-right order has to be
       carried beside it.  Keyed by the mangled clause, exactly as
       clause_of_aset is, and shared between Depends and Recommends because
       Disjunct A and Soft A range over the same A. *)
    clause_order : (DMA.Deb.AtomSet.t, DMA.Deb.Atom.t array) Hashtbl.t;
    class_of : (DMA.Pkg.t, DMA.coq_MAClass) Hashtbl.t;
    (* stanzas whose clauses a slice has asked for, reported under PACPROF:
       the whole point of deferring them is that this stays small *)
    mutable n_clauses_parsed : int;
  }

  let push tbl k v =
    Hashtbl.replace tbl k
      (v :: (match Hashtbl.find_opt tbl k with Some l -> l | None -> []))

  let mangle fields =
    List.map (List.map matom_of) (DF.parse_depends_fields fields)

  (* clauses are content-keyed, so one entry per mangled clause is all a
     hasClauseb/occursAtomb slice needs *)
  let index_clauses idx by_aset by_atom (p : DMA.Pkg.t) alts_list =
    let b = snd (fst p) in
    List.iter
      (fun alts ->
        let aset = maset_of alts in
        let ma_set = DMA.reduceClause b aset in
        Hashtbl.replace by_aset ma_set (p, aset);
        let eatoms = List.map (DMA.reduceAtom b) alts in
        List.iter (fun ea -> Hashtbl.replace by_atom ea (p, aset)) eatoms;
        (* Two clauses may list the same alternatives in different orders;
           whichever is recorded first wins.  That is exactly as sound as the
           content-keying above: both packages already reduce to one gadget
           name, hence to one PubGrub decision, so there was never room for
           the two to be ordered apart.  (Checked: the disagreement is about a
           preference between alternatives all of which remain candidates, so
           nothing becomes satisfiable or unsatisfiable either way.) *)
        if not (Hashtbl.mem idx.clause_order ma_set) then
          Hashtbl.replace idx.clause_order ma_set (Array.of_list eatoms))
      alts_list

  (* the alternative's position in the clause being decided, which is what
     PVersion.compare ranks on; max_int for an atom the clause does not list,
     which cannot arise for a name minted from that clause *)
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
        clause_of_aset = Hashtbl.create 65536;
        clause_of_atom = Hashtbl.create 65536;
        rclause_of_aset = Hashtbl.create 65536;
        rclause_of_atom = Hashtbl.create 65536;
        clause_order = Hashtbl.create 65536;
        class_of = Hashtbl.create 65536;
        n_clauses_parsed = 0;
      }
    in
    List.iter
      (fun st ->
        let ns = normalize ~recommends st in
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
          ns.nconfs)
      stanzas;
    idx

  (* A Disjunct, Soft or Selector name is minted only by reducing a stanza
     that carries the clause, so the clause indices can be filled as stanzas
     are read: nothing can ask about a mangled clause, or an atom of one,
     before the owner it came from has been through here.  That is not true
     of conflicts_on or providers_of, which are preimages -- who conflicts
     with me, and who provides the name I want -- that no row of the asking
     package can reach, so Conflicts, Breaks and Provides stay eager.

     clause_order rides along for the same reason: the alternative order a
     Disjunct or Soft name is ranked by is recorded here, before reduceDeps
     has even built the name, so no lookup can outrun it. *)
  let clauses_of idx (ns : nstanza) =
    match ns.nclauses with
    | Some c -> c
    | None ->
        let c = (mangle ns.raw_deps, mangle ns.raw_recs) in
        ns.nclauses <- Some c;
        idx.n_clauses_parsed <- idx.n_clauses_parsed + 1;
        index_clauses idx idx.clause_of_aset idx.clause_of_atom ns.npkg (fst c);
        index_clauses idx idx.rclause_of_aset idx.rclause_of_atom ns.npkg
          (snd c);
        c

  let deps_of idx ns = fst (clauses_of idx ns)
  let recs_of idx ns = snd (clauses_of idx ns)

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
        DMA.Deps.ofList
          (List.map (fun alts -> (p, maset_of alts)) (deps_of idx ns))

  let ma_recs_of_pkg idx p =
    match Hashtbl.find_opt idx.stanza_of p with
    | None -> DMA.Deps.empty
    | Some ns ->
        DMA.Deps.ofList
          (List.map (fun alts -> (p, maset_of alts)) (recs_of idx ns))

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
    | Some ns -> List.concat_map (List.map DMA.aname) (deps_of idx ns)

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

  (* the same slices on the Recommends side, through reduceRec *)
  let rec_clause_by_aset idx aset =
    match Hashtbl.find_opt idx.rclause_of_aset aset with
    | None -> DMA.Deb.Deps.empty
    | Some (p, mal) -> DMA.reduceRec (DMA.Deps.add (p, mal) DMA.Deps.empty)

  let rec_clause_by_atom idx a =
    match Hashtbl.find_opt idx.rclause_of_atom a with
    | None -> DMA.Deb.Deps.empty
    | Some (p, mal) -> DMA.reduceRec (DMA.Deps.add (p, mal) DMA.Deps.empty)

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
          DMA.Deb.Deps.empty DMA.Deb.Deps.empty DMA.Deb.Prov.empty
          DMA.Deb.Conf.empty n'
    | DMA.Deb.Name.Orig _ ->
        (* embedPkg mints only QAArch names: no reals at :any/group names *)
        DMA.Deb.versions DMA.Deb.Ver.C.PkgSet.empty DMA.Deb.Deps.empty
          DMA.Deb.Deps.empty DMA.Deb.Prov.empty DMA.Deb.Conf.empty n'
    | DMA.Deb.Name.Disjunct aset ->
        (* Lookup.versions_lookupDisjunct *)
        DMA.Deb.versions DMA.Deb.Ver.C.PkgSet.empty (clause_by_aset idx aset)
          DMA.Deb.Deps.empty DMA.Deb.Prov.empty DMA.Deb.Conf.empty n'
    | DMA.Deb.Name.Soft aset ->
        (* Lookup.versions_lookupSoft *)
        DMA.Deb.versions DMA.Deb.Ver.C.PkgSet.empty DMA.Deb.Deps.empty
          (rec_clause_by_aset idx aset)
          DMA.Deb.Prov.empty DMA.Deb.Conf.empty n'
    | DMA.Deb.Name.Selector a ->
        (* Lookup.versions_lookupSelectorAgreeMA: both slices at once is
           sound because the selector reads them only through the occurrence
           test, which both slices together answer as the whole pair does.
           Lookup.versions_lookupSelectorMA and
           Lookup.versions_lookupSelectorRecMA are its one-sided cases: a
           selector is minted from allClauses, so an atom reached only
           through a Recommends needs its recommends clause here too. *)
        let r, pi = sel_slices idx (fst a) in
        DMA.Deb.versions r (clause_by_atom idx a) (rec_clause_by_atom idx a) pi
          DMA.Deb.Conf.empty n'
    | DMA.Deb.Name.Guard (p, _, _) ->
        (* Lookup.versions_lookupGuard *)
        DMA.Deb.versions DMA.Deb.Ver.C.PkgSet.empty DMA.Deb.Deps.empty
          DMA.Deb.Deps.empty DMA.Deb.Prov.empty (guard_conf idx p) n'

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
    | DMA.Deb.Name.Disjunct aset, DMA.Deb.Version.Atom a ->
        (* Lookup.dependees_lookupDisjunct *)
        let r, pi = sel_slices idx (fst a) in
        DMA.Deb.dependees r (clause_by_aset idx aset) DMA.Deb.Deps.empty pi
          DMA.Deb.Conf.empty s
    | DMA.Deb.Name.Soft aset, DMA.Deb.Version.Atom a ->
        (* Lookup.dependees_lookupSoft: an alternative of a recommends clause
           reaches its targets exactly as one of a Depends clause does.  The
           escape (Soft _, Zero) has no case: it falls to the empty catch-all
           below, which is what discharges the clause for free. *)
        let r, pi = sel_slices idx (fst a) in
        DMA.Deb.dependees r DMA.Deb.Deps.empty (rec_clause_by_aset idx aset) pi
          DMA.Deb.Conf.empty s
    | ( DMA.Deb.Name.Selector a,
        (DMA.Deb.Version.Ref (_, _) | DMA.Deb.Version.RefReal _) ) ->
        (* Lookup.dependees_lookupSelectorAgreeMA, over allClauses as in
           vers_sparse; Lookup.dependees_lookupSelectorMA and
           Lookup.dependees_lookupSelectorRecMA are its one-sided cases, the
           latter for an atom reached only through a Recommends *)
        let r, pi = sel_slices idx (fst a) in
        DMA.Deb.dependees r (clause_by_atom idx a) (rec_clause_by_atom idx a) pi
          DMA.Deb.Conf.empty s
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

  module PVersion = struct
    (* pos is the candidate's position in the clause whose name is being
       decided -- supplied by tag, where that name is known -- and is a
       constant for every candidate that is not an alternative of one. *)
    type t = { pos : int; v : DMA.Deb.Version.t }

    (* PubGrub decides the V.compare-maximum candidate, so preference lives
       here: dpkg-newest for real versions, leftmost alternative by clause
       position, a real package above any alias claiming its name, native-arch
       referents first within each, encoded order otherwise.  The calculus
       only makes the real/provided split legible -- RefReal carries no name,
       so it is the one candidate that cannot be an alias -- and says nothing
       about which to try first.

       The escape is likewise a preference and not a constraint: the calculus
       tags it above Version.Atom, but we want the recommends gadget to try
       every real alternative before giving up on the clause, so it is ranked
       below them here.  Only candidates of one name are ever compared
       (PubGrub ranges are per name), and Version.Zero shares a name with
       Version.Atom in the Soft gadget and with Version.One in a guard and
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
      | DMA.Deb.Version.Ref ((_, x), w), DMA.Deb.Version.Ref ((_, x'), w') ->
          let c = Stdlib.compare (is_native x) (is_native x') in
          if c <> 0 then c
          else
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
  let tag idx (n' : DMA.Deb.Name.t) (v : DMA.Deb.Version.t) : PVersion.t =
    match (n', v) with
    | ( (DMA.Deb.Name.Disjunct aset | DMA.Deb.Name.Soft aset),
        DMA.Deb.Version.Atom a ) ->
        { PVersion.pos = atom_pos idx aset a; v }
    | _ -> { PVersion.pos = 0; v }

  module PG = Pubgrub.Make (PName) (PVersion)

  let run_pubgrub ?(debug = false) ~tag ~versions ~dependencies goal =
    let dependencies n (pv : PVersion.t) =
      DMA.Deb.T.DependeesSet.elements (dependencies (n, pv.PVersion.v))
      |> List.map (fun (tn, tvs) ->
          ( tn,
            PG.Ranges.of_list (List.map (tag tn) (DMA.Deb.T.VSet.elements tvs))
          ))
    in
    let versions n = List.map (tag n) (DMA.Deb.T.VSet.elements (versions n)) in
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
        let s' =
          DMA.Deb.T.PkgSet.ofList
            (List.map (fun (n, (pv : PVersion.t)) -> (n, pv.PVersion.v)) sol)
        in
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
      | DMA.Deb.Name.Soft _ -> "soft"
      | DMA.Deb.Name.Selector _ -> "sel"
      | DMA.Deb.Name.Guard _ -> "guard"
    in
    let r =
      run_pubgrub ?debug ~tag:(tag idx)
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
   touches only the slices the lookup theorems bound.  Which of the two
   dominates is the frontend's headline number, so it is printed rather
   than inferred. *)
let solve_files ?debug ?(recommends = true) ~native ~paths ~goal :
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
  match M.solve ?debug idx goal_name goal_arch with
  | None -> None
  | Some pkgs -> Some (pkgs, t1 -. t0, Unix.gettimeofday () -. t1)
