module E = Pac
module DF = Deb_packages

module DebVersionOT = Pac_common.Ot.Make (struct
  type t = string

  let compare = Version.Debian.compare
end)

module type ARCH = sig
  val arches : string list
  val native : string
end

module Make (AP : ARCH) = struct
  module APx = struct
    module A = struct
      include Pac_common.Ot.Str

      let enum = AP.arches
    end

    let native = AP.native
  end

  module DMA = E.DebianMA (Pac_common.Ot.Str) (DebVersionOT) (APx)

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
     are parsed once, on the first sub-instance that reads them. *)
  type nstanza = {
    npkg : DMA.Pkg.t;
    ncls : DMA.coq_MAClass;
    raw_deps : string list;
    raw_recs : string list;
    mutable nclauses : (DMA.Atom.t list list * DMA.Atom.t list list) option;
    nprovs : (string * DMA.Deb.coq_DTop) list;
    nconfs : DMA.Atom.t list;
    (* apt ranks the providers claiming a name by these *)
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
    let _, arch = Apt_args.stanza_key ~native:AP.native st in
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

  type tables = {
    versions_table : (string * string, string list) Hashtbl.t;
    stanza_table : (DMA.Pkg.t, nstanza) Hashtbl.t;
    group_table : (string, (string * string) list) Hashtbl.t;
    providers_table : (string, (DMA.Pkg.t * DMA.Deb.coq_DTop) list) Hashtbl.t;
    (* stanzas whose clauses a sub-instance has asked for, reported under
       PACPROF: the whole point of deferring them is that this stays small *)
    mutable n_clauses_parsed : int;
    (* who names a package in a Depends or Pre-Depends, and who in a
       Conflicts or Breaks, by the bare name as written: the watch lists
       apt's Reject propagation walks, built from the field text alone, so
       no clause is parsed for them; only the tool order asks *)
    rev_dep_table : (string, DMA.Pkg.t list) Hashtbl.t Lazy.t;
    rev_conf_table : (string, DMA.Pkg.t list) Hashtbl.t Lazy.t;
    (* the binaries each source name builds, for apt's obsolescence test,
       likewise asked for by the tool order alone *)
    source_table : (string, nstanza list) Hashtbl.t Lazy.t;
    (* selector preimages by name, and a package's clauses in field order,
       both asked for again by every depender and by the rejection cascade *)
    sel_cache :
      (string * DMA.coq_NameArch, DMA.Deb.PkgSet.t * DMA.Deb.Prov.t) Hashtbl.t;
    oc_cache :
      (DMA.Pkg.t, (bool * DMA.Deb.Name.t * DMA.Deb.Atom.t list) list) Hashtbl.t;
  }

  let push = Pac_common.Tbl.push
  let find_list = Pac_common.Tbl.find_list
  let stanza tables p = Hashtbl.find_opt tables.stanza_table p

  let parse_relations fields =
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
     token before any version or architecture qualifier, in one pass.  A
     folded field's continuation lines are joined with "\n", so a name can
     follow one. *)
  let field_names fields =
    let blank c = c = ' ' || c = '\t' || c = '\n' in
    List.concat_map
      (fun f ->
        let n = String.length f in
        let acc = ref [] in
        let i = ref 0 in
        while !i < n do
          while !i < n && blank f.[!i] do
            incr i
          done;
          let s = !i in
          while
            !i < n
            &&
            match f.[!i] with
            | ' ' | '\t' | '\n' | '(' | ':' | ',' | '|' -> false
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

  let rev_dep stanza_table =
    let d = Hashtbl.create 65536 in
    Hashtbl.iter
      (fun p (stz : nstanza) ->
        List.iter (fun n -> push d n p) (field_names stz.raw_deps))
      stanza_table;
    d

  let rev_conf stanza_table =
    let c = Hashtbl.create 4096 in
    Hashtbl.iter
      (fun p (stz : nstanza) ->
        List.iter (fun a -> push c (DMA.aname a) p) stz.nconfs)
      stanza_table;
    c

  let by_source stanza_table =
    let t = Hashtbl.create 65536 in
    Hashtbl.iter (fun _ (s : nstanza) -> push t (fst s.nsrc) s) stanza_table;
    t

  (* Of two stanzas at one version apt keeps the first read, Provides and
     all.  An arch:all stanza is a version of its own to apt (Version::All),
     which the package's one version here cannot be, so that pair is still
     read as one version with both stanzas' Provides, in the stanza as in
     providers_table; its Depends, Recommends and Conflicts are the later
     stanza's. *)
  let build_tables ~recommends (index : DF.stanza list) : tables =
    let versions_table = Hashtbl.create 65536
    and stanza_table = Hashtbl.create 65536
    and group_table = Hashtbl.create 65536
    and providers_table = Hashtbl.create 4096 in
    List.iter
      (fun st ->
        let stz = normalize ~recommends st in
        let (n, b), v = stz.npkg in
        let add stored =
          Hashtbl.replace stanza_table stz.npkg stored;
          List.iter
            (fun (m, vt) -> push providers_table m (stz.npkg, vt))
            stz.nprovs
        in
        match Hashtbl.find_opt stanza_table stz.npkg with
        | None ->
            push versions_table (n, b) v;
            push group_table n (b, v);
            add stz
        | Some old when old.nall <> stz.nall ->
            add { stz with nprovs = old.nprovs @ stz.nprovs }
        | Some _ -> ())
      index;
    {
      versions_table;
      stanza_table;
      group_table;
      providers_table;
      n_clauses_parsed = 0;
      rev_dep_table = lazy (rev_dep stanza_table);
      rev_conf_table = lazy (rev_conf stanza_table);
      source_table = lazy (by_source stanza_table);
      sel_cache = Hashtbl.create 4096;
      oc_cache = Hashtbl.create 4096;
    }

  (* apt's ObsoletedByNewerSourceVersion (solver3.cc:863-888): another
     binary of the same source, on the same architecture and equally arch:all
     or not, comes from a newer source version.  apt also asks that binary's
     pin priority to be no lower, which with no pins every version meets. *)
  let obsolete tables (stz : nstanza) =
    let (_, b), _ = stz.npkg in
    List.exists
      (fun (s : nstanza) ->
        let (_, b'), _ = s.npkg in
        fst s.npkg <> fst stz.npkg
        && String.equal b b' && s.nall = stz.nall
        && Version.Debian.compare (snd s.nsrc) (snd stz.nsrc) > 0)
      (find_list (Lazy.force tables.source_table) (fst stz.nsrc))

  (* Only a lookup at a stanza's own package reads its clauses, so they can
     wait until one does.  providers_table cannot: it is a preimage -- who
     provides the name I want -- that no clause of the asking package can
     reach, so Provides stays eager. *)
  let clauses_of tables (stz : nstanza) =
    match stz.nclauses with
    | Some c -> c
    | None ->
        let c = (parse_relations stz.raw_deps, parse_relations stz.raw_recs) in
        stz.nclauses <- Some c;
        tables.n_clauses_parsed <- tables.n_clauses_parsed + 1;
        c

  let deps_of tables stz = fst (clauses_of tables stz)
  let recs_of tables stz = snd (clauses_of tables stz)

  (* One package's clauses in control-file order, Depends before Recommends,
     each with its mangled alternatives and the synthetic name a multi-way
     clause would have: the order apt's Propagate walks the watches of a
     package that just became true, which is the order its work items enter
     the heap.  A one-alternative Depends has no disjunct package: its work
     item, when it has one, is the alternative's selector, which the caller
     resolves because a selector in turn exists only where a Provides
     matches the atom. *)
  let ordered_clauses tables (p : DMA.Pkg.t) :
      (bool * DMA.Deb.Name.t * DMA.Deb.Atom.t list) list =
    match Hashtbl.find_opt tables.oc_cache p with
    | Some r -> r
    | None ->
        let r =
          match stanza tables p with
          | None -> []
          | Some stz ->
              let b = snd (fst p) in
              (* the alternatives as the calculus counts them, which names
                 a clause by its atom set (Debian.dependees): a | a, or
                 a (>= 1.0) | a (>= 1.00), is one atom, a direct edge *)
              let mk opt synth alts =
                let ma = DMA.reduceClause b alts in
                ( opt,
                  synth ma,
                  DMA.Deb.AtomSet.elements (DMA.Deb.clauseAtoms ma) )
              in
              List.map
                (fun alts -> mk false (fun s -> DMA.Deb.Name.Disjunct s) alts)
                (deps_of tables stz)
              @ List.map
                  (fun alts -> mk true (fun s -> DMA.Deb.Name.Soft s) alts)
                  (recs_of tables stz)
        in
        Hashtbl.add tables.oc_cache p r;
        r

  let sat f w = DMA.Deb.vfHolds f w

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

    let compare a b = Pac_common.Ot.r2c (DMA.Deb.NameOT.compare a b)

    let pp fmt = function
      | DMA.Deb.Name.Orig m -> pp_mname fmt m
      | DMA.Deb.Name.Disjunct _ -> Format.fprintf fmt "<alts>"
      | DMA.Deb.Name.Soft _ -> Format.fprintf fmt "<rec>"
      | DMA.Deb.Name.Selector a -> Format.fprintf fmt "<sel %a>" pp_atom a
  end
end

(* what the replay is written against; the instance's own types, whatever
   the architectures *)
module type S = module type of Make (struct
  let arches = []
  let native = ""
end)
