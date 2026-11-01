module DebianVersionOT = Pac_common.Ot.Make (struct
  type t = string

  let compare = Version.Debian.compare
end)

type stats = { names : int; versions : int }

module type ARCH = sig
  val arches : string list
  val native : string
end

module type S = sig
  module APx : sig
    module Architecture : sig
      type t = string

      val compare : t -> t -> Pac.comparison
      val eq_dec : t -> t -> bool
      val enum : string list
    end

    val native : string
  end

  module MultiarchDebian :
      module type of
        Pac.MultiarchDebian (Pac_common.Ot.Str) (DebianVersionOT) (APx)

  type nstanza = {
    npkg : MultiarchDebian.Package.t;
    ncls : MultiarchDebian.coq_MAClass;
    raw_deps : string list;
    raw_recs : string list;
    mutable nclauses :
      (MultiarchDebian.Atom.t list list * MultiarchDebian.Atom.t list list)
      option;
    nprovs : (string * MultiarchDebian.Debian.coq_DTop) list;
    nconfs : MultiarchDebian.Atom.t list;
    ness : bool;
    nimp : bool;
    nprio : int;
    nsrc : string * string;
    nall : bool;
  }

  type tables
  type eager

  val eager : tables -> eager
  val of_eager : eager -> tables
  val stats : tables -> stats
  val stanza : tables -> MultiarchDebian.Package.t -> nstanza option
  val versions_of : tables -> string * string -> string list
  val group_members : tables -> string -> (string * string) list

  val providers :
    tables ->
    string ->
    (MultiarchDebian.Package.t * MultiarchDebian.Debian.coq_DTop) list

  val dependers : tables -> string -> MultiarchDebian.Package.t list
  val conflicters : tables -> string -> MultiarchDebian.Package.t list

  val atom_pos :
    MultiarchDebian.Debian.Clause.t -> MultiarchDebian.Debian.Atom.t -> int

  val build_tables : recommends:bool -> Deb_packages.stanza list -> tables
  val obsolete : tables -> nstanza -> bool
  val deps_of : nstanza -> MultiarchDebian.Atom.t list list
  val recs_of : nstanza -> MultiarchDebian.Atom.t list list

  val ordered_clauses :
    tables ->
    MultiarchDebian.Package.t ->
    (bool
    * MultiarchDebian.Debian.Reduction.Name.t
    * MultiarchDebian.Debian.Atom.t list)
    list

  val sat : MultiarchDebian.Debian.VersionFormula.coq_Formula -> string -> bool

  val pp_mname :
    Format.formatter -> string * MultiarchDebian.coq_ReducedQualifier -> unit

  val pp_atom : Format.formatter -> MultiarchDebian.Debian.Atom.t -> unit

  module PName : sig
    type t = MultiarchDebian.Debian.Reduction.Name.t

    val compare : t -> t -> int
    val pp : Format.formatter -> t -> unit
    val pp_core : Format.formatter -> t -> unit
  end
end

module Make (AP : ARCH) : S = struct
  module APx = struct
    module Architecture = struct
      include Pac_common.Ot.Str

      let enum = AP.arches
    end

    let native = AP.native
  end

  module MultiarchDebian =
    Pac.MultiarchDebian (Pac_common.Ot.Str) (DebianVersionOT) (APx)

  let formula_of_constr = function
    | None -> MultiarchDebian.Debian.VersionFormula.FTop
    | Some (Deb_packages.Ge, v) ->
        MultiarchDebian.Debian.VersionFormula.FCmp (Pac.OpGe, v)
    | Some (Deb_packages.Gt, v) ->
        MultiarchDebian.Debian.VersionFormula.FCmp (Pac.OpGt, v)
    | Some (Deb_packages.Le, v) ->
        MultiarchDebian.Debian.VersionFormula.FCmp (Pac.OpLe, v)
    | Some (Deb_packages.Lt, v) ->
        MultiarchDebian.Debian.VersionFormula.FCmp (Pac.OpLt, v)
    | Some (Deb_packages.Eq, v) ->
        MultiarchDebian.Debian.VersionFormula.FCmp (Pac.OpEq, v)

  let qual_of = function
    | Deb_packages.Unqual -> MultiarchDebian.QUnq
    | Deb_packages.AnyArch -> MultiarchDebian.QAny
    | Deb_packages.NativeArch -> MultiarchDebian.QNative
    | Deb_packages.ExplicitArch a -> MultiarchDebian.QExact a

  let matom_of (a : Deb_packages.atom) : MultiarchDebian.Atom.t =
    (a.name, (qual_of a.aqual, formula_of_constr a.constr))

  let dtop_of = function
    | Some v -> MultiarchDebian.Debian.DTVal v
    | None -> MultiarchDebian.Debian.DTTop

  type nstanza = {
    npkg : MultiarchDebian.Package.t;
    ncls : MultiarchDebian.coq_MAClass;
    raw_deps : string list;
    raw_recs : string list;
    mutable nclauses :
      (MultiarchDebian.Atom.t list list * MultiarchDebian.Atom.t list list)
      option;
    nprovs : (string * MultiarchDebian.Debian.coq_DTop) list;
    nconfs : MultiarchDebian.Atom.t list;
    ness : bool;
    nimp : bool;
    nprio : int;
    nsrc : string * string;
    nall : bool;
  }

  (* ~recommends false is the --no-install-recommends reading: the Rec
     instance is empty, so every soft disjunct is empty and unreachable. *)
  let normalize ~recommends (st : Deb_packages.stanza) : nstanza =
    let _, arch = Apt_args.stanza_key ~native:AP.native st in
    let ncls =
      match st.multi_arch with
      | Some "foreign" -> MultiarchDebian.MAForeign
      | Some "same" when st.architecture = "all" -> MultiarchDebian.MANo
      | Some "same" -> MultiarchDebian.MASame
      | Some "allowed" -> MultiarchDebian.MAAllowed
      | _ -> MultiarchDebian.MANo
    in
    {
      npkg = ((st.package, arch), st.version);
      ncls;
      raw_deps = st.depends_raw;
      raw_recs = (if recommends then st.recommends_raw else []);
      nclauses = None;
      nprovs =
        List.map
          (fun (pr : Deb_packages.provide) -> (pr.pname, dtop_of pr.pversion))
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

  type eager = {
    versions_table : (string * string, string list) Hashtbl.t;
    stanza_table : (MultiarchDebian.Package.t, nstanza) Hashtbl.t;
    group_table : (string, (string * string) list) Hashtbl.t;
    providers_table :
      ( string,
        (MultiarchDebian.Package.t * MultiarchDebian.Debian.coq_DTop) list )
      Hashtbl.t;
  }

  type tables = {
    eager : eager;
    (* who names a package in a Depends or Pre-Depends, and who in a
       Conflicts or Breaks, by the bare name as written: the watch lists
       apt's Reject propagation walks, built from the field text alone, so
       no clause is parsed for them; only the tool order asks *)
    rev_dep_table : (string, MultiarchDebian.Package.t list) Hashtbl.t Lazy.t;
    rev_conf_table : (string, MultiarchDebian.Package.t list) Hashtbl.t Lazy.t;
    (* the binaries each source name builds, for apt's obsolescence test,
       likewise asked for by the tool order alone *)
    source_table : (string, nstanza list) Hashtbl.t Lazy.t;
    (* a package's clauses in field order, asked for again by every depender
       and by the rejection cascade *)
    oc_cache :
      ( MultiarchDebian.Package.t,
        (bool
        * MultiarchDebian.Debian.Reduction.Name.t
        * MultiarchDebian.Debian.Atom.t list)
        list )
      Hashtbl.t;
  }

  let push = Pac_common.Tbl.push
  let find_list = Pac_common.Tbl.find_list

  let stats tables =
    {
      names = Hashtbl.length tables.eager.group_table;
      versions = Hashtbl.length tables.eager.stanza_table;
    }

  let stanza tables p = Hashtbl.find_opt tables.eager.stanza_table p
  let versions_of tables k = find_list tables.eager.versions_table k
  let group_members tables n = find_list tables.eager.group_table n
  let providers tables n = find_list tables.eager.providers_table n
  let dependers tables n = find_list (Lazy.force tables.rev_dep_table) n
  let conflicters tables n = find_list (Lazy.force tables.rev_conf_table) n

  let parse_relations fields =
    List.map (List.map matom_of) (Deb_packages.parse_depends_fields fields)

  let atom_pos (alts : MultiarchDebian.Debian.Clause.t) a =
    let rec go i = function
      | [] -> max_int
      | b :: bs ->
          if MultiarchDebian.Debian.Atom.eq_dec b a then i else go (i + 1) bs
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
        List.iter (fun a -> push c (MultiarchDebian.aname a) p) stz.nconfs)
      stanza_table;
    c

  let by_source stanza_table =
    let t = Hashtbl.create 65536 in
    Hashtbl.iter (fun _ (s : nstanza) -> push t (fst s.nsrc) s) stanza_table;
    t

  let eager tables = tables.eager

  let of_eager eager =
    {
      eager;
      rev_dep_table = lazy (rev_dep eager.stanza_table);
      rev_conf_table = lazy (rev_conf eager.stanza_table);
      source_table = lazy (by_source eager.stanza_table);
      oc_cache = Hashtbl.create 4096;
    }

  (* Of two stanzas at one version apt keeps the first read, Provides and
     all.  An arch:all stanza is a version of its own to apt (Version::All),
     which the package's one version here cannot be, so that pair is still
     read as one version with both stanzas' Provides, in the stanza as in
     providers_table; its Depends, Recommends and Conflicts are the later
     stanza's. *)
  let build_tables ~recommends (index : Deb_packages.stanza list) : tables =
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
    of_eager { versions_table; stanza_table; group_table; providers_table }

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
  let clauses_of (stz : nstanza) =
    match stz.nclauses with
    | Some c -> c
    | None ->
        let c = (parse_relations stz.raw_deps, parse_relations stz.raw_recs) in
        stz.nclauses <- Some c;
        c

  let deps_of stz = fst (clauses_of stz)
  let recs_of stz = snd (clauses_of stz)

  (* One package's clauses in control-file order, Depends before Recommends,
     each with its mangled alternatives and the synthetic name a multi-way
     clause would have: the order apt's Propagate walks the watches of a
     package that just became true, which is the order its work items enter
     the heap.  A one-alternative Depends has no disjunct package: its work
     item, when it has one, is the alternative's selector, which the caller
     resolves because a selector in turn exists only where a Provides
     matches the atom. *)
  let ordered_clauses tables (p : MultiarchDebian.Package.t) :
      (bool
      * MultiarchDebian.Debian.Reduction.Name.t
      * MultiarchDebian.Debian.Atom.t list)
      list =
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
                let ma = MultiarchDebian.Reduction.reduceClause b alts in
                ( opt,
                  synth ma,
                  MultiarchDebian.Debian.AtomSet.elements
                    (MultiarchDebian.Debian.clauseAtoms ma) )
              in
              List.map
                (fun alts ->
                  mk false
                    (fun s -> MultiarchDebian.Debian.Reduction.Name.Disjunct s)
                    alts)
                (deps_of stz)
              @ List.map
                  (fun alts ->
                    mk true
                      (fun s -> MultiarchDebian.Debian.Reduction.Name.Soft s)
                      alts)
                  (recs_of stz)
        in
        Hashtbl.add tables.oc_cache p r;
        r

  let sat f w = MultiarchDebian.Debian.VersionFormula.satisfiesb w f

  let pp_formula fmt (f : MultiarchDebian.Debian.VersionFormula.coq_Formula) =
    let rec go fmt = function
      | MultiarchDebian.Debian.VersionFormula.FTop -> Format.fprintf fmt "T"
      | MultiarchDebian.Debian.VersionFormula.FBot -> Format.fprintf fmt "F"
      | MultiarchDebian.Debian.VersionFormula.FConj (a, b) ->
          Format.fprintf fmt "(%a & %a)" go a go b
      | MultiarchDebian.Debian.VersionFormula.FDisj (a, b) ->
          Format.fprintf fmt "(%a | %a)" go a go b
      | MultiarchDebian.Debian.VersionFormula.FCmp (op, v) ->
          let ops =
            match op with
            | Pac.OpGe -> ">="
            | Pac.OpGt -> ">>"
            | Pac.OpLe -> "<="
            | Pac.OpLt -> "<<"
            | Pac.OpEq -> "="
            | Pac.OpNe -> "!="
          in
          Format.fprintf fmt "%s %s" ops v
    in
    go fmt f

  let pp_qarch fmt = function
    | MultiarchDebian.QAArch a -> Format.fprintf fmt "%s" a
    | MultiarchDebian.QAExact a -> Format.fprintf fmt "<%s>" a
    | MultiarchDebian.QAAny -> Format.fprintf fmt "any"
    | MultiarchDebian.QAGroup -> Format.fprintf fmt "<group>"

  let pp_mname fmt (n, y) = Format.fprintf fmt "%s:%a" n pp_qarch y
  let pp_atom fmt (m, f) = Format.fprintf fmt "%a (%a)" pp_mname m pp_formula f

  module PName = struct
    type t = MultiarchDebian.Debian.Reduction.Name.t

    let compare a b =
      Pac_common.Ot.r2c (MultiarchDebian.Debian.Reduction.NameOT.compare a b)

    let pp fmt = function
      | MultiarchDebian.Debian.Reduction.Name.Orig m -> pp_mname fmt m
      | MultiarchDebian.Debian.Reduction.Name.Disjunct _ ->
          Format.fprintf fmt "<alts>"
      | MultiarchDebian.Debian.Reduction.Name.Soft _ ->
          Format.fprintf fmt "<rec>"
      | MultiarchDebian.Debian.Reduction.Name.Selector a ->
          Format.fprintf fmt "<sel %a>" pp_atom a

    (* [pp] abbreviates a clause, which the explanations print; the core
       block lists clauses side by side, so it spells each one out *)
    let pp_core fmt n =
      let alts =
        Format.pp_print_list
          ~pp_sep:(fun fmt () -> Format.fprintf fmt " | ")
          pp_atom
      in
      match n with
      | MultiarchDebian.Debian.Reduction.Name.Disjunct a ->
          Format.fprintf fmt "<alts %a>" alts a
      | MultiarchDebian.Debian.Reduction.Name.Soft a ->
          Format.fprintf fmt "<rec %a>" alts a
      | _ -> pp fmt n
  end
end
