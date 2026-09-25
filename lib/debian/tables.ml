(* The parsed Packages file's derived tables, and what reads them without
   deciding anything: the stanza normal form, the clauses in field order,
   apt's obsolescence test, the printers. *)

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

module type ARCH = sig
  val arches : string list
  val native : string
end

module Make (AP : ARCH) = struct
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

  (* Untrusted whole-archive index: its faithfulness to the parsed instance
     is trusted, as are the parser, Deb_version, the Strict-Pinning cut and
     PubGrub. *)
  type index = {
    versions_of : (string * string, string list) Hashtbl.t;
    stanza_of : (DMA.Pkg.t, nstanza) Hashtbl.t;
    group_of : (string, (string * string) list) Hashtbl.t;
    providers_of : (string, (DMA.Pkg.t * DMA.Deb.coq_DTop) list) Hashtbl.t;
    class_of : (DMA.Pkg.t, DMA.coq_MAClass) Hashtbl.t;
    (* stanzas whose clauses a sub-instance has asked for, reported under
       PACPROF: the whole point of deferring them is that this stays small *)
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
    (* Of two stanzas at one version apt keeps the first read, Provides and
       all.  An arch:all stanza is a version of its own to apt
       (Version::All), which the package's one version here cannot be, so
       that pair is still read as one version with both stanzas' Provides. *)
    let first_read (stz : nstanza) =
      match Hashtbl.find_opt idx.stanza_of stz.npkg with
      | Some old -> old.nall <> stz.nall
      | None -> true
    in
    List.iter
      (fun st ->
        let stz = normalize ~recommends st in
        if first_read stz then (
          let (n, b), v = stz.npkg in
          if not (Hashtbl.mem idx.stanza_of stz.npkg) then (
            push idx.versions_of (n, b) v;
            push idx.group_of n (b, v));
          Hashtbl.replace idx.stanza_of stz.npkg stz;
          Hashtbl.replace idx.class_of stz.npkg stz.ncls;
          List.iter
            (fun (m, vt) -> push idx.providers_of m (stz.npkg, vt))
            stz.nprovs))
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
     the heap.  A one-alternative Depends has no disjunct package: its work
     item, when it has one, is the alternative's selector, which the caller
     resolves because a selector in turn exists only where a Provides
     matches the atom. *)
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

  let find_list tbl k =
    match Hashtbl.find_opt tbl k with Some l -> l | None -> []


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
end

(* what the replay is written against; the instance's own types, whatever
   the architectures *)
module type S = module type of Make (struct
  let arches = []
  let native = ""
end)
