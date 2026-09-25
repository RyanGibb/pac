(* Trusted (TCB) ingestion: opam files to instance declarations, applying the
   documented instance-level desugarings -- mixed brace formulas are
   distributed into (filter, version-constraint) atoms, bare boolean
   variables become =-"true" comparisons, package-local variables are
   qualified by their package.  Unhandled constructs are counted and the
   enclosing atom dropped, which can admit a selection opam rejects (an
   unhandled available: makes the package unavailable instead); a file that
   fails to parse is skipped, uncounted, by the loader. *)

open OpamParserTypes.FullPos

type op = Ge | Gt | Le | Lt | Eq | Ne

type filt =
  | FT
  | FF
  | FCmp of op * string * string (* op, variable, constant *)
  | FDef of string
  | FAnd of filt * filt
  | FOr of filt * filt
  | FNot of filt

type vc = VTop | VCmp of op * string | VAnd of vc * vc | VOr of vc * vc
type off = OAtom of string * filt * vc | OAnd of off * off | OOr of off * off

type pkg_meta = {
  name : string;
  version : string;
  depends : off option;
  conflicts : (string * (filt * vc)) list;
  classes : string list;
  available : filt;
  depexts : (string * filt) list;
  pindeps : ((string * string) * string) list;
  (* opam 2.1's avoid-version and 2.2's deprecated: "select this version
     only if nothing else works".  Not a constraint -- a flagged version
     stays installable -- so they are recorded here and spent on solver
     preference, never on the declarations. *)
  avoid_version : bool;
  deprecated : bool;
}

let rejected = ref 0
let reject () = incr rejected

(* opam's package-local variables; everything else is global. *)
let local_vars =
  [
    "build";
    "post";
    "with-test";
    "with-doc";
    "with-dev-setup";
    "dev";
    "pinned";
    "installed";
    "name";
    "version";
  ]

(* opam reads a conflict's filter in the switch's environment
   (get_conflicts, through OpamPackageVar.resolve_switch), where only name
   and version are the package's own and any other variable is looked up as
   a switch or global one.  No such variable is called with-test or build,
   so in a conflict they are undefined, as the manual has it: with-test is
   limited to depends, depopts and the commands, build and post to depends
   and depopts. *)
let switch_local_vars = [ "name"; "version" ]
let qualify ~locals ~owner x = if List.mem x locals then owner ^ ":" ^ x else x

(* The atom syntax opam's command line takes, one element of a query:
   [OpamFormula.atom_of_string] (opamFormula.ml) matches a name -- the run
   before the first character an operator can begin with -- then an
   operator, then a non-empty version, and falls back to reading the whole
   string as a bare name when that fails.  "." spells "=", and the
   operators are tried longest first because a shorter one is what the
   regexp backtracks to when the version would otherwise be empty. *)
let atom_of_string (s : string) : string * vc =
  let n = String.length s in
  let rec cut i =
    if i >= n then None
    else if String.contains ">=<.!" s.[i] then Some i
    else cut (i + 1)
  in
  let spellings =
    [
      ("<=", Le);
      (">=", Ge);
      ("!=", Ne);
      ("<", Lt);
      (">", Gt);
      ("=", Eq);
      (".", Eq);
    ]
  in
  match cut 0 with
  | Some i when i > 0 -> (
      let fits (sp, _) =
        let l = String.length sp in
        i + l < n && String.sub s i l = sp
      in
      match List.find_opt fits spellings with
      | Some (sp, o) ->
          let l = String.length sp in
          (String.sub s 0 i, VCmp (o, String.sub s (i + l) (n - i - l)))
      | None -> (s, VTop))
  | _ -> (s, VTop)

let rel_of = function
  | `Eq -> Eq
  | `Neq -> Ne
  | `Geq -> Ge
  | `Gt -> Gt
  | `Leq -> Le
  | `Lt -> Lt

let rel_flip = function
  | Eq -> Eq
  | Ne -> Ne
  | Ge -> Le
  | Le -> Ge
  | Gt -> Lt
  | Lt -> Gt

(* brace formulas: a tree over filter and constraint leaves *)
type brace =
  | BF of filt
  | BC of op * string
  | BAnd of brace * brace
  | BOr of brace * brace
  | BNot of brace

let rec brace_of ?(locals = local_vars) ~owner ~selfv (v : value) : brace =
  let brace_of = brace_of ~locals ~owner ~selfv in
  let qualify = qualify ~locals in
  match v.pelem with
  | Bool true -> BF FT
  | Bool false -> BF FF
  | Ident x -> BF (FCmp (Eq, qualify ~owner x, "true"))
  | Prefix_relop (r, { pelem = String s; _ }) -> BC (rel_of r.pelem, s)
  | Prefix_relop (r, { pelem = Ident "version"; _ }) ->
      (* {= version}: the owner's own version, which we are parsing and so
         know -- a genuine version constraint on the dependency, not a filter *)
      BC (rel_of r.pelem, selfv)
  | Prefix_relop (r, { pelem = Ident x; _ }) ->
      (* another package's variable (ocaml:version, coq-native:installed):
         not desugarable without that package's value, so the atom is
         removed by the filter semantics *)
      reject ();
      BF (FCmp (rel_of r.pelem, qualify ~owner x, "%v%"))
  | Relop (r, { pelem = Ident x; _ }, { pelem = String s; _ }) ->
      BF (FCmp (rel_of r.pelem, qualify ~owner x, s))
  | Relop (r, { pelem = String s; _ }, { pelem = Ident x; _ }) ->
      BF (FCmp (rel_flip (rel_of r.pelem), qualify ~owner x, s))
  | Relop (r, { pelem = String a; _ }, { pelem = String b; _ }) ->
      let c = Opam_version.compare a b in
      let holds =
        match rel_of r.pelem with
        | Eq -> c = 0
        | Ne -> c <> 0
        | Ge -> c >= 0
        | Gt -> c > 0
        | Le -> c <= 0
        | Lt -> c < 0
      in
      BF (if holds then FT else FF)
  | Logop ({ pelem = `And; _ }, a, b) -> BAnd (brace_of a, brace_of b)
  | Logop ({ pelem = `Or; _ }, a, b) -> BOr (brace_of a, brace_of b)
  | Pfxop ({ pelem = `Not; _ }, a) -> BNot (brace_of a)
  | Pfxop ({ pelem = `Defined; _ }, { pelem = Ident x; _ }) ->
      BF (FDef (qualify ~owner x))
  (* a group's or list's elements are conjoined, as opam does in a
     dependency brace (opamFormat.ml:411,420); opam's filter parser, which
     reads available:, rejects more than one element (opamFormat.ml:315-319),
     so this accepts more there *)
  | Group { pelem = a :: rest; _ } | List { pelem = a :: rest; _ } ->
      List.fold_left (fun acc v -> BAnd (acc, brace_of v)) (brace_of a) rest
  | _ ->
      reject ();
      BF FF

(* negation-pushing DNF: branches of (filter, constraint) conjunctions *)
let rec dnf (neg : bool) (b : brace) : (filt list * vc list) list =
  match (b, neg) with
  | BF f, false -> [ ([ f ], []) ]
  | BF f, true -> [ ([ FNot f ], []) ]
  | BC (o, s), false -> [ ([], [ VCmp (o, s) ]) ]
  | BC (o, s), true -> [ ([], [ VCmp (rel_complement o, s) ]) ]
  | BAnd (a, b), false | BOr (a, b), true ->
      List.concat_map
        (fun (fa, ca) ->
          List.map (fun (fb, cb) -> (fa @ fb, ca @ cb)) (dnf neg b))
        (dnf neg a)
  | BOr (a, b), false | BAnd (a, b), true -> dnf neg a @ dnf neg b
  | BNot a, _ -> dnf (not neg) a

and rel_complement = function
  | Ge -> Lt
  | Gt -> Le
  | Le -> Gt
  | Lt -> Ge
  | Eq -> Ne
  | Ne -> Eq

let conj_f = function
  | [] -> FT
  | f :: fs -> List.fold_left (fun a b -> FAnd (a, b)) f fs

let conj_c = function
  | [] -> VTop
  | c :: cs -> List.fold_left (fun a b -> VAnd (a, b)) c cs

let disj_c = function
  | [] -> VTop
  | c :: cs -> List.fold_left (fun a b -> VOr (a, b)) c cs

(* An atom with a brace formula distributes over the DNF branches, but only
   as far as their filters differ: opam evaluates a brace's filters and
   keeps one version formula for the atom, so the branches sharing a filter
   are one atom at the union of their versions.  Distributing those too
   would make {(>= "4.12" & < "5.0") | >= "5.3"} alternatives, the range
   written first preferred over the newest version. *)
let atom_of ~owner ~selfv (n : string) (braces : value list) : off =
  match braces with
  | [] -> OAtom (n, FT, VTop)
  | _ -> (
      let b =
        List.fold_left
          (fun acc v -> BAnd (acc, brace_of ~owner ~selfv v))
          (BF FT) braces
      in
      let by_filter =
        List.fold_left
          (fun acc (fs, cs) ->
            if List.mem_assoc fs acc then
              List.map
                (fun (g, css) -> if g = fs then (g, css @ [ cs ]) else (g, css))
                acc
            else acc @ [ (fs, [ cs ]) ])
          [] (dnf false b)
      in
      let atoms =
        List.map
          (fun (fs, css) -> OAtom (n, conj_f fs, disj_c (List.map conj_c css)))
          by_filter
      in
      match atoms with
      | [] -> OAtom (n, FF, VTop)
      | a :: rest -> List.fold_left (fun x y -> OOr (x, y)) a rest)

let rec formula_of ~owner ~selfv (v : value) : off option =
  match v.pelem with
  | String n -> Some (OAtom (n, FT, VTop))
  | Option ({ pelem = String n; _ }, braces) ->
      Some (atom_of ~owner ~selfv n braces.pelem)
  | Logop ({ pelem = `And; _ }, a, b) ->
      merge ~owner ~selfv (fun x y -> OAnd (x, y)) a b
  | Logop ({ pelem = `Or; _ }, a, b) ->
      merge ~owner ~selfv (fun x y -> OOr (x, y)) a b
  | Group { pelem = [ a ]; _ } -> formula_of ~owner ~selfv a
  | Group { pelem = l; _ } | List { pelem = l; _ } ->
      List.fold_left
        (fun acc v ->
          match (acc, formula_of ~owner ~selfv v) with
          | None, x -> x
          | x, None -> x
          | Some x, Some y -> Some (OAnd (x, y)))
        None l
  | _ ->
      reject ();
      None

and merge ~owner ~selfv mk a b =
  match (formula_of ~owner ~selfv a, formula_of ~owner ~selfv b) with
  | Some x, Some y -> Some (mk x y)
  | Some x, None | None, Some x -> Some x
  | None, None -> None

(* conflicts are a disjunction of atoms; each DNF branch of each atom's
   braces becomes one prohibition *)
let rec conflict_atoms ~owner ~selfv (v : value) : (string * (filt * vc)) list =
  match v.pelem with
  | String n -> [ (n, (FT, VTop)) ]
  | Option ({ pelem = String n; _ }, braces) ->
      let b =
        List.fold_left
          (fun acc v ->
            BAnd (acc, brace_of ~locals:switch_local_vars ~owner ~selfv v))
          (BF FT) braces.pelem
      in
      List.map (fun (fs, cs) -> (n, (conj_f fs, conj_c cs))) (dnf false b)
  | Logop (_, a, b) ->
      conflict_atoms ~owner ~selfv a @ conflict_atoms ~owner ~selfv b
  | Group { pelem = l; _ } | List { pelem = l; _ } ->
      List.concat_map (conflict_atoms ~owner ~selfv) l
  | _ ->
      reject ();
      []

let depext_entries ~owner ~selfv (v : value) : (string * filt) list =
  let entry (v : value) =
    match v.pelem with
    | Option ({ pelem = Group { pelem = pkgs; _ }; _ }, braces)
    | Option ({ pelem = List { pelem = pkgs; _ }; _ }, braces) ->
        let g =
          List.fold_left
            (fun acc v -> BAnd (acc, brace_of ~owner ~selfv v))
            (BF FT) braces.pelem
        in
        let gf =
          match dnf false g with
          | [ (fs, []) ] -> conj_f fs
          | _ ->
              reject ();
              FF
        in
        List.filter_map
          (fun (p : value) ->
            match p.pelem with
            | String e -> Some (e, gf)
            | _ ->
                reject ();
                None)
          pkgs
    | Group { pelem = pkgs; _ } | List { pelem = pkgs; _ } ->
        List.filter_map
          (fun (p : value) ->
            match p.pelem with
            | String e -> Some (e, FT)
            | _ ->
                reject ();
                None)
          pkgs
    | String e -> [ (e, FT) ]
    | _ ->
        reject ();
        []
  in
  match v.pelem with
  | List { pelem = l; _ } -> List.concat_map entry l
  | _ -> entry v

let class_names (v : value) : string list =
  match v.pelem with
  | String c -> [ c ]
  | List { pelem = l; _ } ->
      List.filter_map
        (fun (x : value) ->
          match x.pelem with
          | String c -> Some c
          | _ ->
              reject ();
              None)
        l
  | _ ->
      reject ();
      []

(* opam takes only the ident form (opamFormat.ml:90-93, via opamFile.ml's
   flags field) *)
let flag_names (v : value) : string list =
  let one (x : value) =
    match x.pelem with
    | Ident f | String f -> Some f
    | _ ->
        reject ();
        None
  in
  match v.pelem with
  | List { pelem = l; _ } | Group { pelem = l; _ } -> List.filter_map one l
  | _ -> ( match one v with Some f -> [ f ] | None -> [])

let pindep_entries (v : value) : ((string * string) * string) list =
  let entry (v : value) =
    match v.pelem with
    | List { pelem = [ { pelem = String nv; _ }; { pelem = String u; _ } ]; _ }
      -> (
        match String.index_opt nv '.' with
        | Some i ->
            [
              ( ( String.sub nv 0 i,
                  String.sub nv (i + 1) (String.length nv - i - 1) ),
                u );
            ]
        | None ->
            reject ();
            [])
    | _ ->
        reject ();
        []
  in
  match v.pelem with
  | List { pelem = l; _ } -> List.concat_map entry l
  | _ -> entry v

let parse_file ~name ~version path : pkg_meta =
  let file = OpamParser.FullPos.file path in
  let owner = name in
  let selfv = version in
  let meta =
    ref
      {
        name;
        version;
        depends = None;
        conflicts = [];
        classes = [];
        available = FT;
        depexts = [];
        pindeps = [];
        avoid_version = false;
        deprecated = false;
      }
  in
  List.iter
    (fun (it : opamfile_item) ->
      match it.pelem with
      | Variable ({ pelem = "depends"; _ }, v) ->
          meta := { !meta with depends = formula_of ~owner ~selfv v }
      | Variable ({ pelem = "conflicts"; _ }, v) ->
          meta := { !meta with conflicts = conflict_atoms ~owner ~selfv v }
      | Variable ({ pelem = "conflict-class"; _ }, v) ->
          meta := { !meta with classes = class_names v }
      | Variable ({ pelem = "available"; _ }, v) ->
          meta :=
            {
              !meta with
              available =
                (match dnf false (brace_of ~owner ~selfv v) with
                | [ (fs, []) ] -> conj_f fs
                | branches -> (
                    match List.filter (fun (_, cs) -> cs = []) branches with
                    | [] ->
                        reject ();
                        FF
                    | l ->
                        List.fold_left
                          (fun a (fs, _) -> FOr (a, conj_f fs))
                          FF l));
            }
      | Variable ({ pelem = "depexts"; _ }, v) ->
          meta := { !meta with depexts = depext_entries ~owner ~selfv v }
      | Variable ({ pelem = "pin-depends"; _ }, v) ->
          meta := { !meta with pindeps = pindep_entries v }
      | Variable ({ pelem = "flags"; _ }, v) ->
          let fl = flag_names v in
          meta :=
            {
              !meta with
              avoid_version = List.mem "avoid-version" fl;
              deprecated = List.mem "deprecated" fl;
            }
      | _ -> ())
    file.file_contents;
  !meta
