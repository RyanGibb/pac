(* Trusted (TCB) ingestion: opam files to instance rows, applying the
   documented instance-level desugarings -- mixed brace formulas are
   distributed into (filter, version-constraint) atoms, bare boolean
   variables become =-"true" comparisons, package-local variables are
   qualified by their package.  Unhandled constructs are counted and the
   enclosing atom conservatively dropped. *)

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

let qualify ~owner x = if List.mem x local_vars then owner ^ ":" ^ x else x

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

let rec brace_of ~owner ~selfv (v : value) : brace =
  let brace_of = brace_of ~owner ~selfv in
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
  (* a group's elements are implicitly conjoined, as they are at the top
     level of a brace: (a b) is a & b, not a parse failure *)
  | Group { pelem = a :: rest; _ } ->
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

(* an atom with a brace formula distributes over the DNF branches *)
let atom_of ~owner ~selfv (n : string) (braces : value list) : off =
  match braces with
  | [] -> OAtom (n, FT, VTop)
  | _ -> (
      let b =
        List.fold_left
          (fun acc v -> BAnd (acc, brace_of ~owner ~selfv v))
          (BF FT) braces
      in
      let branches = dnf false b in
      let atoms =
        List.map (fun (fs, cs) -> OAtom (n, conj_f fs, conj_c cs)) branches
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
   braces becomes one prohibition row *)
let rec conflict_atoms ~owner ~selfv (v : value) : (string * (filt * vc)) list =
  match v.pelem with
  | String n -> [ (n, (FT, VTop)) ]
  | Option ({ pelem = String n; _ }, braces) ->
      let b =
        List.fold_left
          (fun acc v -> BAnd (acc, brace_of ~owner ~selfv v))
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

let depext_rows ~owner ~selfv (v : value) : (string * filt) list =
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

let pindep_rows (v : value) : ((string * string) * string) list =
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
          meta := { !meta with depexts = depext_rows ~owner ~selfv v }
      | Variable ({ pelem = "pin-depends"; _ }, v) ->
          meta := { !meta with pindeps = pindep_rows v }
      | _ -> ())
    file.file_contents;
  !meta

(* every variable mentioned, for the finite X *)
let rec filt_vars acc = function
  | FT | FF -> acc
  | FCmp (_, x, _) | FDef x -> x :: acc
  | FAnd (a, b) | FOr (a, b) -> filt_vars (filt_vars acc a) b
  | FNot a -> filt_vars acc a

let rec off_vars acc = function
  | OAtom (_, g, _) -> filt_vars acc g
  | OAnd (a, b) | OOr (a, b) -> off_vars (off_vars acc a) b

let meta_vars (m : pkg_meta) : string list =
  let acc = match m.depends with None -> [] | Some f -> off_vars [] f in
  let acc =
    List.fold_left (fun a (_, (g, _)) -> filt_vars a g) acc m.conflicts
  in
  let acc = filt_vars acc m.available in
  List.fold_left (fun a (_, g) -> filt_vars a g) acc m.depexts
