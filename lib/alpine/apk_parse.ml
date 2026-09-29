type constr = Any | Op of Apk_version.op * string
type dep = { d_neg : bool; d_name : string; d_constr : constr }
type prov = { p_name : string; p_ver : string option }

type pkg = {
  name : string;
  version : string;
  depends : dep list;
  provides : prov list;
  install_if : dep list;
  priority : int option;
}

let comparer c = c = '<' || c = '>' || c = '=' || c = '~'

let rec index_of c s i b =
  if i < b && s.[i] <> c then index_of c s (i + 1) b else i

(* the first index in [i, b) at which [comparer] is [cmp], else b *)
let rec index_cmp cmp s i b =
  if i < b && comparer s.[i] <> cmp then index_cmp cmp s (i + 1) b else i

(* apk_dep_parse over s.[a, b): [!]name[op ver], where the operator run is
   any of < > = ~ and the name is everything before it.  None is an atom
   apk_blob_pull_dep fails on; the flag is false where it marks the atom
   broken instead, its version not one apk_version_validate accepts. *)
let parse_atom (s : string) (a : int) (b : int) : (dep * bool) option =
  let neg = a < b && s.[a] = '!' in
  let a = if neg then a + 1 else a in
  (* name@tag pins the atom to a repository, which the calculus does not
     model; apk itself rejects a tag in an index dependency. *)
  if a = b || index_of '@' s a b < b then None
  else
    let i = index_cmp true s a b in
    if i = b then
      Some
        ({ d_neg = neg; d_name = String.sub s a (b - a); d_constr = Any }, true)
    else
      let j = index_cmp false s i b in
      if i = a || j = b then None
      else
        let d c =
          { d_neg = neg; d_name = String.sub s a (i - a); d_constr = c }
        in
        let ver = String.sub s j (b - j) in
        (* a mask holding both < and > is exempt from the version check *)
        match Apk_version.op_of_string (String.sub s i (j - i)) with
        | None -> Some (d Any, true)
        | Some Apk_version.Hash -> Some (d (Op (Apk_version.Hash, ver)), true)
        | Some o -> Some (d (Op (o, ver)), Apk_version.validate ver)

(* Only space and newline separate dependency atoms; a tab does not. *)
let atom_end s a b = index_of ' ' s a b

(* the atoms of s.[a, b) pushed onto acc, the last on top; None where
   apk_blob_pull_deps fails, which for D: makes the package uninstallable
   and for i: drops the whole rule *)
let rec push_deps s a b acc : dep list option =
  if a = b then Some acc
  else if s.[a] = ' ' then push_deps s (a + 1) b acc
  else
    let e = atom_end s a b in
    match parse_atom s a e with
    | Some (d, true) -> push_deps s e b (d :: acc)
    | _ -> None

(* apk keeps the provides before an atom it fails on and drops the rest *)
let rec push_provs ~reject s a b acc : prov list =
  if a = b then acc
  else if s.[a] = ' ' then push_provs ~reject s (a + 1) b acc
  else
    let e = atom_end s a b in
    match parse_atom s a e with
    | None ->
        reject ();
        acc
    | Some ({ d_name; d_constr = Any; _ }, _) when index_cmp true s a e = e ->
        push_provs ~reject s e b ({ p_name = d_name; p_ver = None } :: acc)
    | Some ({ d_name; d_constr = Op (Apk_version.Eq, ver); _ }, _) ->
        push_provs ~reject s e b ({ p_name = d_name; p_ver = Some ver } :: acc)
    | Some _ ->
        (* apk only ever emits = in p:, and the calculus has no room
           for an inequality-constrained provides *)
        reject ();
        push_provs ~reject s e b acc

type acc = {
  mutable a_name : string option;
  mutable a_ver : string;
  mutable a_deps : dep list;
  mutable a_provs : prov list;
  mutable a_iif : dep list;
  mutable a_prio : int option;
  mutable a_broken : bool;
}

let fresh () =
  {
    a_name = None;
    a_ver = "";
    a_deps = [];
    a_provs = [];
    a_iif = [];
    a_prio = None;
    a_broken = false;
  }

(* A stanza apk cannot read is still a package of its database, one it
   will not install, so [broken] is told the names it holds a provider of:
   its own and those of its provides read so far. *)
let flush ~reject ~broken a out =
  (match a.a_name with
  | Some n when not a.a_broken ->
      out :=
        {
          name = n;
          version = a.a_ver;
          depends = List.rev a.a_deps;
          provides = List.rev a.a_provs;
          install_if = List.rev a.a_iif;
          priority = a.a_prio;
        }
        :: !out
  | Some n ->
      broken (n :: List.map (fun (p : prov) -> p.p_name) a.a_provs);
      reject ()
  | None -> ());
  a.a_name <- None;
  a.a_ver <- "";
  a.a_deps <- [];
  a.a_provs <- [];
  a.a_iif <- [];
  a.a_prio <- None;
  a.a_broken <- false

(* the value of the field line s.[i, e) *)
let value s i e = String.sub s (i + 2) (e - i - 2)

(* apk_db_fdb_read (apk-tools src/database.c): stanzas end at a line
   shorter than two bytes, with no continuations and no quoting *)
let parse_file ~reject ~broken (path : string) : pkg list =
  let s = In_channel.with_open_bin path In_channel.input_all in
  let n = String.length s in
  let out = ref [] and a = fresh () in
  let rec line i =
    if i < n then begin
      let e = try String.index_from s i '\n' with Not_found -> n in
      (if e - i < 2 then flush ~reject ~broken a out
       else if s.[i + 1] <> ':' then
         (* a line that is not "X:..." cannot be part of a stanza *)
         a.a_broken <- true
       else
         match s.[i] with
         | 'P' -> a.a_name <- Some (value s i e)
         | 'V' -> a.a_ver <- value s i e
         | 'D' -> (
             match push_deps s (i + 2) e a.a_deps with
             | Some ds -> a.a_deps <- ds
             | None -> a.a_broken <- true)
         | 'p' -> a.a_provs <- push_provs ~reject s (i + 2) e a.a_provs
         | 'i' -> (
             match push_deps s (i + 2) e a.a_iif with
             | Some ds -> a.a_iif <- ds
             | None ->
                 reject ();
                 a.a_iif <- [])
         | 'k' -> (
             match int_of_string_opt (value s i e) with
             | Some k -> a.a_prio <- Some k
             | None -> reject ())
         (* A C o S I T U L m t c carry no instance data, and apk skips the
            installed-db fields F M R Z in an index.  apk makes a package
            with an unknown upper-case field uninstallable, which dropping
            the stanza reproduces.  A lower-case field is reserved for
            forward compatibility and ignored. *)
         | 'A' | 'C' | 'o' | 'S' | 'I' | 'T' | 'U' | 'L' | 'm' | 't' | 'c' | 'F'
         | 'M' | 'R' | 'Z' ->
             ()
         | ch when ch >= 'a' && ch <= 'z' -> ()
         | _ -> a.a_broken <- true);
      line (e + 1)
    end
  in
  line 0;
  flush ~reject ~broken a out;
  List.rev !out

let world_of_args (args : string list) : (dep list, string) Stdlib.result =
  let rec go acc = function
    | [] -> Ok (List.rev acc)
    | "" :: rest -> go acc rest
    | a :: rest -> (
        match parse_atom a 0 (String.length a) with
        | Some (d, true) -> go (d :: acc) rest
        | Some (_, false) -> Error (Printf.sprintf "%S: not a valid version" a)
        | None when String.contains a '@' ->
            Error (Printf.sprintf "%S: no repository has that tag" a)
        | None -> Error (Printf.sprintf "%S: not a dependency atom" a))
  in
  go [] args
