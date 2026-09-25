(* The uncompressed APKINDEX: newline-delimited "X:value" lines, stanzas
   separated by a line shorter than two bytes, no continuations and no
   quoting (apk-tools src/database.c, apk_db_fdb_read).  There is no
   header stanza -- APKINDEX.tar.gz carries DESCRIPTION as a sibling tar
   member.  Trusted: this file is TCB. *)

type constr = Any | Op of Apk_version.op * string
type dep = { d_neg : bool; d_name : string; d_constr : constr }

(* A versioned provide is an alias apk treats as a real package of the
   provided name; a bare one offers the empty version, below every
   version, and claims no name. *)
type prov = { p_name : string; p_ver : string option }

type pkg = {
  name : string;
  version : string;
  depends : dep list;
  provides : prov list;
  install_if : dep list;
  priority : int option;
}

let rejected = ref 0
let reject () = incr rejected

(* apk_dep_parse: [!]name[op ver], where the operator run is any of
   < > = ~ and the name is everything before it.  None is an atom
   apk_blob_pull_dep fails on; the flag is false where it marks the atom
   broken instead, its version not one apk_version_validate accepts. *)
let comparer c = c = '<' || c = '>' || c = '=' || c = '~'

let parse_atom (tok : string) : (dep * bool) option =
  let neg = String.length tok > 0 && tok.[0] = '!' in
  let s = if neg then String.sub tok 1 (String.length tok - 1) else tok in
  let len = String.length s in
  (* name@tag pins the atom to a repository, which the calculus does not
     model; apk itself rejects a tag in an index dependency. *)
  if len = 0 || String.contains s '@' then None
  else
    let i = ref 0 in
    while !i < len && not (comparer s.[!i]) do
      incr i
    done;
    if !i = len then Some ({ d_neg = neg; d_name = s; d_constr = Any }, true)
    else
      let j = ref !i in
      while !j < len && comparer s.[!j] do
        incr j
      done;
      let n = String.sub s 0 !i in
      let opstr = String.sub s !i (!j - !i) in
      let ver = String.sub s !j (len - !j) in
      if n = "" || ver = "" then None
      else
        let d c = { d_neg = neg; d_name = n; d_constr = c } in
        (* a mask holding both < and > is exempt from the version check *)
        match Apk_version.op_of_string opstr with
        | None -> Some (d Any, true)
        | Some Apk_version.Hash -> Some (d (Op (Apk_version.Hash, ver)), true)
        | Some o -> Some (d (Op (o, ver)), Apk_version.validate ver)

(* Only space and newline separate dependency atoms; a tab does not. *)
let split_deps (v : string) : string list =
  String.split_on_char ' ' v |> List.filter (fun s -> s <> "")

(* None where apk_blob_pull_deps fails, which for D: makes the package
   uninstallable and for i: drops the whole rule *)
let parse_deps (v : string) : dep list option =
  let ds = List.map parse_atom (split_deps v) in
  if List.for_all (function Some (_, ok) -> ok | None -> false) ds then
    Some (List.map (fun a -> fst (Option.get a)) ds)
  else None

(* apk keeps the provides before an atom it fails on and drops the rest *)
let parse_provs (v : string) : prov list =
  let rec go = function
    | [] -> []
    | tok :: rest -> (
        match parse_atom tok with
        | None ->
            reject ();
            []
        | Some ({ d_name; d_constr = Any; _ }, _)
          when not (String.exists comparer tok) ->
            { p_name = d_name; p_ver = None } :: go rest
        | Some ({ d_name; d_constr = Op (Apk_version.Eq, ver); _ }, _) ->
            { p_name = d_name; p_ver = Some ver } :: go rest
        | Some _ ->
            (* apk only ever emits = in p:, and the calculus has no room
               for an inequality-constrained alias *)
            reject ();
            go rest)
  in
  go (split_deps v)

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

let flush a out =
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
  | Some _ -> reject ()
  | None -> ());
  a.a_name <- None;
  a.a_ver <- "";
  a.a_deps <- [];
  a.a_provs <- [];
  a.a_iif <- [];
  a.a_prio <- None;
  a.a_broken <- false

let parse_file (path : string) : pkg list =
  let ic = open_in_bin path in
  let out = ref [] and a = fresh () in
  (try
     while true do
       let line = input_line ic in
       if String.length line < 2 then flush a out
       else if line.[1] <> ':' then
         (* a line that is not "X:..." cannot be part of a stanza *)
         a.a_broken <- true
       else
         let v = String.sub line 2 (String.length line - 2) in
         match line.[0] with
         | 'P' -> a.a_name <- Some v
         | 'V' -> a.a_ver <- v
         | 'D' -> (
             match parse_deps v with
             | Some ds -> a.a_deps <- List.rev_append ds a.a_deps
             | None -> a.a_broken <- true)
         | 'p' -> a.a_provs <- List.rev_append (parse_provs v) a.a_provs
         | 'i' -> (
             match parse_deps v with
             | Some ds -> a.a_iif <- List.rev_append ds a.a_iif
             | None ->
                 reject ();
                 a.a_iif <- [])
         | 'k' -> a.a_prio <- int_of_string_opt v
         (* A C o S I T U L m t c carry no instance data, and apk skips the
            installed-db fields F M R Z in an index.  apk makes a package
            with an unknown upper-case field uninstallable, which dropping
            the stanza reproduces.  A lower-case field is reserved for
            forward compatibility and ignored. *)
         | 'A' | 'C' | 'o' | 'S' | 'I' | 'T' | 'U' | 'L' | 'm' | 't' | 'c' | 'F'
         | 'M' | 'R' | 'Z' ->
             ()
         | ch when ch >= 'a' && ch <= 'z' -> ()
         | _ -> a.a_broken <- true
     done
   with End_of_file -> ());
  flush a out;
  close_in ic;
  List.rev !out
