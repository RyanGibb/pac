(* The uncompressed APKINDEX: newline-delimited "X:value" lines, stanzas
   separated by a line shorter than two bytes, no continuations and no
   quoting (apk-tools src/database.c, apk_db_fdb_read).  There is no
   header stanza -- APKINDEX.tar.gz carries DESCRIPTION as a sibling tar
   member.  Trusted: this file is TCB. *)

type constr = Any | Op of Apk_version.op * string
type dep = { d_neg : bool; d_name : string; d_constr : constr }

(* A versioned provide is an alias apk treats as a real package of the
   provided name; an unversioned one only answers bare dependencies and
   claims no name, which is the PVirt/PVer split in the calculus. *)
type prov = { p_name : string; p_ver : string option }

type pkg = {
  name : string;
  version : string;
  arch : string;
  digest : string;
  origin : string;
  depends : dep list;
  provides : prov list;
  install_if : dep list;
  priority : int option;
}

let rejected = ref 0
let reject () = incr rejected

(* apk_dep_parse: [!]name[op ver], where the operator run is any of
   < > = ~ and the name is everything before it. *)
let comparer c = c = '<' || c = '>' || c = '=' || c = '~'

let parse_atom (tok : string) : dep option =
  let neg = String.length tok > 0 && tok.[0] = '!' in
  let s = if neg then String.sub tok 1 (String.length tok - 1) else tok in
  let n = String.length s in
  (* name@tag pins the atom to a repository, which the calculus does not
     model; apk itself rejects a tag in an index dependency. *)
  if n = 0 || String.contains s '@' then None
  else
    let i = ref 0 in
    while !i < n && not (comparer s.[!i]) do
      incr i
    done;
    if !i = n then Some { d_neg = neg; d_name = s; d_constr = Any }
    else
      let j = ref !i in
      while !j < n && comparer s.[!j] do
        incr j
      done;
      let nm = String.sub s 0 !i in
      let opstr = String.sub s !i (!j - !i) in
      let ver = String.sub s !j (n - !j) in
      if nm = "" then None
      else
        match Apk_version.op_of_string opstr with
        | None -> None
        | Some o -> Some { d_neg = neg; d_name = nm; d_constr = Op (o, ver) }

(* Only space and newline separate dependency atoms; a tab does not. *)
let split_deps (v : string) : string list =
  String.split_on_char ' ' v |> List.filter (fun s -> s <> "")

let parse_deps (v : string) : dep list =
  List.filter_map
    (fun tok ->
      match parse_atom tok with
      | Some d -> Some d
      | None ->
          reject ();
          None)
    (split_deps v)

let parse_provs (v : string) : prov list =
  List.filter_map
    (fun tok ->
      match parse_atom tok with
      | Some { d_name; d_constr = Any; _ } ->
          Some { p_name = d_name; p_ver = None }
      | Some { d_name; d_constr = Op (Apk_version.Eq, ver); _ } ->
          Some { p_name = d_name; p_ver = Some ver }
      | _ ->
          (* apk only ever emits = in p:, and the calculus has no room
             for an inequality-constrained alias *)
          reject ();
          None)
    (split_deps v)

type acc = {
  mutable a_name : string option;
  mutable a_ver : string;
  mutable a_arch : string;
  mutable a_digest : string;
  mutable a_origin : string;
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
    a_arch = "";
    a_digest = "";
    a_origin = "";
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
          arch = a.a_arch;
          digest = a.a_digest;
          origin = a.a_origin;
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
  a.a_arch <- "";
  a.a_digest <- "";
  a.a_origin <- "";
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
         | 'A' -> a.a_arch <- v
         | 'C' -> a.a_digest <- v
         | 'o' -> a.a_origin <- v
         | 'D' -> a.a_deps <- List.rev_append (parse_deps v) a.a_deps
         | 'p' -> a.a_provs <- List.rev_append (parse_provs v) a.a_provs
         | 'i' -> a.a_iif <- List.rev_append (parse_deps v) a.a_iif
         | 'k' -> a.a_prio <- int_of_string_opt v
         (* S I T U L m t c carry no instance rows; an unknown upper-case
            letter makes the package uninstallable, a lower-case one is
            reserved for forward compatibility and ignored *)
         | 'S' | 'I' | 'T' | 'U' | 'L' | 'm' | 't' | 'c' -> ()
         | ch when ch >= 'a' && ch <= 'z' -> ()
         | _ -> a.a_broken <- true
     done
   with End_of_file -> ());
  flush a out;
  close_in ic;
  List.rev !out
