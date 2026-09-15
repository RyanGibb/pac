(* Packages-index parser, from Debian Policy 5.3 (stanza syntax) and 7.1
   (relationship fields).  Untrusted; architecture qualifiers, build
   profiles, and architecture restriction lists are stripped (single-arch
   assumption). *)

type cmp = Ge | Gt | Le | Lt | Eq
type arch_qual = Unqual | AnyArch | NativeArch | ExplicitArch of string
type atom = { name : string; aqual : arch_qual; constr : (cmp * string) option }
type provide = { pname : string; pversion : string option }

type stanza = {
  package : string;
  version : string;
  architecture : string;
  multi_arch : string option;
  depends : atom list list; (* conjunction of alternative groups *)
  (* same syntax as depends (Policy 7.2), and kept apart from it because a
     recommends clause need not be satisfiable for the solve to succeed *)
  recommends : atom list list;
  provides : provide list;
  conflicts : atom list; (* Conflicts + Breaks atoms *)
}

(* newlines count as whitespace: a relationship field may be folded over
   several lines (Policy 5.1), and its continuations are joined with "\n",
   so an atom can arrive with one still attached *)
let strip s =
  let is_ws c = c = ' ' || c = '\t' || c = '\n' || c = '\r' in
  let n = String.length s in
  let i = ref 0 and j = ref n in
  while !i < n && is_ws s.[!i] do
    incr i
  done;
  while !j > !i && is_ws s.[!j - 1] do
    decr j
  done;
  String.sub s !i (!j - !i)

let split_on c s = String.split_on_char c s |> List.map strip

(* name[:arch] [(op ver)] [\[...\]] [<...>] *)
let parse_atom s =
  let s = strip s in
  let cut mark s =
    match String.index_opt s mark with Some i -> String.sub s 0 i | None -> s
  in
  let split_qual n =
    match String.index_opt n ':' with
    | None -> (n, Unqual)
    | Some i -> (
        let base = String.sub n 0 i in
        match String.sub n (i + 1) (String.length n - i - 1) with
        | "any" -> (base, AnyArch)
        | "native" -> (base, NativeArch)
        | a -> (base, ExplicitArch a))
  in
  (* The '(op ver)' part precedes '[archs]' and '<profiles>' (Policy 7.1),
     so strip those only outside the parens — a bare cut at '<' would eat
     the '<<' operator. *)
  match String.index_opt s '(' with
  | None ->
      let name, aqual = split_qual (strip (cut '[' (cut '<' s))) in
      if name = "" then None else Some { name; aqual; constr = None }
  | Some i ->
      let name, aqual = split_qual (strip (String.sub s 0 i)) in
      let rest = String.sub s (i + 1) (String.length s - i - 1) in
      let rest =
        match String.index_opt rest ')' with
        | Some j -> String.sub rest 0 j
        | None -> rest
      in
      let rest = strip rest in
      let op, v =
        if String.length rest >= 2 && String.sub rest 0 2 = ">=" then
          (Ge, String.sub rest 2 (String.length rest - 2))
        else if String.length rest >= 2 && String.sub rest 0 2 = ">>" then
          (Gt, String.sub rest 2 (String.length rest - 2))
        else if String.length rest >= 2 && String.sub rest 0 2 = "<=" then
          (Le, String.sub rest 2 (String.length rest - 2))
        else if String.length rest >= 2 && String.sub rest 0 2 = "<<" then
          (Lt, String.sub rest 2 (String.length rest - 2))
        else if String.length rest >= 1 && rest.[0] = '=' then
          (Eq, String.sub rest 1 (String.length rest - 1))
        else if String.length rest >= 1 && rest.[0] = '>' then
          (* deprecated ">" means ">=" (Policy 7.1) *)
          (Ge, String.sub rest 1 (String.length rest - 1))
        else if String.length rest >= 1 && rest.[0] = '<' then
          (Le, String.sub rest 1 (String.length rest - 1))
        else (Eq, rest)
      in
      if name = "" then None
      else Some { name; aqual; constr = Some (op, strip v) }

let parse_depends field =
  split_on ',' field
  |> List.filter_map (fun clause ->
      if strip clause = "" then None
      else
        let alts = split_on '|' clause |> List.filter_map parse_atom in
        match alts with [] -> None | _ -> Some alts)

let parse_conflicts field =
  (* Alternatives are not permitted in Conflicts/Breaks (Policy 7.4). *)
  split_on ',' field |> List.filter_map parse_atom

let parse_provides field =
  split_on ',' field
  |> List.filter_map (fun s ->
      (* declared arch-qualified Provides are out of scope: aqual is
            ignored here (single-arch reading of the provided name) *)
      match parse_atom s with
      | Some { name; constr = Some (Eq, v); _ } ->
          Some { pname = name; pversion = Some v }
      | Some { name; constr = None; _ } ->
          Some { pname = name; pversion = None }
      (* only "=" provides exist (Policy 7.5); apt warns-and-ignores,
            dose3 errors — silently reading these as unversioned would be
            strictly more permissive than either *)
      | Some { constr = Some _; _ } ->
          failwith
            (Printf.sprintf "non-'=' version constraint in Provides: %S" s)
      | None -> None)

(* One pass over a stanza's fields, rather than an assoc lookup per field:
   the ten fields below were each a linear scan of the stanza, and an
   archive is ~69k stanzas.  First occurrence wins, as List.assoc_opt did. *)
let stanza_of_fields (fs : (string * string) list) : stanza option =
  let package = ref None
  and version = ref None
  and architecture = ref None
  and multi_arch = ref None
  and predepends = ref None
  and depends = ref None
  and recommends = ref None
  and provides = ref None
  and conflicts = ref None
  and breaks = ref None in
  let set r v = if !r = None then r := Some v in
  List.iter
    (fun (k, v) ->
      match k with
      | "Package" -> set package v
      | "Version" -> set version v
      | "Architecture" -> set architecture v
      | "Multi-Arch" -> set multi_arch v
      | "Pre-Depends" -> set predepends v
      | "Depends" -> set depends v
      | "Recommends" -> set recommends v
      | "Provides" -> set provides v
      | "Conflicts" -> set conflicts v
      | "Breaks" -> set breaks v
      | _ -> ())
    fs;
  match (!package, !version) with
  | Some package, Some version ->
      let opt f = function Some d -> f d | None -> [] in
      Some
        {
          package;
          version;
          architecture =
            (match !architecture with Some a -> a | None -> "all");
          multi_arch = !multi_arch;
          depends = opt parse_depends !predepends @ opt parse_depends !depends;
          recommends = opt parse_depends !recommends;
          provides = opt parse_provides !provides;
          conflicts =
            opt parse_conflicts !conflicts @ opt parse_conflicts !breaks;
        }
  | _ -> None

(* Stanzas are built as the file is read.  Accumulating every physical line
   first cost 1.27M live strings and conses on a Debian archive before any
   stanza was looked at; nothing needs a line once its stanza is closed. *)
let parse_file path =
  let ic = open_in path in
  let acc = ref [] and fields = ref [] in
  let flush () =
    (match !fields with
    | [] -> ()
    | fs -> (
        match stanza_of_fields (List.rev fs) with
        | Some st -> acc := st :: !acc
        | None -> ()));
    fields := []
  in
  (try
     while true do
       let line = input_line ic in
       if line = "" then flush ()
       else if line.[0] = ' ' || line.[0] = '\t' then
         match !fields with
         | (k, v) :: tl -> fields := (k, v ^ "\n" ^ strip line) :: tl
         | [] -> ()
       else
         match String.index_opt line ':' with
         | Some i ->
             let k = String.sub line 0 i in
             let v =
               strip (String.sub line (i + 1) (String.length line - i - 1))
             in
             fields := (k, v) :: !fields
         | None -> ()
     done
   with End_of_file -> close_in ic);
  flush ();
  List.rev !acc
