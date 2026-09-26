type cmp = Ge | Gt | Le | Lt | Eq
type arch_qual = Unqual | AnyArch | NativeArch | ExplicitArch of string
type atom = { name : string; aqual : arch_qual; constr : (cmp * string) option }
type provide = { pname : string; pversion : string option }

(* Depends and Recommends are held as the unparsed field text -- Pre-Depends
   then Depends, in that order -- because they hold the bulk of an archive's
   relationship atoms while a lookup reduces a few dozen of its ~69k stanzas.
   Keeping 340k atom records and list cells live in the major heap cost more
   than reading the whole file did; whoever needs a stanza's clauses calls
   parse_depends_fields on them and keeps only those.  Provides are parsed
   here because their reverse table is a preimage that no single stanza's
   clauses can reach. *)
type stanza = {
  package : string;
  version : string;
  architecture : string;
  multi_arch : string option;
  depends_raw : string list;
  (* same syntax as depends (Policy 7.2), and kept apart from it because a
     recommends clause need not be satisfiable for the solve to succeed *)
  recommends_raw : string list;
  provides : provide list;
  (* and Breaks: to apt's solver both only exclude, and they differ in the
     unpack order dpkg keeps, which is no part of a resolution *)
  conflicts : atom list;
  essential : bool;
  (* apt folds Protected into the same flag as Important (deblistparser.cc
     UsePackage), so the two fields are read as one here *)
  important : bool;
  priority : int;
  (* apt's SourcePkgName and SourceVerStr: a Source field naming no version
     leaves the binary's own, and a stanza with none its own name too *)
  source : string * string;
}

(* apt's pkgCache::State::VerPriority, which is an enum ordered
   required(1) .. extra(5), and its comparator prefers the *smaller* rank.
   A stanza with no Priority field is read as extra, the lowest; apt leaves
   the cache's zero there instead, which would sort above required, but no
   stanza of a Debian index omits the field. *)
let priority_rank = function
  | "required" -> 1
  | "important" -> 2
  | "standard" -> 3
  | "optional" -> 4
  | _ -> 5

let priority_lowest = 5

(* what apt's pkgTagSection::FindFlag (StringToBool) reads as yes, given
   lower-cased: a word, or the whole string as strtol reads 1 in base 0 *)
let flag_yes = function
  | "yes" | "true" | "with" | "on" | "enable" -> true
  | s ->
      let s =
        if String.starts_with ~prefix:"+" s then
          String.sub s 1 (String.length s - 1)
        else s
      in
      let s =
        if String.starts_with ~prefix:"0x" s then
          String.sub s 2 (String.length s - 2)
        else s
      in
      String.ends_with ~suffix:"1" s
      && String.for_all (( = ) '0') (String.sub s 0 (String.length s - 1))

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

(* the two-character operators first, so that ">" is not read off ">=";
   the deprecated one-character ">" and "<" mean ">=" and "<=" (Policy 7.1) *)
let operators =
  [
    (">=", Ge);
    (">>", Gt);
    ("<=", Le);
    ("<<", Lt);
    ("=", Eq);
    (">", Ge);
    ("<", Le);
  ]

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
        match
          List.find_opt
            (fun (p, _) -> String.starts_with ~prefix:p rest)
            operators
        with
        | Some (p, op) ->
            let n = String.length p in
            (op, String.sub rest n (String.length rest - n))
        | None -> (Eq, rest)
      in
      if name = "" then None
      else Some { name; aqual; constr = Some (op, strip v) }

(* The alternatives parse_depends drops, those parse_atom finds no name in:
   an empty one, or one opening on a qualifier or, with no version to cut
   the name at, on a restriction.  apt reads any as an error in the index.
   They are counted as the stanza is read, without the parse, which waits
   until a lookup asks for the field; an empty clause parse_depends skips. *)
let nameless_alternatives field =
  let n = String.length field and count = ref 0 in
  let ws c = c = ' ' || c = '\t' || c = '\n' || c = '\r' in
  let skip_ws i e =
    let i = ref i in
    while !i < e && ws field.[!i] do
      incr i
    done;
    !i
  in
  let upto c i e =
    let i = ref i in
    while !i < e && field.[!i] <> c do
      incr i
    done;
    !i
  in
  let rec clauses i =
    if i <= n then (
      let e = upto ',' i n in
      if skip_ws i e < e then alternatives i e;
      clauses (e + 1))
  and alternatives a e =
    if a <= e then (
      let b = upto '|' a e in
      let s = skip_ws a b in
      (if s = b then incr count
       else
         match (upto '(' s b < b, field.[s]) with
         | true, ('(' | ':') | false, ('[' | '<' | ':') -> incr count
         | _ -> ());
      alternatives (b + 1) e)
  in
  clauses 0;
  !count

let parse_depends field =
  split_on ',' field
  |> List.filter_map (fun clause ->
      if strip clause = "" then None
      else
        let alts = split_on '|' clause |> List.filter_map parse_atom in
        match alts with [] -> None | _ -> Some alts)

(* conjunction of alternative groups, one field after another: a clause never
   straddles a field boundary, so the concatenation is the parse of each *)
let parse_depends_fields fields = List.concat_map parse_depends fields

(* Policy 7.1 allows alternatives only in the Depends family *)
let parse_conflicts ~reject field =
  split_on ',' field
  |> List.filter_map (fun s ->
      match parse_atom s with
      | None ->
          reject ();
          None
      | a -> a)

(* Declared arch-qualified Provides are out of scope, so an atom's
   qualifier is ignored: a single-arch reading of the provided name.  Only
   "=" provides exist (Policy 7.5); apt drops any other entry with a warning
   and keeps the rest of the stanza (ParseProvides, deblistparser.cc), and
   reading it as unversioned would be strictly more permissive. *)
let parse_provides ~reject field =
  split_on ',' field
  |> List.filter_map (fun s ->
      match parse_atom s with
      | Some { name; constr = Some (Eq, v); _ } ->
          Some { pname = name; pversion = Some v }
      | Some { name; constr = None; _ } ->
          Some { pname = name; pversion = None }
      | Some { constr = Some _; _ } | None ->
          reject ();
          None)

(* apt warns on any other value and reads it as no *)
let multi_arch_known = function
  | "no" | "same" | "foreign" | "allowed" -> true
  | _ -> false

(* One pass over a stanza's fields, rather than an assoc lookup per field:
   an archive is ~69k stanzas.  First occurrence wins. *)
let stanza_of_fields ~reject (fs : (string * string) list) : stanza option =
  let package = ref None
  and version = ref None
  and architecture = ref None
  and multi_arch = ref None
  and predepends = ref None
  and depends = ref None
  and recommends = ref None
  and provides = ref None
  and conflicts = ref None
  and breaks = ref None
  and essential = ref None
  and important = ref None
  and protected_ = ref None
  and priority = ref None
  and source = ref None in
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
      | "Essential" -> set essential v
      | "Important" -> set important v
      | "Protected" -> set protected_ v
      | "Priority" -> set priority v
      | "Source" -> set source v
      | _ -> ())
    fs;
  match (!package, !version) with
  | Some package, Some version ->
      let opt f = function Some d -> f d | None -> [] in
      let yes = function
        | Some s -> flag_yes (String.lowercase_ascii s)
        | None -> false
      in
      let raw = List.filter_map Fun.id in
      let depends_raw = raw [ !predepends; !depends ]
      and recommends_raw = raw [ !recommends ] in
      List.iter
        (fun f ->
          for _ = 1 to nameless_alternatives f do
            reject ()
          done)
        (depends_raw @ recommends_raw);
      Some
        {
          package;
          version;
          architecture =
            (match !architecture with Some a -> a | None -> "all");
          multi_arch =
            (match !multi_arch with
            | Some m when not (multi_arch_known m) ->
                reject ();
                None
            | m -> m);
          depends_raw;
          recommends_raw;
          provides = opt (parse_provides ~reject) !provides;
          conflicts =
            opt (parse_conflicts ~reject) !conflicts
            @ opt (parse_conflicts ~reject) !breaks;
          essential = yes !essential;
          important = yes !important || yes !protected_;
          priority =
            (match !priority with
            | Some p -> priority_rank (String.lowercase_ascii p)
            | None -> priority_lowest);
          source =
            (match !source with
            | None -> (package, version)
            | Some s -> (
                match String.index_opt s '(' with
                | None -> (strip s, version)
                | Some i ->
                    let v = String.sub s (i + 1) (String.length s - i - 1) in
                    let v =
                      match String.index_opt v ')' with
                      | Some j -> String.sub v 0 j
                      | None -> v
                    in
                    (strip (String.sub s 0 i), strip v)));
        }
  | _ ->
      reject ();
      None

(* Stanzas are built as the file is read.  Accumulating every physical line
   first cost 1.27M live strings and conses on a Debian archive before any
   stanza was looked at; nothing needs a line once its stanza is closed. *)
let parse_file ~reject path =
  let ic = open_in path in
  Fun.protect ~finally:(fun () -> close_in_noerr ic) @@ fun () ->
  let acc = ref [] and fields = ref [] in
  let flush () =
    (match !fields with
    | [] -> ()
    | fs -> (
        match stanza_of_fields ~reject (List.rev fs) with
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
         | [] -> reject ()
       else
         match String.index_opt line ':' with
         | Some i ->
             let k = String.sub line 0 i in
             let v =
               strip (String.sub line (i + 1) (String.length line - i - 1))
             in
             fields := (k, v) :: !fields
         | None -> reject ()
     done
   with End_of_file -> ());
  flush ();
  List.rev !acc
