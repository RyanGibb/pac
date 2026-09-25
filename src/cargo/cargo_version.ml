(* SemVer 2.0.0 precedence and Cargo's requirement syntax, implemented
   from the specifications: numeric major.minor.patch, then pre-release
   compared identifier-wise (numeric identifiers below alphanumeric ones,
   a shorter identifier list below its extensions, and a version carrying
   a pre-release below the same core release), with build metadata
   ignored.  Requirements are conjunctions of comparators -- one
   comparator set of the calculus's shared semver range language; caret
   is the default and uses the leftmost-nonzero compatibility rule, and a
   pre-release candidate is admitted only by a requirement naming one at
   the same release core.  Trusted (TCB). *)

let is_digit c = c >= '0' && c <= '9'

type t = { major : int; minor : int; patch : int; pre : string list }

(* leading zeros carry no value, and an absurdly long run is saturated
   rather than overflowing int_of_string *)
let strip0 s =
  let n = String.length s in
  let i = ref 0 in
  while !i < n - 1 && s.[!i] = '0' do
    incr i
  done;
  String.sub s !i (n - !i)

let int_of_digits s =
  let s = strip0 s in
  if s = "" then 0 else if String.length s > 9 then max_int else int_of_string s

let split_on c s = String.split_on_char c s

let parse_fresh (s : string) : t =
  let s =
    match String.index_opt s '+' with Some i -> String.sub s 0 i | None -> s
  in
  let core, pre =
    match String.index_opt s '-' with
    | Some i ->
        (String.sub s 0 i, String.sub s (i + 1) (String.length s - i - 1))
    | None -> (s, "")
  in
  let num s =
    let n = String.length s in
    let j = ref 0 in
    while !j < n && is_digit s.[!j] do
      incr j
    done;
    int_of_digits (String.sub s 0 !j)
  in
  let parts = split_on '.' core in
  let get i = match List.nth_opt parts i with Some x -> num x | None -> 0 in
  {
    major = get 0;
    minor = get 1;
    patch = get 2;
    pre = (if pre = "" then [] else split_on '.' pre);
  }

(* compare sits under every range operation the solver makes, and parsing
   afresh there was most of a large solve's time; a run meets a few
   thousand distinct version strings (about 3,400 at most), though a large
   query loads tens of thousands of versions *)
let parsed : (string, t) Hashtbl.t = Hashtbl.create 65536

let parse (s : string) : t =
  match Hashtbl.find_opt parsed s with
  | Some p -> p
  | None ->
      let p = parse_fresh s in
      Hashtbl.add parsed s p;
      p

let is_num s = s <> "" && String.for_all is_digit s

let cmp_id a b =
  match (is_num a, is_num b) with
  | true, true ->
      let a = strip0 a and b = strip0 b in
      let c = compare (String.length a) (String.length b) in
      if c <> 0 then c else String.compare a b
  | true, false -> -1
  | false, true -> 1
  | false, false -> String.compare a b

let rec cmp_ids a b =
  match (a, b) with
  | [], [] -> 0
  | [], _ -> -1
  | _, [] -> 1
  | x :: xs, y :: ys ->
      let c = cmp_id x y in
      if c <> 0 then c else cmp_ids xs ys

let compare_parsed (a : string) (b : string) : int =
  let x = parse a and y = parse b in
  let c = compare x.major y.major in
  if c <> 0 then c
  else
    let c = compare x.minor y.minor in
    if c <> 0 then c
    else
      let c = compare x.patch y.patch in
      if c <> 0 then c
      else
        match (x.pre, y.pre) with
        | [], [] -> 0
        | [], _ -> 1
        | _, [] -> -1
        | p, q -> cmp_ids p q

(* The release cores are compared off the strings themselves, a field at a
   time as parse reads them and no further than the first that differs:
   compare runs under every range operation the solver makes, and even a
   table of parsed versions costs a hash of the string there.  Only equal
   cores leave the pre-release to decide. *)

(* parse's num of the part at !i, leaving !i at the next part, or at the
   end once the core has ended *)
let field s n i =
  let j = ref !i in
  while !j < n && s.[!j] = '0' do
    incr j
  done;
  let v = ref 0 and d = ref 0 in
  while !j < n && is_digit s.[!j] do
    if !d < 9 then v := (!v * 10) + (Char.code s.[!j] - 48);
    incr d;
    incr j
  done;
  while !j < n && s.[!j] <> '.' && s.[!j] <> '-' && s.[!j] <> '+' do
    incr j
  done;
  i := if !j < n && s.[!j] = '.' then !j + 1 else n;
  if !d > 9 then max_int else !v

(* no '-' ahead of the build metadata, so no pre-release *)
let plain s =
  let n = String.length s in
  let rec go i =
    i = n || match s.[i] with '+' -> true | '-' -> false | _ -> go (i + 1)
  in
  go 0

let compare (a : string) (b : string) : int =
  let na = String.length a and nb = String.length b in
  let ia = ref 0 and ib = ref 0 in
  let c = Int.compare (field a na ia) (field b nb ib) in
  if c <> 0 then c
  else
    let c = Int.compare (field a na ia) (field b nb ib) in
    if c <> 0 then c
    else
      let c = Int.compare (field a na ia) (field b nb ib) in
      if c <> 0 then c
      else if plain a && plain b then 0
      else compare_parsed a b

let equal a b = compare a b = 0
let is_prerelease v = (parse v).pre <> []

(* the release core a pre-release belongs to: a requirement admits a
   pre-release candidate only when one of its own comparators names a
   pre-release at the same core, which is Semver.csAdmits in the
   calculus and pre_is_compatible in the semver crate *)
let same_core a b =
  let x = parse a and y = parse b in
  x.major = y.major && x.minor = y.minor && x.patch = y.patch

(* ---- requirements ---- *)

type op = Ge | Gt | Le | Lt | Eq
type req = (op * string) list (* a conjunction; [] is any version *)
type comp = Num of int | Star | Absent

let comp_of = function
  | "" -> Absent
  | "*" | "x" | "X" -> Star
  | s ->
      let n = String.length s in
      let j = ref 0 in
      while !j < n && is_digit s.[!j] do
        incr j
      done;
      if !j = 0 then Star else Num (int_of_digits (String.sub s 0 !j))

let vstr ?(pre = "") maj min pat =
  Printf.sprintf "%d.%d.%d%s" maj min pat (if pre = "" then "" else "-" ^ pre)

(* a comparator's version part: up to three components, any of which may
   be absent or an explicit wildcard, plus an optional pre-release *)
let parse_spec (s : string) =
  let s =
    match String.index_opt s '+' with Some i -> String.sub s 0 i | None -> s
  in
  let core, pre =
    match String.index_opt s '-' with
    | Some i ->
        (String.sub s 0 i, String.sub s (i + 1) (String.length s - i - 1))
    | None -> (s, "")
  in
  let parts = split_on '.' core in
  let get i =
    match List.nth_opt parts i with Some x -> comp_of x | None -> Absent
  in
  (get 0, get 1, get 2, pre)

let num_or d = function Num n -> n | Star | Absent -> d

let caret (ma, mi, pa, pre) =
  match ma with
  | Star | Absent -> []
  | Num m -> (
      match (mi, pa) with
      | (Star | Absent), _ -> [ (Ge, vstr ~pre m 0 0); (Lt, vstr (m + 1) 0 0) ]
      | Num n, (Star | Absent) ->
          [
            (Ge, vstr ~pre m n 0);
            (Lt, if m > 0 then vstr (m + 1) 0 0 else vstr 0 (n + 1) 0);
          ]
      | Num n, Num p ->
          [
            (Ge, vstr ~pre m n p);
            ( Lt,
              if m > 0 then vstr (m + 1) 0 0
              else if n > 0 then vstr 0 (n + 1) 0
              else vstr 0 0 (p + 1) );
          ])

let tilde (ma, mi, pa, pre) =
  match ma with
  | Star | Absent -> []
  | Num m -> (
      match (mi, pa) with
      | (Star | Absent), _ -> [ (Ge, vstr ~pre m 0 0); (Lt, vstr (m + 1) 0 0) ]
      | Num n, (Star | Absent) ->
          [ (Ge, vstr ~pre m n 0); (Lt, vstr m (n + 1) 0) ]
      | Num n, Num p -> [ (Ge, vstr ~pre m n p); (Lt, vstr m (n + 1) 0) ])

let exact (ma, mi, pa, pre) =
  match (ma, mi, pa) with
  | (Star | Absent), _, _ -> []
  | Num m, (Star | Absent), _ -> [ (Ge, vstr m 0 0); (Lt, vstr (m + 1) 0 0) ]
  | Num m, Num n, (Star | Absent) ->
      [ (Ge, vstr m n 0); (Lt, vstr m (n + 1) 0) ]
  | Num m, Num n, Num p -> [ (Eq, vstr ~pre m n p) ]

(* wildcards read as a range over the components left unpinned; a bare
   version with components simply missing is a caret instead *)
let wildcard (ma, mi, pa, pre) =
  match (ma, mi, pa) with
  | (Star | Absent), _, _ -> []
  | Num m, Star, _ -> [ (Ge, vstr m 0 0); (Lt, vstr (m + 1) 0 0) ]
  | Num m, Num n, Star -> [ (Ge, vstr m n 0); (Lt, vstr m (n + 1) 0) ]
  | _ -> caret (ma, mi, pa, pre)

let ineq op (ma, mi, pa, pre) =
  match ma with
  | Star | Absent -> []
  | Num m -> (
      let n = num_or 0 mi and p = num_or 0 pa in
      let has_mi = match mi with Num _ -> true | _ -> false in
      let has_pa = match pa with Num _ -> true | _ -> false in
      match op with
      | Ge -> [ (Ge, vstr ~pre m n p) ]
      | Lt -> [ (Lt, vstr ~pre m n p) ]
      | Gt ->
          if has_pa then [ (Gt, vstr ~pre m n p) ]
          else if has_mi then [ (Ge, vstr m (n + 1) 0) ]
          else [ (Ge, vstr (m + 1) 0 0) ]
      | Le ->
          if has_pa then [ (Le, vstr ~pre m n p) ]
          else if has_mi then [ (Lt, vstr m (n + 1) 0) ]
          else [ (Lt, vstr (m + 1) 0 0) ]
      | Eq -> exact (ma, mi, pa, pre))

let trim s = String.trim s

let comparator (s : string) : req =
  let s = trim s in
  if s = "" then []
  else
    let starts p =
      String.length s >= String.length p && String.sub s 0 (String.length p) = p
    in
    let drop k = trim (String.sub s k (String.length s - k)) in
    if starts "^" then caret (parse_spec (drop 1))
    else if starts "~" then tilde (parse_spec (drop 1))
    else if starts ">=" then ineq Ge (parse_spec (drop 2))
    else if starts "<=" then ineq Le (parse_spec (drop 2))
    else if starts ">" then ineq Gt (parse_spec (drop 1))
    else if starts "<" then ineq Lt (parse_spec (drop 1))
    else if starts "==" then exact (parse_spec (drop 2))
    else if starts "=" then exact (parse_spec (drop 1))
    else wildcard (parse_spec s)

let parse_req (s : string) : req = List.concat_map comparator (split_on ',' s)

let admits (v : string) (r : req) : bool =
  (not (is_prerelease v))
  || List.exists (fun (_, c) -> is_prerelease c && same_core v c) r

let holds (v : string) (r : req) : bool =
  List.for_all
    (fun (op, c) ->
      let s = compare v c in
      match op with
      | Ge -> s >= 0
      | Gt -> s > 0
      | Le -> s <= 0
      | Lt -> s < 0
      | Eq -> s = 0)
    r
  && admits v r

let string_of_op = function
  | Ge -> ">="
  | Gt -> ">"
  | Le -> "<="
  | Lt -> "<"
  | Eq -> "="

let string_of_req r =
  if r = [] then "*"
  else String.concat ", " (List.map (fun (o, v) -> string_of_op o ^ v) r)
