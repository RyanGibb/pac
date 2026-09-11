(* SemVer 2.0.0 precedence and npm's range grammar, implemented from the
   specifications: numeric major.minor.patch, then pre-release compared
   identifier-wise (numeric identifiers below alphanumeric ones, a shorter
   identifier list below its extensions, and a version carrying a
   pre-release below the same core release), with build metadata ignored.

   parse_range only *parses*: it turns a range string into a disjunction
   of comparator sets and never decides which versions match.  Evaluation
   against the real version set is the extracted calculus's job, and the
   prerelease admission rule is Npm.csAdmits there.  The [holds] mirror
   at the bottom exists so the grammar can be tested from OCaml; the
   solver does not use it.  Untrusted (TCB). *)

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

let parse (s : string) : t =
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

(* the comparator is called a few million times per solve -- once per
   candidate per gate row -- so parses are shared *)
let memo : (string, t) Hashtbl.t = Hashtbl.create 4096

let parse_memo (s : string) : t =
  match Hashtbl.find_opt memo s with
  | Some p -> p
  | None ->
      let p = parse s in
      Hashtbl.replace memo s p;
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

let compare (a : string) (b : string) : int =
  if a == b || String.equal a b then 0
  else
    let x = parse_memo a and y = parse_memo b in
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

let equal a b = compare a b = 0
let is_prerelease v = (parse_memo v).pre <> []

(* the release core a prerelease belongs to: node-semver admits a
   prerelease candidate only inside a comparator set that names one at
   the same core *)
let same_core a b =
  let x = parse_memo a and y = parse_memo b in
  x.major = y.major && x.minor = y.minor && x.patch = y.patch

(* ---- ranges ---- *)

type op = Ge | Gt | Le | Lt | Eq | Ne
type comparator = Any | Cmp of op * string
type comp_set = comparator list (* whitespace is conjunction *)
type range = comp_set list (* || is disjunction *)
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

(* caret keeps the leftmost non-zero component: ^0.2.3 is <0.3.0 and
   ^0.0.3 is <0.0.4, which is why it cannot be written as a tilde *)
let caret (ma, mi, pa, pre) =
  match ma with
  | Star | Absent -> [ Any ]
  | Num m ->
      let hi =
        match (mi, pa) with
        | (Star | Absent), _ -> vstr (m + 1) 0 0
        | Num n, (Star | Absent) ->
            if m > 0 then vstr (m + 1) 0 0 else vstr 0 (n + 1) 0
        | Num n, Num p ->
            if m > 0 then vstr (m + 1) 0 0
            else if n > 0 then vstr 0 (n + 1) 0
            else vstr 0 0 (p + 1)
      in
      [ Cmp (Ge, vstr ~pre m (num_or 0 mi) (num_or 0 pa)); Cmp (Lt, hi) ]

let tilde (ma, mi, pa, pre) =
  match ma with
  | Star | Absent -> [ Any ]
  | Num m -> (
      match mi with
      | Star | Absent -> [ Cmp (Ge, vstr m 0 0); Cmp (Lt, vstr (m + 1) 0 0) ]
      | Num n ->
          [ Cmp (Ge, vstr ~pre m n (num_or 0 pa)); Cmp (Lt, vstr m (n + 1) 0) ])

(* a bare or =-prefixed spec: fully given it is an equality, and each
   component left off widens it by one place *)
let bare (ma, mi, pa, pre) =
  match (ma, mi, pa) with
  | (Star | Absent), _, _ -> [ Any ]
  | Num m, (Star | Absent), _ ->
      [ Cmp (Ge, vstr m 0 0); Cmp (Lt, vstr (m + 1) 0 0) ]
  | Num m, Num n, (Star | Absent) ->
      [ Cmp (Ge, vstr m n 0); Cmp (Lt, vstr m (n + 1) 0) ]
  | Num m, Num n, Num p -> [ Cmp (Eq, vstr ~pre m n p) ]

let ineq op (ma, mi, pa, pre) =
  match ma with
  | Star | Absent -> (
      (* >x and <x admit nothing; >=x and <=x admit everything *)
      match op with
      | Ge | Le -> [ Any ]
      | _ -> [ Cmp (Lt, "0.0.0") ])
  | Num m -> (
      let n = num_or 0 mi and p = num_or 0 pa in
      let has_mi = match mi with Num _ -> true | _ -> false in
      let has_pa = match pa with Num _ -> true | _ -> false in
      match op with
      | Ge -> [ Cmp (Ge, vstr ~pre m n p) ]
      | Lt -> [ Cmp (Lt, vstr ~pre m n p) ]
      | Ne -> [ Cmp (Ne, vstr ~pre m n p) ]
      | Gt ->
          if has_pa then [ Cmp (Gt, vstr ~pre m n p) ]
          else if has_mi then [ Cmp (Ge, vstr m (n + 1) 0) ]
          else [ Cmp (Ge, vstr (m + 1) 0 0) ]
      | Le ->
          if has_pa then [ Cmp (Le, vstr ~pre m n p) ]
          else if has_mi then [ Cmp (Lt, vstr m (n + 1) 0) ]
          else [ Cmp (Lt, vstr (m + 1) 0 0) ]
      | Eq -> bare (ma, mi, pa, pre))

(* a hyphen range's ends widen in opposite directions: the lower end
   zero-fills and the upper end becomes an exclusive bound one place up *)
let hyphen a b =
  let ma, mi, pa, pre = parse_spec a in
  let lo =
    match ma with
    | Star | Absent -> []
    | Num m -> [ Cmp (Ge, vstr ~pre m (num_or 0 mi) (num_or 0 pa)) ]
  in
  let mb, mib, pab, preb = parse_spec b in
  let hi =
    match mb with
    | Star | Absent -> []
    | Num m -> (
        match (mib, pab) with
        | (Star | Absent), _ -> [ Cmp (Lt, vstr (m + 1) 0 0) ]
        | Num n, (Star | Absent) -> [ Cmp (Lt, vstr m (n + 1) 0) ]
        | Num n, Num p -> [ Cmp (Le, vstr ~pre:preb m n p) ])
  in
  match lo @ hi with [] -> [ Any ] | l -> l

let starts p s =
  String.length s >= String.length p && String.sub s 0 (String.length p) = p

let comparators_of (tok : string) : comparator list =
  let drop k = String.sub tok k (String.length tok - k) in
  (* the "v" prefix is allowed on the version part after an operator too,
     so "^v1.2.3" is "^1.2.3"; without this the leading v makes the first
     component unparseable and the whole comparator widens to "*" *)
  let spec k =
    let s = drop k in
    parse_spec
      (if starts "v" s || starts "V" s then String.sub s 1 (String.length s - 1)
       else s)
  in
  if tok = "" then []
  else if starts "^" tok then caret (spec 1)
  else if starts "~>" tok then tilde (spec 2)
  else if starts "~" tok then tilde (spec 1)
  else if starts ">=" tok then ineq Ge (spec 2)
  else if starts "<=" tok then ineq Le (spec 2)
  else if starts "!=" tok then ineq Ne (spec 2)
  else if starts ">" tok then ineq Gt (spec 1)
  else if starts "<" tok then ineq Lt (spec 1)
  else if starts "==" tok then bare (spec 2)
  else if starts "=" tok then bare (spec 1)
  else if starts "v" tok then bare (spec 1)
  else bare (spec 0)

let is_op_only s =
  List.mem s [ "^"; "~"; "~>"; ">"; ">="; "<"; "<="; "="; "=="; "!=" ]

let split_ws s =
  List.filter
    (fun x -> x <> "")
    (String.split_on_char ' '
       (String.map (fun c -> if c = '\t' || c = '\n' then ' ' else c) s))

(* npm lets an operator stand apart from its operand: ">= 1.2.3" *)
let rec glue = function
  | a :: b :: rest when is_op_only a -> glue ((a ^ b) :: rest)
  | a :: rest -> a :: glue rest
  | [] -> []

let parse_set (s : string) : comp_set =
  match glue (split_ws s) with
  | [] -> [ Any ]
  | [ a; "-"; b ] -> hyphen a b
  | toks -> (
      match List.concat_map comparators_of toks with [] -> [ Any ] | l -> l)

(* the || alternatives are the unit the prerelease rule is scoped to, so
   they stay separate all the way into the calculus *)
let split_alts (s : string) : string list =
  let n = String.length s in
  let out = ref [] and buf = Buffer.create 16 in
  let i = ref 0 in
  while !i < n do
    if !i + 1 < n && s.[!i] = '|' && s.[!i + 1] = '|' then (
      out := Buffer.contents buf :: !out;
      Buffer.clear buf;
      i := !i + 2)
    else (
      Buffer.add_char buf s.[!i];
      incr i)
  done;
  out := Buffer.contents buf :: !out;
  List.rev !out

let parse_range (s : string) : range =
  let s = String.trim s in
  if s = "" then [ [ Any ] ] else List.map parse_set (split_alts s)

(* ---- the OCaml mirror of the calculus's evaluation, for the tests ---- *)

let comp_match ct v =
  match ct with
  | Any -> true
  | Cmp (o, c) -> (
      let s = compare v c in
      match o with
      | Ge -> s >= 0
      | Gt -> s > 0
      | Le -> s <= 0
      | Lt -> s < 0
      | Eq -> s = 0
      | Ne -> s <> 0)

let cs_admits cs v =
  (not (is_prerelease v))
  || List.exists
       (function
         | Any -> false | Cmp (_, c) -> is_prerelease c && same_core v c)
       cs

let cs_holds cs v =
  List.for_all (fun ct -> comp_match ct v) cs && cs_admits cs v

let holds (v : string) (rg : range) : bool =
  List.exists (fun cs -> cs_holds cs v) rg

let string_of_op = function
  | Ge -> ">="
  | Gt -> ">"
  | Le -> "<="
  | Lt -> "<"
  | Eq -> "="
  | Ne -> "!="

let string_of_comparator = function
  | Any -> "*"
  | Cmp (o, v) -> string_of_op o ^ v

let string_of_range rg =
  String.concat " || "
    (List.map
       (fun cs -> String.concat " " (List.map string_of_comparator cs))
       rg)
