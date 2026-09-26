module V = Version.Semver

let compare = V.Loose.compare
let is_prerelease = V.Loose.is_prerelease
let same_core = V.Loose.same_core

type op = Ge | Gt | Le | Lt | Eq
type comparator = Any | Cmp of op * string
type comp_set = comparator list (* whitespace is conjunction *)
type range = comp_set list (* || is disjunction *)
type comp = V.comp = Num of int | Star | Absent

let vstr = V.vstr
let parse_spec = V.Loose.parse_partial
let num_or = V.num_or

(* caret keeps the leftmost non-zero component: ^0.2.3 is <0.3.0 and
   ^0.0.3 is <0.0.4, which is why it cannot be written as a tilde.  [z]
   and [u], here and in the bounds below, are the prerelease semver gives
   a bound it derives, lower and upper: "0" under includePrerelease, where
   a prerelease is ordered rather than refused and -0 then decides it at
   the bound, and "" otherwise, which admits the same versions as semver's
   -0 would *)
let caret ~z ~u (ma, mi, pa, pre) =
  match ma with
  | Star | Absent -> [ Any ]
  | Num m ->
      let hi =
        match (mi, pa) with
        | (Star | Absent), _ -> vstr ~pre:u (m + 1) 0 0
        | Num n, (Star | Absent) ->
            if m > 0 then vstr ~pre:u (m + 1) 0 0 else vstr ~pre:u 0 (n + 1) 0
        | Num n, Num p ->
            if m > 0 then vstr ~pre:u (m + 1) 0 0
            else if n > 0 then vstr ~pre:u 0 (n + 1) 0
            else vstr ~pre:u 0 0 (p + 1)
      in
      let pre = match pa with Num _ -> pre | Star | Absent -> z in
      [ Cmp (Ge, vstr ~pre m (num_or 0 mi) (num_or 0 pa)); Cmp (Lt, hi) ]

let tilde ~u (ma, mi, pa, pre) =
  match ma with
  | Star | Absent -> [ Any ]
  | Num m -> (
      match mi with
      | Star | Absent ->
          [ Cmp (Ge, vstr m 0 0); Cmp (Lt, vstr ~pre:u (m + 1) 0 0) ]
      | Num n ->
          [
            Cmp (Ge, vstr ~pre m n (num_or 0 pa));
            Cmp (Lt, vstr ~pre:u m (n + 1) 0);
          ])

(* a bare or =-prefixed spec: fully given it is an equality, and each
   component left off widens it by one place *)
let bare ~z ~u (ma, mi, pa, pre) =
  match (ma, mi, pa) with
  | (Star | Absent), _, _ -> [ Any ]
  | Num m, (Star | Absent), _ ->
      [ Cmp (Ge, vstr ~pre:z m 0 0); Cmp (Lt, vstr ~pre:u (m + 1) 0 0) ]
  | Num m, Num n, (Star | Absent) ->
      [ Cmp (Ge, vstr ~pre:z m n 0); Cmp (Lt, vstr ~pre:u m (n + 1) 0) ]
  | Num m, Num n, Num p -> [ Cmp (Eq, vstr ~pre m n p) ]

let ineq ~z ~u op (ma, mi, pa, pre) =
  match ma with
  | Star | Absent -> (
      (* >x and <x admit nothing; >=x and <=x admit everything *)
      match op with
      | Ge | Le -> [ Any ]
      | _ -> [ Cmp (Lt, vstr ~pre:u 0 0 0) ])
  | Num m -> (
      let n = num_or 0 mi and p = num_or 0 pa in
      let has_mi = match mi with Num _ -> true | _ -> false in
      let has_pa = match pa with Num _ -> true | _ -> false in
      let lo = if has_pa then pre else z and up = if has_pa then pre else u in
      match op with
      | Ge -> [ Cmp (Ge, vstr ~pre:lo m n p) ]
      | Lt -> [ Cmp (Lt, vstr ~pre:up m n p) ]
      | Gt ->
          if has_pa then [ Cmp (Gt, vstr ~pre m n p) ]
          else if has_mi then [ Cmp (Ge, vstr ~pre:z m (n + 1) 0) ]
          else [ Cmp (Ge, vstr ~pre:z (m + 1) 0 0) ]
      | Le ->
          if has_pa then [ Cmp (Le, vstr ~pre m n p) ]
          else if has_mi then [ Cmp (Lt, vstr ~pre:u m (n + 1) 0) ]
          else [ Cmp (Lt, vstr ~pre:u (m + 1) 0 0) ]
      | Eq -> bare ~z ~u (ma, mi, pa, pre))

(* a hyphen range's ends widen in opposite directions: the lower end
   zero-fills and the upper end becomes an exclusive bound one place up *)
let hyphen ~z ~u a b =
  let ma, mi, pa, pre = parse_spec a in
  let lo =
    match ma with
    | Star | Absent -> []
    | Num m ->
        let pre = if pre = "" then z else pre in
        [ Cmp (Ge, vstr ~pre m (num_or 0 mi) (num_or 0 pa)) ]
  in
  let mb, mib, pab, preb = parse_spec b in
  let hi =
    match mb with
    | Star | Absent -> []
    | Num m -> (
        match (mib, pab) with
        | (Star | Absent), _ -> [ Cmp (Lt, vstr ~pre:u (m + 1) 0 0) ]
        | Num n, (Star | Absent) -> [ Cmp (Lt, vstr ~pre:u m (n + 1) 0) ]
        | Num n, Num p when preb = "" && u <> "" ->
            [ Cmp (Lt, vstr ~pre:u m n (p + 1)) ]
        | Num n, Num p -> [ Cmp (Le, vstr ~pre:preb m n p) ])
  in
  match lo @ hi with [] -> [ Any ] | l -> l

let is_digit c = c >= '0' && c <= '9'

let is_ident c =
  (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || is_digit c || c = '-'

let rec skip_while f s i =
  if i < String.length s && f s.[i] then skip_while f s (i + 1) else i

(* dot-separated runs of [is_ident] from i, as semver's prerelease and
   build identifiers are: where they end, or None if there is none *)
let idents s i =
  let rec go i =
    let j = skip_while is_ident s i in
    if j = i then None
    else if j < String.length s && s.[j] = '.' then
      match go (j + 1) with Some k -> Some k | None -> Some j
    else Some j
  in
  go i

(* the [v=\s]* semver allows before a version, after any operator *)
let strip_v s =
  let i = skip_while (fun c -> c = 'v' || c = '=') s 0 in
  String.sub s i (String.length s - i)

(* XRANGEPLAINLOOSE at i (internal/re.js): one to three parts, each
   digits, x, X or *, and after three a prerelease, its hyphen optional,
   and a build *)
let xrange_plain s i =
  let n = String.length s in
  let part i =
    if i < n && (s.[i] = 'x' || s.[i] = 'X' || s.[i] = '*') then Some (i + 1)
    else
      let j = skip_while is_digit s i in
      if j > i then Some j else None
  in
  let dotted k i =
    match part i with
    | None -> false
    | Some j -> j = n || (s.[j] = '.' && k (j + 1))
  in
  let tail i =
    let i = if i < n && s.[i] <> '+' then idents s i else Some i in
    match i with
    | None -> false
    | Some i -> i = n || (s.[i] = '+' && idents s (i + 1) = Some n)
  in
  dotted
    (dotted (fun i -> match part i with Some j -> tail j | None -> false))
    (skip_while (fun c -> c = 'v' || c = '=') s i)

(* A comparator node-semver keeps in a loose range: parseComparator strips
   the first build it finds, and what then matches none of its caret,
   tilde and x-range grammars is thrown out of the set. *)
let comparator_ok (tok : string) =
  let n = String.length tok in
  let tok =
    let rec plus i =
      match String.index_from_opt tok i '+' with
      | Some p when p + 1 < n && is_ident tok.[p + 1] -> (
          match idents tok (p + 1) with
          | Some e -> String.sub tok 0 p ^ String.sub tok e (n - e)
          | None -> tok)
      | Some p -> plus (p + 1)
      | None -> tok
    in
    plus 0
  in
  let starts p = String.starts_with ~prefix:p tok in
  if starts "^" then xrange_plain tok 1
  else if starts "~>" then xrange_plain tok 2
  else if starts "~" then xrange_plain tok 1
  else xrange_plain tok (if starts "<" || starts ">" then 1 else 0)

let comparators_of ~z ~u (tok : string) : comparator list =
  let spec k =
    parse_spec (strip_v (String.sub tok k (String.length tok - k)))
  in
  let starts p = String.starts_with ~prefix:p tok in
  if starts "^" then caret ~z ~u (spec 1)
  else if starts "~>" then tilde ~u (spec 2)
  else if starts "~" then tilde ~u (spec 1)
  else if starts ">=" then ineq ~z ~u Ge (spec 2)
  else if starts "<=" then ineq ~z ~u Le (spec 2)
  else if starts ">" then ineq ~z ~u Gt (spec 1)
  else if starts "<" then ineq ~z ~u Lt (spec 1)
  else bare ~z ~u (spec 0)

let is_op_only s =
  List.mem s [ "^"; "~"; "~>"; ">"; ">="; "<"; "<="; "="; "==" ]

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

(* A set whose every comparator is thrown out is thrown out itself; an
   empty one is "*". *)
let parse_set ~z ~u (s : string) : comp_set option =
  match glue (split_ws s) with
  | [] -> Some [ Any ]
  | [ a; "-"; b ] when xrange_plain a 0 && xrange_plain b 0 ->
      Some (hyphen ~z ~u (strip_v a) (strip_v b))
  | toks -> (
      match List.filter comparator_ok toks with
      | [] -> None
      | toks -> Some (List.concat_map (comparators_of ~z ~u) toks))

(* the || alternatives are the unit the prerelease rule is scoped to, so
   they stay separate all the way into the calculus *)
let split_alts (s : string) : string list =
  let n = String.length s in
  let rec go start i acc =
    if i >= n then List.rev (String.sub s start (n - start) :: acc)
    else if i + 1 < n && s.[i] = '|' && s.[i + 1] = '|' then
      go (i + 2) (i + 2) (String.sub s start (i - start) :: acc)
    else go start (i + 1) acc
  in
  go 0 0 []

(* None where node-semver's Range refuses the string, every set having
   been thrown out, and npa then reads the spec as a dist-tag.
   include_prerelease reads the range as semver's includePrerelease does,
   for [holds_pre]. *)
let parse_range_opt ?(include_prerelease = false) (s : string) : range option =
  let z = if include_prerelease then "0" else "" in
  match List.filter_map (parse_set ~z ~u:z) (split_alts s) with
  | [] -> None
  | rg -> Some rg

(* satisfies catches the TypeError of a range semver refuses and answers
   false, so such a range, with no set at all, matches nothing *)
let parse_range ?include_prerelease s =
  Option.value ~default:[] (parse_range_opt ?include_prerelease s)

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
      | Eq -> s = 0)

let cs_admits cs v =
  V.Loose.admits v
    (List.filter_map (function Any -> None | Cmp (_, c) -> Some c) cs)

let cs_holds cs v =
  List.for_all (fun ct -> comp_match ct v) cs && cs_admits cs v

(* for testing the grammar from OCaml: a dependency range is evaluated
   against the real version set by the calculus, not here *)
let holds (v : string) (rg : range) : bool =
  List.exists (fun cs -> cs_holds cs v) rg

(* semver's includePrerelease, which checkEngine passes and a dependency
   range never does: cs_admits is dropped, so a prerelease version is
   ordered by an ordinary comparator rather than refused by one that
   names no prerelease.  It matters only for a prerelease host -- an
   engines range is matched against the running node or npm, not against
   a published version -- and the range must be parsed with
   ~include_prerelease for its -0 bounds. *)
let holds_pre (v : string) (rg : range) : bool =
  List.exists (fun cs -> List.for_all (fun ct -> comp_match ct v) cs) rg

let string_of_op = function
  | Ge -> ">="
  | Gt -> ">"
  | Le -> "<="
  | Lt -> "<"
  | Eq -> "="

let string_of_comparator = function
  | Any -> "*"
  | Cmp (o, v) -> string_of_op o ^ v

let string_of_range rg =
  String.concat " || "
    (List.map
       (fun cs -> String.concat " " (List.map string_of_comparator cs))
       rg)
