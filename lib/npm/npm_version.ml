(* npm's range grammar over node-semver's loose reading of a version
   (lib/version/semver.ml), implemented from the specifications.
   parse_range only *parses*: evaluation against the real version set is
   the extracted calculus's job.  The [holds] mirror at the bottom exists
   so the grammar can be tested from OCaml; its [holds_pre] also decides
   engines in npm_solve, and that use is trusted.  Trusted (TCB). *)

module V = Version.Semver

let compare = V.Loose.compare
let is_prerelease = V.Loose.is_prerelease
let same_core = V.Loose.same_core

type op = Ge | Gt | Le | Lt | Eq | Ne
type comparator = Any | Cmp of op * string
type comp_set = comparator list (* whitespace is conjunction *)
type range = comp_set list (* || is disjunction *)
type comp = V.comp = Num of int | Star | Absent

let vstr = V.vstr
let parse_spec = V.Loose.parse_partial
let num_or = V.num_or

(* [z] and [u] are the prerelease semver gives a bound it derives, lower
   and upper: "0" under includePrerelease, where a prerelease is ordered
   rather than refused and -0 then decides it at the bound, and ""
   otherwise, which admits the same versions as semver's -0 would *)

(* caret keeps the leftmost non-zero component: ^0.2.3 is <0.3.0 and
   ^0.0.3 is <0.0.4, which is why it cannot be written as a tilde *)
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
      | Ne -> [ Cmp (Ne, vstr ~pre m n p) ]
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

let starts p s =
  String.length s >= String.length p && String.sub s 0 (String.length p) = p

let comparators_of ~z ~u (tok : string) : comparator list =
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
  else if starts "^" tok then caret ~z ~u (spec 1)
  else if starts "~>" tok then tilde ~u (spec 2)
  else if starts "~" tok then tilde ~u (spec 1)
  else if starts ">=" tok then ineq ~z ~u Ge (spec 2)
  else if starts "<=" tok then ineq ~z ~u Le (spec 2)
  else if starts ">" tok then ineq ~z ~u Gt (spec 1)
  else if starts "<" tok then ineq ~z ~u Lt (spec 1)
  else if starts "==" tok then bare ~z ~u (spec 2)
  else if starts "=" tok then bare ~z ~u (spec 1)
  else if starts "v" tok then bare ~z ~u (spec 1)
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

let parse_set ~z ~u (s : string) : comp_set =
  match glue (split_ws s) with
  | [] -> [ Any ]
  | [ a; "-"; b ] -> hyphen ~z ~u a b
  | toks -> (
      match List.concat_map (comparators_of ~z ~u) toks with
      | [] -> [ Any ]
      | l -> l)

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

(* include_prerelease reads the range as semver's includePrerelease does,
   for [holds_pre] *)
let parse_range ?(include_prerelease = false) (s : string) : range =
  let z = if include_prerelease then "0" else "" in
  let s = String.trim s in
  if s = "" then [ [ Any ] ]
  else List.map (parse_set ~z ~u:z) (split_alts s)

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
  V.Loose.admits v
    (List.filter_map (function Any -> None | Cmp (_, c) -> Some c) cs)

let cs_holds cs v =
  List.for_all (fun ct -> comp_match ct v) cs && cs_admits cs v

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
  | Ne -> "!="

let string_of_comparator = function
  | Any -> "*"
  | Cmp (o, v) -> string_of_op o ^ v

let string_of_range rg =
  String.concat " || "
    (List.map
       (fun cs -> String.concat " " (List.map string_of_comparator cs))
       rg)
