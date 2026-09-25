(* Cargo's requirement syntax over the semver crate's strict reading of
   a version (lib/version/semver.ml), implemented from the
   specifications.  Trusted (TCB). *)

module V = Version.Semver

type t = V.t = {
  major : int;
  minor : int;
  patch : int;
  pre : string list;
  build : string list;
}

let parse = V.Strict.parse
let compare = V.Strict.compare
let compare_parsed = V.Strict.compare_parsed
let is_prerelease = V.Strict.is_prerelease
let same_core = V.Strict.same_core

type op = Ge | Gt | Le | Lt | Eq
type req = (op * string) list (* a conjunction; [] is any version *)
type comp = V.comp = Num of int | Star | Absent

let vstr = V.vstr
let parse_spec = V.Strict.parse_partial
let num_or = V.num_or

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
let split_on c s = String.split_on_char c s

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

let admits (v : string) (r : req) : bool = V.Strict.admits v (List.map snd r)

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
