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

(* A comparator names a precedence, which the semver crate matches on alone
   (matches_exact and its siblings, eval.rs), while [compare] also orders
   build metadata.  So each bound becomes the version of that precedence the
   order puts at the right end: the build-less one, which is the least, for
   >= and <, and the greatest, a build no version carries, for > and <=;
   = is the two together. *)
let bounds (r : req) : req =
  List.concat_map
    (function
      | ((Ge | Lt), _) as c -> [ c ]
      | ((Gt | Le) as o), v -> [ (o, V.Strict.top v) ]
      | Eq, v -> [ (Ge, v); (Le, V.Strict.top v) ])
    r

let comparator (s : string) : req =
  let s = String.trim s in
  if s = "" then []
  else
    let starts p = String.starts_with ~prefix:p s in
    let drop k = String.trim (String.sub s k (String.length s - k)) in
    bounds
      (if starts "^" then caret (parse_spec (drop 1))
       else if starts "~" then tilde (parse_spec (drop 1))
       else if starts ">=" then ineq Ge (parse_spec (drop 2))
       else if starts "<=" then ineq Le (parse_spec (drop 2))
       else if starts ">" then ineq Gt (parse_spec (drop 1))
       else if starts "<" then ineq Lt (parse_spec (drop 1))
       else if starts "==" then exact (parse_spec (drop 2))
       else if starts "=" then exact (parse_spec (drop 1))
       else wildcard (parse_spec s))

let parse_req (s : string) : req =
  List.concat_map comparator (String.split_on_char ',' s)

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

(* VersionReq::from_str of the semver crate cargo 1.97 links.  The index
   is cargo-validated, so this runs on the root alone; without it
   parse_req would read a malformed requirement as "*".
   Stricter than parse_req: no "==", a wildcard only in trailing
   components or as the whole requirement, no leading zeros, and a comma
   between comparators. *)
let req_ok (s : string) : bool =
  let n = String.length s and i = ref 0 in
  let at c = !i < n && s.[!i] = c in
  let skip c =
    at c
    &&
    (incr i;
     true)
  in
  let spaces () =
    while at ' ' do
      incr i
    done
  in
  let digit c = c >= '0' && c <= '9' in
  let wild () =
    !i < n
    && (match s.[!i] with '*' | 'x' | 'X' -> true | _ -> false)
    &&
    (incr i;
     true)
  in
  let span ok =
    let j = !i in
    while !i < n && ok s.[!i] do
      incr i
    done;
    String.sub s j (!i - j)
  in
  let num () =
    let d = span digit in
    d <> "" && (d = "0" || d.[0] <> '0')
  in
  let ident ~pre =
    let d =
      span (fun c ->
          digit c || (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c = '-')
    in
    d <> ""
    && ((not pre) || (not (String.for_all digit d)) || d = "0" || d.[0] <> '0')
  in
  let rec dotted ~pre = ident ~pre && ((not (skip '.')) || dotted ~pre) in
  let op () =
    ignore
      (List.exists
         (fun o ->
           String.length o <= n - !i
           && String.sub s !i (String.length o) = o
           &&
           (i := !i + String.length o;
            true))
         [ ">="; "<="; ">"; "<"; "="; "~"; "^" ])
  in
  let comparator () =
    op ();
    spaces ();
    num ()
    && ((not (skip '.'))
       ||
       if wild () then (not (skip '.')) || wild ()
       else
         num ()
         && ((not (skip '.'))
            || wild ()
            || num ()
               && ((not (skip '-')) || dotted ~pre:true)
               && ((not (skip '+')) || dotted ~pre:false)))
  in
  let rec comparators () =
    comparator ()
    &&
    (spaces ();
     !i = n
     || skip ','
        &&
        (spaces ();
         comparators ()))
  in
  spaces ();
  if wild () then (
    spaces ();
    !i = n)
  else comparators ()

(* a component, which the semver crate reads as a u64 *)
let num_ok d =
  d <> ""
  && String.for_all (fun c -> c >= '0' && c <= '9') d
  && (d = "0" || d.[0] <> '0')
  && (String.length d < 20
     || (String.length d = 20 && d <= "18446744073709551615"))

(* Version::from_str of the semver crate *)
let version_ok (s : string) : bool =
  let ident ~pre d =
    d <> ""
    && String.for_all
         (fun c ->
           (c >= '0' && c <= '9')
           || (c >= 'a' && c <= 'z')
           || (c >= 'A' && c <= 'Z')
           || c = '-')
         d
    && ((not pre)
       || (not (String.for_all (fun c -> c >= '0' && c <= '9') d))
       || d = "0"
       || d.[0] <> '0')
  in
  let dotted ~pre s = List.for_all (ident ~pre) (String.split_on_char '.' s) in
  let cut c s =
    match String.index_opt s c with
    | Some i ->
        (String.sub s 0 i, Some (String.sub s (i + 1) (String.length s - i - 1)))
    | None -> (s, None)
  in
  let s, build = cut '+' s in
  let core, pre = cut '-' s in
  (match String.split_on_char '.' core with
    | [ a; b; c ] -> num_ok a && num_ok b && num_ok c
    | _ -> false)
  && Option.fold ~none:true ~some:(dotted ~pre:true) pre
  && Option.fold ~none:true ~some:(dotted ~pre:false) build

(* PartialVersion::from_str (cargo-util-schemas): a whole semver version,
   or one to three numbers read as a caret requirement written without its
   '^'.  A rust-version is one with neither prerelease nor build
   (RustVersion::try_from); the toolchain rustc reports may carry either. *)
let partial_ok ~(rust : bool) (s : string) : bool =
  if String.contains s '-' || String.contains s '+' then
    (not rust) && version_ok s
  else
    let parts = String.split_on_char '.' s in
    List.length parts <= 3 && List.for_all num_ok parts
