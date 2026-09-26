let is_digit c = c >= '0' && c <= '9'

type t = {
  major : int;
  minor : int;
  patch : int;
  pre : string list;
  build : string list;
}

(* leading zeros carry no value, and a run past 18 digits, which a 63-bit
   int cannot hold, is saturated rather than overflowing int_of_string:
   the semver crate reads a component as a u64 and node-semver refuses
   one past MAX_SAFE_INTEGER, so no real version comes near it *)
let strip0 s =
  let n = String.length s in
  let i = ref 0 in
  while !i < n - 1 && s.[!i] = '0' do
    incr i
  done;
  String.sub s !i (n - !i)

let int_of_digits s =
  let s = strip0 s in
  if s = "" then 0
  else if String.length s > 18 then max_int
  else int_of_string s

let split_on c s = String.split_on_char c s

let strip_build s =
  match String.index_opt s '+' with
  | Some i -> (String.sub s 0 i, String.sub s (i + 1) (String.length s - i - 1))
  | None -> (s, "")

let split_hyphen s =
  match String.index_opt s '-' with
  | Some i -> (String.sub s 0 i, String.sub s (i + 1) (String.length s - i - 1))
  | None -> (s, "")

(* node-semver's loose grammar (PRERELEASELOOSE in internal/re.js) makes
   the hyphen before a prerelease optional: 2.0.14rc1 is 2.0.14-rc1.
   Only after a full major.minor.patch, and only when a letter follows the
   patch digits, so 1.2.x and 1.2.3.4 keep their readings. *)
let split_hyphen_loose (s : string) : string * string =
  match String.index_opt s '-' with
  | Some _ -> split_hyphen s
  | None -> (
      let n = String.length s in
      let digits i =
        let j = ref i in
        while !j < n && is_digit s.[!j] do
          incr j
        done;
        if !j > i then Some !j else None
      in
      let dot i = if i < n && s.[i] = '.' then Some (i + 1) else None in
      let ( >>= ) = Option.bind in
      let letter c = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') in
      match digits 0 >>= dot >>= digits >>= dot >>= digits with
      | Some i when i < n && letter s.[i] ->
          (String.sub s 0 i, String.sub s i (n - i))
      | _ -> (s, ""))

let ids s = if s = "" then [] else split_on '.' s

let of_parts split (s : string) : t =
  let s, build = strip_build s in
  let core, pre = split s in
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
    pre = ids pre;
    build = ids build;
  }

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

(* semver.org 2.0.0 section 11; build metadata takes no part *)
let precedence (x : t) (y : t) : int =
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

let same_core_parsed (x : t) (y : t) =
  x.major = y.major && x.minor = y.minor && x.patch = y.patch

(* A component of a partial version, as a range names one: 1.2.x and 1.2
   are not versions but bounds to widen. *)
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

let num_or d = function Num n -> n | Star | Absent -> d

let partial_of split (s : string) =
  let s, _ = strip_build s in
  let core, pre = split s in
  let parts = split_on '.' core in
  let get i =
    match List.nth_opt parts i with Some x -> comp_of x | None -> Absent
  in
  (get 0, get 1, get 2, pre)

let vstr ?(pre = "") maj min pat =
  Printf.sprintf "%d.%d.%d%s" maj min pat (if pre = "" then "" else "-" ^ pre)

let memo size f =
  let tbl : (string, t) Hashtbl.t = Hashtbl.create size in
  fun s ->
    match Hashtbl.find_opt tbl s with
    | Some p -> p
    | None ->
        let p = f s in
        Hashtbl.add tbl s p;
        p

(* The semver crate's reading: a prerelease follows a hyphen and nothing
   else.  Cargo and npm differ only in how a string becomes a version, so
   each reading is a module of its own rather than a flag. *)
module Strict = struct
  let parse_fresh = of_parts split_hyphen

  (* compare sits under every range operation a solve makes, and parsing
     afresh there was most of a large cargo solve's time; a run meets a few
     thousand distinct version strings (about 3,400 at most), though a large
     query loads tens of thousands of versions *)
  let parse = memo 65536 parse_fresh
  let compare_parsed a b = precedence (parse a) (parse b)

  (* The release cores are compared off the strings themselves, a field at
     a time as parse reads them and no further than the first that
     differs: even a table of parsed versions costs a hash of the string
     there.  Only equal cores leave the prerelease to decide.  Sound only
     for the strict reading, where the core ends at the first '-' or '+'. *)

  (* parse's num of the part at !i, leaving !i at the next part, or at the
     end once the core has ended *)
  let field s n i =
    let j = ref !i in
    while !j < n && s.[!j] = '0' do
      incr j
    done;
    let v = ref 0 and d = ref 0 in
    while !j < n && is_digit s.[!j] do
      if !d < 18 then v := (!v * 10) + (Char.code s.[!j] - 48);
      incr d;
      incr j
    done;
    while !j < n && s.[!j] <> '.' && s.[!j] <> '-' && s.[!j] <> '+' do
      incr j
    done;
    i := if !j < n && s.[!j] = '.' then !j + 1 else n;
    if !d > 18 then max_int else !v

  (* no '-' ahead of the build metadata, so no prerelease *)
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

  let is_prerelease v = (parse v).pre <> []
  let same_core a b = same_core_parsed (parse a) (parse b)

  (* A requirement admits a prerelease candidate only when one of its own
     comparators names a prerelease at the same release core: the semver
     crate's pre_is_compatible (eval.rs) and node-semver's testSet
     (classes/range.js).  [bounds] are the versions a comparator set
     names. *)
  let admits v bounds =
    (not (is_prerelease v))
    || List.exists (fun c -> is_prerelease c && same_core v c) bounds

  let parse_partial = partial_of split_hyphen
end

(* node-semver's loose reading, which npm passes for every version and
   range it reads. *)
module Loose = struct
  let parse_fresh = of_parts split_hyphen_loose

  (* the comparator runs on every candidate at every gate, so parses are
     shared *)
  let parse = memo 4096 parse_fresh

  let compare (a : string) (b : string) : int =
    if a == b || String.equal a b then 0 else precedence (parse a) (parse b)

  let is_prerelease v = (parse v).pre <> []
  let same_core a b = same_core_parsed (parse a) (parse b)

  let admits v bounds =
    (not (is_prerelease v))
    || List.exists (fun c -> is_prerelease c && same_core v c) bounds

  let parse_partial = partial_of split_hyphen_loose
end
