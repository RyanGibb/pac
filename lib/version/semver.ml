let is_digit c = c >= '0' && c <= '9'

(* the end of the digit run at i *)
let digits_from s i =
  let n = String.length s in
  let rec go j = if j < n && is_digit s.[j] then go (j + 1) else j in
  go i

type t = {
  major : int;
  minor : int;
  patch : int;
  pre : string list;
  build : string list;
}

(* leading zeros carry no value; one is kept of an all-zero run *)
let strip0 s =
  let n = String.length s in
  let i = ref 0 in
  while !i < n - 1 && s.[!i] = '0' do
    incr i
  done;
  String.sub s !i (n - !i)

(* a run past 18 digits, which a 63-bit int cannot hold, is saturated
   rather than overflowing int_of_string: the semver crate reads a
   component as a u64 and node-semver refuses one past MAX_SAFE_INTEGER,
   so no real version comes near it *)
let int_of_digits s =
  let s = strip0 s in
  if s = "" then 0
  else if String.length s > 18 then max_int
  else int_of_string s

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
        let j = digits_from s i in
        if j > i then Some j else None
      in
      let dot i = if i < n && s.[i] = '.' then Some (i + 1) else None in
      let ( >>= ) = Option.bind in
      let letter c = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') in
      match digits 0 >>= dot >>= digits >>= dot >>= digits with
      | Some i when i < n && letter s.[i] ->
          (String.sub s 0 i, String.sub s i (n - i))
      | _ -> (s, ""))

let ids s = if s = "" then [] else String.split_on_char '.' s

let of_parts split (s : string) : t =
  let s, build = strip_build s in
  let core, pre = split s in
  let num s = int_of_digits (String.sub s 0 (digits_from s 0)) in
  let parts = String.split_on_char '.' core in
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
      let j = digits_from s 0 in
      if j = 0 then Star else Num (int_of_digits (String.sub s 0 j))

let num_or d = function Num n -> n | Star | Absent -> d

let partial_of split (s : string) =
  let s, _ = strip_build s in
  let core, pre = split s in
  let parts = String.split_on_char '.' core in
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

(* A reading of version strings: how one splits off its prerelease, and
   how many distinct strings a run meets, which sizes the table of parses
   the comparator shares. *)
module Reading (R : sig
  val split : string -> string * string
  val size : int
end) =
struct
  let parse_fresh = of_parts R.split
  let parse = memo R.size parse_fresh
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

  let parse_partial = partial_of R.split
end

(* The semver crate's reading: a prerelease follows a hyphen and nothing
   else.  Cargo and npm differ only in how a string becomes a version, so
   each reading is a module of its own rather than a flag. *)
module Strict = struct
  include Reading (struct
    let split = split_hyphen

    (* compare sits under every range operation a solve makes, and parsing
       afresh there was most of a large cargo solve's time; a run meets a
       few thousand distinct version strings (about 3,400 at most), though
       a large query loads tens of thousands of versions *)
    let size = 65536
  end)

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

  (* no build identifier holds a '*', so no version carries this one *)
  let top_build = "*"
  let top v = fst (strip_build v) ^ "+" ^ top_build

  (* The semver crate's BuildMetadata order (impls.rs), which Version's
     derived Ord reaches once the precedence ties: identifier by identifier,
     a numeric one below an alphanumeric one, numeric ones by value and then
     by length (0 < 00 < 1), and a list below its extensions.  No build
     metadata splits into one empty identifier, which that order puts below
     every other; [top_build] sits above every one. *)
  let cmp_build a b =
    let value x =
      let n = String.length x in
      let i = ref 0 in
      while !i < n && x.[!i] = '0' do
        incr i
      done;
      String.sub x !i (n - !i)
    in
    let cmp_ident x y =
      match (String.for_all is_digit x, String.for_all is_digit y) with
      | true, true ->
          let vx = value x and vy = value y in
          let c = Int.compare (String.length vx) (String.length vy) in
          if c <> 0 then c
          else
            let c = String.compare vx vy in
            if c <> 0 then c
            else Int.compare (String.length x) (String.length y)
      | true, false -> -1
      | false, true -> 1
      | false, false -> String.compare x y
    in
    let rec go xs ys =
      match (xs, ys) with
      | [], [] -> 0
      | _ :: _, [] -> 1
      | [], _ :: _ -> -1
      | x :: xs, y :: ys ->
          let c = cmp_ident x y in
          if c <> 0 then c else go xs ys
    in
    match (a = top_build, b = top_build) with
    | true, true -> 0
    | true, false -> 1
    | false, true -> -1
    | false, false ->
        go (String.split_on_char '.' a) (String.split_on_char '.' b)

  let tiebreak c a b =
    if c <> 0 then c else cmp_build (snd (strip_build a)) (snd (strip_build b))

  (* the order below, off the parsed versions *)
  let compare_parsed a b = tiebreak (precedence (parse a) (parse b)) a b

  (* The semver crate's Version order, cargo's: precedence, and then the
     build metadata, since cargo keeps two versions that differ only there
     apart (PackageId's equality is Version's) and sorts its candidates by
     this order (VersionPreferences::sort_summaries).  The release cores are
     compared off the strings themselves, a field at a time as parse reads
     them and no further than the first that differs: even a table of
     parsed versions costs a hash of the string there.  Sound only for the
     strict reading, where the core ends at the first '-' or '+'. *)
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
        else if String.equal a b then 0
        else
          tiebreak
            (if plain a && plain b then 0 else precedence (parse a) (parse b))
            a b
end

(* node-semver's loose reading, which npm passes for every version and
   range it reads. *)
module Loose = struct
  include Reading (struct
    let split = split_hyphen_loose

    (* the comparator runs on every candidate at every gate, so parses are
       shared *)
    let size = 4096
  end)

  let compare (a : string) (b : string) : int =
    if a == b || String.equal a b then 0 else precedence (parse a) (parse b)
end
