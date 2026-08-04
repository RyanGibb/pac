(* dpkg version comparison, implemented from Debian Policy 5.6.12.
   [epoch:]upstream_version[-debian_revision]; epoch compared numerically,
   upstream and revision by the dpkg algorithm: alternate maximal non-digit
   and digit parts; non-digit parts compare with '~' before everything
   (including the end of a part) and letters before non-letters; digit parts
   compare numerically.  Untrusted: differential-test against
   `dpkg --compare-versions`. *)

type t = { epoch : int; upstream : string; revision : string }

let parse s =
  let epoch, rest =
    match String.index_opt s ':' with
    | Some i ->
        let e = String.sub s 0 i in
        let ok = e <> "" && String.for_all (fun c -> c >= '0' && c <= '9') e in
        if ok then
          (int_of_string e, String.sub s (i + 1) (String.length s - i - 1))
        else (0, s)
    | None -> (0, s)
  in
  match String.rindex_opt rest '-' with
  | Some i ->
      {
        epoch;
        upstream = String.sub rest 0 i;
        revision = String.sub rest (i + 1) (String.length rest - i - 1);
      }
  | None -> { epoch; upstream = rest; revision = "" }

let is_digit c = c >= '0' && c <= '9'

(* '~' sorts before the end of a part; letters before non-letters. *)
let char_weight c =
  if c = '~' then -1
  else if (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') then Char.code c
  else Char.code c + 256

let compare_nondigit s i s' i' =
  (* Compare the maximal non-digit prefixes starting at i / i'; return
     (cmp, next_i, next_i'). *)
  let len = String.length s and len' = String.length s' in
  let rec go i i' =
    let ended = i >= len || is_digit s.[i] in
    let ended' = i' >= len' || is_digit s'.[i'] in
    if ended && ended' then (0, i, i')
    else
      let w = if ended then 0 else char_weight s.[i] in
      let w' = if ended' then 0 else char_weight s'.[i'] in
      if w <> w' then (compare w w', i, i') else go (i + 1) (i' + 1)
  in
  go i i'

let compare_digit s i s' i' =
  (* Compare the maximal digit prefixes numerically (arbitrary length:
     strip leading zeros, then longer wins, then lexicographic). *)
  let take s i =
    let len = String.length s in
    let j = ref i in
    while !j < len && is_digit s.[!j] do
      incr j
    done;
    (String.sub s i (!j - i), !j)
  in
  let d, ni = take s i and d', ni' = take s' i' in
  let strip x =
    let k = ref 0 in
    let len = String.length x in
    while !k < len && x.[!k] = '0' do
      incr k
    done;
    String.sub x !k (len - !k)
  in
  let d = strip d and d' = strip d' in
  let c =
    if String.length d <> String.length d' then
      compare (String.length d) (String.length d')
    else compare d d'
  in
  (c, ni, ni')

let compare_part s s' =
  let len = String.length s and len' = String.length s' in
  let rec go i i' =
    if i >= len && i' >= len' then 0
    else
      let c, i, i' = compare_nondigit s i s' i' in
      if c <> 0 then c
      else
        let c, i, i' = compare_digit s i s' i' in
        if c <> 0 then c else go i i'
  in
  go 0 0

(* Version strings are compared millions of times during set operations
   (every formula comparison in sorted-list inserts lands here), so cache
   the parse per distinct string. *)
let parse_memo : (string, t) Hashtbl.t = Hashtbl.create 65536

let parse_cached s =
  match Hashtbl.find_opt parse_memo s with
  | Some p -> p
  | None ->
      let p = parse s in
      Hashtbl.replace parse_memo s p;
      p

let compare a b =
  if String.equal a b then 0
  else
    let a = parse_cached a and b = parse_cached b in
    let c = Stdlib.compare a.epoch b.epoch in
    if c <> 0 then c
    else
      let c = compare_part a.upstream b.upstream in
      if c <> 0 then c else compare_part a.revision b.revision

let pp fmt s = Format.pp_print_string fmt s
