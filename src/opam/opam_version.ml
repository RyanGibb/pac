(* opam version comparison, implemented from the opam manual's version
   ordering: Debian's algorithm over the whole string, with no epoch or
   revision treatment.  Alternate maximal non-digit and digit parts;
   non-digit parts compare with '~' before everything (including the end
   of a part) and letters before non-letters; digit parts compare
   numerically.  Untrusted (TCB). *)

let is_digit c = c >= '0' && c <= '9'
let is_alpha c = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')

(* character order within non-digit parts *)
let char_key c =
  if c = '~' then -1 else if is_alpha c then Char.code c else Char.code c + 256

(* compare non-digit prefixes; a part that ends is smaller than any
   character except '~', which sorts below end-of-part *)
let rec cmp_nondigit s1 i1 s2 i2 =
  let e1 = i1 >= String.length s1 || is_digit s1.[i1] in
  let e2 = i2 >= String.length s2 || is_digit s2.[i2] in
  match (e1, e2) with
  | true, true -> (0, i1, i2)
  | true, false -> if s2.[i2] = '~' then (1, i1, i2) else (-1, i1, i2)
  | false, true -> if s1.[i1] = '~' then (-1, i1, i2) else (1, i1, i2)
  | false, false ->
      let c = compare (char_key s1.[i1]) (char_key s2.[i2]) in
      if c <> 0 then (c, i1, i2) else cmp_nondigit s1 (i1 + 1) s2 (i2 + 1)

let digit_run s i =
  let n = String.length s in
  let j = ref i in
  while !j < n && is_digit s.[!j] do
    incr j
  done;
  (String.sub s i (!j - i), !j)

let cmp_digit s1 i1 s2 i2 =
  let d1, j1 = digit_run s1 i1 and d2, j2 = digit_run s2 i2 in
  let strip s =
    let k = ref 0 in
    while !k < String.length s - 1 && s.[!k] = '0' do
      incr k
    done;
    String.sub s !k (String.length s - !k)
  in
  let d1 = strip d1 and d2 = strip d2 in
  let c = compare (String.length d1) (String.length d2) in
  let c = if c <> 0 then c else String.compare d1 d2 in
  (c, j1, j2)

let compare v1 v2 =
  let rec go i1 i2 =
    if i1 >= String.length v1 && i2 >= String.length v2 then 0
    else
      let c, i1, i2 = cmp_nondigit v1 i1 v2 i2 in
      if c <> 0 then c
      else if i1 >= String.length v1 && i2 >= String.length v2 then 0
      else
        let c, i1, i2 = cmp_digit v1 i1 v2 i2 in
        if c <> 0 then c else go i1 i2
  in
  go 0 0

let equal a b = compare a b = 0
