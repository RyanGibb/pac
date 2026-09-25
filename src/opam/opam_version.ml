(* opam version comparison, matching opam 2.5.2's OpamVersionCompare: a
   revision is split off at the last '-', and the two halves compare in
   turn with Debian's algorithm (no epoch).  Within a half, maximal
   non-digit and digit parts alternate; non-digit parts compare with '~'
   before everything (including the end of a part) and letters before
   non-letters; digit parts compare numerically.  A half that runs out
   equals the other's remainder if that is all '0's, wherever they fall.
   Untrusted (TCB). *)

let is_digit c = c >= '0' && c <= '9'
let is_alpha c = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')

(* character order within non-digit parts *)
let char_key c =
  if c = '~' then -1 else if is_alpha c then Char.code c else Char.code c + 256

let rec skip_while f s i e = if i < e && f s.[i] then skip_while f s (i + 1) e else i
let skip_zeros = skip_while (fun c -> c = '0')

(* compare s1.[i1, e1) with s2.[i2, e2) in place: PubGrub compares
   versions millions of times per solve, so this must not allocate *)
let rec lexical s1 i1 e1 s2 i2 e2 =
  match (i1 = e1, i2 = e2) with
  | true, true -> 0
  | true, false ->
      let k = skip_zeros s2 i2 e2 in
      if k = e2 then 0 else if s2.[k] = '~' then 1 else -1
  | false, true ->
      let k = skip_zeros s1 i1 e1 in
      if k = e1 then 0 else if s1.[k] = '~' then -1 else 1
  | false, false -> (
      match (is_digit s1.[i1], is_digit s2.[i2]) with
      | true, true ->
          numeric s1 (skip_zeros s1 i1 e1) e1 s2 (skip_zeros s2 i2 e2) e2
      | true, false -> if s2.[i2] = '~' then 1 else -1
      | false, true -> if s1.[i1] = '~' then -1 else 1
      | false, false ->
          let c = compare (char_key s1.[i1]) (char_key s2.[i2]) in
          if c <> 0 then c else lexical s1 (i1 + 1) e1 s2 (i2 + 1) e2)

(* leading zeros already skipped, so the longer run is the larger number *)
and numeric s1 i1 e1 s2 i2 e2 =
  let j1 = skip_while is_digit s1 i1 e1 and j2 = skip_while is_digit s2 i2 e2 in
  let c = compare (j1 - i1) (j2 - i2) in
  if c <> 0 then c
  else
    let rec digits d =
      if i1 + d = j1 then lexical s1 j1 e1 s2 j2 e2
      else
        let c = Char.compare s1.[i1 + d] s2.[i2 + d] in
        if c <> 0 then c else digits (d + 1)
    in
    digits 0

(* the revision's '-', or the length when there is none *)
let last_dash s =
  let rec go i = if i < 0 then String.length s else if s.[i] = '-' then i else go (i - 1) in
  go (String.length s - 1)

let sign c = if c < 0 then -1 else if c > 0 then 1 else 0

let compare v1 v2 =
  if String.equal v1 v2 then 0
  else
    let n1 = String.length v1 and n2 = String.length v2 in
    let r1 = last_dash v1 and r2 = last_dash v2 in
    let c = lexical v1 0 r1 v2 0 r2 in
    if c <> 0 then sign c
    else sign (lexical v1 (min n1 (r1 + 1)) n1 v2 (min n2 (r2 + 1)) n2)

let equal a b = compare a b = 0
