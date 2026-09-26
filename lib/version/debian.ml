let is_digit c = c >= '0' && c <= '9'
let is_alpha c = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')

(* verrevcmp's order(): '~' before the end of a part, the end before
   letters, letters before every other character *)
let char_key c =
  if c = '~' then -1 else if is_alpha c then Char.code c else Char.code c + 256

let rec skip_while f s i e =
  if i < e && f s.[i] then skip_while f s (i + 1) e else i

let skip_zeros = skip_while (fun c -> c = '0')

(* verrevcmp on s1.[i1, e1) and s2.[i2, e2), in place: a solve compares
   versions millions of times, most of them while the callbacks load and
   encode, so this must not allocate.  A part that runs out equals the
   other's remainder if that is a run of '0's, as verrevcmp's empty digit
   run is 0, and sorts after it if a '~' follows. *)
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

let sign c = if c < 0 then -1 else if c > 0 then 1 else 0

(* the revision is everything after the last '-' (deb-version(7)), which
   opam splits the same way (OpamVersionCompare.extract_revision) *)
let last_dash s i =
  let rec go j =
    if j < i then String.length s else if s.[j] = '-' then j else go (j - 1)
  in
  go (String.length s - 1)

(* s.[i ..] as upstream-revision, the upstream first and the revision only
   on a tie; a missing revision is the empty one, which equals "0" *)
let compare_from v1 i1 v2 i2 =
  let n1 = String.length v1 and n2 = String.length v2 in
  let r1 = last_dash v1 i1 and r2 = last_dash v2 i2 in
  let c = lexical v1 i1 r1 v2 i2 r2 in
  if c <> 0 then sign c
  else sign (lexical v1 (min n1 (r1 + 1)) n1 v2 (min n2 (r2 + 1)) n2)

(* opam's OpamVersionCompare: opam versions have no epoch, so a ':' is an
   ordinary character *)
let compare_no_epoch v1 v2 =
  if String.equal v1 v2 then 0 else compare_from v1 0 v2 0

(* The epoch is the digits before the first ':', when they are all digits
   and there are some; otherwise the version has none, and the ':' is part
   of the upstream version.  An epoch past max_int raises, as dpkg's
   parseversion refuses one too big. *)
let epoch s =
  match String.index_opt s ':' with
  | Some i when i > 0 && String.for_all is_digit (String.sub s 0 i) ->
      (int_of_string (String.sub s 0 i), i + 1)
  | _ -> (0, 0)

(* deb-version(7) and Policy 5.6.12: the epoch, then dpkg's verrevcmp
   (lib/dpkg/version.c) on the upstream version and then on the revision *)
let compare v1 v2 =
  if String.equal v1 v2 then 0
  else
    let e1, i1 = epoch v1 and e2, i2 = epoch v2 in
    let c = Int.compare e1 e2 in
    if c <> 0 then c else compare_from v1 i1 v2 i2
