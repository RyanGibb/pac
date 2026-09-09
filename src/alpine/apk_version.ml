(* apk's version ordering, transcribed from apk-tools src/version.c on
   master (v3.0.0_rc4-23-g652a136): the token state machine of
   digit{.digit}...{letter}{_suffix{number}}...{~hash}{-r#}, the suffix
   table, and apk_version_compare_fuzzy.  apk 2.14 differs in three ways
   that this file does not implement -- its fuzzy match is symmetric, it
   orders leading-zero components by zero count rather than by string,
   and it has no ~hash token -- so a comparison here can disagree with
   the apk shipped in Alpine 3.21.  Trusted: this file is TCB. *)

type token =
  | Initial_digit
  | Digit
  | Letter
  | Suffix
  | Suffix_no
  | Commit_hash
  | Revision_no
  | End
  | Invalid

(* The declaration order in enum PARTS is itself the ordering: it gates
   which token may follow which, and breaks ties between versions that
   diverge in kind rather than in value. *)
let rank = function
  | Initial_digit -> 0
  | Digit -> 1
  | Letter -> 2
  | Suffix -> 3
  | Suffix_no -> 4
  | Commit_hash -> 5
  | Revision_no -> 6
  | End -> 7
  | Invalid -> 8

(* DECLARE_SUFFIXES, with SUFFIX_NONE the pivot a bare version sits at:
   alpha/beta/pre/rc sort below it, cvs/svn/git/hg/p above. *)
let suffix_none = 5

let suffix_value = function
  | "alpha" -> 1
  | "beta" -> 2
  | "pre" -> 3
  | "rc" -> 4
  | "cvs" -> 6
  | "svn" -> 7
  | "git" -> 8
  | "hg" -> 9
  | "p" -> 10
  | _ -> 0

type state = {
  tok : token;
  value : string;
  number : int;
  suffix : int;
  pos : int;
}

let is_digit c = c >= '0' && c <= '9'
let is_lower c = c >= 'a' && c <= 'z'
let is_hex c = is_digit c || (c >= 'a' && c <= 'f')

let span s pos p =
  let n = String.length s in
  let i = ref pos in
  while !i < n && p s.[!i] do
    incr i
  done;
  !i

let invalid st = { st with tok = Invalid; value = ""; number = 0 }

(* token_parse_digits: the raw text is kept alongside the value because
   the leading-zero rule compares it as a string. *)
let parse_digits st s pos tok =
  let stop = span s pos is_digit in
  if stop = pos then invalid st
  else
    let text = String.sub s pos (stop - pos) in
    let n = ref 0 in
    String.iter (fun c -> n := (!n * 10) + (Char.code c - 48)) text;
    { tok; value = text; number = !n; suffix = 0; pos = stop }

let token_first s =
  parse_digits
    { tok = Invalid; value = ""; number = 0; suffix = 0; pos = 0 }
    s 0 Initial_digit

let token_next st s =
  let n = String.length s in
  if st.pos >= n then { st with tok = End; value = ""; number = 0 }
  else
    let c = s.[st.pos] in
    if is_lower c then
      if rank st.tok > rank Digit then invalid st
      else
        {
          tok = Letter;
          value = String.make 1 c;
          number = 0;
          suffix = 0;
          pos = st.pos + 1;
        }
    else if c = '.' || is_digit c then
      let pos = if c = '.' then st.pos + 1 else st.pos in
      if c = '.' && rank st.tok > rank Digit then invalid st
      else
        match st.tok with
        | Initial_digit | Digit -> parse_digits st s pos Digit
        | Suffix -> parse_digits st s pos Suffix_no
        | _ -> invalid st
    else if c = '_' then
      if rank st.tok > rank Suffix_no then invalid st
      else
        let stop = span s (st.pos + 1) is_lower in
        let text = String.sub s (st.pos + 1) (stop - st.pos - 1) in
        let v = suffix_value text in
        if v = 0 then invalid st
        else { tok = Suffix; value = text; number = 0; suffix = v; pos = stop }
    else if c = '~' then
      if rank st.tok >= rank Commit_hash then invalid st
      else
        let stop = span s (st.pos + 1) is_hex in
        if stop = st.pos + 1 then invalid st
        else
          {
            tok = Commit_hash;
            value = String.sub s (st.pos + 1) (stop - st.pos - 1);
            number = 0;
            suffix = 0;
            pos = stop;
          }
    else if c = '-' then
      if rank st.tok >= rank Revision_no then invalid st
      else if st.pos + 1 >= n || s.[st.pos + 1] <> 'r' then invalid st
      else parse_digits st s (st.pos + 2) Revision_no
    else invalid st

(* apk_blob_sort: memcmp over the common prefix, then shorter is less --
   not the length-first apk_blob_compare. *)
let blob_sort a b =
  let la = String.length a and lb = String.length b in
  let n = if la < lb then la else lb in
  let rec go i =
    if i = n then compare la lb
    else
      let c = Char.compare a.[i] b.[i] in
      if c <> 0 then c else go (i + 1)
  in
  go 0

let token_cmp ta tb =
  match ta.tok with
  | Digit when ta.value.[0] = '0' || tb.value.[0] = '0' ->
      (* either side carrying a leading zero switches the component to a
         Gentoo-style fractional string sort *)
      blob_sort ta.value tb.value
  | Initial_digit | Digit | Suffix_no | Revision_no ->
      compare ta.number tb.number
  | Letter -> Char.compare ta.value.[0] tb.value.[0]
  | Suffix -> compare ta.suffix tb.suffix
  | _ -> blob_sort ta.value tb.value

(* apk_version_compare_fuzzy.  With ~fuzzy, the right-hand side running
   out of tokens is equality, which is why ~ is asymmetric and is not a
   range: 1.0_pre1 ~ 1.0 holds even though 1.0_pre1 < 1.0. *)
let compare_fuzzy a b fuzzy =
  let rec go ta tb =
    if ta.tok = tb.tok && rank ta.tok < rank End then
      let r = token_cmp ta tb in
      if r <> 0 then r else go (token_next ta a) (token_next tb b)
    else if ta.tok = tb.tok then 0
    else if tb.tok = End && fuzzy then 0
    else if ta.tok = Suffix && ta.suffix < suffix_none then -1
    else if tb.tok = Suffix && tb.suffix < suffix_none then 1
    else compare (rank tb.tok) (rank ta.tok)
  in
  go (token_first a) (token_first b)

let compare a b = compare_fuzzy a b false

let validate v =
  let rec go st = if rank st.tok < rank End then go (token_next st v) else st in
  (go (token_first v)).tok = End

(* CPrefix: apk's ~ is mask EQUAL|FUZZY, and the comparator never returns
   the FUZZY bit, so it reduces to fuzzy equality. *)
let prefix_match v c = compare_fuzzy v c true = 0

(* CHash: apk resolves >< against the candidate's C: identity digest,
   which its version string does not determine, so the calculus's
   version-only matcher can never witness one. *)
let hash_match (_v : string) (_digest : string) = false

type op = Eq | Lt | Gt | Le | Ge | Fuzzy | Gt_fuzzy | Lt_fuzzy | Hash

(* apk_version_result_mask_blob bit-ORs the operator characters, so <>
   and >< are one operator, and =~ is ~. *)
let op_of_string = function
  | "=" -> Some Eq
  | "<" -> Some Lt
  | ">" -> Some Gt
  | "<=" | "=<" -> Some Le
  | ">=" | "=>" -> Some Ge
  | "~" | "=~" | "~=" -> Some Fuzzy
  | ">~" | ">=~" | "~>=" | "=>~" | "~>" -> Some Gt_fuzzy
  | "<~" | "<=~" | "~<=" | "=<~" | "~<" -> Some Lt_fuzzy
  | "><" | "<>" -> Some Hash
  | _ -> None

let string_of_op = function
  | Eq -> "="
  | Lt -> "<"
  | Gt -> ">"
  | Le -> "<="
  | Ge -> ">="
  | Fuzzy -> "~"
  | Gt_fuzzy -> ">~"
  | Lt_fuzzy -> "<~"
  | Hash -> "><"

let matches v o c =
  match o with
  | Eq -> compare v c = 0
  | Lt -> compare v c < 0
  | Gt -> compare v c > 0
  | Le -> compare v c <= 0
  | Ge -> compare v c >= 0
  | Fuzzy -> prefix_match v c
  | Gt_fuzzy -> compare v c > 0 || prefix_match v c
  | Lt_fuzzy -> compare v c < 0 || prefix_match v c
  | Hash -> hash_match v c
