val compare : string -> string -> int
val validate : string -> bool

(* apk's ~ is mask EQUAL|FUZZY, and the comparator never returns
   the FUZZY bit, so it reduces to fuzzy equality. *)
val prefix_match : string -> string -> bool

(* apk resolves >< against the providing package's C: identity digest
   (package.c:276), a bare provides included, which no version string
   determines, so a version-only matcher can never match one. *)
val hash_match : string -> string -> bool

type op = Eq | Lt | Gt | Le | Ge | Fuzzy | Gt_fuzzy | Lt_fuzzy | Hash

(* apk_version_result_mask_blob bit-ORs the operator characters, so any
   run of them is an operator: <> and >< are one, =~ and == are ~ and =.
   None is a run holding both < and > and = (or ~), a mask apk_version_match
   takes as every version. *)
val op_of_string : string -> op option

(* for test_apk_version alone: a solve matches constraints through the
   calculus, not through this *)
val matches : string -> op -> string -> bool
