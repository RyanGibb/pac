type kind = Normal | Build | Dev

type dep = {
  d_alias : string; (* the manifest key: what dep:/a/feat entries name *)
  d_target : string; (* the published crate, differing under a rename *)
  d_req : Cargo_version.req;
  d_feats : string list;
  d_optional : bool;
  d_default : bool;
  d_kind : kind;
  d_cfg : string; (* the target cfg predicate, "" when unconditional *)
}

type fentry =
  | FFeat of string
  | FDep of string
  | FDepFeat of string * string
  | FWeakFeat of string * string

type ver = {
  v_name : string;
  v_vers : string;
  v_deps : dep list;
  v_feats : (string * fentry list) list;
  v_links : string option;
  (* whether "default" is the manifest's own feature or the placeholder
     with_implicit_features adds; the solve needs the placeholder, the
     reported feature set must not carry it *)
  v_default_declared : bool;
  (* the declared MSRV, kept as written: the index spells it as a partial
     version ("1.71", not "1.71.0"), and the comparison it feeds is a
     caret requirement, which reads a partial spec directly.  None is the
     field absent, which is not the same as an MSRV of 0. *)
  v_msrv : string option;
}

val crate_path : index:string -> string -> string

(* "dep:a" activates an optional slot, "a/feat" is the strong dependency
   feature and "a?/feat" the weak one, and a bare name is another feature
   of the same crate.  The two forms stay apart here because the manifest
   spells them differently; the calculus resolves them alike. *)
val entry_of : string -> fentry

(* build_feature_map's checks (summary.rs), under which a failing index
   entry is IndexSummary::Invalid and never a candidate.  Past ASCII,
   every character is taken for the XID one validate_feature_name wants. *)
val feature_map_ok : dep list -> (string * fentry list) list -> bool

(* "default" always exists, empty when the manifest does not define it:
   every dependency that has not opted out requests it, and cargo treats
   the request as a no-op rather than an error *)
val default_feature : string

(* the implicit features; and, the table complete, a strong a/feat entry
   over an optional a also enables the feature named a where the table has
   one, because cargo's resolver does (dep_cache.rs, require_dep_feature)
   and the calculus states only what the entry asks of a *)
val with_implicit_features :
  dep list -> (string * fentry list) list -> (string * fentry list) list

val load_crate : reject:(unit -> unit) -> index:string -> string -> ver list
