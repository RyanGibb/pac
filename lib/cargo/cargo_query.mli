exception Refused of string

val refuse : ('a, unit, string, 'b) format4 -> 'a

type root = {
  ver : Cargo_parse.ver;
  (* [patch.crates-io] maps the root's own name to it, which is what the
     model's one node per (name, version) already says; without it cargo
     keeps the root apart from the registry's crate of that name *)
  self_patch : bool;
  (* the resolver the manifest selects is 3, the one whose MSRV preference
     reaches version selection *)
  msrv_pref : bool;
}

(* the root's feature request.  All is the lock's: every key of the root's
   feature table, as resolve_with_registry asks with
   CliFeatures::new_all(true).  Named is --features: the named features,
   plus default unless --no-default-features, as CliFeatures reads the
   flags; it resolves afresh rather than filtering the lock. *)
type features = All | Named of { feats : string list; default : bool }

(* as cargo 1.97's util/toml/mod.rs reads a manifest.  The root becomes
   one more crate version, so a field with no place in the index form -- a
   path or git source, another registry, a [patch] other than the root's
   own, workspace inheritance -- would change the question cargo is asked
   without changing ours, and is refused. *)
val of_manifest : string -> root
val crate : root -> string * string

(* cargo splits each --features value on spaces and commas, and an empty
   value names nothing: [-F ""] still asks for default.  A name the root's
   table lacks is cargo's MissingFeature; the placeholder default the parser
   adds is not a key of cargo's. *)
val features_of_flags : root -> string list -> no_default:bool -> features

(* the toolchain resolve.rs ranks candidates against: the root's own
   rust-version, and only when it declares none the installed rustc; under
   resolvers 1 and 2, nothing *)
val toolchain : root -> installed:string option -> string option
