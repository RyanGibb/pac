module Make (Encoding : Encoding.S) : sig
  open Encoding

  type state

  val create :
    Archive.t ->
    Cargo_query.root ->
    features:Cargo_query.features ->
    rustv:string option ->
    state

  val granularity : state -> string -> string
  val meta : state -> string -> string -> Cargo_parse.ver option
  val versions_of : state -> string -> string list
  val root : state -> string * string
  val root_features : state -> Cargo_query.features

  (* the crate version's slots and feature definitions, which is all
     parents reads of it *)
  val slots_and_fdefs :
    state -> string * string -> Cargo.SlotRel.t * Cargo.FeatureDefinitionRel.t

  (* the manifest record a slot name's dependency came from, for choose's
     walk over its candidates: the name carries the dependency but not the
     parsed requirement the comparator reads *)
  val slot_dep : state -> Cargo.DependencyRecord.t -> Cargo_parse.dep option

  (* how many (name, version) pairs PubGrub has asked the dependencies of *)
  val dependency_lookups : state -> int

  (* whether (n, v) fits the toolchain resolver v3 ranks against; every
     version does when there is none *)
  val msrv_fits : state -> string * string -> bool
  val empty_inst : state -> Cargo.coq_Inst
  val dependees : state -> Reduced.Package.t -> Reduced.Dependee.t list

  (* the dependency the owner's fibre holds at a site, which is what a slot
     name carries: the order replay reads raw manifest records, which
     slots_of has not merged, so the name is taken from the fibre.  None for
     a second site with the same ask as one before it, which the slot rule
     merged into that one's slot. *)
  val site_data :
    state -> string * string -> Cargo.Site.t -> Cargo.DependencyRecord.t option

  val tag :
    state -> Cargo.Reduction.Name.t -> Cargo.Reduction.Version.t -> PVersion.t

  val pg_versions : state -> Cargo.Reduction.Name.t -> PVersion.t list

  val pg_dependencies :
    state ->
    Cargo.Reduction.Name.t ->
    PVersion.t ->
    (Cargo.Reduction.Name.t * Resolver.Ranges.t) list
end
