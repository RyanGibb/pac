open Encoding

type fibres = {
  r_slots : Cg.SlotRel.t;
  r_fdefs : Cg.FDefRel.t;
  r_links : Cg.LinkRel.t;
  r_supp : Cg.SupportSet.t;
  r_reads : string list; (* own name plus the slot targets *)
}

type owner_key =
  [ `Slot of string * string * Cg.SlotData.t
  | `Dec of string * string * string * Cg.SlotData.t * string ]

(* One solve's archive, request and memo tables.  Every table is keyed as
   narrowly as it is because this record is: a second solve builds its
   own, so no answer outlives the archive and root it was computed for. *)
type state = {
  ar : Archive.t;
  rc : string * string;
  features : Cargo_query.features;
  rfeats : Cg.FSet.t;
  rustv : string option;
  granularities : (string, string) Hashtbl.t;
  fibres : (string * string, fibres) Hashtbl.t;
  (* the manifest record a slot name's dependency came from, for choose's
     walk over its candidates: the name carries the dependency but not the
     parsed requirement the comparator reads *)
  dep_of_data : (Cg.SlotData.t, Cargo_parse.dep) Hashtbl.t;
  name_sets : (string, Cg.PkgSet.t) Hashtbl.t;
  (* keyed by the read names rather than by the crate version, so that
     versions reading the same names share one entry *)
  repo_preimages : (string list, Cg.PkgSet.t) Hashtbl.t;
  msrv : (string * string, bool) Hashtbl.t;
  supports : (string, Cg.SupportSet.t) Hashtbl.t;
  owners : (owner_key, Cg.SlotRel.t * Cg.FDefRel.t) Hashtbl.t;
  site_datas :
    ((string * string) * Cg.SlotKey.t, Cg.SlotData.t option) Hashtbl.t;
  (* the tagged list, not just the untagged one, has to be memoized:
     PubGrub asks a name for its versions at every propagation step *)
  pg_vers : (Cg.NPlus.t, PVersion.t list) Hashtbl.t;
  (* at each decision PubGrub's dependency_incomps asks for the
     dependencies of the decided version's neighbours, once per
     dependency, to widen each incompatibility's range *)
  pg_deps : (Cg.NPlus.t * Cg.VPlus.t, (Cg.NPlus.t * PG.Ranges.t) list) Hashtbl.t;
}

val create :
  Archive.t ->
  Cargo_query.root ->
  features:Cargo_query.features ->
  rustv:string option ->
  state

val granularity : state -> string -> string
val meta : state -> string -> string -> Cargo_parse.ver option
val versions_of : state -> string -> string list
val fibres_of : state -> string * string -> fibres

(* whether (n, v) fits the toolchain resolver v3 ranks against; every
   version does when there is none *)
val msrv_fits : state -> string * string -> bool
val empty_inst : state -> Cg.coq_Inst
val dependees : state -> T.Pkg.t -> T.Dependees.t list

(* the dependency the owner's fibre holds at a site, which is what a slot
   name carries: the order replay reads raw manifest records, which
   slots_of has not merged, so the name is taken from the fibre *)
val site_data : state -> string * string -> Cg.SlotKey.t -> Cg.SlotData.t option
val tag : state -> Cg.NPlus.t -> Cg.VPlus.t -> PVersion.t
val pg_versions : state -> Cg.NPlus.t -> PVersion.t list

val pg_dependencies :
  state -> Cg.NPlus.t -> PVersion.t -> (Cg.NPlus.t * PG.Ranges.t) list
