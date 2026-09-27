(* How npa's fromRegistry reads a registry spec: a range where node-semver
   reads one, loosely, and otherwise a dist-tag, which only the dependee
   name's packument resolves.  The literal "*", and the empty range npm reads as
   it, is npm's own case apart from every range meaning the same. *)
type spec = Range of Npm_version.range | Star | Tag of string

type dep = {
  d_dir : string; (* the directory key, i.e. the manifest key *)
  d_name : string; (* the registry package, differing under npm: *)
  d_spec : spec;
  d_dev : bool;
  (* not carried into the calculus: it only tells the solver that this
     dependency may be abandoned when the registry cannot satisfy it *)
  d_optional : bool;
  (* the spec as the manifest writes it, which with the directory is the
     dependency's descriptor: Yarn Berry resolves each descriptor once *)
  d_raw : string;
}

(* p_root: whether the root installs a copy for the peer where nothing else
   provides one, which it does not for a peer only Yarn Berry reads *)
type peer = { p_name : string; p_spec : spec; p_optional : bool; p_root : bool }

(* [`Shared] reads the manifests as npm and Yarn Berry both do, so that an
   answer is one both accept *)
type reading = [ `Npm | `Shared ]

type ver = {
  v_name : string;
  v_vers : string;
  v_deps : dep list;
  v_peers : peer list;
  v_ovr : (string * Npm_version.range) list;
  v_deprecated : bool;
  (* engines.node and engines.npm, the two sub-keys checkEngine tests;
     absent means the version imposes no requirement, which is what makes
     it rank above one whose requirement the host fails *)
  v_eng_node : Npm_version.range option;
  v_eng_npm : Npm_version.range option;
}

type packument = {
  pk_latest : string option;
  pk_tags : (string * string) list;
  pk_vers : ver list;
}

(* Yojson's [member] raises on a non-object; a registry manifest may omit
   any field or give it the wrong shape, so lookups go through this. *)
val member : string -> Yojson.Safe.t -> Yojson.Safe.t
val assoc_of : Yojson.Safe.t -> (string * Yojson.Safe.t) list

(* a JavaScript object keeps a new key last *)
val set : 'a -> 'b -> ('a * 'b) list -> ('a * 'b) list
val has_sub : string -> string -> bool
val starts : string -> string -> bool

(* npa's isAliasSpec, which takes the prefix in any case *)
val is_alias : string -> bool

(* git, file and URL specs, and the link:, workspace:, portal: and patch:
   specs npa refuses, are dropped and counted rather than guessed at. *)
val unresolvable : string -> bool

(* encodeURIComponent(s) === s *)
val uri_safe : string -> bool

(* a tag must be a name encodeURIComponent leaves alone, and npa refuses
   any other (EINVALIDTAGNAME) *)
val spec_of_string : string -> spec option

(* "npm:bar@^1" and "npm:@scope/bar@^1": npa splits at the first @ past
   the scope's; this takes the last, which differs only when the range
   itself holds an @ *)
val split_alias : string -> (string * string) option

(* "os", "cpu" and "libc" are not read: npm-pick-manifest never consults
   them and npm tests them only once the tree is built
   (#checkEngineAndPlatform), so reading them would make our instance
   strictly smaller than npm's.  bundleDependencies entries stay ordinary
   registry dependencies although npm takes their versions from the
   tarball, which is neither fetched nor trusted here. *)
val ver_of :
  reading:reading ->
  reject:(unit -> unit) ->
  root:bool ->
  string ->
  Yojson.Safe.t ->
  ver option

(* A packument that will not parse says nothing about the name's versions,
   so it is an error rather than a name with none. *)
val load :
  reading:reading ->
  reject:(unit -> unit) ->
  string ->
  (packument, string) result
