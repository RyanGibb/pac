open Encoding

type t

val create : Archive.t -> string * string -> t
val archive : t -> Archive.t
val root : t -> string * string

(* the range a spec names on package t: a dist-tag's version exactly, and
   "*" as npm-pick-manifest reads it, its latest prerelease included *)
val spec_range : Archive.t -> string -> Npm_parse.spec -> Npm_version.range

(* the range the calculus reads for an edge on directory a: the root's
   flat override on a when there is one *)
val effective : t -> string -> Np.coq_Range -> Np.coq_Range
val peer_dependencies : t -> string * string -> Np.coq_PeerDependency list

(* what the optional-dependency test read and what it abandoned, both in
   distinct (dependee name, range) pairs *)
val optional_verdicts : t -> int * int

(* p's dependencies, the root's override on each one's directory applied *)
val active_dependencies : t -> string * string -> Np.coq_Dependency list

(* the descriptor p's directory m reads, as the calculus's slotOf finds
   its dependency: the first active one of the directory *)
val desc_name : t -> string * string -> string * string -> Np.Nm.name option
val versions : t -> Np.Nm.name -> Np.Vs.version list

(* whether a name's versions may grow after it was first asked *)
val grows : t -> Np.Nm.name -> bool

(* where the copy k at v offers its name a: its sight where it peers on a
   itself, else its own directory; none where it offers itself or
   nothing *)
val holder : t -> (string * string) * string -> string -> Np.Nm.name option

(* the directories opened so far that read descriptor x *)
val desc_dirs : t -> Np.Nm.name -> Np.Nm.name list
val dependees : t -> T.Pkg.t -> T.Dependees.t list

(* the links, opened so far, whose holder shows the name in directory h *)
val links_into : t -> Np.Nm.name -> Np.Nm.name list

(* the directories of p's copy the solver has opened so far *)
val dirs : t -> (string * string) * string -> Np.Nm.name list
