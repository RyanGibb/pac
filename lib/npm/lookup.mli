open Encoding

type t = {
  ar : Archive.t;
  root : string * string;
  (* false under --omit=optional: an optional dependency is then dropped
     outright rather than only when the registry cannot satisfy it *)
  optional : bool;
  ovr : (string * Np.coq_Range) list;
  dep_tbl : (string * string, Np.coq_Dependency list) Hashtbl.t;
  peer_tbl : (string * string, Np.coq_PeerDependency list) Hashtbl.t;
  repo_at : (string, Np.RepoSet.t) Hashtbl.t;
  (* keyed by the names read rather than by the package reading them, so
     packages that read the same names share one set *)
  repo_of : (string list, Np.RepoSet.t) Hashtbl.t;
  vcache : (Np.Nm.name, Np.Vs.version list) Hashtbl.t;
  (* the optional-dependency verdict, keyed by what decides it *)
  opt_keep : (string * string, bool) Hashtbl.t;
  (* each package's directories, as far as the solver has looked: the
     intermediates its granular node and its directories point to, and the
     directory each of its links resolves into *)
  dirs : ((string * string) * string, Np.Nm.name list) Hashtbl.t;
  (* the links resolving into each directory *)
  links_into : (Np.Nm.name, Np.Nm.name) Hashtbl.t;
  raw_tbl : (string * string, Npm_parse.dep list) Hashtbl.t;
  (* the directories reading each descriptor, as far as the solver has
     looked *)
  desc_dirs : (Np.Nm.name, Np.Nm.name) Hashtbl.t;
  mutable n_lookups : int;
}

val create : optional:bool -> Archive.t -> string * string -> t

(* the range the calculus reads for a dependency on t: the root's flat
   override when there is one *)
val effective : t -> string -> Np.coq_Range -> Np.coq_Range
val peer_dependencies : t -> string * string -> Np.coq_PeerDependency list

(* what the optional-dependency test read and what it abandoned, both in
   distinct (dependee name, range) pairs *)
val optional_verdicts : t -> int * int
val active_dependencies : t -> string * string -> Np.coq_Dependency list

(* the descriptor p's directory m reads, as the calculus's slotOf finds
   its dependency: the first active one of the directory *)
val desc_name : t -> string * string -> string * string -> Np.Nm.name option
val versions : t -> Np.Nm.name -> Np.Vs.version list

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
