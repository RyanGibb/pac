module E = Pac
module Ot = Pac_common.Ot

module NVerOT = Ot.Make (struct
  type t = string

  let compare = Npm_version.compare
end)

(* SemverMatch: the two tests the version order cannot express.  sameCore
   takes the candidate version first and the comparator's constant
   second. *)
module PM = struct
  let isPre = Npm_version.is_prerelease
  let sameCore = Npm_version.same_core
end

module Np = E.Npm (Ot.Str) (NVerOT) (PM)
module R = Np.Reduction
module T = Np.T

let xop : Npm_version.op -> E.cmpOp = function
  | Npm_version.Ge -> E.OpGe
  | Npm_version.Gt -> E.OpGt
  | Npm_version.Le -> E.OpLe
  | Npm_version.Lt -> E.OpLt
  | Npm_version.Eq -> E.OpEq

let xcomp : Npm_version.comparator -> Np.coq_Comparator = function
  | Npm_version.Any -> Np.CAny
  | Npm_version.Cmp (o, c) -> Np.COp (xop o, c)

let xrange (rg : Npm_version.range) : Np.coq_Range =
  List.map (fun cs -> List.map xcomp cs) rg

module PName = struct
  type t = Np.Nm.name

  let compare a b = Ot.r2c (Np.Nm.compare a b)

  let pp_key fmt ((a, t) : string * string) =
    if a = t then Format.fprintf fmt "%s" a
    else Format.fprintf fmt "%s(npm:%s)" a t

  let pp fmt (n : t) =
    match n with
    | Np.Nm.Granular (k, w) -> Format.fprintf fmt "%a@%s" pp_key k w
    | Np.Nm.Intermediate (k, v, m) ->
        Format.fprintf fmt "<%a@%s=>%a>" pp_key k v pp_key m
end

module PVersion = struct
  type t = Np.Vs.version

  let compare a b = Ot.r2c (Np.Vs.compare a b)
  let equal a b = compare a b = 0

  let pp fmt (v : t) =
    match v with
    | Np.Vs.Orig v -> Format.fprintf fmt "%s" v
    | Np.Vs.Gran w -> Format.fprintf fmt "gran:%s" w
end

module PG = Pubgrub.Make (PName) (PVersion)
