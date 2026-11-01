module Ot = Pac_common.Ot

let xop : Npm_version.op -> Pac.cmpOp = function
  | Npm_version.Ge -> Pac.OpGe
  | Npm_version.Gt -> Pac.OpGt
  | Npm_version.Le -> Pac.OpLe
  | Npm_version.Lt -> Pac.OpLt
  | Npm_version.Eq -> Pac.OpEq

module type S = sig
  module NpmVersionOT : sig
    type t = string

    val compare : t -> t -> Pac.comparison
    val eq_dec : t -> t -> bool
  end

  module PM : sig
    val isPre : string -> bool
    val sameCore : string -> string -> bool
  end

  module Npm : module type of Pac.Npm (Pac_common.Ot.Str) (NpmVersionOT) (PM)
  module Reduction = Npm.Reduction
  module Reduced = Npm.Reduced

  val xrange : Npm_version.range -> Npm.coq_Range

  module PName : sig
    type t = Npm.Name.name

    val compare : t -> t -> int
    val pp : Format.formatter -> t -> unit
  end

  module PVersion : sig
    type t = Npm.Version.version

    val compare : t -> t -> int
    val equal : t -> t -> bool
    val pp : Format.formatter -> t -> unit
  end

  module Resolver : module type of Pubgrub.Make (PName) (PVersion)
end

module Make () = struct
  module NpmVersionOT = Ot.Make (struct
    type t = string

    let compare = Npm_version.compare
  end)

  module PM = struct
    let isPre = Npm_version.is_prerelease
    let sameCore = Npm_version.same_core
  end

  module Npm = Pac.Npm (Ot.Str) (NpmVersionOT) (PM)
  module Reduction = Npm.Reduction
  module Reduced = Npm.Reduced

  let xcomp : Npm_version.comparator -> Npm.coq_Comparator = function
    | Npm_version.Any -> Npm.CAny
    | Npm_version.Cmp (o, c) -> Npm.COp (xop o, c)

  let xrange (rg : Npm_version.range) : Npm.coq_Range =
    List.map (fun cs -> List.map xcomp cs) rg

  module PName = struct
    type t = Npm.Name.name

    let compare a b = Ot.r2c (Npm.Name.compare a b)

    let pp_key fmt ((a, t) : string * string) =
      if a = t then Format.fprintf fmt "%s" a
      else Format.fprintf fmt "%s(npm:%s)" a t

    let pp fmt (n : t) =
      match n with
      | Npm.Name.Granular (k, w) -> Format.fprintf fmt "%a@%s" pp_key k w
      | Npm.Name.Intermediate (k, v, m) ->
          Format.fprintf fmt "<%a@%s=>%a>" pp_key k v pp_key m
      | Npm.Name.Sight (k, v, a) -> Format.fprintf fmt "<%a@%s^%s>" pp_key k v a
      | Npm.Name.Link (k, v, m, u, a) ->
          Format.fprintf fmt "<%a@%s=>%a@%s^%s>" pp_key k v pp_key m u a
      | Npm.Name.Desc (a, t, s) -> Format.fprintf fmt "<%a@%s>" pp_key (a, t) s
  end

  module PVersion = struct
    type t = Npm.Version.version

    let compare a b = Ot.r2c (Npm.Version.compare a b)
    let equal a b = compare a b = 0

    let pp fmt (v : t) =
      match v with
      | Npm.Version.Orig v -> Format.fprintf fmt "%s" v
      | Npm.Version.Bot -> Format.fprintf fmt "⊥"
      | Npm.Version.Free -> Format.fprintf fmt "∗"
  end

  module Resolver = Pubgrub.Make (PName) (PVersion)
end
