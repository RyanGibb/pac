module type S = sig
  module Ot = Pac_common.Ot

  module IVer : sig
    type t = { s : string; p : Version.Semver.t }

    val make : string -> t
    val compare : t -> t -> int
  end

  module IVerOT : sig
    type t = IVer.t

    val compare : t -> t -> Pac.comparison
    val eq_dec : t -> t -> bool
  end

  module IPM : sig
    val isPre : IVer.t -> bool
    val sameCore : IVer.t -> IVer.t -> bool
  end

  module NpmPlacement :
      module type of Pac.NpmPlacement (Pac_common.Ot.Str) (IVerOT) (IPM)

  module Placement = NpmPlacement.Placement
  module Reduction = Placement.Reduction
  module Reduced = Reduction.Reduced
  module ReductionLookup = NpmPlacement.Reduction.Lookup

  val xrange : Npm_version.range -> NpmPlacement.coq_Range
  val lock_path : string list -> string
  val occ_compare : NpmPlacement.Occupant.t -> NpmPlacement.Occupant.t -> int

  module PName : sig
    type t = Reduction.Name.t

    val compare : t -> t -> int
    val pp : Format.formatter -> t -> unit
  end

  module PVersion : sig
    type t = Reduction.Version.t

    val compare : t -> t -> int
    val equal : t -> t -> bool
    val pp : Format.formatter -> t -> unit
  end

  module Resolver : module type of Pubgrub.Make (PName) (PVersion)
end

module Make () = struct
  module Ot = Pac_common.Ot
  module Semver = Version.Semver

  (* every set of occupants and every walk's versions compares versions of
     one name over and over, and the npm reading's comparator looks each
     string's parse up in a bounded table at every comparison *)
  module IVer = struct
    type t = { s : string; p : Semver.t }

    let tbl : (string, t) Hashtbl.t = Hashtbl.create 65536

    let make (s : string) : t =
      match Hashtbl.find_opt tbl s with
      | Some v -> v
      | None ->
          let v = { s; p = Semver.Loose.parse s } in
          Hashtbl.add tbl s v;
          v

    let compare (a : t) (b : t) =
      if a == b || String.equal a.s b.s then 0 else Semver.precedence a.p b.p
  end

  module IVerOT = Ot.Make (IVer)

  module IPM = struct
    let isPre (v : IVer.t) = v.IVer.p.Semver.pre <> []

    let sameCore (a : IVer.t) (b : IVer.t) =
      Semver.same_core_parsed a.IVer.p b.IVer.p
  end

  module NpmPlacement = Pac.NpmPlacement (Ot.Str) (IVerOT) (IPM)
  module Placement = NpmPlacement.Placement
  module Reduction = Placement.Reduction
  module Reduced = Reduction.Reduced
  module ReductionLookup = NpmPlacement.Reduction.Lookup

  (* NpmPlacement's ranges are its own type, as each application of Semver makes one *)
  let xcomp : Npm_version.comparator -> NpmPlacement.coq_Comparator = function
    | Npm_version.Any -> NpmPlacement.CAny
    | Npm_version.Cmp (o, c) -> NpmPlacement.COp (Encoding.xop o, IVer.make c)

  let xrange (rg : Npm_version.range) : NpmPlacement.coq_Range =
    List.map (fun cs -> List.map xcomp cs) rg

  (* a location is stored deepest key first, as the calculus stores it *)
  let path_string (l : string list) =
    match l with [] -> "" | _ -> String.concat "/" (List.rev l)

  let lock_path (l : string list) =
    String.concat "/"
      (List.concat_map (fun k -> [ "node_modules"; k ]) (List.rev l))

  (* The orders of the extracted Name and Version, restated: PubGrub compares
     versions under every range operation, and the extracted ones measure a
     path's length in unary each time.  [check] compares against them. *)
  let check = Sys.getenv_opt "PAC_NPM_CHECKCMP" <> None

  let rec path_compare (x : string list) (y : string list) =
    match (x, y) with
    | [], [] -> 0
    | [], _ :: _ -> -1
    | _ :: _, [] -> 1
    | a :: x', b :: y' -> (
        match String.compare a b with 0 -> path_compare x' y' | c -> c)

  let checked name fast slow a b =
    let c = fast a b in
    if check && c <> Ot.r2c (slow a b) then failwith ("order mismatch: " ^ name);
    c

  let occ_compare (x : NpmPlacement.Occupant.t) (y : NpmPlacement.Occupant.t) =
    match (x, y) with
    | NpmPlacement.Occupant.Proj, NpmPlacement.Occupant.Proj -> 0
    | NpmPlacement.Occupant.Proj, NpmPlacement.Occupant.Reg _ -> -1
    | NpmPlacement.Occupant.Reg _, NpmPlacement.Occupant.Proj -> 1
    | NpmPlacement.Occupant.Reg (m, v), NpmPlacement.Occupant.Reg (m', v') -> (
        match String.compare m m' with 0 -> IVer.compare v v' | c -> c)

  module PName = struct
    type t = Reduction.Name.t

    let rank = function
      | Reduction.Name.Root -> 0
      | Reduction.Name.Loc _ -> 1
      | Reduction.Name.Walk _ -> 2

    let fast (a : t) (b : t) =
      match (a, b) with
      | Reduction.Name.Loc (l1, a1), Reduction.Name.Loc (l2, a2)
      | Reduction.Name.Walk (l1, a1), Reduction.Name.Walk (l2, a2) -> (
          match path_compare l1 l2 with 0 -> String.compare a1 a2 | c -> c)
      | _ -> Int.compare (rank a) (rank b)

    let compare = checked "name" fast Reduction.NameOT.compare

    let pp fmt (n : t) =
      let p l = match l with [] -> "ε" | _ -> path_string l in
      match n with
      | Reduction.Name.Root -> Format.fprintf fmt "<ε>"
      | Reduction.Name.Loc (l, a) -> Format.fprintf fmt "<%s,%s>" (p l) a
      | Reduction.Name.Walk (l, a) -> Format.fprintf fmt "<%s⇑%s>" (p l) a
  end

  module PVersion = struct
    type t = Reduction.Version.t

    let rank = function
      | Reduction.Version.Occ _ -> 0
      | Reduction.Version.Found _ -> 1
      | Reduction.Version.Bot -> 2

    (* a shallower location is greater *)
    let fast (a : t) (b : t) =
      match (a, b) with
      | Reduction.Version.Occ x, Reduction.Version.Occ y -> occ_compare x y
      | Reduction.Version.Found (l1, x), Reduction.Version.Found (l2, y) -> (
          match Int.compare (List.length l2) (List.length l1) with
          | 0 -> (
              match path_compare l1 l2 with 0 -> occ_compare x y | c -> c)
          | c -> c)
      | _ -> Int.compare (rank a) (rank b)

    let compare = checked "version" fast Reduction.VersionOT.compare
    let equal a b = compare a b = 0

    let pp_occ fmt = function
      | NpmPlacement.Occupant.Proj -> Format.fprintf fmt "project"
      | NpmPlacement.Occupant.Reg (m, v) ->
          Format.fprintf fmt "%s@%s" m v.IVer.s

    let pp fmt (v : t) =
      match v with
      | Reduction.Version.Occ x -> pp_occ fmt x
      | Reduction.Version.Found ([], x) -> Format.fprintf fmt "(ε,%a)" pp_occ x
      | Reduction.Version.Found (l, x) ->
          Format.fprintf fmt "(%s,%a)" (path_string l) pp_occ x
      | Reduction.Version.Bot -> Format.fprintf fmt "⊥"
  end

  module Resolver = Pubgrub.Make (PName) (PVersion)
end
