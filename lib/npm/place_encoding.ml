module E = Pac
module Ot = Pac_common.Ot
module SV = Version.Semver

(* every set of occupants and every walk's versions compares versions of
   one name over and over, and the npm reading's comparator looks each
   string's parse up in a bounded table at every comparison *)
module IVer = struct
  type t = { s : string; p : SV.t }

  let tbl : (string, t) Hashtbl.t = Hashtbl.create 65536

  let make (s : string) : t =
    match Hashtbl.find_opt tbl s with
    | Some v -> v
    | None ->
        let v = { s; p = SV.Loose.parse s } in
        Hashtbl.add tbl s v;
        v

  let compare (a : t) (b : t) =
    if a == b || String.equal a.s b.s then 0 else SV.precedence a.p b.p
end

module IVerOT = Ot.Make (IVer)

module IPM = struct
  let isPre (v : IVer.t) = v.IVer.p.SV.pre <> []
  let sameCore (a : IVer.t) (b : IVer.t) = SV.same_core_parsed a.IVer.p b.IVer.p
end

module Npl = E.NpmPlacement (Ot.Str) (IVerOT) (IPM)
module Pl = Npl.Pl
module R = Pl.Reduction
module T = R.T
module Lk = Npl.Lookup

(* Npl's ranges are its own type, as each application of Semver makes one *)
let xcomp : Npm_version.comparator -> Npl.coq_Comparator = function
  | Npm_version.Any -> Npl.CAny
  | Npm_version.Cmp (o, c) -> Npl.COp (Encoding.xop o, IVer.make c)

let xrange (rg : Npm_version.range) : Npl.coq_Range =
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

let occ_compare (x : Npl.Occ.t) (y : Npl.Occ.t) =
  match (x, y) with
  | Npl.Occ.Top, Npl.Occ.Top -> 0
  | Npl.Occ.Top, Npl.Occ.Reg _ -> -1
  | Npl.Occ.Reg _, Npl.Occ.Top -> 1
  | Npl.Occ.Reg (m, v), Npl.Occ.Reg (m', v') -> (
      match String.compare m m' with 0 -> IVer.compare v v' | c -> c)

module PName = struct
  type t = R.Name.t

  let rank = function
    | R.Name.Root -> 0
    | R.Name.Loc _ -> 1
    | R.Name.Walk _ -> 2

  let fast (a : t) (b : t) =
    match (a, b) with
    | R.Name.Loc (l1, a1), R.Name.Loc (l2, a2)
    | R.Name.Walk (l1, a1), R.Name.Walk (l2, a2) -> (
        match path_compare l1 l2 with 0 -> String.compare a1 a2 | c -> c)
    | _ -> Int.compare (rank a) (rank b)

  let compare = checked "name" fast R.NameOT.compare

  let pp fmt (n : t) =
    let p l = match l with [] -> "ε" | _ -> path_string l in
    match n with
    | R.Name.Root -> Format.fprintf fmt "<ε>"
    | R.Name.Loc (l, a) -> Format.fprintf fmt "<%s,%s>" (p l) a
    | R.Name.Walk (l, a) -> Format.fprintf fmt "<%s⇑%s>" (p l) a
end

module PVersion = struct
  type t = R.Version.t

  let rank = function
    | R.Version.Occ _ -> 0
    | R.Version.Found _ -> 1
    | R.Version.Bot -> 2

  (* a shallower location is greater *)
  let fast (a : t) (b : t) =
    match (a, b) with
    | R.Version.Occ x, R.Version.Occ y -> occ_compare x y
    | R.Version.Found (l1, x), R.Version.Found (l2, y) -> (
        match Int.compare (List.length l2) (List.length l1) with
        | 0 -> ( match path_compare l1 l2 with 0 -> occ_compare x y | c -> c)
        | c -> c)
    | _ -> Int.compare (rank a) (rank b)

  let compare = checked "version" fast R.VersionOT.compare
  let equal a b = compare a b = 0

  let pp_occ fmt = function
    | Npl.Occ.Top -> Format.fprintf fmt "project"
    | Npl.Occ.Reg (m, v) -> Format.fprintf fmt "%s@%s" m v.IVer.s

  let pp fmt (v : t) =
    match v with
    | R.Version.Occ x -> pp_occ fmt x
    | R.Version.Found ([], x) -> Format.fprintf fmt "(ε,%a)" pp_occ x
    | R.Version.Found (l, x) ->
        Format.fprintf fmt "(%s,%a)" (path_string l) pp_occ x
    | R.Version.Bot -> Format.fprintf fmt "⊥"
end

module PG = Pubgrub.Make (PName) (PVersion)
