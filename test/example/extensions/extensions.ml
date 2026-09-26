module E = Pac
module S = Pac_common.Ot.Str
module Core = Pac_common.Core

let r2c = Pac_common.Ot.r2c

module type EXAMPLE = sig
  type name
  type version

  val compare_name : name -> name -> E.comparison
  val compare_version : version -> version -> E.comparison
  val pp_name : Format.formatter -> name -> unit
  val pp_version : Format.formatter -> version -> unit
  val root : name * version
  val versions : name -> version list
  val dependees : name * version -> (name * version list) list

  (* the global reduction, as the definition gives it *)
  val real : (name * version) list
  val deps : ((name * version) * (name * version list)) list
  val decode : (name * version) list -> unit
end

(* The lookup theorems hold only of packages versions answered. *)
let unasked () = invalid_arg "dependees of a version no lookup answers"
let str = Format.pp_print_string
let set l = "{" ^ String.concat ", " l ^ "}"
let edges vels dels ds = List.map (fun (m, vs) -> (m, vels vs)) (dels ds)
let rel vels dels d = List.map (fun (p, (m, vs)) -> (p, (m, vels vs))) (dels d)

let packages title l =
  Printf.printf "%s (%d):\n" title (List.length l);
  List.iter (fun s -> Printf.printf "  %s\n" s) (List.sort compare l)

let pkgs l = packages "packages" (List.map (fun (n, v) -> n ^ " " ^ v) l)

let parents l =
  packages "parents"
    (List.map
       (fun ((n, v), (m, u)) -> Printf.sprintf "%s %s <- %s %s" n v m u)
       l)

module Run (X : EXAMPLE) = struct
  module PG =
    Pubgrub.Make
      (struct
        type t = X.name

        let compare a b = r2c (X.compare_name a b)
        let pp = X.pp_name
      end)
      (struct
        type t = X.version

        let compare a b = r2c (X.compare_version a b)
        let pp = X.pp_version
      end)

  let pkg (n, v) = Format.asprintf "%a %a" X.pp_name n X.pp_version v

  let edge (p, (m, vs)) =
    Format.asprintf "%s -> %a %s" (pkg p) X.pp_name m
      (set (List.map (Format.asprintf "%a" X.pp_version) vs))

  let only title (a : _ Core.t) (b : _ Core.t) =
    let show f l l' =
      List.iter
        (fun x ->
          if not (List.mem x l') then Printf.printf "%s only: %s\n" title (f x))
        l
    in
    show pkg a.packages b.packages;
    show edge a.edges b.edges

  let run () =
    let whole = { Core.packages = X.real; edges = X.deps } in
    Core.print ~pp_name:X.pp_name ~pp_version:X.pp_version whole;
    let at k l =
      List.filter_map (fun (j, x) -> if j = k then Some x else None) l
    in
    let reach =
      Core.walk
        ~versions:(fun n -> at n whole.packages)
        ~dependees:(fun p -> at p whole.edges)
        [ fst X.root ]
    in
    let lookups =
      Core.walk ~versions:X.versions ~dependees:X.dependees [ fst X.root ]
    in
    if lookups = reach then
      print_endline "lookups agree with the global reduction from the root"
    else begin
      only "lookups" lookups reach;
      only "global" reach lookups;
      exit 1
    end;
    match
      PG.solve ~vers:X.versions
        ~deps:(fun n v ->
          List.map
            (fun (m, vs) -> (m, PG.Ranges.of_list vs))
            (X.dependees (n, v)))
        [ (fst X.root, PG.Ranges.of_list [ snd X.root ]) ]
    with
    | Ok sol -> X.decode sol
    | Error inc -> Format.printf "%a@." PG.explain_incompatibility inc
end

module Conflict_class = struct
  module M = E.ConflictClass (S) (S)
  module R = M.Reduction
  module L = R.Lookup

  type name = R.Name.t
  type version = R.Version.t

  let compare_name = R.NameOT.compare
  let compare_version = R.VersionOT.compare

  let pp_name f = function
    | R.Name.Orig n -> str f n
    | R.Name.Cls k -> Format.fprintf f "<%s>" k

  let pp_version f = function
    | R.Version.Orig v -> str f v
    | R.Version.Name n -> str f n

  let vs l = M.VSet.ofList l

  let r =
    M.PkgSet.ofList
      [ ("A", "1"); ("B", "1"); ("B", "2"); ("C", "1"); ("D", "1") ]

  let d =
    M.C.DepRel.ofList
      [ (("A", "1"), ("B", vs [ "1"; "2" ])); (("A", "1"), ("C", vs [ "1" ])) ]

  let om =
    M.InClassRel.ofList
      [ (("B", "1"), "k"); (("C", "1"), "k"); (("D", "1"), "k") ]

  let root = R.embedPkg ("A", "1")

  let versions n =
    R.T.VSet.elements
      (match n with
      | R.Name.Orig m ->
          R.T.versions
            (R.reduceReal (L.PkgFibred.tailFibre r m) M.InClassRel.empty)
            n
      | R.Name.Cls k ->
          R.T.versions (R.reduceReal (L.inClass r om k) (L.classRelAt om k)) n)

  let dependees = function
    | (R.Name.Orig n, R.Version.Orig v) as p ->
        edges R.T.VSet.elements R.T.DependeesSet.elements
          (R.T.dependees
             (R.reduceDeps
                (L.DepRelFibred.tailFibre d (n, v))
                (L.InClassFibred.tailFibre om (n, v)))
             p)
    | R.Name.Cls _, _ -> []
    | R.Name.Orig _, R.Version.Name _ -> unasked ()

  let real = R.T.PkgSet.elements (R.reduceReal r om)
  let deps = rel R.T.VSet.elements R.T.DepRel.elements (R.reduceDeps d om)

  let decode s =
    pkgs (M.PkgSet.elements (R.classResolution (R.T.PkgSet.ofList s)))
end

module Conflict = struct
  module M = E.Conflict (S) (S)
  module R = M.Reduction
  module L = R.Lookup

  type name = string
  type version = R.Version.t

  let compare_name = S.compare
  let compare_version = R.VersionOT.compare
  let pp_name = str

  let pp_version f = function
    | R.Version.Orig v -> str f v
    | R.Version.Bot -> str f "⊥"

  let r = M.PkgSet.ofList [ ("A", "1"); ("B", "1"); ("B", "2") ]
  let d = M.C.DepRel.empty
  let g = M.ConflictRel.ofList [ (("A", "1"), ("B", M.VSet.ofList [ "2" ])) ]
  let root = R.embedPkg ("A", "1")

  let versions n =
    R.T.VSet.elements
      (R.T.VSet.add R.Version.Bot
         (R.embedVS (M.C.versions (L.PkgFibred.tailFibre r n) n)))

  let dependees = function
    | (n, R.Version.Orig v) as p ->
        let gp = L.ConflictRelFibred.tailFibre g (n, v) in
        edges R.T.VSet.elements R.T.DependeesSet.elements
          (R.T.dependees
             (R.reduceDeps
                (L.realPreimage r (L.conflictNames gp))
                (L.DepRelFibred.tailFibre d (n, v))
                gp)
             p)
    | _, R.Version.Bot -> []

  let real = R.T.PkgSet.elements (R.reduceReal r d g)
  let deps = rel R.T.VSet.elements R.T.DepRel.elements (R.reduceDeps r d g)

  let decode s =
    pkgs (M.PkgSet.elements (R.conflictResolution (R.T.PkgSet.ofList s)))
end

module Concurrent = struct
  module M = E.Concurrent (S) (S) (S)
  module R = M.Reduction
  module L = R.Lookup

  type name = R.Name.t
  type version = R.Version.t

  let compare_name = R.NameOT.compare
  let compare_version = R.VersionOT.compare

  let pp_name f = function
    | R.Name.Granular (n, w) -> Format.fprintf f "<%s,%s>" n w
    | R.Name.Intermediate (n, v, m) -> Format.fprintf f "<%s,%s,%s>" n v m

  let pp_version f = function R.Version.Orig v | R.Version.Gran v -> str f v
  let g v = List.hd (String.split_on_char '.' v)
  let vs l = M.VSet.ofList l

  let r =
    M.PkgSet.ofList
      [
        ("A", "1.0.0");
        ("B", "1.0.0");
        ("C", "1.0.0");
        ("D", "1.0.0");
        ("D", "2.0.0");
        ("D", "2.0.1");
        ("D", "3.0.0");
      ]

  let d =
    M.C.DepRel.ofList
      [
        (("A", "1.0.0"), ("B", vs [ "1.0.0" ]));
        (("A", "1.0.0"), ("C", vs [ "1.0.0" ]));
        (("B", "1.0.0"), ("D", vs [ "1.0.0"; "2.0.0"; "2.0.1" ]));
        (("C", "1.0.0"), ("D", vs [ "2.0.0"; "2.0.1"; "3.0.0" ]));
      ]

  let root = R.embedPkg g ("A", "1.0.0")

  let versions n =
    R.T.VSet.elements
      (match n with
      | R.Name.Granular (m, w) ->
          R.T.versions (R.reduceReal (L.granFibre g r m w) M.C.DepRel.empty g) n
      | R.Name.Intermediate (m, v, o) ->
          R.T.versions
            (R.reduceReal M.PkgSet.empty
               (L.DepRelFibred.endsFibre d (m, v) o)
               g)
            n)

  let dependees p =
    edges R.T.VSet.elements R.T.DependeesSet.elements
      (match p with
      | R.Name.Granular (n, _), R.Version.Orig v ->
          R.T.dependees (R.reduceDeps (L.DepRelFibred.tailFibre d (n, v)) g) p
      | R.Name.Intermediate (n, v, m), R.Version.Gran _ ->
          R.T.dependees (R.reduceDeps (L.DepRelFibred.endsFibre d (n, v) m) g) p
      | R.Name.Granular _, R.Version.Gran _
      | R.Name.Intermediate _, R.Version.Orig _ ->
          R.T.DependeesSet.empty)

  let real = R.T.PkgSet.elements (R.reduceReal r d g)
  let deps = rel R.T.VSet.elements R.T.DepRel.elements (R.reduceDeps d g)

  let decode s =
    let s = R.T.PkgSet.ofList s in
    pkgs (M.PkgSet.elements (R.concurrentResolution g s));
    parents (M.ParentRel.elements (R.parents d g s))
end

module Peer = struct
  module M = E.PeerDependency (S) (S) (S)
  module R = M.Reduction
  module L = R.Lookup
  module CR = M.Conc.Reduction

  type name = R.Name.t
  type version = R.Version.t

  let compare_name = CR.NameOT.compare
  let compare_version = CR.VersionOT.compare
  let pp_name = Concurrent.pp_name
  let pp_version = Concurrent.pp_version
  let g v = v
  let vs l = M.VSet.ofList l

  let r =
    M.PkgSet.ofList
      [ ("A", "1"); ("B", "1"); ("C", "1"); ("C", "2"); ("C", "3") ]

  let d =
    M.C.DepRel.ofList
      [ (("A", "1"), ("B", vs [ "1" ])); (("A", "1"), ("C", vs [ "2"; "3" ])) ]

  let th = M.PeerRel.ofList [ (("B", "1"), ("C", vs [ "1"; "2" ])) ]
  let root = CR.embedPkg g ("A", "1")

  let versions n =
    R.T.VSet.elements
      (match n with
      | R.Name.Granular (m, w) ->
          R.T.versions
            (R.reduceReal
               (CR.Lookup.granFibre g r m w)
               M.C.DepRel.empty M.PeerRel.empty g)
            n
      | R.Name.Intermediate (m, v, o) ->
          R.T.versions
            (R.reduceReal M.PkgSet.empty
               (L.DepRelFibred.tailFibre d (m, v))
               (L.peersOfDeps d th (m, v) o)
               g)
            n)

  let dependees p =
    edges R.T.VSet.elements R.T.DependeesSet.elements
      (match p with
      | R.Name.Granular (n, _), R.Version.Orig v ->
          R.T.dependees
            (R.reduceDeps (L.DepRelFibred.tailFibre d (n, v)) M.PeerRel.empty g)
            p
      | R.Name.Intermediate (n, v, o), R.Version.Orig u ->
          R.T.dependees
            (R.reduceDeps
               (L.DepRelFibred.tailFibre d (n, v))
               (L.PeerRelFibred.tailFibre th (o, u))
               g)
            p
      | R.Name.Intermediate _, R.Version.Gran _ -> R.T.DependeesSet.empty
      | R.Name.Granular _, R.Version.Gran _ -> unasked ())

  let real = R.T.PkgSet.elements (R.reduceReal r d th g)
  let deps = rel R.T.VSet.elements R.T.DepRel.elements (R.reduceDeps d th g)

  let decode s =
    let s = R.T.PkgSet.ofList s in
    pkgs (M.PkgSet.elements (CR.concurrentResolution g s));
    parents (M.ParentRel.elements (R.parents d g s))
end

module Visibility = struct
  module M = E.Visibility (S) (S)
  module R = M.Reduction
  module L = R.Lookup

  type name = R.Name.t
  type version = string

  let compare_name = R.NameOT.compare
  let compare_version = S.compare

  let pp_name f = function
    | R.Name.Occurrence (n, (m, u)) -> Format.fprintf f "<%s,(%s,%s)>" n m u
    | R.Name.Intermediate (n, v, m, (o, u)) ->
        Format.fprintf f "<%s,%s,%s,(%s,%s)>" n v m o u
    | R.Name.Agreement (n, v, m) -> Format.fprintf f "<%s,%s,%s>" n v m

  let pp_version = str
  let vs l = M.VSet.ofList l

  let r =
    M.PkgSet.ofList
      [ ("A", "1"); ("B", "1"); ("C", "1"); ("C", "2"); ("D", "1"); ("E", "1") ]

  let d =
    M.C.DepRel.ofList
      [
        (("A", "1"), ("B", vs [ "1" ]));
        (("A", "1"), ("C", vs [ "1"; "2" ]));
        (("A", "1"), ("D", vs [ "1" ]));
        (("B", "1"), ("C", vs [ "1" ]));
        (("D", "1"), ("C", vs [ "2" ]));
        (("D", "1"), ("E", vs [ "1" ]));
      ]

  let pub =
    M.PubRel.ofList
      [
        (("A", "1"), "B");
        (("A", "1"), "C");
        (("A", "1"), "D");
        (("B", "1"), "C");
        (("D", "1"), "E");
      ]

  let rc = ("A", "1")
  let root = R.embedRoot rc

  let versions n =
    R.T.VSet.elements
      (match n with
      | R.Name.Occurrence (m, _) -> R.embedVS (M.C.versions r m)
      | R.Name.Intermediate (m, v, o, _) -> R.embedVS (L.depRange d (m, v) o)
      | R.Name.Agreement (m, v, o) ->
          R.T.versions
            (R.reduceReal M.PkgSet.empty
               (L.DepFibred.endsFibre d (m, v) o)
               M.PubRel.empty rc)
            n)

  let dependees ((n, v) as p) =
    edges R.T.VSet.elements R.T.DependeesSet.elements
      (match n with
      | R.Name.Occurrence (m, q) ->
          R.T.dependees
            (R.reduceDeps
               (M.PkgSet.singleton (m, v))
               (L.DepFibred.tailFibre d (m, v))
               (L.PubFibred.tailFibre pub (m, v))
               q)
            p
      | R.Name.Intermediate (m, u, _, q) ->
          R.T.dependees
            (R.reduceDeps M.PkgSet.empty
               (L.DepFibred.tailFibre d (m, u))
               (L.PubFibred.tailFibre pub (m, u))
               q)
            p
      | R.Name.Agreement _ -> R.T.DependeesSet.empty)

  let real = R.T.PkgSet.elements (R.reduceReal r d pub rc)
  let deps = rel R.T.VSet.elements R.T.DepRel.elements (R.reduceDeps r d pub rc)

  let decode s =
    let s = R.T.PkgSet.ofList s in
    pkgs (M.PkgSet.elements (R.visibilityResolution r d pub rc s));
    parents (M.ParentRel.elements (R.parents r d pub rc s))
end

module Features = struct
  module M = E.Feature (S) (S) (S)
  module R = M.Reduction
  module L = R.Lookup

  type name = R.Name.t
  type version = string

  let compare_name = R.NameOT.compare
  let compare_version = S.compare

  let pp_name f = function
    | R.Name.Orig n -> str f n
    | R.Name.FeatPkg (n, x) -> Format.fprintf f "<%s,%s>" n x

  let pp_version = str
  let dep n v fs = (n, (M.VSet.ofList v, M.FSet.ofList fs))

  let r =
    M.PkgSet.ofList
      [ ("A", "1"); ("B", "1"); ("C", "1"); ("D", "1"); ("E", "1"); ("F", "1") ]

  let sup = M.SupportSet.ofList [ (("D", "1"), "α"); (("D", "1"), "β") ]

  let df =
    M.FeatDepRel.ofList
      [
        (("A", "1"), dep "B" [ "1" ] []);
        (("A", "1"), dep "C" [ "1" ] []);
        (("B", "1"), dep "D" [ "1" ] [ "α"; "β" ]);
        (("C", "1"), dep "D" [ "1" ] [ "β" ]);
      ]

  let da =
    M.AddlDepRel.ofList
      [
        ((("D", "1"), "α"), dep "E" [ "1" ] []);
        ((("D", "1"), "β"), dep "F" [ "1" ] []);
      ]

  let root = R.embedPkg ("A", "1")

  let versions n =
    R.T.VSet.elements
      (match n with
      | R.Name.Orig m ->
          R.T.versions
            (R.reduceReal (L.PkgFibred.tailFibre r m) M.SupportSet.empty)
            n
      | R.Name.FeatPkg (m, x) ->
          R.T.versions
            (R.reduceReal (L.PkgFibred.tailFibre r m) (L.supportFibre sup m x))
            n)

  let dependees ((n, v) as p) =
    edges R.T.VSet.elements R.T.DependeesSet.elements
      (match n with
      | R.Name.Orig m ->
          R.T.dependees
            (R.reduceDeps M.PkgSet.empty M.SupportSet.empty
               (L.FeatDepRelFibred.tailFibre df (m, v))
               M.AddlDepRel.empty)
            p
      | R.Name.FeatPkg (m, x) ->
          R.T.dependees
            (R.reduceDeps
               (M.PkgSet.singleton (m, v))
               (M.SupportSet.singleton ((m, v), x))
               M.FeatDepRel.empty
               (L.AddlDepRelFibred.tailFibre da ((m, v), x)))
            p)

  let real = R.T.PkgSet.elements (R.reduceReal r sup)

  let deps =
    rel R.T.VSet.elements R.T.DepRel.elements (R.reduceDeps r sup df da)

  let decode s =
    packages "packages"
      (List.map
         (fun ((n, v), fs) ->
           Printf.sprintf "%s %s %s" n v (set (M.FSet.elements fs)))
         (M.FeaturedSet.elements (R.featureResolution (R.T.PkgSet.ofList s))))
end

let spine form fs = "<" ^ String.concat " ∨ " (List.map form fs) ^ ">"

module Package_formula = struct
  module M = E.PackageFormula (S) (S)
  module R = M.Reduction
  module L = R.Lookup

  type name = R.Name.t
  type version = R.Version.t

  let compare_name = R.NameOT.compare
  let compare_version = R.VersionOT.compare

  let rec form = function
    | M.FDep (n, vs) -> Printf.sprintf "(%s,%s)" n (set (M.VSet.elements vs))
    | M.FConj (a, b) -> Printf.sprintf "(%s ∧ %s)" (form a) (form b)
    | M.FDisj (a, b) -> Printf.sprintf "(%s ∨ %s)" (form a) (form b)
    | M.FNeg a -> "¬" ^ form a

  let pp_name f = function
    | R.Name.Orig n -> str f n
    | R.Name.Disjunct fs -> str f (spine form fs)

  let pp_version f = function
    | R.Version.Orig v -> str f v
    | R.Version.Idx i -> Format.pp_print_int f (Pac_common.Ot.nat_int i)
    | R.Version.Bot -> str f "⊥"

  let dep n vs = M.FDep (n, M.VSet.ofList vs)
  let r = M.PkgSet.ofList [ ("A", "1"); ("B", "1"); ("B", "2"); ("C", "1") ]

  let d =
    M.DepRel.ofList
      [
        ( ("A", "1"),
          M.FDisj
            ( M.FConj (dep "B" [ "2" ], dep "C" [ "1" ]),
              M.FConj (dep "B" [ "1" ], M.FNeg (dep "C" [ "1" ])) ) );
      ]

  let root = R.embedPkg ("A", "1")

  let versions n =
    R.T.VSet.elements
      (match n with
      | R.Name.Orig m ->
          R.T.VSet.add R.Version.Bot
            (R.embedVS (M.C.versions (L.PkgFibred.tailFibre r m) m))
      | R.Name.Disjunct fs -> R.idxSet (Pac_common.Ot.int_nat (List.length fs)))

  let dependees p =
    edges R.T.VSet.elements R.T.DependeesSet.elements
      (match p with
      | R.Name.Orig m, R.Version.Orig v ->
          let dp = L.DepRelFibred.tailFibre d (m, v) in
          R.T.dependees
            (R.reduceDeps (L.realPreimage r (L.ownNegDepNames dp)) dp)
            p
      | R.Name.Orig _, R.Version.Bot -> R.T.DependeesSet.empty
      | R.Name.Disjunct fs, i -> (
          match L.disjAlt fs i with
          | Some g -> R.T.dependees (R.encodeNNF (M.C.versions r) p g) p
          | None -> R.T.DependeesSet.empty)
      | R.Name.Orig _, R.Version.Idx _ -> unasked ())

  let real = R.T.PkgSet.elements (R.reduceReal r d)
  let deps = rel R.T.VSet.elements R.T.DepRel.elements (R.reduceDeps r d)

  let decode s =
    pkgs (M.PkgSet.elements (R.packageFormulaResolution (R.T.PkgSet.ofList s)))
end

module Variable_formula = struct
  module X = struct
    include S

    let enum = [ "os" ]
  end

  module M = E.VariableFormula (S) (S) (X) (S)
  module PF = M.PF
  module R = M.Reduction
  module L = R.Lookup

  type name = R.Name.t
  type version = R.Version.t

  let compare_name = PF.Reduction.NameOT.compare
  let compare_version = PF.Reduction.VersionOT.compare
  let nx = function E.Inl n -> n | E.Inr x -> "<" ^ x ^ ">"
  let vy = function E.Inl s | E.Inr s -> s

  let rec form = function
    | PF.FDep (n, vs) ->
        Printf.sprintf "(%s,%s)" (nx n)
          (set (List.map vy (PF.VSet.elements vs)))
    | PF.FConj (a, b) -> Printf.sprintf "(%s ∧ %s)" (form a) (form b)
    | PF.FDisj (a, b) -> Printf.sprintf "(%s ∨ %s)" (form a) (form b)
    | PF.FNeg a -> "¬" ^ form a

  let pp_name f = function
    | R.Name.Orig n -> str f (nx n)
    | R.Name.Disjunct fs -> str f (spine form fs)

  let pp_version f = function
    | R.Version.Orig v -> str f (vy v)
    | R.Version.Idx i -> Format.pp_print_int f (Pac_common.Ot.nat_int i)
    | R.Version.Bot -> str f "⊥"

  let yx x = R.YSet.ofList (if x = "os" then [ "linux"; "macos" ] else [])
  let r = M.PkgSet.ofList [ ("A", "1"); ("B", "1") ]

  let d =
    M.DepRel.ofList
      [
        ( ("A", "1"),
          M.FDisj
            ( M.FNeg (M.FVarCmp ("os", E.OpEq, "linux")),
              M.FDep ("B", M.VSet.ofList [ "1" ]) ) );
      ]

  let root = R.embedPkg ("A", "1")

  let versions n =
    R.T.VSet.elements
      (match n with
      | R.Name.Orig (E.Inl m) ->
          R.T.VSet.add R.Version.Bot
            (R.embedVS (M.C.versions (L.PkgFibred.tailFibre r m) m))
      | R.Name.Orig (E.Inr x) ->
          R.T.versions
            (R.reduceReal (L.valuesAt yx x) M.PkgSet.empty M.DepRel.empty)
            n
      | R.Name.Disjunct fs ->
          PF.Reduction.idxSet (Pac_common.Ot.int_nat (List.length fs)))

  let dependees p =
    edges R.T.VSet.elements R.T.DependeesSet.elements
      (match p with
      | R.Name.Orig (E.Inl m), R.Version.Orig (E.Inl v) ->
          let dp = L.DepRelFibred.tailFibre d (m, v) in
          R.T.dependees
            (R.reduceDeps yx (L.realPreimage r (L.ownNegDepNames dp)) dp)
            p
      | R.Name.Orig (E.Inl _), R.Version.Bot | R.Name.Orig (E.Inr _), _ ->
          R.T.DependeesSet.empty
      | R.Name.Disjunct fs, i -> (
          match PF.Reduction.Lookup.disjAlt fs i with
          | Some g ->
              R.T.dependees
                (PF.Reduction.encodeNNF (R.liftOracle yx (M.C.versions r)) p g)
                p
          | None -> R.T.DependeesSet.empty)
      | R.Name.Orig (E.Inl _), _ -> unasked ())

  let real = R.T.PkgSet.elements (R.reduceReal yx r d)
  let deps = rel R.T.VSet.elements R.T.DepRel.elements (R.reduceDeps yx r d)

  let decode s =
    let s = R.T.PkgSet.ofList s in
    pkgs (M.PkgSet.elements (R.variableFormulaResolution s));
    Printf.printf "assignment: os = %s\n"
      (R.extractAssignment "linux" yx s "os")
end

module Virtual = struct
  module M = E.Virtual (S) (S)
  module R = M.Reduction
  module L = R.Lookup

  type name = R.Name.t
  type version = R.Version.t

  let compare_name = R.NameOT.compare
  let compare_version = R.VersionOT.compare

  let pp_name f = function
    | R.Name.Orig n -> str f n
    | R.Name.Selector ((n, v), m) -> Format.fprintf f "<(%s,%s),%s>" n v m

  let pp_version f = function
    | R.Version.Orig v -> str f v
    | R.Version.Provider (m, w) -> Format.fprintf f "<%s,%s>" m w

  let vs l = M.VSet.ofList l

  let r =
    M.PkgSet.ofList
      [ ("A", "1"); ("B", "1"); ("C", "1"); ("E", "1"); ("F", "1") ]

  let d =
    M.C.DepRel.ofList
      [ (("A", "1"), ("D", vs [ "1" ])); (("A", "1"), ("E", vs [ "1" ])) ]

  let pi =
    M.ProvidesRel.ofList
      [
        (("B", "1"), ("D", M.VTVal "1"));
        (("C", "1"), ("D", M.VTVal "1"));
        (("F", "1"), ("E", M.VTVal "1"));
      ]

  let root = R.embedPkg ("A", "1")

  let versions n =
    R.T.VSet.elements
      (match n with
      | R.Name.Orig m ->
          R.T.versions
            (R.reduceReal
               (L.PkgFibred.tailFibre r m)
               M.C.DepRel.empty M.ProvidesRel.empty)
            n
      | R.Name.Selector (q, m) ->
          R.T.versions
            (R.reduceReal
               (L.PkgFibred.tailFibre r m)
               (L.DepRelFibred.endsFibre d q m)
               (L.ProvFibred.nodeFibre pi m))
            n)

  let dependees p =
    edges R.T.VSet.elements R.T.DependeesSet.elements
      (match p with
      | R.Name.Orig n, R.Version.Orig v ->
          let dp = L.DepRelFibred.tailFibre d (n, v) in
          R.T.dependees
            (R.reduceDeps (L.realPreimage r dp) dp (L.provPreimage pi dp))
            p
      | R.Name.Selector (q, m), R.Version.Provider _ ->
          R.T.dependees
            (R.reduceDeps
               (L.PkgFibred.tailFibre r m)
               (L.DepRelFibred.tailFibre d q)
               (L.ProvFibred.nodeFibre pi m))
            p
      | R.Name.Orig _, R.Version.Provider _
      | R.Name.Selector _, R.Version.Orig _ ->
          unasked ())

  let real = R.T.PkgSet.elements (R.reduceReal r d pi)
  let deps = rel R.T.VSet.elements R.T.DepRel.elements (R.reduceDeps r d pi)

  let decode s =
    let s = R.T.PkgSet.ofList s in
    pkgs (M.PkgSet.elements (R.virtualResolution s));
    packages "providers"
      (List.map
         (fun ((m, u), (n, (p, v))) ->
           Printf.sprintf "%s %s for %s <- %s %s" m u n p v)
         (M.RhoRel.elements (R.providers d pi s)))
end

module Concurrent_features = struct
  module M = E.FeatureConcurrent (S) (S) (S) (S)
  module F = M.Feat
  module R = M.Reduction
  module L = R.Lookup

  type name = R.Name.t
  type version = string

  let compare_name = R.NameOT.compare
  let compare_version = S.compare

  let pp_name f = function
    | R.Name.GranularOrig (n, w) -> Format.fprintf f "<%s,%s>" n w
    | R.Name.GranularFeatPkg (n, x, w) -> Format.fprintf f "<<%s,%s>,%s>" n x w
    | R.Name.Intermediate (n, v, m) -> Format.fprintf f "<%s,%s,%s>" n v m
    | R.Name.IntermediateF (n, v, m, x) ->
        Format.fprintf f "<%s,%s,%s,%s>" n v m x
    | R.Name.IntermediateA (n, v, x, m, y) ->
        Format.fprintf f "<%s,%s,%s,%s,%s>" n v x m y

  let pp_version = str
  let g v = v
  let dep n v fs = (n, (M.VSet.ofList v, F.FSet.ofList fs))

  let r =
    M.PkgSet.ofList
      [
        ("A", "1");
        ("B", "1");
        ("C", "1");
        ("D", "1");
        ("D", "2");
        ("D", "3");
        ("F", "1");
      ]

  let sup =
    F.SupportSet.ofList
      [
        (("D", "1"), "α");
        (("D", "2"), "α");
        (("D", "1"), "β");
        (("D", "2"), "β");
        (("D", "3"), "β");
        (("F", "1"), "γ");
        (("F", "1"), "δ");
      ]

  let df =
    F.FeatDepRel.ofList
      [
        (("A", "1"), dep "B" [ "1" ] []);
        (("A", "1"), dep "C" [ "1" ] []);
        (("B", "1"), dep "D" [ "1"; "2" ] [ "α" ]);
        (("C", "1"), dep "D" [ "2"; "3" ] [ "β" ]);
      ]

  let da =
    F.AddlDepRel.ofList
      [
        ((("D", "1"), "α"), dep "F" [ "1" ] [ "γ" ]);
        ((("D", "1"), "β"), dep "F" [ "1" ] [ "δ" ]);
      ]

  let root = R.embedOrigPkg g ("A", "1")

  let versions n =
    R.T.VSet.elements
      (match n with
      | R.Name.GranularOrig (m, w) ->
          R.T.versions
            (R.reduceReal (L.granFibre g r m w) F.SupportSet.empty
               F.FeatDepRel.empty F.AddlDepRel.empty g)
            n
      | R.Name.GranularFeatPkg (m, x, w) ->
          R.T.versions
            (R.reduceReal (L.granFibre g r m w)
               (F.Reduction.Lookup.supportFibre sup m x)
               F.FeatDepRel.empty F.AddlDepRel.empty g)
            n
      | R.Name.Intermediate (m, u, o) ->
          R.T.versions
            (R.reduceReal M.PkgSet.empty F.SupportSet.empty
               (L.FeatDepRelFibred.endsFibre df (m, u) o)
               (L.pkgNodeFibre da (m, u) o)
               g)
            n
      | R.Name.IntermediateF (m, u, o, _) ->
          R.T.versions
            (R.reduceReal M.PkgSet.empty F.SupportSet.empty
               (L.FeatDepRelFibred.endsFibre df (m, u) o)
               F.AddlDepRel.empty g)
            n
      | R.Name.IntermediateA (m, u, x, o, _) ->
          R.T.versions
            (R.reduceReal M.PkgSet.empty F.SupportSet.empty F.FeatDepRel.empty
               (L.AddlDepRelFibred.endsFibre da ((m, u), x) o)
               g)
            n)

  let dependees ((n, v) as p) =
    edges R.T.VSet.elements R.T.DependeesSet.elements
      (match n with
      | R.Name.GranularOrig (m, _) ->
          R.T.dependees
            (R.reduceDeps M.PkgSet.empty F.SupportSet.empty
               (L.FeatDepRelFibred.tailFibre df (m, v))
               F.AddlDepRel.empty g)
            p
      | R.Name.GranularFeatPkg (m, x, _) ->
          R.T.dependees
            (R.reduceDeps
               (M.PkgSet.singleton (m, v))
               (F.SupportSet.singleton ((m, v), x))
               F.FeatDepRel.empty
               (L.AddlDepRelFibred.tailFibre da ((m, v), x))
               g)
            p
      | R.Name.Intermediate (m, u, o) ->
          R.T.dependees
            (R.reduceDeps M.PkgSet.empty F.SupportSet.empty
               (L.FeatDepRelFibred.endsFibre df (m, u) o)
               (L.pkgNodeFibre da (m, u) o)
               g)
            p
      | R.Name.IntermediateF (m, u, o, _) ->
          R.T.dependees
            (R.reduceDeps M.PkgSet.empty F.SupportSet.empty
               (L.FeatDepRelFibred.endsFibre df (m, u) o)
               F.AddlDepRel.empty g)
            p
      | R.Name.IntermediateA (m, u, x, o, _) ->
          R.T.dependees
            (R.reduceDeps M.PkgSet.empty F.SupportSet.empty F.FeatDepRel.empty
               (L.AddlDepRelFibred.endsFibre da ((m, u), x) o)
               g)
            p)

  let real = R.T.PkgSet.elements (R.reduceReal r sup df da g)

  let deps =
    rel R.T.VSet.elements R.T.DepRel.elements (R.reduceDeps r sup df da g)

  let decode s =
    let s = R.T.PkgSet.ofList s in
    packages "packages"
      (List.map
         (fun ((n, v), fs) ->
           Printf.sprintf "%s %s %s" n v (set (F.FSet.elements fs)))
         (F.FeaturedSet.elements (R.featureConcurrentResolution g s)));
    parents (M.ParentRel.elements (R.parents s))
end

let examples : (string * (module EXAMPLE)) list =
  [
    ("conflict-class", (module Conflict_class));
    ("conflict", (module Conflict));
    ("concurrent", (module Concurrent));
    ("peer", (module Peer));
    ("visibility", (module Visibility));
    ("features", (module Features));
    ("package-formula", (module Package_formula));
    ("variable-formula", (module Variable_formula));
    ("virtual", (module Virtual));
    ("concurrent-features", (module Concurrent_features));
  ]

let () =
  match
    List.assoc_opt
      (if Array.length Sys.argv > 1 then Sys.argv.(1) else "")
      examples
  with
  | Some x ->
      let module X = (val x) in
      let module R = Run (X) in
      R.run ()
  | None ->
      prerr_endline
        ("usage: extensions <" ^ String.concat "|" (List.map fst examples) ^ ">");
      exit 2
