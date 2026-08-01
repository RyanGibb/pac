(* Per-extension reduction case studies.  Each one encodes a small concrete
   calculus instance into the corresponding nat-instantiated Smoke module,
   then prints the source instance and the core reduction (reduceReal
   packages, reduceDeps edges).  Symbolic names/versions are mapped to nat
   per the header comment of each case study. *)

module E = Pac

let rec i2n i = if i <= 0 then E.O else E.S (i2n (i - 1))
let rec n2i = function E.O -> 0 | E.S n -> 1 + n2i n

(* Package names are nat codes 1,2,3,...; render them as A,B,C,... *)
let nm n =
  if n >= 1 && n <= 26 then String.make 1 (Char.chr (Char.code 'A' + n - 1))
  else string_of_int n

(* ------------------------------------------------------------------ *)
(* Conflict: (A,1) conflicts B (<< 3), i.e. B at versions {1,2}.       *)
(* ------------------------------------------------------------------ *)
let conflict () =
  let module M = E.Cfl in
  let module R = M.Reduction in
  let pkg n v = (i2n n, i2n v) in
  let vset l =
    List.fold_left (fun s v -> M.C.VSet.add (i2n v) s) M.C.VSet.empty l
  in
  let pset l =
    List.fold_left (fun s p -> M.C.PkgSet.add p s) M.C.PkgSet.empty l
  in
  let pp_vs vs =
    "{"
    ^ String.concat ","
        (List.map (fun v -> string_of_int (n2i v)) (M.C.VSet.elements vs))
    ^ "}"
  in
  let pp_src (n, v) = Printf.sprintf "(%s,%d)" (nm (n2i n)) (n2i v) in
  (* source *)
  let r = pset [ pkg 1 1; pkg 2 1; pkg 2 2 ] in
  let g =
    M.ConflictRel.add (pkg 1 1, (i2n 2, vset [ 1; 2 ])) M.ConflictRel.empty
  in
  let d = M.C.DepRel.empty in
  Printf.printf "Conflict Package Calculus\n";
  Printf.printf "  packages R_G: %s\n"
    (String.concat " " (List.map pp_src (M.C.PkgSet.elements r)));
  Printf.printf "  conflicts G:\n";
  List.iter
    (fun (p, (n, vs)) ->
      Printf.printf "    %s conflicts %s %s\n" (pp_src p)
        (nm (n2i n))
        (pp_vs vs))
    (M.ConflictRel.elements g);
  (* target pretty-printers *)
  let pp_tn = function
    | R.Name.Orig n -> nm (n2i n)
    | R.Name.Synthetic (n, vs) ->
        Printf.sprintf "<%s,%s>" (nm (n2i n)) (pp_vs vs)
  in
  let pp_tv = function
    | R.Version.Orig v -> string_of_int (n2i v)
    | R.Version.Zero -> "0"
    | R.Version.One -> "1"
  in
  let pp_tp (n, v) = Printf.sprintf "(%s,%s)" (pp_tn n) (pp_tv v) in
  let pp_tvs vs =
    "{" ^ String.concat "," (List.map pp_tv (R.T.VSet.elements vs)) ^ "}"
  in
  Printf.printf "reduceReal -> core packages:\n";
  List.iter
    (fun p -> Printf.printf "    %s\n" (pp_tp p))
    (R.T.PkgSet.elements (R.reduceReal r g));
  Printf.printf "reduceDeps -> core dependencies:\n";
  List.iter
    (fun (s, (n, vs)) ->
      Printf.printf "    %s -> (%s,%s)\n" (pp_tp s) (pp_tn n) (pp_tvs vs))
    (R.T.DepRel.elements (R.reduceDeps d g))

(* ------------------------------------------------------------------ *)
(* Concurrent, g(x.y.z)=x.  Versions map x.y.z -> xyz                   *)
(* as x*100+y*10+z; g v = v/100.                                        *)
(* ------------------------------------------------------------------ *)
let concurrent () =
  let module M = E.Conc in
  let module R = M.Reduction in
  let vshow = function
    | 100 -> "1.0.0"
    | 200 -> "2.0.0"
    | 201 -> "2.0.1"
    | 300 -> "3.0.0"
    | k -> string_of_int k
  in
  let pkg n v = (i2n n, i2n v) in
  let vset l =
    List.fold_left (fun s v -> M.C.VSet.add (i2n v) s) M.C.VSet.empty l
  in
  let pset l = List.fold_left (fun s p -> M.PkgSet.add p s) M.PkgSet.empty l in
  let drel l =
    List.fold_left
      (fun s ((sn, sv), (dn, dvs)) ->
        M.C.DepRel.add ((i2n sn, i2n sv), (i2n dn, vset dvs)) s)
      M.C.DepRel.empty l
  in
  let g u = i2n (n2i u / 100) in
  let r =
    pset
      [
        pkg 1 100;
        pkg 2 100;
        pkg 3 100;
        pkg 4 100;
        pkg 4 200;
        pkg 4 201;
        pkg 4 300;
      ]
  in
  let d =
    drel
      [
        ((1, 100), (2, [ 100 ]));
        ((1, 100), (3, [ 100 ]));
        ((2, 100), (4, [ 100; 200; 201 ]));
        ((3, 100), (4, [ 200; 201; 300 ]));
      ]
  in
  let pp_src (n, v) = Printf.sprintf "(%s,%s)" (nm (n2i n)) (vshow (n2i v)) in
  let pp_vs vs =
    "{"
    ^ String.concat ","
        (List.map (fun v -> vshow (n2i v)) (M.C.VSet.elements vs))
    ^ "}"
  in
  Printf.printf "Concurrent Package Calculus, g(x.y.z)=x\n";
  Printf.printf "  packages R: %s\n"
    (String.concat " " (List.map pp_src (M.PkgSet.elements r)));
  Printf.printf "  dependencies D_C:\n";
  List.iter
    (fun (s, (n, vs)) ->
      Printf.printf "    %s -> %s %s\n" (pp_src s) (nm (n2i n)) (pp_vs vs))
    (M.C.DepRel.elements d);
  let pp_tn = function
    | R.Name.Granular (n, w) -> Printf.sprintf "<%s,%d>" (nm (n2i n)) (n2i w)
    | R.Name.Intermediate (n, v, m) ->
        Printf.sprintf "<%s,%s,%s>" (nm (n2i n)) (vshow (n2i v)) (nm (n2i m))
  in
  let pp_tv = function
    | R.Version.Orig v -> vshow (n2i v)
    | R.Version.Gran w -> string_of_int (n2i w)
  in
  let pp_tp (n, v) = Printf.sprintf "(%s,%s)" (pp_tn n) (pp_tv v) in
  let pp_tvs vs =
    "{" ^ String.concat "," (List.map pp_tv (R.T.VSet.elements vs)) ^ "}"
  in
  Printf.printf "reduceReal -> core packages:\n";
  List.iter
    (fun p -> Printf.printf "    %s\n" (pp_tp p))
    (R.T.PkgSet.elements (R.reduceReal r d g));
  Printf.printf "reduceDeps -> core dependencies:\n";
  List.iter
    (fun (s, (n, vs)) ->
      Printf.printf "    %s -> (%s,%s)\n" (pp_tp s) (pp_tn n) (pp_tvs vs))
    (R.T.DepRel.elements (R.reduceDeps d g))

let () =
  match if Array.length Sys.argv > 1 then Sys.argv.(1) else "" with
  | "conflict" -> conflict ()
  | "concurrent" -> concurrent ()
  | s ->
      Printf.eprintf "usage: reductions <conflict|concurrent> (got %S)\n" s;
      exit 2
