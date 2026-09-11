open Cmdliner

let debug_arg =
  Arg.(value & flag & info [ "debug" ] ~doc:"Trace the PubGrub search.")

let debian_run debug mono native goal paths =
  Pubgrub.set_debug debug;
  match Deb_solve.solve_files ~debug ~monolithic:mono ~native ~paths ~goal with
  | None -> 1
  | Some pkgs ->
      List.iter (fun (n, b, v) -> Printf.printf "%s:%s %s\n" n b v) pkgs;
      0

let debian_cmd =
  let mono =
    Arg.(
      value & flag
      & info [ "mono" ]
          ~doc:"Translate the whole archive instead of per-name slices.")
  in
  let native =
    Arg.(
      value & opt string "amd64"
      & info [ "native" ] ~docv:"ARCH" ~doc:"Native architecture.")
  in
  let goal =
    Arg.(
      required
      & pos 0 (some string) None
      & info [] ~docv:"GOAL" ~doc:"Package to install, optionally NAME:ARCH.")
  in
  let paths =
    Arg.(
      non_empty & pos_right 0 file []
      & info [] ~docv:"PACKAGES" ~doc:"Debian Packages index files.")
  in
  Cmd.v
    (Cmd.info "debian" ~doc:"Solve against Debian Packages indices.")
    Term.(const debian_run $ debug_arg $ mono $ native $ goal $ paths)

let opam_run debug repo goal =
  let t0 = Unix.gettimeofday () in
  let ar = Opam_solve.load_repo repo in
  let vars = ref [] in
  Hashtbl.iter
    (fun _ vs ->
      List.iter (fun (_, m) -> vars := Opam_parse.meta_vars m @ !vars) vs)
    ar.Opam_solve.pkgs;
  let vars = List.sort_uniq String.compare !vars in
  let t1 = Unix.gettimeofday () in
  Printf.printf "archive loaded: %d variables, %.2fs\n%!" (List.length vars)
    (t1 -. t0);
  if !Opam_parse.rejected > 0 then
    Printf.printf "parser dropped %d rows\n%!" !Opam_parse.rejected;
  let module S = Opam_solve.Make (struct
    let vars = vars
  end) in
  match S.solve ~debug ar goal with
  | None -> 1
  | Some (reals, total, depexts) ->
      let t3 = Unix.gettimeofday () in
      Printf.printf "opam packages (%d, core solution %d nodes):\n"
        (List.length reals) total;
      List.iter (fun (n, v) -> Printf.printf "  %s.%s\n" n v) reals;
      if depexts <> [] then begin
        Printf.printf "system packages (%d):\n" (List.length depexts);
        List.iter (fun e -> Printf.printf "  %s\n" e) depexts
      end;
      Printf.printf "solve %.2fs\n" (t3 -. t1);
      0

let opam_cmd =
  let repo =
    Arg.(
      required
      & pos 0 (some dir) None
      & info [] ~docv:"REPO" ~doc:"opam repository root.")
  in
  let goal =
    Arg.(
      required
      & pos 1 (some string) None
      & info [] ~docv:"GOAL" ~doc:"Package to install.")
  in
  Cmd.v
    (Cmd.info "opam" ~doc:"Solve against an opam repository.")
    Term.(const opam_run $ debug_arg $ repo $ goal)

let cargo_run debug index goal wanted rfeats =
  let t0 = Unix.gettimeofday () in
  let ar = Cargo_solve.empty_archive index in
  let vs = Cargo_solve.versions_of ar goal in
  if vs = [] then (
    Printf.eprintf "no resolvable versions of %s under %s\n" goal index;
    1)
  else begin
    let rv =
      match wanted with
      | Some v -> v
      | None ->
          List.fold_left
            (fun a b -> if Cargo_version.compare b a > 0 then b else a)
            (List.hd vs) vs
    in
    let rc = (goal, rv) in
    Printf.printf "root %s %s%s\n%!" goal rv
      (match rfeats with
      | None -> ""
      | Some fs -> " with features " ^ String.concat "," fs);
    let module S = Cargo_solve.Make () in
    let r =
      match rfeats with
      | None -> S.solve ~debug ar rc
      | Some fs -> S.solve ~debug ~rfeats:fs ar rc
    in
    (* the crates the run parsed, known only once it is over: there is no
       cone, so this is what the solver asked for and nothing more *)
    let loaded () =
      let t2 = Unix.gettimeofday () in
      Printf.printf "loaded: %d crates, %d versions\n" ar.Cargo_solve.n_names
        ar.Cargo_solve.n_vers;
      if !Cargo_parse.rejected > 0 then
        Printf.printf "parser dropped %d rows\n" !Cargo_parse.rejected;
      Printf.printf "parse %.2fs\nsolve %.2fs\n" ar.Cargo_solve.t_parse
        (t2 -. t0 -. ar.Cargo_solve.t_parse)
    in
    match r with
    | None ->
        loaded ();
        1
    | Some r ->
        Printf.printf "crates (%d):\n" (List.length r.S.crates);
        List.iter
          (fun (n, v) ->
            let fs =
              match
                List.find_opt (fun (m, u, _) -> m = n && u = v) r.S.feats
              with
              | Some (_, _, fs) -> fs
              | None -> []
            in
            Printf.printf "  %s %s%s\n" n v
              (if fs = [] then "" else " [" ^ String.concat "," fs ^ "]"))
          r.S.crates;
        Printf.printf
          "encoded solution: %d core nodes (%d crate versions encoded)\n"
          r.S.nodes r.S.processed;
        Printf.printf "selections: %d\n" (List.length r.S.sel);
        loaded ();
        0
  end

let cargo_cmd =
  let index =
    Arg.(
      required
      & pos 0 (some dir) None
      & info [] ~docv:"INDEX" ~doc:"crates.io-index checkout.")
  in
  let goal =
    Arg.(
      required
      & pos 1 (some string) None
      & info [] ~docv:"CRATE" ~doc:"Crate to build.")
  in
  let wanted =
    Arg.(
      value
      & pos 2 (some string) None
      & info [] ~docv:"VERSION" ~doc:"Root version; defaults to the newest.")
  in
  let rfeats =
    Arg.(
      value
      & opt (some (list string)) None
      & info [ "features" ] ~docv:"FEATS"
          ~doc:"Comma-separated features to enable on the root crate.")
  in
  Cmd.v
    (Cmd.info "cargo" ~doc:"Solve against a crates.io index.")
    Term.(const cargo_run $ debug_arg $ index $ goal $ wanted $ rfeats)

let alpine_run debug path goals =
  let t0 = Unix.gettimeofday () in
  let ar = Apk_solve.load_index path in
  let t1 = Unix.gettimeofday () in
  Printf.printf
    "index %s\n\
     cone: %d packages, %d provide rows, %d install_if rows\n\
     parse %.2fs\n\
     %!"
    path ar.Apk_solve.n_pkgs ar.Apk_solve.n_provs ar.Apk_solve.n_trigs (t1 -. t0);
  if !Apk_parse.rejected > 0 then
    Printf.printf "parser dropped %d rows\n%!" !Apk_parse.rejected;
  let world = Apk_solve.world_of_args goals in
  if world = [] then 2
  else
    match Apk_solve.solve ~debug ar world with
    | None -> 1
    | Some r ->
        let t2 = Unix.gettimeofday () in
        Printf.printf "packages (%d):\n" (List.length r.Apk_solve.pkgs);
        List.iter (fun (n, v) -> Printf.printf "  %s %s\n" n v) r.Apk_solve.pkgs;
        Printf.printf
          "encoded solution: %d core nodes (%d Alpine packages encoded)\n"
          r.Apk_solve.nodes r.Apk_solve.processed;
        Printf.printf "solve %.2fs\n" (t2 -. t1);
        0

let alpine_cmd =
  let path =
    Arg.(
      required
      & pos 0 (some file) None
      & info [] ~docv:"APKINDEX" ~doc:"Uncompressed APKINDEX file.")
  in
  let goals =
    Arg.(
      non_empty & pos_right 0 string []
      & info [] ~docv:"PKG" ~doc:"Packages forming the world.")
  in
  Cmd.v
    (Cmd.info "alpine" ~doc:"Solve against an Alpine APKINDEX.")
    Term.(const alpine_run $ debug_arg $ path $ goals)

let npm_run debug cache offline tree goal wanted =
  let t0 = Unix.gettimeofday () in
  let ar = Npm_solve.empty_archive ~cache ~offline in
  let vs =
    List.map
      (fun (v : Npm_parse.ver) -> v.Npm_parse.v_vers)
      (Npm_solve.load_name ar ~root:true goal)
  in
  if vs = [] then (
    Printf.eprintf "no packument for %s under %s%s\n" goal cache
      (if offline then " (offline)" else "");
    1)
  else begin
    let rv =
      match wanted with
      | Some v -> v
      | None -> (
          match Hashtbl.find_opt ar.Npm_solve.latest goal with
          | Some l when List.mem l vs -> l
          | _ ->
              List.fold_left
                (fun a b -> if Npm_version.compare b a > 0 then b else a)
                (List.hd vs) vs)
    in
    let rc = (goal, rv) in
    Printf.printf "root %s %s\n%!" goal rv;
    match Npm_solve.solve ~debug ar rc with
    | None -> 1
    | Some r ->
        let t2 = Unix.gettimeofday () in
        let show (a, t) v =
          if a = t then Printf.sprintf "%s %s" t v
          else Printf.sprintf "%s %s at %s" t v a
        in
        Printf.printf "packages (%d):\n" (List.length r.Npm_solve.installs);
        List.iter
          (fun (k, v) -> Printf.printf "  %s\n" (show k v))
          r.Npm_solve.installs;
        if tree then begin
          Printf.printf "node_modules (%d edges):\n"
            (List.length r.Npm_solve.tree);
          List.iter
            (fun ((ck, cv), (pk, pv)) ->
              Printf.printf "  %s <- %s\n" (show pk pv) (show ck cv))
            r.Npm_solve.tree
        end
        else
          Printf.printf "node_modules edges: %d\n"
            (List.length r.Npm_solve.tree);
        Printf.printf "cone: %d packages, %d versions, %d packuments fetched\n"
          ar.Npm_solve.n_names ar.Npm_solve.n_vers ar.Npm_solve.n_fetched;
        if !Npm_parse.rejected > 0 then
          Printf.printf "parser dropped %d rows\n" !Npm_parse.rejected;
        if !Npm_parse.skipped_optional > 0 then
          Printf.printf "optionalDependencies not modelled: %d\n"
            !Npm_parse.skipped_optional;
        Printf.printf "encoded solution: %d core nodes (%d lookups)\n"
          r.Npm_solve.nodes r.Npm_solve.queries;
        Printf.printf "solve %.2fs\n" (t2 -. t0);
        0
  end

let npm_cmd =
  let cache =
    Arg.(
      value & opt string "repos/npm"
      & info [ "cache" ] ~docv:"DIR" ~doc:"Packument cache directory.")
  in
  let offline =
    Arg.(
      value & flag
      & info [ "offline" ] ~doc:"Fail rather than fetch a missing packument.")
  in
  let tree =
    Arg.(value & flag & info [ "tree" ] ~doc:"Print the node_modules nesting.")
  in
  let goal =
    Arg.(
      required
      & pos 0 (some string) None
      & info [] ~docv:"PACKAGE" ~doc:"Package to install.")
  in
  let wanted =
    Arg.(
      value
      & pos 1 (some string) None
      & info [] ~docv:"VERSION"
          ~doc:"Root version; defaults to dist-tags.latest.")
  in
  Cmd.v
    (Cmd.info "npm" ~doc:"Solve against the npm registry.")
    Term.(const npm_run $ debug_arg $ cache $ offline $ tree $ goal $ wanted)

let () =
  let doc = "Solve dependencies through the verified package calculus." in
  exit
    (Cmd.eval'
       (Cmd.group (Cmd.info "pac" ~doc)
          [ debian_cmd; opam_cmd; cargo_cmd; alpine_cmd; npm_cmd ]))
