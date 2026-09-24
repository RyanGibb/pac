open Cmdliner

let debug_arg =
  Arg.(value & flag & info [ "debug" ] ~doc:"Trace the PubGrub search.")

let debian_run debug apt_heap no_recs no_strict native goal paths =
  Pubgrub.set_debug debug;
  match
    Deb_solve.solve_files ~debug ~apt_heap ~recommends:(not no_recs)
      ~strict_pinning:(not no_strict) ~native ~paths ~goal
  with
  | None -> 1
  | Some (pkgs, t_parse, t_solve) ->
      List.iter (fun (n, b, v) -> Printf.printf "%s:%s %s\n" n b v) pkgs;
      Printf.printf "parse %.2fs\nsolve %.2fs\n" t_parse t_solve;
      0

let debian_cmd =
  (* Recommends are installed by default, as under apt's
     APT::Install-Recommends; the flag spells the same opt-out apt does. *)
  let no_recs =
    Arg.(
      value & flag
      & info [ "no-install-recommends" ]
          ~doc:"Ignore Recommends fields rather than satisfying them.")
  in
  let apt_heap =
    Arg.(
      value & flag
      & info [ "apt-heap" ]
          ~doc:"Replay apt's work-heap scheduling for exact correspondence.")
  in
  (* the same opt-out apt-get spells for APT::Solver::Strict-Pinning *)
  let no_strict =
    Arg.(
      value & flag
      & info [ "no-strict-pinning" ]
          ~doc:
            "Offer every version in the Packages files, not only apt's \
             candidate (the newest).")
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
    Term.(
      const debian_run $ debug_arg $ apt_heap $ no_recs $ no_strict $ native
      $ goal $ paths)

let opam_run debug zi_order with_test with_doc with_dev_setup opam_version
    repo atoms =
  let t0 = Unix.gettimeofday () in
  let ar = Opam_solve.empty_archive repo in
  let module S = Opam_solve.Make () in
  let query = List.map Opam_parse.atom_of_string atoms in
  let r =
    S.solve ~debug ~zi_order ~with_test ~with_doc ~with_dev_setup
      ~opam_version ar query
  in
  (* the names the run parsed, known only once it is over: there is no
     cone, so this is what the solver asked for and nothing more *)
  let loaded () =
    let t1 = Unix.gettimeofday () in
    Printf.printf "loaded: %d names, %d package versions\n"
      ar.Opam_solve.n_names ar.Opam_solve.n_vers;
    if !Opam_parse.rejected > 0 then
      Printf.printf "parser dropped %d declarations\n" !Opam_parse.rejected;
    Printf.printf "parse %.2fs\nsolve %.2fs\n" ar.Opam_solve.t_parse
      (t1 -. t0 -. ar.Opam_solve.t_parse)
  in
  match r with
  | None ->
      loaded ();
      1
  | Some (reals, total, depexts) ->
      Printf.printf "opam packages (%d, core solution %d nodes):\n"
        (List.length reals) total;
      List.iter (fun (n, v) -> Printf.printf "  %s.%s\n" n v) reals;
      if depexts <> [] then begin
        Printf.printf "system packages (%d):\n" (List.length depexts);
        List.iter (fun e -> Printf.printf "  %s\n" e) depexts
      end;
      loaded ();
      0

let opam_cmd =
  (* opam's builtin-0install backend decides a name as soon as its decider
     walks onto it, which is not the order PubGrub's own heuristic picks;
     the flag replays that walk for exact correspondence. *)
  let zi_order =
    Arg.(
      value & flag
      & info [ "0install-order" ]
          ~doc:
            "Replay builtin-0install's decision order for exact \
             correspondence.")
  in
  (* the flags opam install itself has for enabling dependencies, and only
     those: build is true whenever opam solves, since nothing is installed
     without being built, so there is no --with-build to match.  Each is
     query-scoped rather than global -- it holds of the names the query
     asks for and of nothing they pull in -- which is what the instance's
     namespaced variables express; see [rho] in opam_solve.ml. *)
  let with_test =
    Arg.(
      value & flag
      & info [ "t"; "with-test" ]
          ~doc:"Enable the queried packages' test-only dependencies.")
  in
  let with_doc =
    Arg.(
      value & flag
      & info [ "with-doc" ]
          ~doc:"Enable the queried packages' doc-only dependencies.")
  in
  let with_dev_setup =
    Arg.(
      value & flag
      & info [ "with-dev-setup" ]
          ~doc:"Enable the queried packages' developer-only dependencies.")
  in
  (* the one global variable that is a fact about opam itself rather than
     about the host, which opam answers with its own version and refuses to
     have set; whoever compares against an opam says which one here *)
  let opam_version =
    Arg.(
      value
      & opt string Opam_solve.default_opam_version
      & info [ "opam-version" ] ~docv:"VERSION"
          ~doc:
            "Value of the opam-version variable, the version of the opam \
             whose answer is being matched.")
  in
  let repo =
    Arg.(
      required
      & pos 0 (some dir) None
      & info [] ~docv:"REPO" ~doc:"opam repository root.")
  in
  (* an installation request is a query: a set of names each with a set of
     acceptable versions, which the frontend realises as the synthetic
     root's dependencies.  The syntax of one element is opam's own
     (OpamFormula.atom_of_string), and many of them make one request, as
     [atom_list] in opamArg.ml does. *)
  let query =
    Arg.(
      non_empty & pos_right 0 string []
      & info [] ~docv:"PACKAGES"
          ~doc:
            "Packages to install, each a name with an optional version or \
             constraint, e.g. $(b,pkg), $(b,pkg.1.0) or $(b,pkg>=0.5).")
  in
  Cmd.v
    (Cmd.info "opam" ~doc:"Solve against an opam repository.")
    Term.(
      const opam_run $ debug_arg $ zi_order $ with_test $ with_doc
      $ with_dev_setup $ opam_version $ repo $ query)

let cargo_run debug print_parents index goal wanted rfeats rustv =
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
    Printf.printf "root %s %s%s%s\n%!" goal rv
      (match rfeats with
      | None -> ""
      | Some fs -> " with features " ^ String.concat "," fs)
      (match rustv with None -> "" | Some t -> " for rust " ^ t);
    let module S = Cargo_solve.Make () in
    let r = S.solve ~debug ?rfeats ~rustv ar rc in
    (* the crates the run parsed, known only once it is over: there is no
       cone, so this is what the solver asked for and nothing more *)
    let loaded () =
      let t2 = Unix.gettimeofday () in
      Printf.printf "loaded: %d crates, %d versions\n" ar.Cargo_solve.n_names
        ar.Cargo_solve.n_vers;
      if !Cargo_parse.rejected > 0 then
        Printf.printf "parser dropped %d declarations\n" !Cargo_parse.rejected;
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
        Printf.printf "parent edges: %d\n" (List.length r.S.parents);
        if print_parents then begin
          Printf.printf "parent-edges:\n";
          List.iter
            (fun (n, v, a, t, u) ->
              Printf.printf "  %s %s -> %s(%s) %s\n" n v a t u)
            r.S.parents
        end;
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
  (* unset, the root gets every feature it declares, which is the
     resolution cargo writes to Cargo.lock; naming features asks instead
     for the filtered view cargo builds from that lock *)
  let rfeats =
    Arg.(
      value
      & opt (some (list string)) None
      & info [ "features" ] ~docv:"FEATS"
          ~doc:
            "Comma-separated features to enable on the root crate; unset, \
             every feature the root declares is enabled, as when cargo \
             writes a lockfile.")
  in
  (* resolver v3's MSRV-aware preference, which is off unless a toolchain
     is configured -- cargo reads one from rust-version or rustc, this
     asks for it *)
  let rustv =
    Arg.(
      value
      & opt (some string) None
      & info [ "rust-version" ] ~docv:"VERSION"
          ~doc:
            "Toolchain version to prefer MSRV-compatible crate versions \
             for, as resolver v3 does; unset leaves the preference off.")
  in
  (* the decoded parent relation, one line per edge, for a correspondence
     harness to diff against cargo's own (depender, dependee) edges; off by
     default because the edge list dwarfs the version set it accompanies *)
  let print_parents =
    Arg.(
      value & flag
      & info [ "print-parents" ]
          ~doc:"Print the decoded parent relation, one edge per line.")
  in
  Cmd.v
    (Cmd.info "cargo" ~doc:"Solve against a crates.io index.")
    Term.(
      const cargo_run $ debug_arg $ print_parents $ index $ goal $ wanted
      $ rfeats $ rustv)

let alpine_run debug path goals =
  let t0 = Unix.gettimeofday () in
  let ar = Apk_solve.load_index path in
  let t1 = Unix.gettimeofday () in
  Printf.printf
    "index %s\n\
     cone: %d packages, %d provides entries, %d install_if rules\n\
     parse %.2fs\n\
     %!"
    path ar.Apk_solve.n_pkgs ar.Apk_solve.n_provs ar.Apk_solve.n_iif (t1 -. t0);
  if !Apk_parse.rejected > 0 then
    Printf.printf "parser dropped %d declarations\n%!" !Apk_parse.rejected;
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

let npm_run debug cache offline tree omit nodev npmv goal wanted =
  let t0 = Unix.gettimeofday () in
  let ar =
    Npm_solve.empty_archive
      ~optional:(not (List.mem "optional" omit))
      ~node:nodev ~npm:npmv ~cache ~offline ()
  in
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
          Printf.printf "parser dropped %d declarations\n" !Npm_parse.rejected;
        if !Npm_parse.optional_count > 0 then
          Printf.printf "optionalDependencies: %d entries, %d dropped\n"
            !Npm_parse.optional_count ar.Npm_solve.n_opt_dropped;
        Printf.printf "encoded solution: %d core nodes (%d lookups)\n"
          r.Npm_solve.nodes r.Npm_solve.lookups;
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
  (* optionalDependencies are installed by default, as npm does; the flag
     spells the same opt-out npm does, and only the class this frontend
     distinguishes is recognised. *)
  let omit =
    Arg.(
      value & opt_all string []
      & info [ "omit" ] ~docv:"TYPE"
          ~doc:
            "Omit a dependency class; $(b,optional) is the class \
             distinguished here.")
  in
  (* npm-pick-manifest's engines preference, which needs a host to rank
     against -- npm reads its own and node's, this asks for them *)
  let nodev =
    Arg.(
      value
      & opt (some string) None
      & info [ "node-version" ] ~docv:"VERSION"
          ~doc:
            "Host node version to prefer engines-compatible package \
             versions for; unset leaves engines.node untested.")
  in
  let npmv =
    Arg.(
      value
      & opt (some string) None
      & info [ "npm-version" ] ~docv:"VERSION"
          ~doc:
            "Host npm version, the other sub-key checkEngine reads; unset \
             leaves engines.npm untested.")
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
    Term.(
      const npm_run $ debug_arg $ cache $ offline $ tree $ omit $ nodev $ npmv
      $ goal $ wanted)

let () =
  let doc = "Solve dependencies through the verified package calculus." in
  exit
    (Cmd.eval'
       (Cmd.group (Cmd.info "pac" ~doc)
          [ debian_cmd; opam_cmd; cargo_cmd; alpine_cmd; npm_cmd ]))
