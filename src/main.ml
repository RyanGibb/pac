open Cmdliner

let debug_arg =
  Arg.(value & flag & info [ "debug" ] ~doc:"Trace the PubGrub search.")

let debian_run debug apt_heap no_recs no_strict native query path =
  Pubgrub.set_debug debug;
  match
    Deb_solve.solve_files ~debug ~apt_heap ~recommends:(not no_recs)
      ~strict_pinning:(not no_strict) ~native ~paths:[ path ] ~query
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
  (* the index goes last so that a query stays apt-get install's argument
     list verbatim, however many elements it has *)
  let query =
    Arg.(
      non_empty
      & pos_left ~rev:true 0 string []
      & info [] ~docv:"QUERY"
          ~doc:
            "Packages to install, as $(b,apt-get install) takes them: \
             $(b,NAME[:ARCH]), optionally with $(b,=VERSION) or \
             $(b,/RELEASE).")
  in
  let path =
    Arg.(
      required
      & pos ~rev:true 0 (some file) None
      & info [] ~docv:"PACKAGES" ~doc:"Debian Packages index file.")
  in
  Cmd.v
    (Cmd.info "debian" ~doc:"Solve against a Debian Packages index.")
    Term.(
      const debian_run $ debug_arg $ apt_heap $ no_recs $ no_strict $ native
      $ query $ path)

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

(* The root package r_N: the manifest a path argument names, or an empty
   project's, with each spec added as `npm install` adds it.  arborist's
   #add resolves a tag to its version only after an await, so the other
   specs are all added first, in order. *)
let npm_root ar (query : string list) : (Npm_parse.ver, string) result =
  let paths, specs = List.partition Npm_parse.is_manifest_arg query in
  let ( let* ) = Result.bind in
  let* pkg =
    match paths with
    | [] -> Ok (`Assoc [])
    | [ p ] -> (
        match Yojson.Safe.from_file p with
        | `Assoc _ as j -> Ok j
        | _ | (exception _) -> Error (p ^ ": not a package.json"))
    | _ -> Error "more than one package.json"
  in
  let* plain, tagged =
    List.fold_left
      (fun acc s ->
        let* plain, tagged = acc in
        match Npm_parse.spec_of s with
        | None ->
            Error
              (s
             ^ ": not a registry spec (name, name@range, name@tag, \
                key@npm:name@range)")
        | Some (k, r) when Npm_parse.split_alias r <> None || r = "*" ->
            Ok ((k, r) :: plain, tagged)
        | Some (k, r) -> (
            (* npm refuses a dist-tag that is a range, so a spec the
               packument tags is a tag, and one it does not is a range
               unless it can only be a tag *)
            match Npm_solve.dist_tag ar k (String.trim r) with
            | Some v -> Ok (plain, (k, v) :: tagged)
            | None when Npm_parse.looks_like_tag (String.trim r) ->
                Error (s ^ ": no such dist-tag")
            | None -> Ok ((k, r) :: plain, tagged)))
      (Ok ([], [])) specs
  in
  let specs = List.rev plain @ List.rev tagged in
  (* npm's #add fetches each argument's manifest, and E404s on a name the
     registry lacks rather than resolving without it *)
  let* () =
    match
      List.find_opt
        (fun (k, r) ->
          let t = match Npm_parse.split_alias r with Some (t, _) -> t | None -> k in
          Npm_solve.versions_of ar t = [])
        specs
    with
    | Some (k, r) ->
        let t = match Npm_parse.split_alias r with Some (t, _) -> t | None -> k in
        Error
          (Printf.sprintf "no packument for %s under %s%s" t ar.Npm_solve.cache
             (if ar.Npm_solve.offline then " (offline)" else ""))
    | None -> Ok ()
  in
  let pkg = List.fold_left Npm_parse.add_to pkg specs in
  (* arborist names a root with no name by its directory, which is no
     part of the query; "." is a name no registry package can have *)
  let str k = match Npm_parse.member k pkg with `String s -> s | _ -> "" in
  let name = match str "name" with "" -> "." | n -> n in
  match Npm_parse.ver_of ~root:true (str "version") pkg with
  | Some v -> Ok { v with Npm_parse.v_name = name }
  | None -> Error "not a package.json"

let npm_run debug cache offline tree omit nodev npmv query =
  let t0 = Unix.gettimeofday () in
  let ar =
    Npm_solve.empty_archive
      ~optional:(not (List.mem "optional" omit))
      ~node:nodev ~npm:npmv ~cache ~offline ()
  in
  match npm_root ar query with
  | Error e ->
      prerr_endline e;
      1
  | Ok root -> begin
    let node n v = if v = "" then n else Printf.sprintf "%s %s" n v in
    let rc = Npm_solve.add_root ar root in
    Printf.printf "root %s\n%!" (node (fst rc) (snd rc));
    match Npm_solve.solve ~debug ar rc with
    | None -> 1
    | Some r ->
        let t2 = Unix.gettimeofday () in
        let show (a, t) v =
          if a = t then node t v else Printf.sprintf "%s at %s" (node t v) a
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
  let query =
    Arg.(
      non_empty & pos_all string []
      & info [] ~docv:"QUERY"
          ~doc:
            "What $(b,npm install) takes: the path of a project's \
             package.json, and specs to add to it (name, name@range, \
             name@tag, key@npm:name@range); with no path, the project is \
             empty.")
  in
  Cmd.v
    (Cmd.info "npm" ~doc:"Solve against the npm registry.")
    Term.(
      const npm_run $ debug_arg $ cache $ offline $ tree $ omit $ nodev $ npmv
      $ query)

let () =
  let doc = "Solve dependencies through the verified package calculus." in
  exit
    (Cmd.eval'
       (Cmd.group (Cmd.info "pac" ~doc)
          [ debian_cmd; opam_cmd; cargo_cmd; alpine_cmd; npm_cmd ]))
