open Cmdliner

let debug_arg =
  Arg.(value & flag & info [ "debug" ] ~doc:"Trace the PubGrub search.")

(* the tool's own order is the default because the evaluation's first
   question is whether pac answers as the tool does *)
let order_arg ~tool ~pubgrub =
  Arg.(
    value
    & opt (enum [ ("tool", `Tool); ("pubgrub", `Pubgrub) ]) `Tool
    & info [ "order" ] ~docv:"ORDER"
        ~doc:
          (Printf.sprintf
             "Which name to decide next and which version to try: \
              $(b,tool) as %s, $(b,pubgrub) as %s."
             tool pubgrub))

let debian_run debug apt_heap no_recs no_strict native query path =
  Pubgrub.set_debug debug;
  let r =
    Deb_solve.solve_files ~debug ~apt_heap ~recommends:(not no_recs)
      ~strict_pinning:(not no_strict) ~native ~paths:[ path ] ~query
  in
  let dropped = !Debian_frontend.Deb_packages.rejected in
  let report_dropped () =
    if dropped > 0 then Printf.printf "parser dropped %d declarations\n" dropped
  in
  match r with
  | None ->
      report_dropped ();
      1
  | Some (pkgs, t_parse, t_solve) ->
      List.iter (fun (n, b, v) -> Printf.printf "%s:%s %s\n" n b v) pkgs;
      report_dropped ();
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
          ~doc:"Replay apt's work-heap scheduling for closer correspondence.")
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
             $(b,/RELEASE); no Release file is read, so of releases only \
             $(b,*) matches.")
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

let opam_run debug order with_test with_doc with_dev_setup opam_version repo
    atoms =
  let t0 = Unix.gettimeofday () in
  let ar = Opam_solve.empty_archive repo in
  let query = List.map Opam_parse.atom_of_string atoms in
  let r =
    Opam_solve.solve ~debug ~order ~with_test ~with_doc ~with_dev_setup
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
  | Some { Opam_solve.reals; nodes; depexts } ->
      Printf.printf "opam packages (%d, core solution %d nodes):\n"
        (List.length reals) nodes;
      List.iter (fun (n, v) -> Printf.printf "  %s.%s\n" n v) reals;
      if depexts <> [] then begin
        Printf.printf "system packages (%d):\n" (List.length depexts);
        List.iter (fun e -> Printf.printf "  %s\n" e) depexts
      end;
      loaded ();
      0

let opam_cmd =
  (* opam's builtin-0install backend decides a name as soon as its decider
     walks onto it, which is not the order PubGrub's own heuristic picks *)
  let order =
    order_arg ~tool:"builtin-0install's walk does"
      ~pubgrub:"PubGrub's own order does, absence last"
  in
  (* the flags opam install itself has for enabling dependencies, and only
     those: build is true whenever opam solves, since nothing is installed
     without being built, so there is no --with-build to match.  Each is
     query-scoped rather than global -- it holds of the names the query
     asks for and of nothing they pull in. *)
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
     about the host: opam answers it with its own version unless
     OPAMVAR_opam_version or a variable overrides it, so whoever compares
     against an opam says which one here *)
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
  (* the syntax of one element is opam's own (OpamFormula.atom_of_string),
     and many of them make one request, as [atom_list] in opamArg.ml does *)
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
      const opam_run $ debug_arg $ order $ with_test $ with_doc
      $ with_dev_setup $ opam_version $ repo $ query)

let cargo_run debug order print_parents index manifest features no_default
    installed =
  let t0 = Unix.gettimeofday () in
  match Cargo_query.of_manifest manifest with
  | exception Cargo_query.Refused e ->
      Printf.eprintf "error: %s\n" e;
      2
  | root -> (
      let features = Cargo_query.features_of_flags features ~no_default in
      let rustv = Cargo_query.toolchain root ~installed in
      let n, v = Cargo_query.crate root in
      Printf.printf "root %s %s%s%s\n%!" n v
        (match features with
        | Cargo_query.All -> ""
        | Cargo_query.Named { feats = []; default = true } ->
            " with default features"
        | Cargo_query.Named { feats = []; default = false } -> " with no features"
        | Cargo_query.Named { feats; default } ->
            " with features " ^ String.concat "," feats
            ^ if default then "" else " and no default feature")
        (match rustv with None -> "" | Some t -> " for rust " ^ t);
      let r = Cargo_solve.solve ~debug ~order ~index ~features ~rustv root in
      (* the crates the run parsed, known only once it is over: there is no
         cone, so this is what the solver asked for and nothing more *)
      let loaded () =
        let t2 = Unix.gettimeofday () in
        Printf.printf "loaded: %d crates, %d versions\n" r.Cargo_solve.n_names
          r.Cargo_solve.n_vers;
        if !Cargo_parse.rejected > 0 then
          Printf.printf "parser dropped %d declarations\n"
            !Cargo_parse.rejected;
        Printf.printf "parse %.2fs\nsolve %.2fs\n" r.Cargo_solve.t_parse
          (t2 -. t0 -. r.Cargo_solve.t_parse)
      in
      match r.Cargo_solve.answer with
      | None ->
          loaded ();
          1
      | Some a when Cargo_solve.reaches_registry_root root a ->
          loaded ();
          Printf.eprintf
            "error: the answer reaches %s %s through the registry, which \
             cargo keeps apart from the root unless [patch.crates-io] maps \
             %s to it with { path = \".\" }\n"
            n v n;
          2
      | Some a ->
          Printf.printf "crates (%d):\n" (List.length a.Cargo_solve.crates);
          List.iter
            (fun (n, v) ->
              let fs =
                match
                  List.find_opt (fun (m, u, _) -> m = n && u = v)
                    a.Cargo_solve.feats
                with
                | Some (_, _, fs) -> fs
                | None -> []
              in
              Printf.printf "  %s %s%s\n" n v
                (if fs = [] then "" else " [" ^ String.concat "," fs ^ "]"))
            a.Cargo_solve.crates;
          Printf.printf
            "encoded solution: %d core nodes (%d crate versions encoded)\n"
            a.Cargo_solve.nodes a.Cargo_solve.processed;
          Printf.printf "parent edges: %d\n" (List.length a.Cargo_solve.parents);
          if print_parents then begin
            Printf.printf "parent-edges:\n";
            List.iter
              (fun (n, v, a, t, u) ->
                Printf.printf "  %s %s -> %s(%s) %s\n" n v a t u)
              a.Cargo_solve.parents
          end;
          loaded ();
          0)

let cargo_cmd =
  let index =
    Arg.(
      required
      & pos 0 (some dir) None
      & info [] ~docv:"INDEX" ~doc:"crates.io-index checkout.")
  in
  (* what cargo resolves: it has no command-line query, only the root
     manifest of the workspace it is run in *)
  let manifest =
    Arg.(
      required
      & pos 1 (some file) None
      & info [] ~docv:"CARGO_TOML" ~doc:"The root package's Cargo.toml.")
  in
  (* unset, the root gets every feature it declares, which is the
     resolution cargo writes to Cargo.lock; named features are resolved
     afresh, not filtered out of that lock as cargo does *)
  let features =
    Arg.(
      value & opt_all string []
      & info [ "F"; "features" ] ~docv:"FEATURES"
          ~doc:
            "Space or comma separated features to enable on the root, \
             beside its default feature, resolved afresh rather than \
             filtered out of the lock.  With neither this nor \
             $(b,--no-default-features), every feature the root declares \
             is enabled, as when cargo writes a lockfile.")
  in
  let no_default =
    Arg.(
      value & flag
      & info [ "no-default-features" ]
          ~doc:"Do not enable the root's default feature.")
  in
  (* cargo's own order is the default, the one whose answers are compared
     with cargo's; PubGrub's is the one the benchmarks state *)
  let order =
    Arg.(
      value
      & opt (enum [ ("tool", `Tool); ("pubgrub", `Pubgrub) ]) `Tool
      & info [ "order" ] ~docv:"ORDER"
          ~doc:
            "Decision order: $(b,tool) replays cargo's activation order, \
             $(b,pubgrub) leaves PubGrub's own.")
  in
  (* the toolchain resolver v3 falls back to when the root declares no
     rust-version; cargo reads it off rustc, this asks for it *)
  let rustv =
    Arg.(
      value
      & opt (some string) None
      & info [ "rust-version" ] ~docv:"VERSION"
          ~doc:
            "The installed toolchain, which resolver v3 prefers \
             MSRV-compatible crate versions for when the root declares no \
             rust-version; unset leaves the preference off.")
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
    (Cmd.info "cargo" ~doc:"Solve a root Cargo.toml against a crates.io index.")
    Term.(
      const cargo_run $ debug_arg $ order $ print_parents $ index $ manifest
      $ features $ no_default $ rustv)

let alpine_run debug order path goals =
  match Apk_solve.world_of_args goals with
  | Error e ->
      Printf.eprintf "error: %s\n" e;
      2
  | Ok world -> (
      let t0 = Unix.gettimeofday () in
      let ar = Apk_solve.load_index path in
      let t1 = Unix.gettimeofday () in
      Printf.printf
        "index %s: %d packages, %d provides entries, %d install_if rules\n\
         parse %.2fs\n\
         %!"
        path ar.Apk_solve.n_pkgs ar.Apk_solve.n_provs ar.Apk_solve.n_iif
        (t1 -. t0);
      if !Apk_parse.rejected > 0 then
        Printf.printf "parser dropped %d declarations\n%!" !Apk_parse.rejected;
      match Apk_solve.solve ~debug ~order ar world with
      | None -> 1
      | Some r ->
          let t2 = Unix.gettimeofday () in
          Printf.printf "packages (%d):\n" (List.length r.Apk_solve.pkgs);
          List.iter
            (fun (n, v) -> Printf.printf "  %s %s\n" n v)
            r.Apk_solve.pkgs;
          Printf.printf
            "encoded solution: %d core nodes (%d dependees lookups)\n"
            r.Apk_solve.nodes r.Apk_solve.processed;
          Printf.printf "solve %.2fs\n" (t2 -. t1);
          0)

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
  (* apk accepts only what its own solver would keep, so the rules an
     answer's validity rests on hold in both orders *)
  let order =
    order_arg ~tool:"apk does"
      ~pubgrub:
        "PubGrub does, but for the rules apk's acceptance of an answer \
         rests on"
  in
  Cmd.v
    (Cmd.info "alpine" ~doc:"Solve against an Alpine APKINDEX.")
    Term.(const alpine_run $ debug_arg $ order $ path $ goals)

module Npm = Npm_solve

let npm_exits =
  Cmd.Exit.
    [
      info 0 ~doc:"on a solution.";
      info 1 ~doc:"when no solution exists.";
      info 2 ~doc:"when the query is refused.";
      info 3 ~doc:"when the registry cannot be read.";
    ]
  @ List.filter (fun i -> Cmd.Exit.info_code i <> 0) Cmd.Exit.defaults

let npm_answer debug order omit tree t0 ar root =
  let rc = Npm.Archive.add_root ar root in
  Npm.Print.root rc;
  match
    Npm.Solve.solve ~debug ~order ~omit_dev:(List.mem `Dev omit)
      ~omit_optional:(List.mem `Optional omit) ar rc
  with
  | Error inc ->
      Npm.Print.unsat inc;
      1
  | Ok r ->
      Npm.Print.answer ~full:tree ~elapsed:(Unix.gettimeofday () -. t0) ar r;
      0

let npm_run debug order cache offline tree omit nodev npmv query =
  let t0 = Unix.gettimeofday () in
  let ar = Npm.Archive.create ?node:nodev ?npm:npmv ~cache ~offline () in
  try
    match Npm.Query.root ar query with
    | Error e ->
        prerr_endline e;
        2
    | Ok root -> npm_answer debug order omit tree t0 ar root
  with Npm.Archive.Fetch_failed e ->
    Printf.eprintf "error: %s\n" e;
    3

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
  let order =
    Arg.(
      value
      & opt (enum [ ("tool", Npm.Solve.Tool); ("pubgrub", Npm.Solve.Pubgrub) ])
          Npm.Solve.Tool
      & info [ "order" ] ~docv:"ORDER"
          ~doc:
            "Which order decides: $(b,tool) replays npm's, $(b,pubgrub) \
             leaves PubGrub's own.")
  in
  (* npm's flag also takes peer, which is refused rather than ignored:
     nothing here leaves peers out of an answer *)
  let omit =
    Arg.(
      value
      & opt_all (enum [ ("dev", `Dev); ("optional", `Optional) ]) []
      & info [ "omit" ] ~docv:"TYPE"
          ~doc:
            "Omit a dependency class, $(b,dev) or $(b,optional). dev \
             dependencies are still resolved, as npm resolves them, and \
             only what they alone reach is left out; optional ones are \
             dropped before solving.")
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
            "What $(b,npm install) takes, though a project is named by the \
             path of its package.json, not its directory: that path, and \
             specs to add to it (name, name@range, name@tag, \
             key@npm:name@range); with no path, the project is empty.")
  in
  Cmd.v
    (Cmd.info "npm" ~exits:npm_exits ~doc:"Solve against the npm registry.")
    Term.(
      const npm_run $ debug_arg $ order $ cache $ offline $ tree $ omit $ nodev
      $ npmv $ query)

let () =
  let doc = "Solve dependencies through the verified package calculus." in
  exit
    (Cmd.eval'
       (Cmd.group (Cmd.info "pac" ~doc)
          [ debian_cmd; opam_cmd; cargo_cmd; alpine_cmd; npm_cmd ]))
