open Cmdliner
module Report = Pac_common.Report

let debug_arg =
  Arg.(value & flag & info [ "debug" ] ~doc:"Trace the PubGrub search.")

(* the tool's own order is the default because the evaluation's first
   question is whether pac answers as the tool does *)
let order_arg ~tool ~pubgrub : Pac_common.Order.t Term.t =
  let order =
    Arg.(
      value
      & opt
          (enum [ ("tool", `Tool); ("pubgrub", `Pubgrub); ("random", `Random) ])
          `Tool
      & info [ "order" ] ~docv:"ORDER"
          ~doc:
            (Printf.sprintf
               "Which name to decide next and which version to try: $(b,tool) \
                as %s, $(b,pubgrub) as %s, $(b,random) uniformly, from a \
                generator seeded by $(b,--seed)."
               tool pubgrub))
  in
  let seed =
    Arg.(
      value & opt int 0
      & info [ "seed" ] ~docv:"N"
          ~doc:"The seed $(b,--order=random) draws from.")
  in
  Term.(
    const (fun order seed ->
        match order with
        | `Random -> `Random seed
        | (`Tool | `Pubgrub) as o -> o)
    $ order $ seed)

let exits =
  Cmd.Exit.
    [
      info 0 ~doc:"on an answer.";
      info 1 ~doc:"when the query has no answer.";
      info 2
        ~doc:
          "when the query or an input is refused, a command-line error \
           included.";
      info 3 ~doc:"when an index, a file or the registry cannot be read.";
      info 125 ~doc:"on an internal error.";
    ]

let error code fmt =
  Printf.ksprintf
    (fun s ->
      Printf.eprintf "error: %s\n%!" s;
      code)
    fmt

let guard f = try f () with Sys_error e -> error 3 "%s" e

(* solve time is the wall time since [t0] less what went on loading, which
   the lazy loaders interleave with the solve *)
let report ~t0 (loaded : Report.loaded) answer print =
  let t1 = Unix.gettimeofday () in
  let code =
    match answer with
    | Ok a ->
        print a;
        0
    | Error why ->
        Report.unsatisfiable why;
        1
  in
  Report.loaded loaded ~solve:(t1 -. t0 -. loaded.Report.parse);
  code

let debian_run debug order no_recs no_strict native query path =
  guard @@ fun () ->
  Pac_common.Input.file path;
  let t0 = Unix.gettimeofday () in
  match
    Debian_solve.solve_files ~debug ~order ~recommends:(not no_recs)
      ~strict_pinning:(not no_strict) ~native ~paths:[ path ] ~query
  with
  | Error e -> error 2 "%s" e
  | Ok r ->
      report ~t0
        {
          Report.names = r.Debian_solve.names;
          versions = r.Debian_solve.versions;
          extra = [];
          dropped = r.Debian_solve.dropped;
          parse = r.Debian_solve.t_parse;
        } r.Debian_solve.answer (fun a ->
          Report.packages
            (List.map
               (fun (n, b, v) -> Printf.sprintf "%s:%s %s" n b v)
               a.Debian_solve.pkgs);
          Report.encoded ~nodes:a.Debian_solve.nodes
            ~lookups:a.Debian_solve.lookups)

let debian_cmd =
  (* Recommends are installed by default, as under apt's
     APT::Install-Recommends; the flag spells the same opt-out apt does. *)
  let no_recs =
    Arg.(
      value & flag
      & info
          [ "no-install-recommends" ]
          ~doc:"Ignore Recommends fields rather than satisfying them.")
  in
  let order =
    order_arg ~tool:"apt's work heap and propagation queue, replayed, do"
      ~pubgrub:"PubGrub's own order does, absence last"
  in
  (* the same opt-out apt-get spells for APT::Solver::Strict-Pinning *)
  let no_strict =
    Arg.(
      value & flag
      & info [ "no-strict-pinning" ]
          ~doc:
            "Offer every version in the Packages files, not only apt's \
             candidate (the newest).  The $(b,tool) order's replay of apt \
             assumes one version per package, so without Strict-Pinning it \
             approximates apt's order; the answer is still a resolution.")
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
             $(b,NAME[:ARCH]), optionally with $(b,=VERSION) or $(b,/RELEASE); \
             no Release file is read, so of releases only $(b,*) matches.")
  in
  let path =
    Arg.(
      required
      & pos ~rev:true 0 (some string) None
      & info [] ~docv:"PACKAGES" ~doc:"Debian Packages index file.")
  in
  Cmd.v
    (Cmd.info "debian" ~exits ~doc:"Solve against a Debian Packages index.")
    Term.(
      const debian_run $ debug_arg $ order $ no_recs $ no_strict $ native
      $ query $ path)

let opam_run debug order with_test with_doc with_dev_setup opam_version repo
    atoms =
  guard @@ fun () ->
  Pac_common.Input.dir repo;
  match Opam_parse.query_of_args atoms with
  | Error e -> error 2 "%s" e
  | Ok query -> (
      let t0 = Unix.gettimeofday () in
      let ar = Opam_solve.empty_archive repo in
      match Opam_solve.sanitize ar query with
      | Error e -> error 2 "%s" e
      | Ok query ->
          let r =
            Opam_solve.solve ~debug ~order ~with_test ~with_doc ~with_dev_setup
              ~opam_version ar query
          in
          report ~t0
            {
              Report.names = ar.Opam_solve.n_names;
              versions = ar.Opam_solve.n_vers;
              extra = [];
              dropped = ar.Opam_solve.n_dropped;
              parse = ar.Opam_solve.t_parse;
            } r (fun a ->
              Report.packages
                (List.map (fun (n, v) -> n ^ " " ^ v) a.Opam_solve.reals);
              if a.Opam_solve.depexts <> [] then
                Report.section "system packages" a.Opam_solve.depexts;
              Report.encoded ~nodes:a.Opam_solve.nodes
                ~lookups:a.Opam_solve.lookups))

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
            "Value of the opam-version variable, the version of the opam whose \
             answer is being matched.")
  in
  let repo =
    Arg.(
      required
      & pos 0 (some string) None
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
    (Cmd.info "opam" ~exits ~doc:"Solve against an opam repository.")
    Term.(
      const opam_run $ debug_arg $ order $ with_test $ with_doc $ with_dev_setup
      $ opam_version $ repo $ query)

let cargo_run debug order print_parents index manifest features no_default
    installed =
  guard @@ fun () ->
  Pac_common.Input.dir index;
  Pac_common.Input.file manifest;
  let t0 = Unix.gettimeofday () in
  try
    let root = Cargo_query.of_manifest manifest in
    let features = Cargo_query.features_of_flags root features ~no_default in
    let rustv = Cargo_query.toolchain root ~installed in
    let n, v = Cargo_query.crate root in
    Report.root
      (Printf.sprintf "%s %s%s%s" n v
         (match features with
         | Cargo_query.All -> ""
         | Cargo_query.Named { feats = []; default = true } ->
             " with default features"
         | Cargo_query.Named { feats = []; default = false } ->
             " with no features"
         | Cargo_query.Named { feats; default } ->
             " with features " ^ String.concat "," feats
             ^ if default then "" else " and no default feature")
         (match rustv with None -> "" | Some t -> " for rust " ^ t));
    let r = Cargo_solve.solve ~debug ~order ~index ~features ~rustv root in
    match r.Cargo_solve.answer with
    | Ok a when Cargo_solve.reaches_registry_root root a ->
        error 2
          "the answer reaches %s %s through the registry, which cargo keeps \
           apart from the root unless [patch.crates-io] maps %s to it with { \
           path = \".\" }"
          n v n
    | answer ->
        report ~t0
          {
            Report.names = r.Cargo_solve.n_names;
            versions = r.Cargo_solve.n_vers;
            extra = [];
            dropped = r.Cargo_solve.dropped;
            parse = r.Cargo_solve.t_parse;
          } answer (fun a ->
            Report.packages
              (List.map
                 (fun (n, v, fs) ->
                   Printf.sprintf "%s %s%s" n v
                     (if fs = [] then "" else " [" ^ String.concat "," fs ^ "]"))
                 a.Cargo_solve.crates);
            if print_parents then
              Report.section "parent edges"
                (List.map
                   (fun (n, v, a, t, u) ->
                     Printf.sprintf "%s %s -> %s(%s) %s" n v a t u)
                   a.Cargo_solve.parents);
            Report.encoded ~nodes:a.Cargo_solve.nodes
              ~lookups:a.Cargo_solve.lookups)
  with Cargo_query.Refused e -> error 2 "%s" e

let cargo_cmd =
  let index =
    Arg.(
      required
      & pos 0 (some string) None
      & info [] ~docv:"INDEX" ~doc:"crates.io-index checkout.")
  in
  (* what cargo resolves: it has no command-line query, only the root
     manifest of the workspace it is run in *)
  let manifest =
    Arg.(
      required
      & pos 1 (some string) None
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
            "Space or comma separated features to enable on the root, beside \
             its default feature, resolved afresh rather than filtered out of \
             the lock.  With neither this nor $(b,--no-default-features), \
             every feature the root declares is enabled, as when cargo writes \
             a lockfile.")
  in
  let no_default =
    Arg.(
      value & flag
      & info [ "no-default-features" ]
          ~doc:"Do not enable the root's default feature.")
  in
  let order =
    order_arg ~tool:"cargo's activation order, replayed, does"
      ~pubgrub:"PubGrub's own order does"
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
    (Cmd.info "cargo" ~exits
       ~doc:"Solve a root Cargo.toml against a crates.io index.")
    Term.(
      const cargo_run $ debug_arg $ order $ print_parents $ index $ manifest
      $ features $ no_default $ rustv)

let alpine_run debug order path goals =
  guard @@ fun () ->
  Pac_common.Input.file path;
  match Apk_parse.world_of_args goals with
  | Error e -> error 2 "%s" e
  | Ok world ->
      let t0 = Unix.gettimeofday () in
      let module A = Alpine_solve.Make (struct
        let table = Hashtbl.create 4096
      end) in
      let ar = A.load_index path in
      let parse = Unix.gettimeofday () -. t0 in
      let r = A.solve ~debug ~order ar world in
      report ~t0
        {
          Report.names = Hashtbl.length ar.A.by_name;
          versions = ar.A.n_pkgs;
          extra =
            [
              Printf.sprintf "%d provides entries" ar.A.n_provs;
              Printf.sprintf "%d install_if rules" ar.A.n_iif;
            ];
          dropped = ar.A.n_dropped;
          parse;
        }
        r
        (fun a ->
          Report.packages (List.map (fun (n, v) -> n ^ " " ^ v) a.A.pkgs);
          Report.encoded ~nodes:a.A.nodes ~lookups:a.A.lookups)

let alpine_cmd =
  let path =
    Arg.(
      required
      & pos 0 (some string) None
      & info [] ~docv:"APKINDEX" ~doc:"Uncompressed APKINDEX file.")
  in
  let goals =
    Arg.(
      non_empty & pos_right 0 string []
      & info [] ~docv:"PKG" ~doc:"Packages forming the world.")
  in
  (* apk would change an answer that departs from its own choices, so the
     rules that keep an answer minimal hold in both orders *)
  let order =
    order_arg ~tool:"apk does"
      ~pubgrub:"PubGrub does, but for the rules that keep apk's own choices"
  in
  Cmd.v
    (Cmd.info "alpine" ~exits ~doc:"Solve against an Alpine APKINDEX.")
    Term.(const alpine_run $ debug_arg $ order $ path $ goals)

module Npm = Npm_solve

let npm_run debug order cache offline tree omit nodev npmv query =
  guard @@ fun () ->
  let t0 = Unix.gettimeofday () in
  let ar = Npm.Archive.create ?node:nodev ?npm:npmv ~cache ~offline () in
  try
    match Npm.Query.root ar query with
    | Error e -> error 2 "%s" e
    | Ok root ->
        let rc = Npm.Archive.add_root ar root in
        Report.root (Npm.Print.root rc);
        let r =
          Npm.Solve.solve ~debug ~order ~omit_dev:(List.mem `Dev omit)
            ~omit_optional:(List.mem `Optional omit) ar rc
        in
        let optional =
          match r with
          | Ok a when a.Npm.Solve.optional_read > 0 ->
              [
                Printf.sprintf
                  "%d of %d optionalDependencies (target, range) pairs dropped"
                  a.Npm.Solve.optional_dropped a.Npm.Solve.optional_read;
              ]
          | _ -> []
        in
        report ~t0
          {
            Report.names = ar.Npm.Archive.n_names;
            versions = ar.Npm.Archive.n_vers;
            extra =
              Printf.sprintf "%d packuments fetched" ar.Npm.Archive.n_fetched
              :: optional;
            dropped = ar.Npm.Archive.n_dropped;
            parse = ar.Npm.Archive.t_parse;
          }
          r
          (fun a ->
            Report.packages (Npm.Print.packages a);
            if tree then Report.section "node_modules" (Npm.Print.tree a);
            Report.encoded ~nodes:a.Npm.Solve.nodes ~lookups:a.Npm.Solve.lookups)
  with Npm.Archive.Fetch_failed e -> error 3 "%s" e

let npm_cmd =
  (* a user's cache, as npm keeps its own, so that where pac runs from
     does not decide which packuments it reads *)
  let cache =
    let default =
      match Sys.getenv_opt "XDG_CACHE_HOME" with
      | Some d when d <> "" -> Filename.concat d "pac/npm"
      | _ ->
          Filename.concat
            (Option.value (Sys.getenv_opt "HOME") ~default:".")
            ".cache/pac/npm"
    in
    Arg.(
      value & opt string default
      & info [ "cache" ] ~docv:"DIR"
          ~absent:"$(b,\\$XDG_CACHE_HOME)/pac/npm, else ~/.cache/pac/npm"
          ~doc:"Packument cache directory.")
  in
  let offline =
    Arg.(
      value & flag
      & info [ "offline" ]
          ~doc:
            "Fetch nothing: a packument missing from the cache is read as the \
             registry's 404, so a dependency on it cannot be met, and a \
             command-line spec naming it is refused.")
  in
  let tree =
    Arg.(value & flag & info [ "tree" ] ~doc:"Print the node_modules nesting.")
  in
  let order =
    order_arg ~tool:"npm's, replayed, does" ~pubgrub:"PubGrub's own order does"
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
             dependencies are still resolved, as npm resolves them, and only \
             what they alone reach is left out; optional ones are dropped \
             before solving.")
  in
  (* npm-pick-manifest's engines preference, which needs a host to rank
     against -- npm reads its own and node's, this asks for them *)
  let nodev =
    Arg.(
      value
      & opt (some string) None
      & info [ "node-version" ] ~docv:"VERSION"
          ~doc:
            "Host node version to prefer engines-compatible package versions \
             for; unset leaves engines.node untested.")
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
             path of its package.json, not its directory: that path, and specs \
             to add to it (name, name@range, name@tag, key@npm:name@range); \
             with no path, the project is empty.")
  in
  Cmd.v
    (Cmd.info "npm" ~exits ~doc:"Solve against the npm registry.")
    Term.(
      const npm_run $ debug_arg $ order $ cache $ offline $ tree $ omit $ nodev
      $ npmv $ query)

(* a command-line error is a refused query like any other, and 124 is
   left to timeout(1) *)
let () =
  let doc = "Solve dependencies through the verified package calculus." in
  let code =
    Cmd.eval'
      (Cmd.group
         (Cmd.info "pac" ~exits ~doc)
         [ debian_cmd; opam_cmd; cargo_cmd; alpine_cmd; npm_cmd ])
  in
  exit (if code = Cmd.Exit.cli_error then 2 else code)
