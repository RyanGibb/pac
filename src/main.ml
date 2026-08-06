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

let () =
  let doc = "Solve dependencies through the verified package calculus." in
  exit (Cmd.eval' (Cmd.group (Cmd.info "pac" ~doc) [ debian_cmd; opam_cmd ]))
