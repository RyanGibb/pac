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

let () =
  let doc = "Solve dependencies through the verified package calculus." in
  exit (Cmd.eval' (Cmd.group (Cmd.info "pac" ~doc) [ debian_cmd ]))
