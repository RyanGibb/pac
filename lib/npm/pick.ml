module A = Archive

module Make
    (Encoding : Encoding.S)
    (L : module type of Lookup.Make (Encoding)) =
struct
  open Encoding

  (* npm-pick-manifest's sort above semver (lib/index.js:167-181): runnable
     and not deprecated, then runnable, then not deprecated, so a deprecated
     version the host can run outranks a current one it cannot.  Neither
     drops a candidate.  Its avoid (npm audit fix's), policyRestrictions and
     stagedVersions criteria have no counterpart: no ordinary install passes
     avoid, and no public packument carries the other two. *)
  let rank ar (n : string) (c : PVersion.t) : bool * bool * bool =
    match c with
    | Np.Vs.Bot | Np.Vs.Free -> (true, true, true)
    | Np.Vs.Orig v -> (
        match A.meta ar (n, v) with
        | Some m -> A.ver_rank ar m
        | None -> (true, true, true))

  let best ar (n : string) (cands : PVersion.t list) : PVersion.t =
    match cands with
    | [] -> invalid_arg "best"
    | c :: cs ->
        List.fold_left
          (fun a b ->
            let d = compare (rank ar n b) (rank ar n a) in
            if d > 0 || (d = 0 && PVersion.compare b a > 0) then b else a)
          c cs

  (* npm-pick-manifest takes dist-tags.latest whenever the range admits it,
     if it passes the sort's engine and deprecation tests (index.js:119-132),
     so it can outrank a newer version; a tag naming no version the archive
     keeps is no shortcut (index.js:123).  Preference only: the tag is sought
     among [cands]. *)
  let tagged ar (n : string) (cands : PVersion.t list) : PVersion.t option =
    match A.loaded_latest ar n with
    | Some l -> (
        match A.meta ar (n, l) with
        | Some m when A.ver_rank ar m = (true, true, true) ->
            List.find_opt (PVersion.equal (Np.Vs.Orig l)) cands
        | _ -> None)
    | None -> None

  let pick ar (t : string) (cands : PVersion.t list) : PVersion.t =
    match tagged ar t cands with Some c -> c | None -> best ar t cands

  let pick_in st (t : string) (rg : Np.coq_Range) : string option =
    let pool =
      List.filter_map
        (fun u -> if Np.rgHolds rg u then Some (Np.Vs.Orig u) else None)
        (A.versions_of (L.archive st) t)
    in
    match pool with
    | [] -> None
    | pool -> (
        match pick (L.archive st) t pool with
        | Np.Vs.Orig u -> Some u
        | Np.Vs.Bot | Np.Vs.Free -> None)
end
