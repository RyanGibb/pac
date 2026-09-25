(* npm-pick-manifest: which of a range's versions npm takes. *)

open Encoding
module A = Archive
module L = Lookup

(* npm-pick-manifest's sort keys above semver, lib/index.js:167-181:

     ((notdeprb && engineb) - (notdepra && enginea)) ||
     (engineb - enginea) ||
     (notdeprb - notdepra) ||
     semver.rcompare(vera, verb, sortSemverOpt)

   deprecated and engines are one preference because they are one sort
   function, and the middle key is what orders them against each other: a
   deprecated version the host can run outranks a current one it cannot.
   Neither drops a candidate, so neither can make anything unsatisfiable
   -- a package whose every version is deprecated resolves to its newest,
   and a pinned version the host cannot run still installs, which is what
   --engine-strict exists to refuse at install time.

   The three keys npm sorts above these have no counterpart here.  avoid
   is npm audit fix's, passed by nothing that writes an ordinary
   lockfile; policyRestrictions and stagedVersions appear in no public
   packument, and the parser reads neither, so restricted and staged are
   uniformly false.  A Gran version stands for a granularity class rather
   than a release, so it carries neither key. *)
let keys ar (n : string) (c : PVersion.t) : bool * bool * bool =
  match c with
  | Np.Vs.Gran _ -> (true, true, true)
  | Np.Vs.Orig v ->
      let p = (n, v) in
      let nd = not (A.deprecated ar p) and eng = A.engine_ok ar p in
      (nd && eng, eng, nd)

let best ar (n : string) (cands : PVersion.t list) : PVersion.t =
  match cands with
  | [] -> invalid_arg "best"
  | c :: cs ->
      List.fold_left
        (fun a b ->
          let d = compare (keys ar n b) (keys ar n a) in
          if d > 0 || (d = 0 && PVersion.compare b a > 0) then b else a)
        c cs

(* npm-pick-manifest offers dist-tags.latest before the highest version
   the range admits, and takes it whenever the range admits it; only the
   ordering differs from ours, so a package published ahead of its own
   latest tag no longer drags its newest release in.  Preference only:
   the tag is consulted inside the candidates, never outside them.

   The fast path is guarded by the same two keys as the sort
   (index.js:119-132, [engineOk(mani, ..) && !mani.deprecated]), so a
   deprecated or unrunnable latest is not a shortcut past them.  It is
   not merely redundant with the sort: the tag may name a version the
   sort would rank below a newer one. *)
let tagged ar (n : string) (cands : PVersion.t list) : PVersion.t option =
  match Hashtbl.find_opt ar.A.latest n with
  | Some l when (not (A.deprecated ar (n, l))) && A.engine_ok ar (n, l) ->
      List.find_opt (PVersion.equal (Np.Vs.Orig l)) cands
  | _ -> None

let pick ar (t : string) (cands : PVersion.t list) : PVersion.t =
  match tagged ar t cands with Some c -> c | None -> best ar t cands

(* npm's pick for a range over every published version, under the root's
   flat override as the calculus reads one *)
let pick_in st (t : string) (rg : Np.coq_Range) : string option =
  let rg = L.effective st t rg in
  let pool =
    List.filter_map
      (fun u -> if Np.rgHolds rg u then Some (Np.Vs.Orig u) else None)
      (A.versions_of st.L.ar t)
  in
  match pool with
  | [] -> None
  | pool -> (
      match pick st.L.ar t pool with
      | Np.Vs.Orig u -> Some u
      | Np.Vs.Gran _ -> None)
