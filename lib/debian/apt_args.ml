(* apt-get install's arguments, and the candidate versions they leave:
   pure functions over the index (the parsed Packages file). *)

module DF = Deb_packages

(* Nothing is an element whose named version apt finds no match for; it
   refuses the whole request, which an empty range says. *)
type accepts = Any | Only of string | Nothing

(* apt's solver rejects every version but the candidate before it starts
   (APT::Solver::Strict-Pinning, on by default: FromDepCache, solver3.cc),
   so its answer holds only candidates, though its cache still lists the
   rest, rejected.  The cut is made on the index, before any table is
   built, so that the lookups answer over the instance their theorems are
   stated over.  The candidate
   is the version of highest pin priority, the newest among equals
   (pkgPolicy::GetCandidateVer), and an arch:all stanza belongs to the
   native architecture's package (pkgCacheGenerator::NewPackage).  What
   sets one version's priority apart is a pin (a preferences file,
   APT::Default-Release) or a Release file's NotAutomatic or
   ButAutomaticUpgrades; pac reads Packages files alone, which carry none
   of them, so they are out of scope and every version ties.
   A query naming a version (apt-get install pkg=ver) makes it pkg's
   candidate (TryToInstall, apt-private/private-install.cc), so [named]
   overrides the newest.  Of two stanzas at one version the first read is
   kept: apt files the later one behind it in the package's version list,
   and the candidate is the first to reach the top priority. *)
let stanza_key ~native (st : DF.stanza) =
  (st.package, if st.architecture = "all" then native else st.architecture)

let pin_candidates ~native ~named (index : DF.stanza list) =
  let key = stanza_key ~native in
  let best = Hashtbl.create 65536 in
  let better (st : DF.stanza) (b : DF.stanza) =
    match Hashtbl.find_opt named (key st) with
    | Some v ->
        Deb_version.compare st.version v = 0
        && Deb_version.compare b.version v <> 0
    | None -> Deb_version.compare st.version b.version > 0
  in
  List.iter
    (fun (st : DF.stanza) ->
      match Hashtbl.find_opt best (key st) with
      | Some b when not (better st b) -> ()
      | _ -> Hashtbl.replace best (key st) st)
    index;
  List.filter (fun st -> Hashtbl.find best (key st) == st) index

(* fnmatch(3) with FNM_CASEFOLD, which pkgVersionMatch::ExpressionMatches
   calls on a version pattern *)
let fnmatch p s =
  let p = String.lowercase_ascii p and s = String.lowercase_ascii s in
  let np = String.length p and ns = String.length s in
  let bracket i =
    let neg, i =
      if i < np && (p.[i] = '!' || p.[i] = '^') then (true, i + 1)
      else (false, i)
    in
    let rec scan k acc first =
      if k >= np then None
      else if p.[k] = ']' && not first then Some (k + 1, acc)
      else if k + 2 < np && p.[k + 1] = '-' && p.[k + 2] <> ']' then
        scan (k + 3) ((p.[k], p.[k + 2]) :: acc) false
      else scan (k + 1) ((p.[k], p.[k]) :: acc) false
    in
    Option.map
      (fun (e, rs) ->
        (e, fun c -> neg <> List.exists (fun (a, b) -> a <= c && c <= b) rs))
      (scan i [] true)
  in
  let rec go i j =
    if i = np then j = ns
    else
      match p.[i] with
      | '*' -> go (i + 1) j || (j < ns && go i (j + 1))
      | '?' -> j < ns && go (i + 1) (j + 1)
      | '\\' when i + 1 < np -> j < ns && p.[i + 1] = s.[j] && go (i + 2) (j + 1)
      | '[' -> (
          match bracket (i + 1) with
          | Some (e, test) -> j < ns && test s.[j] && go e (j + 1)
          | None -> j < ns && s.[j] = '[' && go (i + 1) (j + 1))
      | c -> j < ns && c = s.[j] && go (i + 1) (j + 1)
  in
  go 0 0

(* pkgVersionMatch::VersionMatches for a Version matcher
   (apt-pkg/versionmatch.cc): the whole string, case-insensitively, or a
   prefix of it where the pattern ends in '*', or a glob of the pattern less
   that '*', so 1.*2* matches 1.2 and not 1.23.  apt would read /regex/ as a
   regex, but its argument splits at the last '/', so no argument reaches
   that branch. *)
let version_matches pat v =
  let n = String.length pat in
  let pre = n > 0 && pat.[n - 1] = '*' in
  let b = if pre then String.sub pat 0 (n - 1) else pat in
  let lb = String.length b and lv = String.length v in
  (lv = lb || (pre && lv > lb))
  && String.lowercase_ascii (String.sub v 0 lb) = String.lowercase_ascii b
  || fnmatch b v

(* One argument of apt-get install, as VersionContainerInterface::FromString
   (apt-pkg/cacheset.cc) reads it: whatever follows the last '/' or '='
   selects a version, by release or by version string, and what precedes it
   names the package, NAME[:ARCH] (PackageFromPackageName). *)
let query_element ~native ~arches (index : DF.stanza list) arg =
  let tag =
    match (String.rindex_opt arg '=', String.rindex_opt arg '/') with
    | Some i, Some j -> Some (max i j)
    | t, None | None, t -> t
  in
  let pkg, sel =
    match tag with
    | Some i ->
        ( String.sub arg 0 i,
          Some (arg.[i], String.sub arg (i + 1) (String.length arg - i - 1)) )
    | None -> (arg, None)
  in
  let has (n, b) =
    List.exists (fun st -> stanza_key ~native st = (n, b)) index
  in
  (* an unqualified name is apt's preferred package of the group
     (GrpIterator::FindPreferredPkg): the native one if it has a version,
     else the first architecture that does.  apt tries them in
     APT::Architectures order, which pac cannot read, and takes the
     index's architectures in sorted order instead. *)
  let key =
    match String.rindex_opt pkg ':' with
    | Some i ->
        let b = String.sub pkg (i + 1) (String.length pkg - i - 1) in
        ( String.sub pkg 0 i,
          if b = "all" || b = "native" then native else b )
    | None -> (
        match
          List.find_opt
            (fun b -> has (pkg, b))
            (native :: List.filter (( <> ) native) arches)
        with
        | Some b -> (pkg, b)
        | None -> (pkg, native))
  in
  (* the package's version list, newest first and the first read ahead of
     a later stanza at the same version *)
  let vlist =
    List.stable_sort
      (fun (a : DF.stanza) (b : DF.stanza) ->
        Deb_version.compare b.version a.version)
      (List.filter (fun st -> stanza_key ~native st = key) index)
  in
  let first p =
    match List.find_opt (fun (st : DF.stanza) -> p st.version) vlist with
    | Some st -> Only st.version
    | None -> Nothing
  in
  (* failing every version, pkgVersionMatch::Find takes a version whose
     package provides itself at a matching version *)
  let self_provided v =
    List.find_map
      (fun (st : DF.stanza) ->
        if
          List.exists
            (fun (p : DF.provide) ->
              p.pname = fst key
              && Option.fold ~none:false ~some:(version_matches v) p.pversion)
            st.provides
        then Some (Only st.version)
        else None)
      vlist
  in
  let acc =
    match sel with
    | None -> Any
    (* apt tests these keywords before the tag, so they read the same after
       '/'; nothing is installed, as pac reads no dpkg status *)
    | Some (_, "installed") -> Nothing
    (* without pins the candidate is the newest, which heads the list *)
    | Some (_, ("candidate" | "newest")) -> first (fun _ -> true)
    | Some ('=', v) -> (
        match first (version_matches v) with
        | Nothing -> Option.value (self_provided v) ~default:Nothing
        | a -> a)
    (* a release is matched against Release files, which pac does not
       read; "*" matches every file (pkgVersionMatch::FileMatch) *)
    | Some (_, "*") -> first (fun _ -> true)
    | Some _ -> Nothing
  in
  (key, acc)

(* apt installs each element's version in argument order, setting it as the
   candidate, so of two naming one package the later wins; the versions the
   query names are what Strict-Pinning then keeps *)
let parse_query ~native ~arches (index : DF.stanza list) args =
  let query =
    List.fold_left
      (fun acc arg ->
        let k, a = query_element ~native ~arches index arg in
        List.remove_assoc k acc @ [ (k, a) ])
      [] args
  in
  let named = Hashtbl.create 8 in
  List.iter (function k, Only v -> Hashtbl.replace named k v | _ -> ()) query;
  (query, named)
