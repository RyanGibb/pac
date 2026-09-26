module DF = Deb_packages

type accepts = Any | Only of string

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
   ButAutomaticUpgrades; pac reads Packages files alone, which hold none
   of them, so they are out of scope and every version ties.
   A query naming a version (apt-get install pkg=ver) makes it pkg's
   candidate (TryToInstall, apt-private/private-install.cc), so [named]
   overrides the newest.  That version is a string: apt keeps two versions
   that compare equal apart (pkgCacheGenerator::MergeListVersion, when
   their hashes differ), and the one named is the one whose string matched.
   Of two stanzas at one version the first read is kept: apt files the
   later one behind it in the package's version list, and the candidate is
   the first to reach the top priority. *)
let stanza_key ~native (st : DF.stanza) =
  (st.package, if st.architecture = "all" then native else st.architecture)

let pin_candidates ~native ~named (index : DF.stanza list) =
  let key = stanza_key ~native in
  let best = Hashtbl.create 65536 in
  let better (st : DF.stanza) (b : DF.stanza) =
    match Hashtbl.find_opt named (key st) with
    | Some v -> String.equal st.version v && not (String.equal b.version v)
    | None -> Version.Debian.compare st.version b.version > 0
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
   names the package, NAME[:ARCH] (PackageFromPackageName).  A selector
   nothing meets is apt's error before it solves, with the message
   CacheSetHelper::canNotGetVersion prints; FullName(true) leaves the native
   architecture out. *)
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
        (String.sub pkg 0 i, if b = "all" || b = "native" then native else b)
    | None -> (
        match
          List.find_opt
            (fun b -> has (pkg, b))
            (native :: List.filter (( <> ) native) arches)
        with
        | Some b -> (pkg, b)
        | None -> (pkg, native))
  in
  let full = if snd key = native then fst key else fst key ^ ":" ^ snd key in
  (* the package's version list, newest first and the first read ahead of
     a later stanza at the same version *)
  let vlist =
    List.stable_sort
      (fun (a : DF.stanza) (b : DF.stanza) ->
        Version.Debian.compare b.version a.version)
      (List.filter (fun st -> stanza_key ~native st = key) index)
  in
  let first p =
    List.find_map
      (fun (st : DF.stanza) -> if p st.version then Some st.version else None)
      vlist
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
        then Some st.version
        else None)
      vlist
  in
  let only why = function Some v -> Ok (key, Only v) | None -> Error why in
  let provides (st : DF.stanza) =
    List.exists (fun (p : DF.provide) -> p.pname = fst key) st.provides
  in
  (* a name no stanza carries, provides or relates to is no package of
     apt's cache.  apt-get would go on to read one with glob or regex
     characters as a pattern over the cache's names, which pac does not *)
  let located () =
    let named (a : DF.atom) = a.name = fst key in
    let mentions raw =
      let n = String.length (fst key) in
      let rec at i =
        i + n <= String.length raw
        && (String.sub raw i n = fst key || at (i + 1))
      in
      at 0 && List.exists (List.exists named) (DF.parse_depends raw)
    in
    List.exists
      (fun (st : DF.stanza) -> st.package = fst key || provides st)
      index
    || List.exists
         (fun (st : DF.stanza) ->
           List.exists named st.conflicts
           || List.exists mentions (st.depends_raw @ st.recommends_raw))
         index
  in
  (* CacheSetHelperAPTGet::tryVirtualPackage for a candidate: the provider
     versions that are their package's candidate, taken when one package
     holds them all, and of its architectures the one asked for, else
     arch:all, else the native one.  A Multi-Arch: foreign package provides
     itself and its Provides to every architecture. *)
  let virtual_candidate () =
    let providers =
      List.filter
        (fun (st : DF.stanza) ->
          (provides st && snd (stanza_key ~native st) = snd key)
          || st.multi_arch = Some "foreign"
             && (provides st || st.package = fst key))
        (pin_candidates ~native ~named:(Hashtbl.create 1) index)
    in
    let rank (st : DF.stanza) =
      if st.architecture = snd key then 0
      else if st.architecture = "all" then 1
      else if st.architecture = native then 2
      else 3
    in
    match List.stable_sort (fun a b -> compare (rank a) (rank b)) providers with
    | st :: rest
      when List.for_all (fun (o : DF.stanza) -> o.package = st.package) rest ->
        Ok (stanza_key ~native st, Only st.version)
    | _ ->
        Error (Printf.sprintf "Package '%s' has no installation candidate" full)
  in
  if not (located ()) then
    Error (Printf.sprintf "Unable to locate package %s" pkg)
  else
    match sel with
    | None when vlist = [] -> virtual_candidate ()
    | None -> Ok (key, Any)
    (* apt tests these keywords before the tag, so they read the same after
     '/'; nothing is installed, as pac reads no dpkg status *)
    | Some (_, "installed") ->
        Error
          (Printf.sprintf
             "Can't select installed version from package %s as it is not \
              installed"
             full)
    (* without pins the candidate is the newest, which heads the list *)
    | Some (_, "candidate") ->
        only
          (Printf.sprintf
             "Can't select candidate version from package %s as it has no \
              candidate"
             full)
          (first (fun _ -> true))
    | Some (_, "newest") ->
        only
          (Printf.sprintf
             "Can't select newest version from package '%s' as it is purely \
              virtual"
             full)
          (first (fun _ -> true))
    | Some ('=', v) ->
        only
          (Printf.sprintf "Version '%s' for '%s' was not found" v full)
          (match first (version_matches v) with
          | None -> self_provided v
          | found -> found)
    (* a release is matched against Release files, which pac does not
     read; "*" matches every file (pkgVersionMatch::FileMatch) *)
    | Some (_, r) ->
        only
          (Printf.sprintf "Release '%s' for '%s' was not found" r full)
          (if r = "*" then first (fun _ -> true) else None)

(* apt installs each element's version in argument order, setting it as the
   candidate, so of two naming one package the later wins; the versions the
   query names are what Strict-Pinning then keeps *)
let parse_query ~native ~arches (index : DF.stanza list) args =
  let rec go acc = function
    | [] -> Ok acc
    | arg :: rest -> (
        match query_element ~native ~arches index arg with
        | Error e -> Error e
        | Ok (k, a) -> go (List.remove_assoc k acc @ [ (k, a) ]) rest)
  in
  Result.map
    (fun query ->
      let named = Hashtbl.create 8 in
      List.iter
        (function k, Only v -> Hashtbl.replace named k v | _ -> ())
        query;
      (query, named))
    (go [] args)
