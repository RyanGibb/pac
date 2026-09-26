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

(* The names apt's cache holds a package for: every name a stanza carries,
   provides, or relates to (pkgCacheGenerator makes a package of each), read
   off the whole index, since the cache lists every version and not only
   the candidates Strict-Pinning later keeps.  The solve's own tables cannot
   answer this: they are built after the query has chosen the candidates.
   The relations are parsed only if some name is neither carried nor
   provided.  apt-get would go on to read an unknown name with glob or
   regex characters as a pattern over the cache's names, which pac does
   not. *)
let cache_names (index : DF.stanza list) : string -> bool =
  let own = Hashtbl.create 65536 in
  List.iter
    (fun (st : DF.stanza) ->
      Hashtbl.replace own st.package ();
      List.iter (fun (p : DF.provide) -> Hashtbl.replace own p.pname ()) st.provides)
    index;
  let related =
    lazy
      (let t = Hashtbl.create 65536 in
       let add (a : DF.atom) = Hashtbl.replace t a.name () in
       List.iter
         (fun (st : DF.stanza) ->
           List.iter add st.conflicts;
           List.iter
             (fun raw -> List.iter (List.iter add) (DF.parse_depends raw))
             (st.depends_raw @ st.recommends_raw))
         index;
       t)
  in
  fun n -> Hashtbl.mem own n || Hashtbl.mem (Lazy.force related) n

(* One argument of apt-get install, as VersionContainerInterface::FromString
   (apt-pkg/cacheset.cc) reads it: whatever follows the last '/' or '='
   selects a version, by release or by version string, and what precedes it
   names the package, NAME[:ARCH] (PackageFromPackageName). *)
let split_arg arg =
  let tag =
    match (String.rindex_opt arg '=', String.rindex_opt arg '/') with
    | Some i, Some j -> Some (max i j)
    | t, None | None, t -> t
  in
  match tag with
  | Some i ->
      ( String.sub arg 0 i,
        Some (arg.[i], String.sub arg (i + 1) (String.length arg - i - 1)) )
  | None -> (arg, None)

(* an unqualified name is apt's preferred package of the group
   (GrpIterator::FindPreferredPkg): the native one if it has a version,
   else the first architecture that does.  apt tries them in
   APT::Architectures order, which pac cannot read, and takes the index's
   architectures in sorted order instead. *)
let package_key ~native ~arches (index : DF.stanza list) pkg =
  match String.rindex_opt pkg ':' with
  | Some i ->
      let b = String.sub pkg (i + 1) (String.length pkg - i - 1) in
      (String.sub pkg 0 i, if b = "all" || b = "native" then native else b)
  | None -> (
      let has b =
        List.exists (fun st -> stanza_key ~native st = (pkg, b)) index
      in
      match List.find_opt has (native :: List.filter (( <> ) native) arches) with
      | Some b -> (pkg, b)
      | None -> (pkg, native))

(* FullName(true), which leaves the native architecture out *)
let full_name ~native (n, b) = if b = native then n else n ^ ":" ^ b

(* the package's version list, newest first and the first read ahead of
   a later stanza at the same version *)
let version_list ~native (index : DF.stanza list) key =
  List.stable_sort
    (fun (a : DF.stanza) (b : DF.stanza) ->
      Version.Debian.compare b.version a.version)
    (List.filter (fun st -> stanza_key ~native st = key) index)

let provides name (st : DF.stanza) =
  List.exists (fun (p : DF.provide) -> p.pname = name) st.provides

(* failing every version, pkgVersionMatch::Find takes a version whose
   package provides itself at a matching version *)
let self_provided name (vlist : DF.stanza list) v =
  List.find_map
    (fun (st : DF.stanza) ->
      if
        List.exists
          (fun (p : DF.provide) ->
            p.pname = name
            && Option.fold ~none:false ~some:(version_matches v) p.pversion)
          st.provides
      then Some st.version
      else None)
    vlist

(* CacheSetHelperAPTGet::tryVirtualPackage for a candidate: the provider
   versions that are their package's candidate, taken when one package
   holds them all, and of its architectures the one asked for, else
   arch:all, else the native one.  A Multi-Arch: foreign package provides
   itself and its Provides to every architecture. *)
let virtual_candidate ~native (index : DF.stanza list) ((n, b) as key) =
  let providers =
    List.filter
      (fun (st : DF.stanza) ->
        (provides n st && snd (stanza_key ~native st) = b)
        || st.multi_arch = Some "foreign" && (provides n st || st.package = n))
      (pin_candidates ~native ~named:(Hashtbl.create 1) index)
  in
  let rank (st : DF.stanza) =
    if st.architecture = b then 0
    else if st.architecture = "all" then 1
    else if st.architecture = native then 2
    else 3
  in
  match List.stable_sort (fun a b -> compare (rank a) (rank b)) providers with
  | st :: rest
    when List.for_all (fun (o : DF.stanza) -> o.package = st.package) rest ->
      Ok (stanza_key ~native st, Only st.version)
  | _ ->
      Error
        (Printf.sprintf "Package '%s' has no installation candidate"
           (full_name ~native key))

(* The version a selector picks from the version list.  One nothing meets
   is apt's error before it solves, with the message
   CacheSetHelper::canNotGetVersion prints. *)
let select ~native key (vlist : DF.stanza list) (how, what) =
  let full = full_name ~native key in
  let first p =
    List.find_map
      (fun (st : DF.stanza) -> if p st.version then Some st.version else None)
      vlist
  in
  let only why = function Some v -> Ok (key, Only v) | None -> Error why in
  match (how, what) with
  (* apt tests these keywords before the tag, so they read the same after
     '/'; nothing is installed, as pac reads no dpkg status *)
  | _, "installed" ->
      Error
        (Printf.sprintf
           "Can't select installed version from package %s as it is not \
            installed"
           full)
  (* without pins the candidate is the newest, which heads the list *)
  | _, "candidate" ->
      only
        (Printf.sprintf
           "Can't select candidate version from package %s as it has no \
            candidate"
           full)
        (first (fun _ -> true))
  | _, "newest" ->
      only
        (Printf.sprintf
           "Can't select newest version from package '%s' as it is purely \
            virtual"
           full)
        (first (fun _ -> true))
  | '=', v ->
      only
        (Printf.sprintf "Version '%s' for '%s' was not found" v full)
        (match first (version_matches v) with
        | None -> self_provided (fst key) vlist v
        | found -> found)
  (* a release is matched against Release files, which pac does not
     read; "*" matches every file (pkgVersionMatch::FileMatch) *)
  | _, r ->
      only
        (Printf.sprintf "Release '%s' for '%s' was not found" r full)
        (if r = "*" then first (fun _ -> true) else None)

(* A name apt's cache lacks is "Unable to locate package" whatever selects
   its version. *)
let query_element ~native ~arches ~located (index : DF.stanza list) arg =
  let pkg, sel = split_arg arg in
  let key = package_key ~native ~arches index pkg in
  if not (located (fst key)) then
    Error (Printf.sprintf "Unable to locate package %s" pkg)
  else
    let vlist = version_list ~native index key in
    match sel with
    | None when vlist = [] -> virtual_candidate ~native index key
    | None -> Ok (key, Any)
    | Some sel -> select ~native key vlist sel

(* apt installs each element's version in argument order, setting it as the
   candidate, so of two naming one package the later wins; the versions the
   query names are what Strict-Pinning then keeps *)
let parse_query ~native ~arches (index : DF.stanza list) args =
  let located = cache_names index in
  let rec go acc = function
    | [] -> Ok acc
    | arg :: rest -> (
        match query_element ~native ~arches ~located index arg with
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
