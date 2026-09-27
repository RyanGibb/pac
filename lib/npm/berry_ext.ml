type t = {
  x_range : Npm_version.range;
  x_deps : (string * string) list;
  x_peers : (string * string) list;
  x_meta : (string * bool) list;
}

let strings j =
  List.filter_map
    (function k, `String v -> Some (k, v) | _ -> None)
    (match j with `Assoc l -> l | _ -> [])

let optional j =
  List.filter_map
    (function
      | k, `Assoc m -> (
          match List.assoc_opt "optional" m with
          | Some (`Bool b) -> Some (k, b)
          | _ -> None)
      | _ -> None)
    (match j with `Assoc l -> l | _ -> [])

let field f = function
  | `Assoc l -> Option.value (List.assoc_opt f l) ~default:`Null
  | _ -> `Null

(* Yarn Berry's built-in packageExtensions, @yarnpkg/extensions 2.0.6 as
   Yarn 4.14.1 bundles it (packages/yarnpkg-extensions/sources/index.ts),
   from berry-extensions.json, which the npm check reads too.  A key is a
   name and a range, split at the last @ as the range holds none; each
   name's entries are kept in the list's order, since the first to add a
   dependency wins and the last to set a peer's meta does. *)
let by_name : (string, t list) Hashtbl.t Lazy.t =
  lazy
    (let tbl = Hashtbl.create 256 in
     (match Yojson.Safe.from_string Berry_ext_data.json with
     | `List l ->
         List.iter
           (function
             | `List [ `String key; x ] ->
                 let i = String.rindex key '@' in
                 let name = String.sub key 0 i in
                 let e =
                   {
                     x_range =
                       Npm_version.parse_range ~include_prerelease:true
                         (String.sub key (i + 1) (String.length key - i - 1));
                     x_deps = strings (field "dependencies" x);
                     x_peers = strings (field "peerDependencies" x);
                     x_meta = optional (field "peerDependenciesMeta" x);
                   }
                 in
                 Hashtbl.replace tbl name
                   (Option.value (Hashtbl.find_opt tbl name) ~default:[] @ [ e ])
             | _ -> invalid_arg "berry-extensions.json")
           l
     | _ -> invalid_arg "berry-extensions.json");
     tbl)

let of_name (n : string) : t list =
  Option.value (Hashtbl.find_opt (Lazy.force by_name) n) ~default:[]

(* Berry's satisfiesWithPrereleases (yarnpkg-core/sources/semverUtils.ts):
   the range with prereleases included, and failing that the version with
   its prerelease tags dropped.  Berry drops the comparators' tags too, but
   node-semver compares a comparator by its text, which keeps them, so
   3.13.0 does not match 3.13.0-next.1. *)
let matches (vers : string) (x : t) : bool =
  Npm_version.holds_pre vers x.x_range
  || Npm_version.holds_pre (Npm_version.release vers) x.x_range
