module P = Npm_parse

let ( let* ) = Result.bind

let manifest (paths : string list) : (Yojson.Safe.t, string) result =
  match paths with
  | [] -> Ok (`Assoc [])
  | [ p ] -> (
      match Yojson.Safe.from_file p with
      | `Assoc _ as j -> Ok j
      | _ | (exception (Yojson.Json_error _ | Sys_error _)) ->
          Error (p ^ ": not a package.json"))
  | _ -> Error "more than one package.json"

let not_registry s =
  Error
    (s
   ^ ": not a registry spec (name, name@range, name@tag, key@npm:name@range)")

(* npm refuses a dist-tag that is a range, so a spec the packument tags is
   a tag, and one it does not is a range unless it can only be a tag *)
let classify ar s : ([ `Plain | `Tagged ] * (string * string), string) result =
  match P.spec_of s with
  | None -> not_registry s
  | Some (k, r) when P.split_alias r <> None || r = "*" -> Ok (`Plain, (k, r))
  | Some (k, r) -> (
      let r' = String.trim r in
      match Archive.dist_tag ar k r' with
      | Some v -> Ok (`Tagged, (k, v))
      | None when P.looks_like_tag r' -> Error (s ^ ": no such dist-tag")
      | None -> Ok (`Plain, (k, r)))

(* arborist's #add resolves a tag to its version only after an await, so
   the other specs are all added first, in order. *)
let resolve_specs ar specs =
  let* classified =
    List.fold_left
      (fun acc s ->
        let* l = acc in
        let* c = classify ar s in
        Ok (c :: l))
      (Ok []) specs
  in
  let only kind =
    List.rev
      (List.filter_map
         (fun (k, e) -> if k = kind then Some e else None)
         classified)
  in
  Ok (only `Plain @ only `Tagged)

let target (k, r) = match P.split_alias r with Some (t, _) -> t | None -> k

(* npm fetches each spec's packument while building the tree, and E404s
   on a name the registry lacks rather than resolving without it *)
let check_published ar specs =
  let unpublished s = Archive.versions_of ar (target s) = [] in
  match List.find_opt unpublished specs with
  | None -> Ok ()
  | Some s ->
      Error
        (Printf.sprintf "no packument for %s under %s%s" (target s)
           ar.Archive.cache
           (if ar.Archive.offline then " (offline)" else ""))

(* arborist names a root with no name by its directory, which is no part
   of the query; "." is a name no registry package can have *)
let root_of pkg =
  let str k = match P.member k pkg with `String s -> s | _ -> "" in
  let name = match str "name" with "" -> "." | n -> n in
  match P.ver_of ~root:true (str "version") pkg with
  | Some v -> Ok { v with P.v_name = name }
  | None -> Error "not a package.json"

let root ar (args : string list) : (P.ver, string) result =
  let paths, specs = List.partition P.is_manifest_arg args in
  let* pkg = manifest paths in
  let* specs = resolve_specs ar specs in
  let* () = check_published ar specs in
  root_of (List.fold_left P.add_to pkg specs)
