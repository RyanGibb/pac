module P = Cargo_parse
module C = Pac_common.Cache

(* What the parser makes of a file is a function of the file's bytes and
   of the parser alone, so an entry is keyed by a digest of the bytes. *)
let load ~cache ~reject ~index n =
  let path = P.crate_path ~index n in
  if not (Sys.file_exists path) then ([], false)
  else
    let s = In_channel.with_open_bin path In_channel.input_all in
    let parse () =
      let k = ref 0 in
      let vs = P.parse_crate ~reject:(fun () -> incr k) s in
      (vs, !k)
    in
    let (vs, k), hit =
      match cache with
      | None -> (parse (), false)
      | Some cache -> (
          let f =
            C.entry cache ~format:Index_format.digest
              (Digest.to_hex (Digest.string s))
          in
          match (C.read f : (P.ver list * int) option) with
          | Some e -> (e, true)
          | None ->
              let e = parse () in
              C.store f (fun oc -> Marshal.to_channel oc e []);
              (e, false))
    in
    for _ = 1 to k do
      reject ()
    done;
    (vs, hit)
