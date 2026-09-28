module P = Cargo_parse

(* What the parser makes of a file is a function of the file's bytes and
   of the parser alone, so an entry is stored under a digest of each, as
   cargo keeps the index entries it has read under CARGO_HOME: a changed
   file or a rebuilt parser misses the cache rather than reading a stale or
   differently laid out entry, and no entry is ever invalidated. *)
let entry cache key =
  let ( / ) = Filename.concat in
  cache / Index_format.digest / String.sub key 0 2 / key

let rec mkdir_p d =
  if not (Sys.file_exists d) then begin
    mkdir_p (Filename.dirname d);
    try Sys.mkdir d 0o755 with Sys_error _ -> ()
  end

(* an entry that is not whole Marshal data is a miss, never a misread *)
let read f : (P.ver list * int) option =
  match In_channel.with_open_bin f In_channel.input_all with
  | exception Sys_error _ -> None
  | s -> (
      match Marshal.total_size (Bytes.unsafe_of_string s) 0 with
      | n when n = String.length s -> Some (Marshal.from_string s 0)
      | _ | (exception (Failure _ | Invalid_argument _)) -> None)

(* One scratch file per process, renamed into place within its directory,
   which is atomic: runs sharing a cache write the same entry at once, and
   a reader sees none of it or all of it.  A cache that cannot be written
   only costs the next run a parse. *)
let write f v =
  let tmp = Printf.sprintf "%s.%d.tmp" f (Unix.getpid ()) in
  try
    mkdir_p (Filename.dirname f);
    Out_channel.with_open_bin tmp (fun oc -> Marshal.to_channel oc v []);
    Sys.rename tmp f
  with Sys_error _ -> ( try Sys.remove tmp with Sys_error _ -> ())

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
          let f = entry cache (Digest.to_hex (Digest.string s)) in
          match read f with
          | Some e -> (e, true)
          | None ->
              let e = parse () in
              write f e;
              (e, false))
    in
    for _ = 1 to k do
      reject ()
    done;
    (vs, hit)
