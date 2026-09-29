(* An entry is a function of its key and of the code that wrote it alone,
   so it is stored under a digest of each, as cargo keeps the index entries
   it has read under CARGO_HOME: a changed input or a rebuilt pac misses
   the cache rather than reading a stale or differently laid out entry,
   and no entry is ever invalidated. *)
let entry dir ~format key =
  let ( / ) = Filename.concat in
  dir / format / String.sub key 0 2 / key

let rec mkdir_p d =
  if not (Sys.file_exists d) then begin
    mkdir_p (Filename.dirname d);
    try Sys.mkdir d 0o755 with Sys_error _ -> ()
  end

(* an entry that is not whole Marshal values end to end is a miss, never a
   misread *)
let open_entry f =
  match open_in_bin f with
  | exception Sys_error _ -> None
  | ic -> (
      let n = in_channel_length ic in
      let h = Bytes.create Marshal.header_size in
      let rec whole pos =
        pos = n
        || pos < n
           && begin
             seek_in ic pos;
             really_input ic h 0 Marshal.header_size;
             whole (pos + Marshal.total_size h 0)
           end
      in
      match whole 0 with
      | true ->
          seek_in ic 0;
          Some ic
      | false | (exception (End_of_file | Failure _ | Invalid_argument _)) ->
          close_in_noerr ic;
          None)

let value ic =
  try Some (Marshal.from_channel ic) with End_of_file | Failure _ -> None

let read f =
  Option.bind (open_entry f) (fun ic ->
      Fun.protect ~finally:(fun () -> close_in_noerr ic) (fun () -> value ic))

(* One scratch file per process, renamed into place within its directory,
   which is atomic: runs sharing a cache write the same entry at once, and
   a reader sees none of it or all of it.  A cache that cannot be written
   only costs the next run a parse. *)
let store f write =
  let tmp = Printf.sprintf "%s.%d.tmp" f (Unix.getpid ()) in
  try
    mkdir_p (Filename.dirname f);
    Out_channel.with_open_bin tmp write;
    Sys.rename tmp f
  with Sys_error _ -> ( try Sys.remove tmp with Sys_error _ -> ())
