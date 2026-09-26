(* a directory opens, and only the read fails, with an error that does not
   name the path as open_in's own does *)
let file path =
  if Sys.is_directory path then raise (Sys_error (path ^ ": Is a directory"))

(* a missing directory would read as one holding nothing, which makes every
   name unknown rather than the input unreadable *)
let dir path =
  if not (Sys.is_directory path) then
    raise (Sys_error (path ^ ": Not a directory"))
