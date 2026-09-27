let file path =
  if Sys.is_directory path then raise (Sys_error (path ^ ": Is a directory"))

let dir path =
  if not (Sys.is_directory path) then
    raise (Sys_error (path ^ ": Not a directory"))
