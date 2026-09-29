(* gen_format <name=value>... <file>...: the digest a cache's entries are
   kept under, of the values (the toolchain's versions) and of each file's
   name and contents *)
let () =
  let b = Buffer.create 65536 in
  Array.iteri
    (fun i a ->
      if i > 0 then begin
        Buffer.add_string b a;
        Buffer.add_char b '\000';
        if not (String.contains a '=') then
          Buffer.add_string b (In_channel.with_open_bin a In_channel.input_all)
      end)
    Sys.argv;
  Printf.printf "let digest = %S\n"
    (Digest.to_hex (Digest.string (Buffer.contents b)))
