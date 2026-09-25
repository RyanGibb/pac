(* Debian versions order as deb-version(7) has it, epoch included.
   Untrusted, and tested only on the cases in test_version.ml and
   lib/version/test_debian.ml. *)

let compare = Version.Debian.compare
