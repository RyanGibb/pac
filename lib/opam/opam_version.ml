(* opam 2.5.2's OpamVersionCompare, which is Debian's ordering with no
   epoch.  Untrusted (TCB). *)

let compare = Version.Debian.compare_no_epoch
let equal a b = compare a b = 0
