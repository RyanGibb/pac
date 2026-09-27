open Encoding

(* build-ideal-tree.js places what each copy's problem edges fetch, taking
   copies from a queue ordered by where they sit in node_modules
   (#buildDepStep), and takes for each edge the version npm-pick-manifest
   picks, unless the copy's node_modules lookup already finds one the
   range admits.  The replay rebuilds that tree from the solver's
   decisions, so next names the directory npm resolves next and choose
   picks what npm would put there.  [`Pubgrub] leaves both to PubGrub. *)
val hooks :
  (Lookup.t, PName.t, PG.selection, PVersion.t) Pac_common.Order.driver
