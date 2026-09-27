open Place_encoding

(* npm's queue and placement replayed over the placement reduction: next
   takes the walks of the copy npm's queue resolves next, and choose on a
   walk keeps the copy the walk already reaches or places npm's pick at the
   shallowest level that takes it.  [`Pubgrub] leaves both to PubGrub, whose
   version order also hoists. *)
val hooks :
  (Place_lookup.t, PName.t, PG.selection, PVersion.t) Pac_common.Order.driver
