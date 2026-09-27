open Encoding

val is_orig : Np.Vs.version -> bool
val within : (PName.t -> PG.selection) -> PName.t -> PVersion.t -> bool

(* A link, its holder's directory and the copy's sight are one version
   wherever the sight is read, and each constraint between them is one
   dependency per version, so a random pick that breaks it rules out only
   itself: a peer like @types/node (2364 versions) then costs a conflict
   per version.  A random order therefore picks among the versions the
   others already leave open, and leaves a link that may be Bot at Bot
   while nothing else opens its holder's directory, as npm installs no
   optional peer by itself.  Preference only: an empty filter keeps
   [cands]. *)
val viable :
  Lookup.t ->
  assigned:(PName.t -> PG.selection) ->
  PName.t ->
  PVersion.t list ->
  PVersion.t list
