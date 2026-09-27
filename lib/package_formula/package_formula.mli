module Make
    (N : Pac.UsualOrderedType)
    (V : Pac.UsualOrderedType)
    (PF :
      module type of Pac.PackageFormula (N) (V))
        (P : sig
          type t

          val v : t -> PF.Reduction.Version.t

          (* the absent version, tagged: [tag] must give it at every name *)
          val bot : t
          val compare : t -> t -> int
          val pp : Format.formatter -> t -> unit
        end)
        (_ : sig
          val pp_name : Format.formatter -> PF.Reduction.Name.t -> unit
        end) : sig
  module Name : sig
    type t = PF.Reduction.Name.t

    val compare : t -> t -> int
    val pp : Format.formatter -> t -> unit
  end

  module PG : module type of Pubgrub.Make (Name) (P)

  type t

  (* [oracle] is the versions lookup at an original name, before tagging;
     the encoder reads it at the names a formula negates, so it must be
     complete when asked.  Its answer is memoised except at a [volatile]
     name, whose versions may grow as the run loads more of the archive. *)
  val create :
    root:N.t * V.t ->
    tag:(PF.Reduction.Name.t -> PF.Reduction.Version.t -> P.t) ->
    oracle:(N.t -> PF.VSet.t) ->
    ?volatile:(N.t -> bool) ->
    unit ->
    t

  val lookups : t -> int

  (* [dependees] is PF.Reduction's dependees lookup at the package, read off
     the sub-instance the driver builds for it; a thunk, so a package asked
     about twice builds it once *)
  val process : t -> PF.Pkg.t -> (unit -> PF.coq_Formula list) -> unit
  val dependees : t -> PF.Reduction.T.Pkg.t -> PF.Reduction.T.Dependees.t list

  val dependencies :
    t ->
    touch:(PF.Reduction.T.Pkg.t -> unit) ->
    PF.Reduction.Name.t ->
    P.t ->
    (PF.Reduction.Name.t * PG.Ranges.t) list

  val defer_bot :
    ?last:(PF.Reduction.Name.t -> bool) ->
    assigned:(PF.Reduction.Name.t -> PG.selection) ->
    (PF.Reduction.Name.t * int) list ->
    PF.Reduction.Name.t

  val core : t -> touch:(PF.Reduction.T.Pkg.t -> unit) -> unit

  (* The core solution back through the proved decoder to the package
     formula's packages.  Reading the ecosystem's packages off the
     solution directly would be a further, unproved, decoder, and it is
     the decoded one the soundness theorem is stated about. *)
  val solve :
    t ->
    touch:(PF.Reduction.T.Pkg.t -> unit) ->
    (Name.t, PG.selection, P.t) Pac_common.Order.hooks ->
    (PF.PkgSet.t * int, Pac_common.Report.explanation) result
end
