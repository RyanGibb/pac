From PackageCalculus Require Import Prelude Core Versions Conflict Visibility
  Debian DebianMA Opam Cargo Alpine Npm Smoke.
From Stdlib Require Import Extraction ExtrOcamlBasic.

Extraction Language OCaml.

(* dune's coq.extraction runs coqc inside _build/default/extraction; the
   implicit output directory is the intended one. *)
Set Extraction Output Directory ".".

(* The nat-instantiated smoke modules reach stdlib Type-valued parity
   constants (Nat.EvenT/OddT) that are Qed-opaque; extraction opens them,
   which is sound here because every extracted definition is audited
   Closed under the global context (notes/validate.sh). *)
Set Warnings "-extraction-opaque-accessed".

Extraction "pac_extraction.ml"
  Smoke.C Smoke.Ver Smoke.Cfl Smoke.Conc Smoke.Peer Smoke.Vis
  Smoke.Feat Smoke.Virt Smoke.PkgF Smoke.VarF Smoke.FC Smoke.Op Smoke.Cgo Smoke.Alp
  Debian DebianMA Opam Cargo Alpine Npm.
