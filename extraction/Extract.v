From PackageCalculus Require Import Prelude Core Versions Conflict Visibility
  Debian DebianMA Opam Cargo Alpine Npm Smoke.
From Stdlib Require Import Extraction ExtrOcamlBasic.

Extraction Language OCaml.

(* dune's coq.extraction runs coqc inside _build/default/extraction; the
   implicit output directory is the intended one. *)
Set Extraction Output Directory ".".

(* The nat-instantiated smoke modules reach stdlib Type-valued parity
   constants (Nat.EvenT/OddT) that are Qed-opaque; extraction opens them,
   which is sound here because the reduction products are audited Closed
   under the global context (scripts/check-axioms.sh). *)
Set Warnings "-extraction-opaque-accessed".

(* lex is a function, so OCaml's strictness evaluates both legs of every
   lexicographic comparison even when the first decides; inlining restores
   the short circuit. *)
Extraction Inline lex.

Extraction "pac_extraction.ml"
  Smoke.C Smoke.Ver Smoke.Cfl Smoke.Conc Smoke.Peer Smoke.Vis
  Smoke.Feat Smoke.Virt Smoke.PkgF Smoke.VarF Smoke.FC Smoke.Op Smoke.Cgo Smoke.Alp
  Debian DebianMA Opam Cargo Alpine Npm.
