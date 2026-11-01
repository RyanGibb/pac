From PackageCalculus Require Import Prelude Core VersionFormula Conflict
  Visibility Debian MultiarchDebian Opam Cargo Alpine Npm Placement
  NpmPlacement.
(* Smoke's instances are named after their functors, so importing it would
   shadow the functors extracted below. *)
From PackageCalculus Require Smoke.
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
  Smoke.Core Smoke.VersionFormula Smoke.Conflict Smoke.Concurrent
  Smoke.PeerDependency Smoke.Visibility Smoke.Feature Smoke.Virtual
  Smoke.PackageFormula Smoke.VariableFormula Smoke.ConcurrentFeature
  Smoke.Opam Smoke.Cargo Smoke.Alpine
  Debian MultiarchDebian Opam Cargo Alpine Npm Placement NpmPlacement.
