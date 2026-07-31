(lang dune 3.17)
(using coq 0.10)
(name pac)

(generate_opam_files true)

(source (github RyanGibb/pac))
(license MIT)

(authors "Ryan Gibb")
(maintainers "Ryan Gibb")

(package
 (name pac)
 (synopsis "Rocq formalization of the package calculus")
 (description
  "Definitions and theorem statements for a core dependency-resolution
calculus and its extensions with reductions to the core with OCaml
extraction.")
 (depends
  (ocaml (>= 4.14))
  (rocq-stdlib (>= 9.2))
  (coq-core (>= 9.2))
  pubgrub
  (ocamlformat :with-dev-setup)))
