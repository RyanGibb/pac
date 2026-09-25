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
  "A core dependency-resolution calculus and its extensions, each
reduction to the core proved sound and complete in Rocq and extracted to
OCaml, with PubGrub frontends for five package managers.")
 (depends
  (ocaml (>= 4.14))
  (rocq-stdlib (>= 9.2))
  (coq-core (>= 9.2))
  pubgrub
  cmdliner
  yojson
  opam-file-format
  (ocamlformat :with-dev-setup)))
