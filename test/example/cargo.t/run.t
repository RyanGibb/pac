app depends on serde with its derive feature and on derivative, every
record opting out of the default feature; serde_derive, which derive
activates, and derivative depend on syn at the semver-incompatible "2" and
"1".  The root is resolved with no features, which is
--no-default-features: unset, the root would get the default feature the
parser supplies to a crate declaring none, and with it a featured name of
its own.

  $ . ../../frontends/untimed.sh

root () carries the root; a granular name n@c is n in semver class c,
the class written in full (1.0.0, 0.1.0); a featured name n/f@c is n's
feature f in class c; and a slot name n@c->a(req) is n's dependency a,
whose version granularity:c is the class it resolves in.  The core is 14
packages and 14 edges, and this encoding has no ⊥.

  $ untimed ../../../bin/main.exe cargo --core --no-default-features --print-parents index app/Cargo.toml
  root app 0.1.0 with no features
  core: 14 packages, 14 edges
  app@0.1.0 0.1.0
    -> app@0.1.0->derivative(>=2.0.0,<3.0.0) {granularity:2.0.0}
    -> app@0.1.0->serde(>=1.0.0,<2.0.0) {granularity:1.0.0}
  app@0.1.0->derivative(>=2.0.0,<3.0.0) granularity:2.0.0
    -> derivative@2.0.0 {2.2.0}
  app@0.1.0->serde(>=1.0.0,<2.0.0) granularity:1.0.0
    -> serde/derive@1.0.0 {1.0.210}
    -> serde@1.0.0 {1.0.210}
  derivative@2.0.0 2.2.0
    -> derivative@2.0.0->syn(>=1.0.0,<2.0.0) {granularity:1.0.0}
  derivative@2.0.0->syn(>=1.0.0,<2.0.0) granularity:1.0.0
    -> syn@1.0.0 {1.0.109}
  root ()
    -> app@0.1.0 {0.1.0}
  serde/derive@1.0.0 1.0.210
    -> serde@1.0.0 {1.0.210}
    -> serde@1.0.0->serde_derive(>=1.0.0,<2.0.0) {granularity:1.0.0}
  serde@1.0.0 1.0.210
  serde@1.0.0->serde_derive(>=1.0.0,<2.0.0) granularity:1.0.0
    -> serde_derive@1.0.0 {1.0.209, 1.0.210}
  serde_derive@1.0.0 1.0.209
    -> serde_derive@1.0.0->syn(>=2.0.0,<3.0.0) {granularity:2.0.0}
  serde_derive@1.0.0 1.0.210
    -> serde_derive@1.0.0->syn(>=2.0.0,<3.0.0) {granularity:2.0.0}
  serde_derive@1.0.0->syn(>=2.0.0,<3.0.0) granularity:2.0.0
    -> syn@2.0.0 {2.0.77}
  syn@1.0.0 1.0.109
  syn@2.0.0 2.0.77
  packages (6):
    app 0.1.0
    derivative 2.2.0
    serde 1.0.210 [derive]
    serde_derive 1.0.210
    syn 1.0.109
    syn 2.0.77
  parent edges (5):
    app 0.1.0 -> derivative(derivative) 2.2.0
    app 0.1.0 -> serde(serde) 1.0.210
    derivative 2.2.0 -> syn(syn) 1.0.109
    serde 1.0.210 -> serde_derive(serde_derive) 1.0.210
    serde_derive 1.0.210 -> syn(syn) 2.0.77
  encoded solution: 13 core nodes (14 lookups)
  loaded: 5 names, 6 versions
