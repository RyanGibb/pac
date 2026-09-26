The paper's Cargo worked example: app depends on serde with its derive
feature and on derivative, every record opting out of the default
feature; serde_derive, which derive activates, and derivative depend on
syn at the semver-incompatible "2" and "1".  The example resolves the root
with no features, which is --no-default-features: unset, the root would
get the default feature the parser supplies to a crate declaring none,
and with it a featured name the figure does not have.

  $ . ../../frontends/untimed.sh

In the figure's notation, pac's names read:
- root () is r *;
- a granular name n@c is <n, c>, the class c written in full (1.0.0 for
the figure's 1, 0.1.0 for its 0.1);
- a featured name n/f@c is <<n, f>, c>;
- a slot name n@c->a(req) is <n, c, a>, and its version granularity:c is
the class c.
All 14 packages and 14 edges of the figure's reduction are here and
nothing else; this encoding has no ⊥.

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
