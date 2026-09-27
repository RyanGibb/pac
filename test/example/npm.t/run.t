app depends on preset and plugin, and, under the directory key legacy, on
core ^6 through an npm: alias; preset peers on core ^6 || ^7 and plugin on
core ^7.

  $ . ../../frontends/untimed.sh

app@1.0.0 is the granular name of app 1.0.0, and legacy(npm:core)@6.0.0
that of core 6.0.0 under the key legacy; <app@1.0.0=>plugin> is app's
directory for plugin, and likewise for preset, core and
legacy(npm:core).  Each peer on core reaches the copy it resolves to
through two names: <app@1.0.0=>plugin@1.0.0^core>, the link from app's
directory holding plugin 1.0.0, at a version of app's core that plugin's
range admits, and <plugin@1.0.0^core>, plugin's sight of core, which the
link sets to that version or leaves ∗ where no copy below plugin reads it
(⊥ would read that nothing is offered); the same two names serve preset.
app is the root, which may leave a core no peer asks for absent, so
<app@1.0.0=>core> has ⊥ too.  The core is 22 packages and 16 edges.

  $ untimed ../../../bin/main.exe npm --core --offline --cache . --tree ./app/package.json
  root app 1.0.0
  core: 22 packages, 16 edges
  <app@1.0.0=>core> 6.0.0
    -> core@6.0.0 {6.0.0}
  <app@1.0.0=>core> 7.0.0
    -> core@7.0.0 {7.0.0}
  <app@1.0.0=>core> ⊥
  <app@1.0.0=>legacy(npm:core)> 6.0.0
    -> legacy(npm:core)@6.0.0 {6.0.0}
  <app@1.0.0=>plugin> 1.0.0
    -> <app@1.0.0=>plugin@1.0.0^core> {7.0.0}
    -> plugin@1.0.0 {1.0.0}
  <app@1.0.0=>plugin@1.0.0^core> 7.0.0
    -> <app@1.0.0=>core> {7.0.0}
    -> <plugin@1.0.0^core> {7.0.0, ∗}
  <app@1.0.0=>preset> 1.0.0
    -> <app@1.0.0=>preset@1.0.0^core> {6.0.0, 7.0.0}
    -> preset@1.0.0 {1.0.0}
  <app@1.0.0=>preset@1.0.0^core> 6.0.0
    -> <app@1.0.0=>core> {6.0.0}
    -> <preset@1.0.0^core> {6.0.0, ∗}
  <app@1.0.0=>preset@1.0.0^core> 7.0.0
    -> <app@1.0.0=>core> {7.0.0}
    -> <preset@1.0.0^core> {7.0.0, ∗}
  <plugin@1.0.0^core> 7.0.0
  <plugin@1.0.0^core> ∗
  <plugin@1.0.0^core> ⊥
  <preset@1.0.0^core> 6.0.0
  <preset@1.0.0^core> 7.0.0
  <preset@1.0.0^core> ∗
  <preset@1.0.0^core> ⊥
  app@1.0.0 1.0.0
    -> <app@1.0.0=>legacy(npm:core)> {6.0.0}
    -> <app@1.0.0=>plugin> {1.0.0}
    -> <app@1.0.0=>preset> {1.0.0}
  core@6.0.0 6.0.0
  core@7.0.0 7.0.0
  legacy(npm:core)@6.0.0 6.0.0
  plugin@1.0.0 1.0.0
  preset@1.0.0 1.0.0
  packages (5):
    app 1.0.0
    core 7.0.0
    core 6.0.0 at legacy
    plugin 1.0.0
    preset 1.0.0
  node_modules (4):
    app 1.0.0 <- core 7.0.0
    app 1.0.0 <- core 6.0.0 at legacy
    app 1.0.0 <- plugin 1.0.0
    app 1.0.0 <- preset 1.0.0
  encoded solution: 13 core nodes (16 lookups)
  loaded: 4 names, 5 versions, 0 packuments fetched
