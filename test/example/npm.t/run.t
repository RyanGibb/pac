The paper's npm worked example: app depends on preset and plugin, and,
under the directory key legacy, on core ^6 through an npm: alias; preset
peers on core ^6 || ^7 and plugin on core ^7.

  $ . ../../frontends/untimed.sh

In the figure's notation, which writes a version x.0.0 as x, pac's names
read:
- app@1.0.0 is the granular name <app, 1>, and likewise for plugin@1.0.0,
preset@1.0.0, core@6.0.0, core@7.0.0 and legacy(npm:core)@6.0.0, the last
<(legacy, core), 6>;
- <app@1.0.0=>plugin> is the intermediate <app, 1, plugin>, and likewise
for preset and core, and <app@1.0.0=>legacy(npm:core)> is
<app, 1, (legacy, core)>.
All 11 packages and 10 edges of the figure's reduction are here and
nothing else; this encoding has no ⊥.

  $ untimed ../../../bin/main.exe npm --core --offline --cache . --tree ./app/package.json
  root app 1.0.0
  core: 11 packages, 10 edges
  <app@1.0.0=>core> 6.0.0
    -> core@6.0.0 {6.0.0}
  <app@1.0.0=>core> 7.0.0
    -> core@7.0.0 {7.0.0}
  <app@1.0.0=>legacy(npm:core)> 6.0.0
    -> legacy(npm:core)@6.0.0 {6.0.0}
  <app@1.0.0=>plugin> 1.0.0
    -> <app@1.0.0=>core> {7.0.0}
    -> plugin@1.0.0 {1.0.0}
  <app@1.0.0=>preset> 1.0.0
    -> <app@1.0.0=>core> {6.0.0, 7.0.0}
    -> preset@1.0.0 {1.0.0}
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
  encoded solution: 9 core nodes (10 lookups)
  loaded: 4 names, 5 versions, 0 packuments fetched
