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
The figure's 11 packages are here, and 11 more that carry each peer on
core to where it resolves.  <app@1.0.0=>plugin@1.0.0^core> is the link
from app's directory holding plugin 1.0.0 for plugin's peer on core, at a
version of app's core that plugin's range admits, and <plugin@1.0.0^core>
is plugin's sight of core, which the link sets to that version or leaves
∗ where no copy below plugin reads it (⊥ would read that nothing is
offered); the same two names serve preset.  app is the root, which may
leave a core no peer asks for empty, so <app, 1, core> has ⊥ too.  The
directory holding each declarer now reaches <app, 1, core> through its
link rather than directly, so the figure's two peer edges become two
edges into the links, and each version of a link adds 2 edges more.
app's copies are nested as before.

  $ untimed ../../../bin/main.exe npm --core --offline --cache . --tree ./app/package.json
  root app 1.0.0
  core: 26 packages, 19 edges
  <app@1.0.0=>core> 6.0.0
    -> core@6.0.0 {6.0.0}
  <app@1.0.0=>core> 7.0.0
    -> core@7.0.0 {7.0.0}
  <app@1.0.0=>core> ⊥
  <app@1.0.0=>legacy(npm:core)> 6.0.0
    -> <legacy(npm:core)@app@1.0.0 npm:core@^6> {6.0.0}
    -> legacy(npm:core)@6.0.0 {6.0.0}
  <app@1.0.0=>plugin> 1.0.0
    -> <app@1.0.0=>plugin@1.0.0^core> {7.0.0}
    -> <plugin@app@1.0.0 ^1> {1.0.0}
    -> plugin@1.0.0 {1.0.0}
  <app@1.0.0=>plugin@1.0.0^core> 7.0.0
    -> <app@1.0.0=>core> {7.0.0}
    -> <plugin@1.0.0^core> {7.0.0, ∗}
  <app@1.0.0=>preset> 1.0.0
    -> <app@1.0.0=>preset@1.0.0^core> {6.0.0, 7.0.0}
    -> <preset@app@1.0.0 ^1> {1.0.0}
    -> preset@1.0.0 {1.0.0}
  <app@1.0.0=>preset@1.0.0^core> 6.0.0
    -> <app@1.0.0=>core> {6.0.0}
    -> <preset@1.0.0^core> {6.0.0, ∗}
  <app@1.0.0=>preset@1.0.0^core> 7.0.0
    -> <app@1.0.0=>core> {7.0.0}
    -> <preset@1.0.0^core> {7.0.0, ∗}
  <legacy(npm:core)@app@1.0.0 npm:core@^6> 6.0.0
  <legacy(npm:core)@app@1.0.0 npm:core@^6> 7.0.0
  <plugin@1.0.0^core> 7.0.0
  <plugin@1.0.0^core> ∗
  <plugin@1.0.0^core> ⊥
  <plugin@app@1.0.0 ^1> 1.0.0
  <preset@1.0.0^core> 6.0.0
  <preset@1.0.0^core> 7.0.0
  <preset@1.0.0^core> ∗
  <preset@1.0.0^core> ⊥
  <preset@app@1.0.0 ^1> 1.0.0
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
  encoded solution: 16 core nodes (19 lookups)
  loaded: 4 names, 5 versions, 0 packuments fetched
