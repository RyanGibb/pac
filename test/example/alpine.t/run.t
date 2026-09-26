The paper's Alpine worked example: the world lua-stdlib-debug lua-stringy
vim gvim over seven packages, lua provided bare by lua5.2 and lua5.4, vim
claimed by gvim's versioned provides, and lua5.4-stringy's install-if
rule on lua-stringy=0.5.1-r3 and lua5.4.  APKINDEX is the figure's index
with the A: field its cut drops.

  $ . ../../frontends/untimed.sh

In the figure's notation, pac's names read:
- @root () is r *;
- <lua5.2{5.2.4-r13} | lua5.4{5.4.7-r0} | lua{}> is <psi_lua>, its
versions 0, 1 and 2 the figure's;
- <!lua5.4{5.4.7-r0} | lua5.4-stringy{0.5.1-r3}> is <psi_T>, whose
version 0, the negated atom's alternative, depends on lua5.4 at the
complement {⊥};
- vim's version provided=9.1.1105-r0(gvim-9.1.1105-r0) is the provides
<gvim, 9.1.1105-r0>.
Every node and all 14 edges of the figure's reduction are here.  The
figure draws ⊥ only where an edge admits it, so it omits on purpose the ⊥
of gvim, lua-stdlib-debug, lua-stringy, lua5.2, lua5.4-stringy and vim,
and lua ⊥, lua's only version, which is why its dashed lua has none.

  $ untimed ../../../bin/main.exe alpine --core APKINDEX lua-stdlib-debug lua-stringy vim gvim
  core: 22 packages, 14 edges
  <!lua5.4{5.4.7-r0} | lua5.4-stringy{0.5.1-r3}> 0
    -> lua5.4 {⊥}
  <!lua5.4{5.4.7-r0} | lua5.4-stringy{0.5.1-r3}> 1
    -> lua5.4-stringy {0.5.1-r3}
  <lua5.2{5.2.4-r13} | lua5.4{5.4.7-r0} | lua{}> 0
    -> lua5.2 {5.2.4-r13}
  <lua5.2{5.2.4-r13} | lua5.4{5.4.7-r0} | lua{}> 1
    -> lua5.4 {5.4.7-r0}
  <lua5.2{5.2.4-r13} | lua5.4{5.4.7-r0} | lua{}> 2
    -> lua {}
  @root ()
    -> gvim {9.1.1105-r0}
    -> lua-stdlib-debug {1.0.1-r1}
    -> lua-stringy {0.5.1-r3}
    -> vim {9.1.1105-r0, provided=9.1.1105-r0(gvim-9.1.1105-r0)}
  gvim 9.1.1105-r0
    -> vim {provided=9.1.1105-r0(gvim-9.1.1105-r0)}
  gvim ⊥
  lua ⊥
  lua-stdlib-debug 1.0.1-r1
    -> <lua5.2{5.2.4-r13} | lua5.4{5.4.7-r0} | lua{}> {0, 1, 2}
  lua-stdlib-debug ⊥
  lua-stringy 0.5.1-r3
    -> <!lua5.4{5.4.7-r0} | lua5.4-stringy{0.5.1-r3}> {0, 1}
  lua-stringy ⊥
  lua5.2 5.2.4-r13
  lua5.2 ⊥
  lua5.4 5.4.7-r0
  lua5.4 ⊥
  lua5.4-stringy 0.5.1-r3
    -> lua5.4 {5.4.7-r0}
  lua5.4-stringy ⊥
  vim 9.1.1105-r0
  vim provided=9.1.1105-r0(gvim-9.1.1105-r0)
    -> gvim {9.1.1105-r0}
  vim ⊥
  packages (5):
    gvim 9.1.1105-r0
    lua-stdlib-debug 1.0.1-r1
    lua-stringy 0.5.1-r3
    lua5.4 5.4.7-r0
    lua5.4-stringy 0.5.1-r3
  encoded solution: 9 core nodes (16 lookups)
  loaded: 7 names, 7 versions, 3 provides entries, 1 install_if rules
