The world lua-stdlib-debug lua-stringy vim gvim over seven packages: lua
is provided bare by lua5.2 and lua5.4, vim by gvim's versioned provides,
and lua5.4-stringy has an install-if rule on lua-stringy=0.5.1-r3 and
lua5.4.

  $ . ../../frontends/untimed.sh

@root () carries the world.  <lua5.2{5.2.4-r13} | lua5.4{5.4.7-r0} | lua{}>
chooses among lua's providers, one version per alternative;
<!lua5.4{5.4.7-r0} | lua5.4-stringy{0.5.1-r3}> is the install-if rule's
formula, whose version 0, the negated atom's alternative, depends on
lua5.4 at the complement {⊥}; and vim's version
provided=9.1.1105-r0(gvim-9.1.1105-r0) is gvim's provides.  The core is 22
packages and 14 edges; lua, which no package of its own provides, has
only ⊥.

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
