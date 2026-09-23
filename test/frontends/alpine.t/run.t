  $ ../../../src/main.exe alpine APKINDEX app docs | sed -E '/^(parse|solve) [0-9.]+s$/d'
  index APKINDEX
  cone: 3 packages, 0 provides entries, 1 install_if rules
  packages (3):
    app 1.0
    app-doc 1.0
    docs 1.0
  encoded solution: 5 core nodes (4 Alpine packages encoded)

apk picks among the providers of a name with compare_providers, whose first
live key on a fresh root is the version the provider offers *at the
requested name* -- a package's own version where it claims the name itself,
the p: operand where it is an alias, and null where the provides carries no
version at all.  provider_priority (k:) is only the key after that.

An unversioned provides offers a null version, which loses to every real
one, so k: decides only between unversioned providers.  nano and vim both
provide editor, nano sorts first and so heads the encoded disjunction, but
vim carries the higher k: and is what apk installs:

  $ ../../../src/main.exe alpine PROVIDERS editor | sed -E '/^(parse|solve) [0-9.]+s$/d'
  index PROVIDERS
  cone: 14 packages, 7 provides entries, 0 install_if rules
  packages (1):
    vim 1.0
  encoded solution: 3 core nodes (2 Alpine packages encoded)

The same null is why a package of the name itself beats an unversioned
provider of it however high that provider's k:.  tool-extra provides tool
with k:50 and heads the disjunction, but tool 2.0 offers 2.0 against
tool-extra's null:

  $ ../../../src/main.exe alpine PROVIDERS tool | sed -E '/^(parse|solve) [0-9.]+s$/d'
  index PROVIDERS
  cone: 14 packages, 7 provides entries, 0 install_if rules
  packages (1):
    tool 2.0
  encoded solution: 3 core nodes (2 Alpine packages encoded)

An unversioned provides without k: is not a low-ranked candidate but no
candidate at all: apk-package(5) says such a provides "will not be
selected automatically for installation", and specifying k: is what
enables that selection.  orphan provides nokey and nothing else does, so
the dependency has nothing to satisfy it:

  $ ../../../src/main.exe alpine PROVIDERS nokey | sed -E '/^(parse|solve) [0-9.]+s$/d'
  index PROVIDERS
  cone: 14 packages, 7 provides entries, 0 install_if rules
  unsatisfiable:
  Because @root () -> nokey ∅ and root -> @root (), version solving failed..

A *versioned* provides offers a real version, and a package claiming a name
itself gets no privilege over one: the two are compared on the versions
they offer and nothing else.  vers-alt provides vers=9.9 where the real
vers is 1.0, and apk installs vers-alt:

  $ ../../../src/main.exe alpine PROVIDERS vers-user | sed -E '/^(parse|solve) [0-9.]+s$/d'
  index PROVIDERS
  cone: 14 packages, 7 provides entries, 0 install_if rules
  packages (2):
    vers-alt 9.9
    vers-user 1.0
  encoded solution: 4 core nodes (5 Alpine packages encoded)

k: is the key below the offered version, and it is read off whichever
package offers it, alias or not.  prio-alt provides prio=1.0, tying the
real prio 1.0 on version, and prio's own k:100 beats prio-alt's k:1:

  $ ../../../src/main.exe alpine PROVIDERS prio-user | sed -E '/^(parse|solve) [0-9.]+s$/d'
  index PROVIDERS
  cone: 14 packages, 7 provides entries, 0 install_if rules
  packages (2):
    prio 1.0
    prio-user 1.0
  encoded solution: 3 core nodes (3 Alpine packages encoded)

and the same tie goes the other way when the alias is the one carrying the
k:.  prio-lo-alt provides prio-lo=1.0 with k:5 against a real prio-lo 1.0
with none, so the alias wins:

  $ ../../../src/main.exe alpine PROVIDERS prio-lo-user | sed -E '/^(parse|solve) [0-9.]+s$/d'
  index PROVIDERS
  cone: 14 packages, 7 provides entries, 0 install_if rules
  packages (2):
    prio-lo-alt 2.0
    prio-lo-user 1.0
  encoded solution: 4 core nodes (5 Alpine packages encoded)

An unversioned provides without k: still satisfies a dependency when the
world names its owner: apk-package(5) says that without a provider-priority
"user is expected to manually select one of the concrete package names in
world".  pv-prov provides pv-virt with no k:, and here the world names it:

  $ ../../../src/main.exe alpine BARE pv-prov pv-user | sed -E '/^(parse|solve) [0-9.]+s$/d'
  index BARE
  cone: 9 packages, 4 provides entries, 1 install_if rules
  packages (2):
    pv-prov 1.0
    pv-user 1.0
  encoded solution: 4 core nodes (3 Alpine packages encoded)

while without it pv-user has nothing to satisfy pv-virt, as in apk:

  $ ../../../src/main.exe alpine BARE pv-user | sed -E '/^(parse|solve) [0-9.]+s$/d'
  index BARE
  cone: 9 packages, 4 provides entries, 1 install_if rules
  unsatisfiable:
  Because @root () -> pv-user 1.0 and pv-user 1.0 -> pv-virt ∅, @root * is forbidden..
  And because root -> @root (), version solving failed.

apk installs each of the next four by behaviour beyond its documentation,
out of scope here because it depends on why a package is present:

  $ ../../../src/main.exe alpine BARE pv-both | sed -E '/^(parse|solve) [0-9.]+s$/d'
  index BARE
  cone: 9 packages, 4 provides entries, 1 install_if rules
  unsatisfiable:
  Because @root () -> pv-both 1.0 and pv-both 1.0 -> pv-virt ∅, @root * is forbidden..
  And because root -> @root (), version solving failed.

  $ ../../../src/main.exe alpine BARE pv-user pv-mid | sed -E '/^(parse|solve) [0-9.]+s$/d'
  index BARE
  cone: 9 packages, 4 provides entries, 1 install_if rules
  unsatisfiable:
  Because @root () -> pv-user 1.0 and pv-user 1.0 -> pv-virt ∅, @root * is forbidden..
  And because root -> @root (), version solving failed.

  $ ../../../src/main.exe alpine BARE al-user | sed -E '/^(parse|solve) [0-9.]+s$/d'
  index BARE
  cone: 9 packages, 4 provides entries, 1 install_if rules
  unsatisfiable:
  Because @root () -> al-user 1.0 and al-user 1.0 -> al-virt ∅, @root * is forbidden..
  And because root -> @root (), version solving failed.

  $ ../../../src/main.exe alpine BARE ii-anchor ii-user | sed -E '/^(parse|solve) [0-9.]+s$/d'
  index BARE
  cone: 9 packages, 4 provides entries, 1 install_if rules
  unsatisfiable:
  Because @root () -> ii-user 1.0 and ii-user 1.0 -> ii-virt ∅, @root * is forbidden..
  And because root -> @root (), version solving failed.

apk never chooses among the providers of a name that is already taken:
selecting a package assigns it every name it provides, so a later
dependency on one of them is already met.  ru-lo and ru-hi both provide
ru-virt, and ru-app needs ru-lo directly and ru-virt through ru-user, so
apk keeps ru-lo for ru-virt and never adds ru-hi despite its higher k:

  $ ../../../src/main.exe alpine REUSE ru-app | sed -E '/^(parse|solve) [0-9.]+s$/d'
  index REUSE
  cone: 10 packages, 6 provides entries, 0 install_if rules
  packages (3):
    ru-app 1.0
    ru-lo 1.0
    ru-user 1.0
  encoded solution: 5 core nodes (4 Alpine packages encoded)

and the same when the owner arrives only several steps below the
dependency on the virtual name:

  $ ../../../src/main.exe alpine REUSE ru-virt ru-deep | sed -E '/^(parse|solve) [0-9.]+s$/d'
  index REUSE
  cone: 10 packages, 6 provides entries, 0 install_if rules
  packages (3):
    ru-deep 1.0
    ru-lo 1.0
    ru-mid 1.0
  encoded solution: 5 core nodes (4 Alpine packages encoded)

  $ ../../../src/main.exe alpine REUSE ru-user ru-deep | sed -E '/^(parse|solve) [0-9.]+s$/d'
  index REUSE
  cone: 10 packages, 6 provides entries, 0 install_if rules
  packages (4):
    ru-deep 1.0
    ru-lo 1.0
    ru-mid 1.0
    ru-user 1.0
  encoded solution: 6 core nodes (5 Alpine packages encoded)

With no owner already there, k: still decides:

  $ ../../../src/main.exe alpine REUSE ru-user | sed -E '/^(parse|solve) [0-9.]+s$/d'
  index REUSE
  cone: 10 packages, 6 provides entries, 0 install_if rules
  packages (2):
    ru-hi 1.0
    ru-user 1.0
  encoded solution: 4 core nodes (3 Alpine packages encoded)

Two providers that offer the same version at a name and tie on k: are
separated by the order apk read them in: select_package replaces its pick
only on a strictly better compare_providers, and the index is where the
provider list gets its order.  So tie-a beats tie-b, and tie2-b, listed
first, beats tie2-a:

  $ ../../../src/main.exe alpine REUSE tie-cmd | sed -E '/^(parse|solve) [0-9.]+s$/d'
  index REUSE
  cone: 10 packages, 6 provides entries, 0 install_if rules
  packages (1):
    tie-a 1.0
  encoded solution: 3 core nodes (4 Alpine packages encoded)

  $ ../../../src/main.exe alpine REUSE tie2-cmd | sed -E '/^(parse|solve) [0-9.]+s$/d'
  index REUSE
  cone: 10 packages, 6 provides entries, 0 install_if rules
  packages (1):
    tie2-b 1.0
  encoded solution: 3 core nodes (4 Alpine packages encoded)

LUA is the part of the snapshot's APKINDEX that lua5.1-lyaml and dmvpn can
reach.  lua-stdlib-debug depends on the bare name lua, which lua5.1 to
lua5.4 all provide with k:, and each goal already needs one of them:
lua5.1-lyaml needs lua5.1, and dmvpn needs lua5.2.  apk installs no other
lua:

  $ ../../../src/main.exe alpine LUA lua5.1-lyaml | sed -E '/^(parse|solve) [0-9.]+s$/d'
  index LUA
  cone: 81 packages, 219 provides entries, 11 install_if rules
  packages (7):
    lua-stdlib-debug 1.0.1-r1
    lua-stdlib-normalize 2.0.3-r1
    lua5.1 5.1.5-r13
    lua5.1-libs 5.1.5-r13
    lua5.1-lyaml 6.2.8-r1
    musl 1.2.5-r11
    yaml 0.2.5-r2
  encoded solution: 24 core nodes (23 Alpine packages encoded)

  $ ../../../src/main.exe alpine LUA dmvpn | grep -E '^  lua5\.[0-9] '
    lua5.2 5.2.4-r13

A negated requirement holds whichever side of it is decided first.  nega
requires !negb and negc requires nega; asking for negc and negb=1.0 has
PubGrub decide negb before it reaches negc, let alone nega.  The requirement
is nega's own edge: every name has an absent version ⊥ besides its real
ones, and !negb is a dependency on negb at the versions the requirement
does not exclude, or absent -- here ⊥ alone.  Nothing hangs on negb's side,
so the order in which the two are decided cannot lose it:

  $ ../../../src/main.exe alpine NEGDEP negc negb=1.0 | sed -E '/^(parse|solve) [0-9.]+s$/d'
  index NEGDEP
  cone: 4 packages, 0 provides entries, 0 install_if rules
  unsatisfiable:
  Because negc 1.0 -> nega 1.0 and nega 1.0 -> negb ⊥, negc (-∞, ⊥) requires negb ⊥.
  And because @root () -> negb 1.0, negc (-∞, ⊥) or @root * is forbidden.
  And because @root () -> negc 1.0 and root -> @root (), version solving failed.

A name only a negated requirement reaches is left absent rather than
installed: ⊥ is the greatest version, and PubGrub decides the greatest:

  $ ../../../src/main.exe alpine NEGDEP negc | sed -E '/^(parse|solve) [0-9.]+s$/d'
  index NEGDEP
  cone: 4 packages, 0 provides entries, 0 install_if rules
  packages (2):
    nega 1.0
    negc 1.0
  encoded solution: 4 core nodes (3 Alpine packages encoded)
