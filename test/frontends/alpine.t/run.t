  $ ../../../src/main.exe alpine APKINDEX app docs | sed -E '/^(parse|solve) [0-9.]+s$/d'
  index APKINDEX
  cone: 3 packages, 0 provides entries, 1 install_if rules
  packages (3):
    app 1.0
    app-doc 1.0
    docs 1.0
  encoded solution: 6 core nodes (4 Alpine packages encoded)

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
