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

An unversioned provides without k: is selectable once something names its
owner: the world, a package in the solution depending on it or on a name it
provides with a version, or its own install_if.  Any package that could be
such a requirer or trigger, and anything that could lead to one, must itself
be led to from the world, so none is installed only to serve as one.

  $ ../../../src/main.exe alpine BARE pv-prov pv-user | sed -E '/^(parse|solve) [0-9.]+s$/d'
  index BARE
  cone: 9 packages, 4 provides entries, 1 install_if rules
  packages (2):
    pv-prov 1.0
    pv-user 1.0
  encoded solution: 4 core nodes (3 Alpine packages encoded)

  $ ../../../src/main.exe alpine BARE pv-both | sed -E '/^(parse|solve) [0-9.]+s$/d'
  index BARE
  cone: 9 packages, 4 provides entries, 1 install_if rules
  packages (2):
    pv-both 1.0
    pv-prov 1.0
  encoded solution: 4 core nodes (3 Alpine packages encoded)

  $ ../../../src/main.exe alpine BARE pv-user pv-mid | sed -E '/^(parse|solve) [0-9.]+s$/d'
  index BARE
  cone: 9 packages, 4 provides entries, 1 install_if rules
  packages (3):
    pv-mid 1.0
    pv-prov 1.0
    pv-user 1.0
  encoded solution: 5 core nodes (4 Alpine packages encoded)

  $ ../../../src/main.exe alpine BARE al-user | sed -E '/^(parse|solve) [0-9.]+s$/d'
  index BARE
  cone: 9 packages, 4 provides entries, 1 install_if rules
  packages (2):
    al-prov 1.0
    al-user 1.0
  encoded solution: 5 core nodes (4 Alpine packages encoded)

  $ ../../../src/main.exe alpine BARE ii-anchor ii-user | sed -E '/^(parse|solve) [0-9.]+s$/d'
  index BARE
  cone: 9 packages, 4 provides entries, 1 install_if rules
  packages (3):
    ii-anchor 1.0
    ii-prov 1.0
    ii-user 1.0
  encoded solution: 5 core nodes (4 Alpine packages encoded)

pv-both or pv-mid would make pv-prov selectable for pv-user, and
ii-anchor would trigger ii-prov for ii-user, but nothing leads to them, so
both refuse, as apk does:

  $ ../../../src/main.exe alpine BARE pv-user | sed -E '/^(parse|solve) [0-9.]+s$/d'
  index BARE
  cone: 9 packages, 4 provides entries, 1 install_if rules
  unsatisfiable:
  Because <(pv-both{1}&pv-prov{1})|(pv-mid{1}&pv-prov{1})|pv-virt{0}> 2 -> pv-virt ∅ and <(pv-both{1}&pv-prov{1})|(pv-mid{1}&pv-prov{1})|pv-virt{0}> 0 -> pv-both 1.0, <(pv-both{1}&pv-prov{1})|(pv-mid{1}&pv-prov{1})|pv-virt{0}> (-∞, 1) ∪ [0, +∞) requires pv-both 1.0.
  And because <(pv-both{1}&pv-prov{1})|(pv-mid{1}&pv-prov{1})|pv-virt{0}> 1 -> pv-mid 1.0, not pv-both 1.0 or not pv-mid 1.0 or <(pv-both{1}&pv-prov{1})|(pv-mid{1}&pv-prov{1})|pv-virt{0}> * is forbidden.
  Because @root () -> pv-user 1.0 and pv-user 1.0 -> <(pv-both{1}&pv-prov{1})|(pv-mid{1}&pv-prov{1})|pv-virt{0}> 2 ∪ 1 ∪ 0, @root * requires <(pv-both{1}&pv-prov{1})|(pv-mid{1}&pv-prov{1})|pv-virt{0}> 2 ∪ 1 ∪ 0.
  Thus, not pv-both 1.0 or not pv-mid 1.0 or @root * is forbidden.
  And because pv-mid 1.0 -> pv-mid ∅, @root * requires pv-both 1.0
  And because pv-both 1.0 -> pv-both ∅ and root -> @root (), version solving failed.

  $ ../../../src/main.exe alpine BARE ii-user | sed -E '/^(parse|solve) [0-9.]+s$/d'
  index BARE
  cone: 9 packages, 4 provides entries, 1 install_if rules
  unsatisfiable:
  Because <(ii-anchor{1}&ii-prov{1})|ii-virt{0}> 1 -> ii-virt ∅ and <(ii-anchor{1}&ii-prov{1})|ii-virt{0}> 0 -> ii-anchor 1.0, <(ii-anchor{1}&ii-prov{1})|ii-virt{0}> * requires ii-anchor 1.0.
  Because @root () -> ii-user 1.0 and ii-user 1.0 -> <(ii-anchor{1}&ii-prov{1})|ii-virt{0}> 1 ∪ 0, @root * requires <(ii-anchor{1}&ii-prov{1})|ii-virt{0}> 1 ∪ 0.
  Thus, @root * requires ii-anchor 1.0
  And because ii-anchor 1.0 -> ii-anchor ∅ and root -> @root (), version solving failed.
