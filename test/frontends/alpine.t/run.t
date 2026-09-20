  $ ../../../src/main.exe alpine APKINDEX app docs | sed -E '/^(parse|solve) [0-9.]+s$/d'
  index APKINDEX
  cone: 3 packages, 0 provides entries, 1 install_if rules
  packages (3):
    app 1.0
    app-doc 1.0
    docs 1.0
  encoded solution: 6 core nodes (4 Alpine packages encoded)

provider_priority (k:) is apk's preference among the unversioned providers
of a name.  nano and vim both provide editor, nano sorts first and so heads
the encoded disjunction, but vim carries the higher k: and is what apk
installs:

  $ ../../../src/main.exe alpine PROVIDERS editor | sed -E '/^(parse|solve) [0-9.]+s$/d'
  index PROVIDERS
  cone: 5 packages, 4 provides entries, 0 install_if rules
  packages (1):
    vim 1.0
  encoded solution: 3 core nodes (2 Alpine packages encoded)

A package of the name itself outranks every unversioned provider of it,
which is apk's rule and the reason k: only ever arbitrates between
providers.  tool-extra provides tool and heads the disjunction, but the
real tool is there and is what apk installs:

  $ ../../../src/main.exe alpine PROVIDERS tool | sed -E '/^(parse|solve) [0-9.]+s$/d'
  index PROVIDERS
  cone: 5 packages, 4 provides entries, 0 install_if rules
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
  cone: 5 packages, 4 provides entries, 0 install_if rules
  unsatisfiable:
  Because @root () -> nokey ∅ and root -> @root (), version solving failed..
