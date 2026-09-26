  $ ../../../bin/main.exe alpine APKINDEX app docs | sed -E '/^(parse|solve) [0-9.]+s$/d'
  packages (3):
    app 1.0
    app-doc 1.0
    docs 1.0
  encoded solution: 5 core nodes (4 lookups)
  loaded: 3 names, 3 versions, 0 provides entries, 1 install_if rules

apk picks among the providers of a name with compare_providers, whose first
key between providers it has not disqualified is the version the provider
offers *at the requested name* -- a package's own version where it claims
the name itself, the p: operand where it is a versioned provides, and the empty version
where the provides carries no version at all.  provider_priority (k:) is only the
key after that.

An unversioned provides offers the empty version, which loses to every real
one, so k: ranks it only against other unversioned providers.  nano and
vim both provide editor, nano sorts first and so heads the encoded
disjunction, but vim carries the higher k: and is what apk installs:

  $ ../../../bin/main.exe alpine PROVIDERS editor | sed -E '/^(parse|solve) [0-9.]+s$/d'
  packages (1):
    vim 1.0
  encoded solution: 3 core nodes (2 lookups)
  loaded: 14 names, 14 versions, 7 provides entries, 0 install_if rules

--order=random picks the next name and the provider to try uniformly, from
a generator seeded by --seed: the same seed gives the same answer, and
another seed may give another, a resolution all the same:

  $ seed0() { ../../../bin/main.exe alpine --order=random --seed 0 PROVIDERS editor | sed -E '/^(parse|solve) [0-9.]+s$/d'; }; [ "$(seed0)" = "$(seed0)" ] && seed0
  packages (1):
    vim 1.0
  encoded solution: 3 core nodes (2 lookups)
  loaded: 14 names, 14 versions, 7 provides entries, 0 install_if rules
  $ ../../../bin/main.exe alpine --order=random --seed 1 PROVIDERS editor | sed -E '/^(parse|solve) [0-9.]+s$/d'
  packages (1):
    nano 1.0
  encoded solution: 3 core nodes (2 lookups)
  loaded: 14 names, 14 versions, 7 provides entries, 0 install_if rules

The same empty version is why a package of the name itself beats an
unversioned provider of it however high that provider's k:.  tool-extra
provides tool with k:50 and heads the disjunction, but tool 2.0 offers 2.0
against tool-extra's empty version:

  $ ../../../bin/main.exe alpine PROVIDERS tool | sed -E '/^(parse|solve) [0-9.]+s$/d'
  packages (1):
    tool 2.0
  encoded solution: 3 core nodes (2 lookups)
  loaded: 14 names, 14 versions, 7 provides entries, 0 install_if rules

An unversioned provides without k: is not a low-ranked candidate but no
candidate at all: apk-package(5) says such a provides "will not be
selected automatically for installation", and specifying k: is what
enables that selection.  orphan provides nokey and nothing else does, so
the dependency has nothing to satisfy it:

  $ ../../../bin/main.exe alpine PROVIDERS nokey | sed -E '/^(parse|solve) [0-9.]+s$/d'
  unsatisfiable:
  Because @root () -> nokey ∅ and root -> @root (), version solving failed..
  loaded: 14 names, 14 versions, 7 provides entries, 0 install_if rules

A *versioned* provides offers a real version, and a package claiming a name
itself gets no privilege over one: the two are compared first on the
versions they offer.  vers-alt provides vers=9.9 where the real vers is
1.0, and apk installs vers-alt:

  $ ../../../bin/main.exe alpine PROVIDERS vers-user | sed -E '/^(parse|solve) [0-9.]+s$/d'
  packages (2):
    vers-alt 9.9
    vers-user 1.0
  encoded solution: 4 core nodes (5 lookups)
  loaded: 14 names, 14 versions, 7 provides entries, 0 install_if rules

k: is the key below the offered version, and it is read off whichever
package offers it, provider or not.  prio-alt provides prio=1.0, tying the
real prio 1.0 on version, and prio's own k:100 beats prio-alt's k:1:

  $ ../../../bin/main.exe alpine PROVIDERS prio-user | sed -E '/^(parse|solve) [0-9.]+s$/d'
  packages (2):
    prio 1.0
    prio-user 1.0
  encoded solution: 3 core nodes (3 lookups)
  loaded: 14 names, 14 versions, 7 provides entries, 0 install_if rules

and the same tie goes the other way when the provider is the one carrying the
k:.  prio-lo-alt provides prio-lo=1.0 with k:5 against a real prio-lo 1.0
with none, so the provider wins:

  $ ../../../bin/main.exe alpine PROVIDERS prio-lo-user | sed -E '/^(parse|solve) [0-9.]+s$/d'
  packages (2):
    prio-lo-alt 2.0
    prio-lo-user 1.0
  encoded solution: 4 core nodes (5 lookups)
  loaded: 14 names, 14 versions, 7 provides entries, 0 install_if rules

An unversioned provides without k: still satisfies a dependency when the
world names its owner: apk-package(5) says that without a provider-priority
"user is expected to manually select one of the concrete package names in
world".  pv-prov provides pv-virt with no k:, and here the world names it:

  $ ../../../bin/main.exe alpine BARE pv-prov pv-user | sed -E '/^(parse|solve) [0-9.]+s$/d'
  packages (2):
    pv-prov 1.0
    pv-user 1.0
  encoded solution: 4 core nodes (3 lookups)
  loaded: 9 names, 9 versions, 4 provides entries, 1 install_if rules

while without it pv-user has nothing to satisfy pv-virt, as in apk:

  $ ../../../bin/main.exe alpine BARE pv-user | sed -E '/^(parse|solve) [0-9.]+s$/d'
  unsatisfiable:
  Because @root () -> pv-user 1.0 and pv-user 1.0 -> pv-virt ∅, @root * is forbidden..
  And because root -> @root (), version solving failed.
  loaded: 9 names, 9 versions, 4 provides entries, 1 install_if rules

apk installs each of the next four by behaviour beyond its documentation,
out of scope here because it depends on why a package is present:

  $ ../../../bin/main.exe alpine BARE pv-both | sed -E '/^(parse|solve) [0-9.]+s$/d'
  unsatisfiable:
  Because @root () -> pv-both 1.0 and pv-both 1.0 -> pv-virt ∅, @root * is forbidden..
  And because root -> @root (), version solving failed.
  loaded: 9 names, 9 versions, 4 provides entries, 1 install_if rules

  $ ../../../bin/main.exe alpine BARE pv-user pv-mid | sed -E '/^(parse|solve) [0-9.]+s$/d'
  unsatisfiable:
  Because @root () -> pv-user 1.0 and pv-user 1.0 -> pv-virt ∅, @root * is forbidden..
  And because root -> @root (), version solving failed.
  loaded: 9 names, 9 versions, 4 provides entries, 1 install_if rules

  $ ../../../bin/main.exe alpine BARE al-user | sed -E '/^(parse|solve) [0-9.]+s$/d'
  unsatisfiable:
  Because @root () -> al-user 1.0 and al-user 1.0 -> al-virt ∅, @root * is forbidden..
  And because root -> @root (), version solving failed.
  loaded: 9 names, 9 versions, 4 provides entries, 1 install_if rules

  $ ../../../bin/main.exe alpine BARE ii-anchor ii-user | sed -E '/^(parse|solve) [0-9.]+s$/d'
  unsatisfiable:
  Because @root () -> ii-user 1.0 and ii-user 1.0 -> ii-virt ∅, @root * is forbidden..
  And because root -> @root (), version solving failed.
  loaded: 9 names, 9 versions, 4 provides entries, 1 install_if rules

apk never chooses among the providers of a name that is already taken:
selecting a package assigns it every name it provides, so a later
dependency on one of them is already met.  ru-lo and ru-hi both provide
ru-virt, and ru-app needs ru-lo directly and ru-virt through ru-user, so
apk keeps ru-lo for ru-virt and never adds ru-hi despite its higher k:

  $ ../../../bin/main.exe alpine REUSE ru-app | sed -E '/^(parse|solve) [0-9.]+s$/d'
  packages (3):
    ru-app 1.0
    ru-lo 1.0
    ru-user 1.0
  encoded solution: 5 core nodes (4 lookups)
  loaded: 10 names, 10 versions, 6 provides entries, 0 install_if rules

and the same when the owner arrives only several steps below the
dependency on the virtual name:

  $ ../../../bin/main.exe alpine REUSE ru-virt ru-deep | sed -E '/^(parse|solve) [0-9.]+s$/d'
  packages (3):
    ru-deep 1.0
    ru-lo 1.0
    ru-mid 1.0
  encoded solution: 5 core nodes (4 lookups)
  loaded: 10 names, 10 versions, 6 provides entries, 0 install_if rules

  $ ../../../bin/main.exe alpine REUSE ru-user ru-deep | sed -E '/^(parse|solve) [0-9.]+s$/d'
  packages (4):
    ru-deep 1.0
    ru-lo 1.0
    ru-mid 1.0
    ru-user 1.0
  encoded solution: 6 core nodes (5 lookups)
  loaded: 10 names, 10 versions, 6 provides entries, 0 install_if rules

With no owner already there, k: still decides:

  $ ../../../bin/main.exe alpine REUSE ru-user | sed -E '/^(parse|solve) [0-9.]+s$/d'
  packages (2):
    ru-hi 1.0
    ru-user 1.0
  encoded solution: 4 core nodes (3 lookups)
  loaded: 10 names, 10 versions, 6 provides entries, 0 install_if rules

Two providers that offer the same version at a name and tie on k: are
separated by the order apk read them in: select_package replaces its pick
only on a strictly better compare_providers, and the index is where the
provider list gets its order.  So tie-a beats tie-b, and tie2-b, listed
first, beats tie2-a:

  $ ../../../bin/main.exe alpine REUSE tie-cmd | sed -E '/^(parse|solve) [0-9.]+s$/d'
  packages (1):
    tie-a 1.0
  encoded solution: 3 core nodes (4 lookups)
  loaded: 10 names, 10 versions, 6 provides entries, 0 install_if rules

  $ ../../../bin/main.exe alpine REUSE tie2-cmd | sed -E '/^(parse|solve) [0-9.]+s$/d'
  packages (1):
    tie2-b 1.0
  encoded solution: 3 core nodes (4 lookups)
  loaded: 10 names, 10 versions, 6 provides entries, 0 install_if rules

LUA is the part of the snapshot's APKINDEX that lua5.1-lyaml and dmvpn can
reach.  lua-stdlib-debug depends on the bare name lua, which lua5.1 to
lua5.4 all provide with k:, and each goal already needs one of them:
lua5.1-lyaml needs lua5.1, and dmvpn needs lua5.2.  apk installs no other
lua:

  $ ../../../bin/main.exe alpine LUA lua5.1-lyaml | sed -E '/^(parse|solve) [0-9.]+s$/d'
  packages (7):
    lua-stdlib-debug 1.0.1-r1
    lua-stdlib-normalize 2.0.3-r1
    lua5.1 5.1.5-r13
    lua5.1-libs 5.1.5-r13
    lua5.1-lyaml 6.2.8-r1
    musl 1.2.5-r11
    yaml 0.2.5-r2
  encoded solution: 24 core nodes (23 lookups)
  loaded: 81 names, 81 versions, 219 provides entries, 11 install_if rules

  $ ../../../bin/main.exe alpine LUA dmvpn | grep -E '^  lua5\.[0-9] '
    lua5.2 5.2.4-r13

A negated requirement holds whichever side of it is decided first.  nega
requires !negb and negc requires nega; asking for negc and negb=1.0 has
PubGrub decide negb before it reaches negc, let alone nega.  The requirement
is nega's own edge: every name has an absent version ⊥ besides its real
ones, and !negb is a dependency on negb at the versions the requirement
does not exclude, or absent -- here ⊥ alone.  Nothing hangs on negb's side,
so the order in which the two are decided cannot lose it:

  $ ../../../bin/main.exe alpine NEGDEP negc negb=1.0 | sed -E '/^(parse|solve) [0-9.]+s$/d'
  unsatisfiable:
  Because negc 1.0 -> nega 1.0 and nega 1.0 -> negb ⊥, negc (-∞, ⊥) requires negb ⊥.
  And because @root () -> negb 1.0, negc (-∞, ⊥) or @root * is forbidden.
  And because @root () -> negc 1.0 and root -> @root (), version solving failed.
  loaded: 3 names, 4 versions, 0 provides entries, 0 install_if rules

A name only a negated requirement reaches is left absent rather than
installed: ⊥ is the greatest version, and PubGrub decides the greatest:

  $ ../../../bin/main.exe alpine NEGDEP negc | sed -E '/^(parse|solve) [0-9.]+s$/d'
  packages (2):
    nega 1.0
    negc 1.0
  encoded solution: 4 core nodes (3 lookups)
  loaded: 3 names, 4 versions, 0 provides entries, 0 install_if rules

An install-if condition may be negated, i:ni-a !ni-b, and apk then fires
the rule only while no package holds ni-b.  ni-z carries exactly that
rule, ni-lt the constrained !ni-b<2, and ni-self the negation of a name
it provides itself, which apk's own package is exempt from.  With ni-b
absent all three fire; ni-only, whose one condition is negated, does not,
since apk reaches a rule only from an installed package that bears or
provides one of its conditions' names:

  $ ../../../bin/main.exe alpine NEGIIF ni-a | sed -E '/^(parse|solve) [0-9.]+s$/d'
  packages (4):
    ni-a 1.0
    ni-lt 1.0
    ni-self 1.0
    ni-z 1.0
  encoded solution: 8 core nodes (5 lookups)
  loaded: 8 names, 9 versions, 3 provides entries, 4 install_if rules

Requiring ni-b falsifies !ni-b.  apk takes ni-alias, which provides it at
3.0, which !ni-b<2 does not exclude, so ni-lt still fires:

  $ ../../../bin/main.exe alpine NEGIIF ni-a ni-b | sed -E '/^(parse|solve) [0-9.]+s$/d'
  packages (4):
    ni-a 1.0
    ni-alias 1.0
    ni-lt 1.0
    ni-self 1.0
  encoded solution: 10 core nodes (7 lookups)
  loaded: 8 names, 9 versions, 3 provides entries, 4 install_if rules

and ni-b 1.0 falsifies both:

  $ ../../../bin/main.exe alpine NEGIIF ni-a 'ni-b<2' | sed -E '/^(parse|solve) [0-9.]+s$/d'
  packages (3):
    ni-a 1.0
    ni-b 1.0
    ni-self 1.0
  encoded solution: 9 core nodes (4 lookups)
  loaded: 8 names, 9 versions, 3 provides entries, 4 install_if rules

apk gives a bare provides the empty version, which it orders below every
version, so a bare provides meets a constrained atom exactly when the
constraint admits a version below all others: bv-virt<2 but not
bv-virt>=1, in every place an atom is read.  bv-prov provides bv-virt
bare, with k:, and so meets bv-lt's requirement:

  $ ../../../bin/main.exe alpine BAREVER bv-lt | sed -E '/^(parse|solve) [0-9.]+s$/d'
  packages (2):
    bv-lt 1.0
    bv-prov 1.0
  encoded solution: 4 core nodes (3 lookups)
  loaded: 8 names, 8 versions, 1 provides entries, 3 install_if rules

and not bv-ge's:

  $ ../../../bin/main.exe alpine BAREVER bv-ge | sed -E '/^(parse|solve) [0-9.]+s$/d'
  unsatisfiable:
  Because @root () -> bv-ge 1.0 and bv-ge 1.0 -> bv-virt ∅, @root * is forbidden..
  And because root -> @root (), version solving failed.
  loaded: 8 names, 8 versions, 1 provides entries, 3 install_if rules

It falsifies the conflict !bv-virt<2:

  $ ../../../bin/main.exe alpine BAREVER bv-no bv-prov | sed -E '/^(parse|solve) [0-9.]+s$/d'
  unsatisfiable:
  Because bv-no 1.0 -> bv-prov ⊥ and @root () -> bv-no 1.0, @root * requires bv-prov ⊥.
  And because @root () -> bv-prov 1.0 and root -> @root (), version solving failed.
  loaded: 8 names, 8 versions, 1 provides entries, 3 install_if rules

With bv-anc it fires the install-if rule on bv-virt<2, and neither the one
on !bv-virt<2 nor the one on bv-virt>=1:

  $ ../../../bin/main.exe alpine BAREVER bv-anc bv-prov | sed -E '/^(parse|solve) [0-9.]+s$/d'
  packages (3):
    bv-anc 1.0
    bv-iif 1.0
    bv-prov 1.0
  encoded solution: 9 core nodes (4 lookups)
  loaded: 8 names, 8 versions, 1 provides entries, 3 install_if rules

It answers a constrained world entry:

  $ ../../../bin/main.exe alpine BAREVER 'bv-virt<2' | sed -E '/^(parse|solve) [0-9.]+s$/d'
  packages (1):
    bv-prov 1.0
  encoded solution: 3 core nodes (2 lookups)
  loaded: 8 names, 8 versions, 1 provides entries, 3 install_if rules

And in NEGIIF the bare provider ni-virt falsifies ni-lt's !ni-b<2:

  $ ../../../bin/main.exe alpine NEGIIF ni-a ni-virt | sed -E '/^(parse|solve) [0-9.]+s$/d'
  packages (3):
    ni-a 1.0
    ni-self 1.0
    ni-virt 1.0
  encoded solution: 9 core nodes (4 lookups)
  loaded: 8 names, 9 versions, 3 provides entries, 4 install_if rules

A >< atom names a package digest, which pac cannot match, so bh-user's
bh-virt><Q1... has nothing to satisfy it.  apk tests it against the
providing package's C: digest, bare provides included, and installs
bh-prov and bh-user:

  $ ../../../bin/main.exe alpine BAREHASH bh-user | sed -E '/^(parse|solve) [0-9.]+s$/d'
  unsatisfiable:
  Because @root () -> bh-user 1.0 and bh-user 1.0 -> bh-virt ∅, @root * is forbidden..
  And because root -> @root (), version solving failed.
  loaded: 2 names, 2 versions, 1 provides entries, 0 install_if rules

The index is read as apk_pkgtmpl_add_info reads it.  A D: atom apk cannot
parse, here one with a tag, or one whose version is not a version, makes
the package uninstallable:

  $ ../../../bin/main.exe alpine PARSE pr-bad | sed -E '/^(parse|solve) [0-9.]+s$/d'
  unsatisfiable:
  Because @root () -> pr-bad ∅ and root -> @root (), version solving failed..
  loaded: 6 names, 7 versions, 1 provides entries, 0 install_if rules
  parser dropped 4 declarations

  $ ../../../bin/main.exe alpine PARSE pr-badver | sed -E '/^(parse|solve) [0-9.]+s$/d'
  unsatisfiable:
  Because @root () -> pr-badver ∅ and root -> @root (), version solving failed..
  loaded: 6 names, 7 versions, 1 provides entries, 0 install_if rules
  parser dropped 4 declarations

Any run of < > = ~ is an operator, the bit-OR of its characters, so == is =:

  $ ../../../bin/main.exe alpine PARSE pr-eq | sed -E '/^(parse|solve) [0-9.]+s$/d'
  packages (2):
    pr-eq 1.0
    pr-lib 1.0
  encoded solution: 3 core nodes (3 lookups)
  loaded: 6 names, 7 versions, 1 provides entries, 0 install_if rules
  parser dropped 4 declarations

An i: atom apk cannot parse drops the whole rule, so pr-iif never
fires:

  $ ../../../bin/main.exe alpine PARSE pr-trig | sed -E '/^(parse|solve) [0-9.]+s$/d'
  packages (1):
    pr-trig 1.0
  encoded solution: 2 core nodes (2 lookups)
  loaded: 6 names, 7 versions, 1 provides entries, 0 install_if rules
  parser dropped 4 declarations

An index skips the installed-db fields F M R Z:

  $ ../../../bin/main.exe alpine PARSE pr-files | sed -E '/^(parse|solve) [0-9.]+s$/d'
  packages (1):
    pr-files 1.0
  encoded solution: 2 core nodes (2 lookups)
  loaded: 6 names, 7 versions, 1 provides entries, 0 install_if rules
  parser dropped 4 declarations

And a p: atom apk cannot parse ends the provides, so pr-provs provides
pr-pa and not pr-pc:

  $ ../../../bin/main.exe alpine PARSE pr-pa | sed -E '/^(parse|solve) [0-9.]+s$/d'
  packages (1):
    pr-provs 1.0
  encoded solution: 3 core nodes (3 lookups)
  loaded: 6 names, 7 versions, 1 provides entries, 0 install_if rules
  parser dropped 4 declarations

  $ ../../../bin/main.exe alpine PARSE pr-pc | sed -E '/^(parse|solve) [0-9.]+s$/d'
  unsatisfiable:
  Because @root () -> pr-pc ∅ and root -> @root (), version solving failed..
  loaded: 6 names, 7 versions, 1 provides entries, 0 install_if rules
  parser dropped 4 declarations

A world atom apk cannot read makes it refuse the whole world, and pac
refuses it too, exiting 2 rather than solving the other atoms: one tagged
with a repository, as none here is; one whose version is not a version;
and one with no version after its operator:

  $ ../../../bin/main.exe alpine APKINDEX app docs@edge
  error: "docs@edge": no repository has that tag
  [2]
  $ ../../../bin/main.exe alpine APKINDEX app 'docs=1.x!'
  error: "docs=1.x!": not a valid version
  [2]
  $ ../../../bin/main.exe alpine APKINDEX app 'docs='
  error: "docs=": not a dependency atom
  [2]

An empty argument is no atom at all, and apk skips it:

  $ ../../../bin/main.exe alpine APKINDEX app '' | sed -E '/^(parse|solve) [0-9.]+s$/d'
  packages (1):
    app 1.0
  encoded solution: 4 core nodes (2 lookups)
  loaded: 3 names, 3 versions, 0 provides entries, 1 install_if rules

PubGrub's own order keeps the rules apk's acceptance rests on, since apk
keeps an installed set only where its own solver would: a name a selected
package provides stays that package's, so ru-hi's higher k: does not bring
it in beside ru-lo:

  $ ../../../bin/main.exe alpine --order=pubgrub REUSE ru-app | sed -E '/^(parse|solve) [0-9.]+s$/d'
  packages (3):
    ru-app 1.0
    ru-lo 1.0
    ru-user 1.0
  encoded solution: 5 core nodes (4 lookups)
  loaded: 10 names, 10 versions, 6 provides entries, 0 install_if rules
