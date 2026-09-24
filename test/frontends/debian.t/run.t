Two providers of a name that differ in nothing apt ranks on -- no Essential or
Important flag, the same architecture, the same Priority -- are separated by
its last key, the package name:

  $ ../../../src/main.exe debian --native amd64 app Packages | sed -E '/^(parse|solve) [0-9.]+s$/d'
  app:amd64 1
  lib:amd64 1
  prov1:amd64 1

The Priority field outranks the name, and sorts the other way round -- this is
apt taking mawk, which is Priority: required, for a bare Depends on awk:

  $ ../../../src/main.exe debian --native amd64 prioapp Packages | sed -E '/^(parse|solve) [0-9.]+s$/d'
  prioapp:amd64 1
  zprio:amd64 1

The Essential flag outranks both, and apt's cache generator sets it on the
package named apt whatever the stanza says, so apt beats aaaess for essvirt
where the name would have gone the other way:

  $ ../../../src/main.exe debian --native amd64 essapp Packages | sed -E '/^(parse|solve) [0-9.]+s$/d'
  apt:amd64 1
  essapp:amd64 1

A relationship field may be folded over several lines (Policy 5.1); the
newline is not part of the atom that follows it:

  $ ../../../src/main.exe debian --native amd64 folded Packages | sed -E '/^(parse|solve) [0-9.]+s$/d'
  folded:amd64 1
  lib:amd64 1
  zzz:amd64 1

Provides makes an alias for a name, not the name itself: a real package is
preferred over anything claiming its name.  altlib alone would not
discriminate -- it sorts before lib, so the referent ordering hides the
question; zzlib sorts after it and does not:

  $ ../../../src/main.exe debian --native amd64 realdep Packages | sed -E '/^(parse|solve) [0-9.]+s$/d'
  lib:amd64 1
  realdep:amd64 1

Recommends are installed by default, as under apt's APT::Install-Recommends,
and the leftmost alternative is preferred as in a Depends clause:

  $ ../../../src/main.exe debian --native amd64 softpair Packages | sed -E '/^(parse|solve) [0-9.]+s$/d'
  softa:amd64 1
  softpair:amd64 1

  $ ../../../src/main.exe debian --native amd64 --no-install-recommends softpair Packages | sed -E '/^(parse|solve) [0-9.]+s$/d'
  softpair:amd64 1

A one-alternative Recommends still gets its soft disjunct: unlike a Depends
clause, which is inlined below two alternatives, the escape is the whole point
of the encoding and there is no cardinality test to skip it:

  $ ../../../src/main.exe debian --native amd64 softone Packages | sed -E '/^(parse|solve) [0-9.]+s$/d'
  softlib:amd64 1
  softone:amd64 1

An unsatisfiable Recommends is not an error.  softconf recommends softnope,
which conflicts with the softkeep it depends on; the solve succeeds by taking
the escape, and softnope is absent:

  $ ../../../src/main.exe debian --native amd64 softconf Packages | sed -E '/^(parse|solve) [0-9.]+s$/d'
  softconf:amd64 1
  softkeep:amd64 1

The escape sorts below every alternative, so it is reached only once they have
all failed: softalt recommends softnope | softb, and softnope is ruled out by
the same conflict, so softb is installed rather than nothing:

  $ ../../../src/main.exe debian --native amd64 softalt Packages | sed -E '/^(parse|solve) [0-9.]+s$/d'
  softalt:amd64 1
  softb:amd64 1
  softkeep:amd64 1

A Conflicts is an edge of the package that declares it, admitting the
target's non-matching versions and its absence ⊥.  cfla conflicts with cflb
(every version), so cfla 1 admits cflb only at ⊥; cflc depends on cfla, and
cfld depends on cflb (= 1) and cflc, whichever order the solver reaches them.
cflb 1 is not the candidate, so both versions are offered, as with apt's
Strict-Pinning off (below):

  $ ../../../src/main.exe debian --native amd64 --no-strict-pinning cfld Packages | sed -E '/^(parse|solve) [0-9.]+s$/d'
  unsatisfiable:
  Because cflc:amd64 1 -> cfla:amd64 1 and cfla:amd64 1 -> cflb:amd64 ⊥, cflc:amd64 (-∞, ⊥) requires cflb:amd64 ⊥.
  And because cfld:amd64 1 -> cflb:amd64 1, cfld:amd64 (-∞, ⊥) or cflc:amd64 (-∞, ⊥) is forbidden.
  And because cfld:amd64 1 -> cflc:amd64 1 and root -> cfld:amd64 1, version solving failed.

Absence is a version of the encoding, not an installation: cflc alone
decides cflb to ⊥, and the answer lists what is present.

  $ ../../../src/main.exe debian --native amd64 cflc Packages | sed -E '/^(parse|solve) [0-9.]+s$/d'
  cfla:amd64 1
  cflc:amd64 1

A clause's alternatives are tried in its own order, whichever clause listing
the same alternatives the solver read first.  ordapp recommends ordx | ordy
and depends on orddep, which depends on ordy | ordx; apt takes ordy for
orddep, and the recommendation is then already met:

  $ ../../../src/main.exe debian --native amd64 ordapp Packages | sed -E '/^(parse|solve) [0-9.]+s$/d'
  ordapp:amd64 1
  orddep:amd64 1
  ordy:amd64 1

  $ ../../../src/main.exe debian --apt-heap --native amd64 ordapp Packages | sed -E '/^(parse|solve) [0-9.]+s$/d'
  ordapp:amd64 1
  orddep:amd64 1
  ordy:amd64 1

A selector the solution is committed to is not yet a package it carries.
selcommon depends on selbase, which selutils provides, so its selector is
entailed before seldep's selutils | selbase is decided; apt reaches seldep's
clause first, takes selutils, and selutils then provides selbase:

  $ ../../../src/main.exe debian --native amd64 selapp Packages | sed -E '/^(parse|solve) [0-9.]+s$/d'
  selapp:amd64 1
  selcommon:amd64 1
  seldep:amd64 1
  selutils:amd64 1

  $ ../../../src/main.exe debian --apt-heap --native amd64 selapp Packages | sed -E '/^(parse|solve) [0-9.]+s$/d'
  selapp:amd64 1
  selcommon:amd64 1
  seldep:amd64 1
  selutils:amd64 1

Nor is a name a conflict has reached: its range still admits ⊥.  botcfl
conflicts with botx (<< 2), which leaves botx at 2 or ⊥, and botdep's
boty | botx takes its leftmost:

  $ ../../../src/main.exe debian --native amd64 botapp Packages | sed -E '/^(parse|solve) [0-9.]+s$/d'
  botapp:amd64 1
  botcfl:amd64 1
  botdep:amd64 1
  boty:amd64 1

  $ ../../../src/main.exe debian --apt-heap --native amd64 botapp Packages | sed -E '/^(parse|solve) [0-9.]+s$/d'
  botapp:amd64 1
  botcfl:amd64 1
  botdep:amd64 1
  boty:amd64 1

Under --apt-heap the shadow of apt's work heap decides which Recommends is
taken first, and the heap's ties fall to push order, which is apt's
propagation order: a package's dependencies are queued when its clause is
found unit, behind everything queued before, not when the package is first
named as an alternative.  hgoal names hgui as an alternative before hopengl
requires it, so hgui's Recommends (htheme -> hsysd, providing hsysusers) is
pushed after hglib's (hdbus: hadduser | hsysusers), and hdbus pops first,
taking hadduser before hsysd arrives, as apt does:

  $ ../../../src/main.exe debian --apt-heap --native amd64 hgoal Packages | sed -E '/^(parse|solve) [0-9.]+s$/d'
  hadduser:amd64 1
  hcore:amd64 1
  hdbus:amd64 1
  hglib:amd64 1
  hgoal:amd64 1
  hgui:amd64 1
  hopengl:amd64 1
  hsysd:amd64 1
  htheme:amd64 1

apt rejects a package the moment a hard clause of its loses its last
solution, and the rejection cascades: kgui conflicts with kgui-gles, so
kquick-gles (which needs it) is rejected, and by the time kcomp is reached
its kquick | kquick-gles is unit, so kquick is enqueued behind kcomp rather
than left as a work item for after the queue.  kquick's Recommends (krq ->
ksysd, providing ksysusers) is then pushed before that of kcore, five
dependencies deep (krc: kadduser | ksysusers), and krc finds ksysusers
carried:

  $ ../../../src/main.exe debian --apt-heap --native amd64 kgoal Packages | sed -E '/^(parse|solve) [0-9.]+s$/d'
  kc1:amd64 1
  kc2:amd64 1
  kc3:amd64 1
  kc4:amd64 1
  kc5:amd64 1
  kcomp:amd64 1
  kcore:amd64 1
  kgoal:amd64 1
  kgui:amd64 1
  kmid:amd64 1
  kmid2:amd64 1
  kmid3:amd64 1
  kquick:amd64 1
  krc:amd64 1
  krq:amd64 1
  ksysd:amd64 1

apt counts a clause's solutions as the entries of its target's provides
list and versions (AllTargets, pkgcache.cc).  Its cache drops a Provides of
the package's own name, except through the every-architecture path a
Multi-Arch: foreign package's Provides take, so mself, foreign, is two
solutions of ma's Recommends mself | mnone, and nself, not foreign, one.
A two-solution item ranks behind mb's one-solution mc, which pops first and
brings in my, and mself's mx | my then finds my carried; the one-solution
items tie, and na's, pushed first, pops first:

  $ ../../../src/main.exe debian --apt-heap --native amd64 mgoal Packages | sed -E '/^(parse|solve) [0-9.]+s$/d'
  ma:amd64 1
  mb:amd64 1
  mc:amd64 1
  mgoal:amd64 1
  mself:amd64 1
  my:amd64 1

  $ ../../../src/main.exe debian --apt-heap --native amd64 ngoal Packages | sed -E '/^(parse|solve) [0-9.]+s$/d'
  na:amd64 1
  nb:amd64 1
  nc:amd64 1
  ngoal:amd64 1
  nself:amd64 1
  nx:amd64 1
  ny:amd64 1

A conflict on an explicit :arch names another architecture's package, one
apt's cache holds as an empty pseudo-package, so ca's Conflicts: cb:x32
does not reject ca when cb is installed, and cq's ca | cz takes its
leftmost:

  $ ../../../src/main.exe debian --apt-heap --native amd64 cgoal Packages | sed -E '/^(parse|solve) [0-9.]+s$/d'
  ca:amd64 1
  cb:amd64 1
  cgoal:amd64 1
  cq:amd64 1

apt folds a second single-target dependency into an earlier one on the
same target when they share a solution, and takes the first undecided of
the intersection (RegisterClause, solver3.cc): dfoo (<< 3) has the real
dfoo and dbar's dfoo (= 2), dfoo (>= 2) has dbar's and dbaz's dfoo (= 3),
so the merged clause is unit at dbar, and the real dfoo, which each half
alone would have let a leftmost-first choice install, is never installed:

  $ ../../../src/main.exe debian --apt-heap --native amd64 dgoal Packages | sed -E '/^(parse|solve) [0-9.]+s$/d'
  dbar:amd64 1
  dgoal:amd64 1

apt assigns a rejection the moment it is derived but propagates it only when
its turn in the queue comes, and a package is two literals: fp's Conflicts
rejects fx's version var during fp's wave, and fx's package var -- what an
unversioned, unprovided alternative reads -- only when that rejection pops,
after fq's wave has counted fx | fw as two live solutions.  A two-solution
Recommends ranks behind fo's one-solution fz, so fz is installed first, and
its conflict with fw leaves fq's Recommends with nothing:

  $ ../../../src/main.exe debian --apt-heap --native amd64 fgoal Packages | sed -E '/^(parse|solve) [0-9.]+s$/d'
  fgoal:amd64 1
  fo:amd64 1
  fp:amd64 1
  fq:amd64 1
  fz:amd64 1

apt takes the first solution of an item that is still undecided (Solve,
solver3.cc), so a rejected one is never tried: gb's gv is queued as a
two-solution item, then ga's conflict rejects gq, whose loss rejects gr and
gv, and the item pops with gw its one solution left.  The answer is the
same either way; what trying the rejected gv first would cost is a
backjump, which the shadow heap's counters count:

  $ PACSHADOW=1 ../../../src/main.exe debian --apt-heap --native amd64 ggoal Packages 2>&1 | sed -E '/^(parse|solve) [0-9.]+s$/d; s/^PACSHADOW.* (backjump=[0-9]+).*/\1/'
  backjump=0
  ga:amd64 1
  gb:amd64 1
  ggoal:amd64 1
  gw:amd64 1

apt's solver never leaves the candidate version (APT::Solver::Strict-Pinning,
on by default), which with no pins is the newest.  pinv 2 needs pinnone,
which nothing provides, and apt refuses pinapp rather than fall back to
pinv 1; with Strict-Pinning off it takes pinv 1:

  $ ../../../src/main.exe debian --native amd64 pinapp Packages | sed -E '/^(parse|solve) [0-9.]+s$/d'
  unsatisfiable:
  Because pinapp:amd64 1 -> pinv:amd64 2 and pinv:amd64 2 -> pinnone:amd64 ∅, pinapp:amd64 (-∞, ⊥) is forbidden..
  And because root -> pinapp:amd64 1, version solving failed.

  $ ../../../src/main.exe debian --native amd64 --no-strict-pinning pinapp Packages | sed -E '/^(parse|solve) [0-9.]+s$/d'
  pinapp:amd64 1
  pinv:amd64 1

  $ ../../../src/main.exe debian --apt-heap --native amd64 pinapp Packages | sed -E '/^(parse|solve) [0-9.]+s$/d'
  unsatisfiable:
  Because pinapp:amd64 1 -> pinv:amd64 2 and pinv:amd64 2 -> pinnone:amd64 ∅, pinapp:amd64 (-∞, ⊥) is forbidden..
  And because root -> pinapp:amd64 1, version solving failed.

  $ ../../../src/main.exe debian --apt-heap --native amd64 --no-strict-pinning pinapp Packages | sed -E '/^(parse|solve) [0-9.]+s$/d'
  pinapp:amd64 1
  pinv:amd64 1

apt refuses too where a dependency's range misses the candidate, however
installable an older version is: pinok 2 installs, and pinrange asks for
pinok (<< 2):

  $ ../../../src/main.exe debian --native amd64 pinrange Packages | sed -E '/^(parse|solve) [0-9.]+s$/d'
  unsatisfiable:
  Because pinrange:amd64 1 -> pinok:amd64 ∅ and root -> pinrange:amd64 1, version solving failed..

  $ ../../../src/main.exe debian --native amd64 --no-strict-pinning pinrange Packages | sed -E '/^(parse|solve) [0-9.]+s$/d'
  pinok:amd64 1
  pinrange:amd64 1

apt holds an arch:all stanza under the native architecture's package, so
pinmix 2 (all), which needs pinnone, is the candidate over pinmix 1 (amd64);
and of two stanzas at one version, apt keeps the first read:

  $ ../../../src/main.exe debian --native amd64 pinmix Packages | sed -E '/^(parse|solve) [0-9.]+s$/d'
  unsatisfiable:
  Because pinmix:amd64 2 -> pinnone:amd64 ∅ and root -> pinmix:amd64 2, version solving failed..

  $ ../../../src/main.exe debian --native amd64 pindup Packages | sed -E '/^(parse|solve) [0-9.]+s$/d'
  pindup:amd64 1

With a second architecture configured, apt satisfies an atom qualified
with an explicit architecture b only with b's own package, or with a
Provides one of b's packages declares: a Multi-Arch: foreign package of
another architecture meets an unqualified atom, but never a qualified one
("if a dependency has an explicit arch-qualifier then the value foreign is
ignored", deb-control(5)).  apt, with i386 configured beside amd64, refuses
xdep, whose xfor:i386 only the foreign xfor:amd64 could meet, while it
meets the unqualified xfor of xunq:i386:

  $ ../../../src/main.exe debian --native amd64 xdep Packages.multiarch | sed -E '/^(parse|solve) [0-9.]+s$/d'
  unsatisfiable:
  Because xdep:amd64 1 -> xfor:<i386> ∅ and root -> xdep:amd64 1, version solving failed..

  $ ../../../src/main.exe debian --native amd64 xunq:i386 Packages.multiarch | sed -E '/^(parse|solve) [0-9.]+s$/d'
  xfor:amd64 1
  xunq:i386 1

:native is an explicit qualifier of the native architecture: xnat:i386
needs xforn:native, and xforn is foreign but only at i386:

  $ ../../../src/main.exe debian --native amd64 xnat:i386 Packages.multiarch | sed -E '/^(parse|solve) [0-9.]+s$/d'
  unsatisfiable:
  Because xnat:i386 1 -> xforn:<amd64> ∅ and root -> xnat:i386 1, version solving failed..

A declared Provides meets an explicit qualifier from its own architecture
alone: the foreign xvprov:amd64 does not meet xvdep's xvirt:i386, while
xvprov2:i386 meets xvok's xvirt2:i386; and where b's own package exists it
is taken, as xfor2:i386 is for xboth:

  $ ../../../src/main.exe debian --native amd64 xvdep Packages.multiarch | sed -E '/^(parse|solve) [0-9.]+s$/d'
  unsatisfiable:
  Because xvdep:amd64 1 -> xvirt:<i386> ∅ and root -> xvdep:amd64 1, version solving failed..

  $ ../../../src/main.exe debian --native amd64 xvok Packages.multiarch | sed -E '/^(parse|solve) [0-9.]+s$/d'
  xvok:amd64 1
  xvprov2:i386 1

  $ ../../../src/main.exe debian --apt-heap --native amd64 xvok Packages.multiarch | sed -E '/^(parse|solve) [0-9.]+s$/d'
  xvok:amd64 1
  xvprov2:i386 1

  $ ../../../src/main.exe debian --native amd64 xboth Packages.multiarch | sed -E '/^(parse|solve) [0-9.]+s$/d'
  xboth:amd64 1
  xfor2:i386 1

A Conflicts or Breaks on pkg:b is apt's negative on the same
pseudo-package, so it reaches what the atom would meet as a dependency:
xcfl's Conflicts: xfc:i386 spares the foreign xfc:amd64 it depends on, and
xcfl2's xvc:i386 the foreign xpc:amd64 providing xvc, while xcfl3's
xvc3:i386 excludes the xpc3:i386 it needs:

  $ ../../../src/main.exe debian --native amd64 xcfl Packages.multiarch | sed -E '/^(parse|solve) [0-9.]+s$/d'
  xcfl:amd64 1
  xfc:amd64 1

  $ ../../../src/main.exe debian --apt-heap --native amd64 xcfl2 Packages.multiarch | sed -E '/^(parse|solve) [0-9.]+s$/d'
  xcfl2:amd64 1
  xpc:amd64 1

  $ ../../../src/main.exe debian --native amd64 xcfl3 Packages.multiarch | sed -E '/^(parse|solve) [0-9.]+s$/d'
  unsatisfiable:
  Because <sel xpc3:<i386> (T)> ref:xpc3:i386=1 -> xpc3:i386 1 and xcfl3:amd64 1 -> xpc3:i386 ⊥, xcfl3:amd64 (-∞, ⊥) or <sel xpc3:<i386> (T)> * is forbidden..
  And because xcfl3:amd64 1 -> <sel xpc3:<i386> (T)> ref:xpc3:i386=1 and root -> xcfl3:amd64 1, version solving failed.

A query is not a relationship: apt-get's command line takes a name with no
version of its own to the one package providing it (tryVirtualPackage,
apt-private/private-cacheset.cc), so apt-get install xfor:i386 installs
xfor:amd64.  The query here names a real package, and there is none:

  $ ../../../src/main.exe debian --native amd64 xfor:i386 Packages.multiarch | sed -E '/^(parse|solve) [0-9.]+s$/d'
  unsatisfiable:
  root -> xfor:i386 ∅
