untimed drops the timings from pac's output and keeps its exit status:

  $ untimed() { "$@" > out 2>&1; s=$?; sed -E '/^(parse|solve) [0-9.]+s$/d' out; return $s; }

Two providers of a name that differ in nothing apt ranks on -- no Essential or
Important flag, the same architecture, the same Priority -- are separated by
its last key, the package name:

  $ untimed ../../../bin/main.exe debian --order=pubgrub --native amd64 Packages app
  packages (3):
    app:amd64 1
    lib:amd64 1
    prov1:amd64 1
  encoded solution: 5 core nodes (8 lookups)
  loaded: 176 names, 176 versions

--order=random picks the next name and the version to try uniformly, from
a generator seeded by --seed: the same seed gives the same answer, and
another seed may give another, a resolution all the same:

  $ seed0() { untimed ../../../bin/main.exe debian --order=random --seed 0 --native amd64 Packages app; }; [ "$(seed0)" = "$(seed0)" ] && seed0
  packages (3):
    altlib:amd64 1
    app:amd64 1
    prov2:amd64 1
  encoded solution: 5 core nodes (9 lookups)
  loaded: 176 names, 176 versions
  $ untimed ../../../bin/main.exe debian --order=random --seed 1 --native amd64 Packages app
  packages (3):
    app:amd64 1
    lib:amd64 1
    prov2:amd64 1
  encoded solution: 5 core nodes (8 lookups)
  loaded: 176 names, 176 versions

The Priority field outranks the name, and sorts the other way round -- this is
apt taking mawk, which is Priority: required, for a bare Depends on awk:

  $ untimed ../../../bin/main.exe debian --order=pubgrub --native amd64 Packages prioapp
  packages (2):
    prioapp:amd64 1
    zprio:amd64 1
  encoded solution: 3 core nodes (5 lookups)
  loaded: 176 names, 176 versions

The Essential flag outranks both, and apt's cache generator sets it on the
package named apt whatever the stanza says, so apt beats aaaess for essvirt
where the name would have gone the other way:

  $ untimed ../../../bin/main.exe debian --order=pubgrub --native amd64 Packages essapp
  packages (2):
    apt:amd64 1
    essapp:amd64 1
  encoded solution: 3 core nodes (5 lookups)
  loaded: 176 names, 176 versions

apt reads the flag's value as StringToBool does, so enable, and 0x1 as
strtol reads it, are yes:

  $ untimed ../../../bin/main.exe debian --order=pubgrub --native amd64 Packages enapp
  packages (2):
    enapp:amd64 1
    zzen:amd64 1
  encoded solution: 3 core nodes (5 lookups)
  loaded: 176 names, 176 versions

  $ untimed ../../../bin/main.exe debian --order=pubgrub --native amd64 Packages hexapp
  packages (2):
    hexapp:amd64 1
    zzhex:amd64 1
  encoded solution: 3 core nodes (5 lookups)
  loaded: 176 names, 176 versions

A relationship field may be folded over several lines (Policy 5.1); the
newline is not part of the atom that follows it:

  $ untimed ../../../bin/main.exe debian --order=pubgrub --native amd64 Packages folded
  packages (3):
    folded:amd64 1
    lib:amd64 1
    zzz:amd64 1
  encoded solution: 4 core nodes (6 lookups)
  loaded: 176 names, 176 versions

Provides makes a package a provider of a name, not a package of it: a real package is
preferred over anything claiming its name.  altlib alone would not
discriminate -- it sorts before lib, so the referent ordering hides the
question; zzlib sorts after it and does not:

  $ untimed ../../../bin/main.exe debian --order=pubgrub --native amd64 Packages realdep
  packages (2):
    lib:amd64 1
    realdep:amd64 1
  encoded solution: 3 core nodes (5 lookups)
  loaded: 176 names, 176 versions

Recommends are installed by default, as under apt's APT::Install-Recommends,
and the leftmost alternative is preferred as in a Depends clause:

  $ untimed ../../../bin/main.exe debian --order=pubgrub --native amd64 Packages softpair
  packages (2):
    softa:amd64 1
    softpair:amd64 1
  encoded solution: 3 core nodes (6 lookups)
  loaded: 176 names, 176 versions

  $ untimed ../../../bin/main.exe debian --order=pubgrub --native amd64 --no-install-recommends Packages softpair
  packages (1):
    softpair:amd64 1
  encoded solution: 1 core nodes (1 lookups)
  loaded: 176 names, 176 versions

A one-alternative Recommends still gets its soft disjunct: unlike a Depends
clause, which is inlined below two alternatives, the escape is the whole point
of the encoding and there is no cardinality test to skip it:

  $ untimed ../../../bin/main.exe debian --order=pubgrub --native amd64 Packages softone
  packages (2):
    softlib:amd64 1
    softone:amd64 1
  encoded solution: 3 core nodes (5 lookups)
  loaded: 176 names, 176 versions

An unsatisfiable Recommends is not an error.  softconf recommends softnope,
which conflicts with the softkeep it depends on; the solve succeeds by taking
the escape, and softnope is absent:

  $ untimed ../../../bin/main.exe debian --order=pubgrub --native amd64 Packages softconf
  packages (2):
    softconf:amd64 1
    softkeep:amd64 1
  encoded solution: 4 core nodes (7 lookups)
  loaded: 176 names, 176 versions

The escape sorts below every alternative, so it is reached only once they have
all failed: softalt recommends softnope | softb, and softnope is ruled out by
the same conflict, so softb is installed rather than nothing:

  $ untimed ../../../bin/main.exe debian --order=pubgrub --native amd64 Packages softalt
  packages (3):
    softalt:amd64 1
    softb:amd64 1
    softkeep:amd64 1
  encoded solution: 5 core nodes (9 lookups)
  loaded: 176 names, 176 versions

A Conflicts is an edge of the package that declares it, admitting the
target's non-matching versions and its absence ⊥.  cfla conflicts with cflb
(every version), so cfla 1 admits cflb only at ⊥; cflc depends on cfla, and
cfld depends on cflb (= 1) and cflc, whichever order the solver reaches them.
cflb 1 is not the candidate, so both versions are offered, as with apt's
Strict-Pinning off (below):

  $ untimed ../../../bin/main.exe debian --order=pubgrub --native amd64 --no-strict-pinning Packages cfld
  unsatisfiable:
  Because cflc:amd64 1 -> cfla:amd64 1 and cfla:amd64 1 -> cflb:amd64 ⊥, cflc:amd64 (-∞, ⊥) requires cflb:amd64 ⊥.
  And because cfld:amd64 1 -> cflb:amd64 1, cfld:amd64 (-∞, ⊥) or cflc:amd64 (-∞, ⊥) is forbidden.
  And because cfld:amd64 1 -> cflc:amd64 1 and root -> cfld:amd64 1, version solving failed.
  loaded: 176 names, 182 versions
  [1]

Absence is a version of the encoding, not an installation: cflc alone
decides cflb to ⊥, and the answer lists what is present.

  $ untimed ../../../bin/main.exe debian --order=pubgrub --native amd64 Packages cflc
  packages (2):
    cfla:amd64 1
    cflc:amd64 1
  encoded solution: 3 core nodes (5 lookups)
  loaded: 176 names, 176 versions

A clause's alternatives are tried in its own order, whichever clause listing
the same alternatives the solver read first.  ordapp recommends ordx | ordy
and depends on orddep, which depends on ordy | ordx; apt takes ordy for
orddep, and the recommendation is then already met:

  $ untimed ../../../bin/main.exe debian --order=pubgrub --native amd64 Packages ordapp
  packages (3):
    ordapp:amd64 1
    orddep:amd64 1
    ordy:amd64 1
  encoded solution: 5 core nodes (10 lookups)
  loaded: 176 names, 176 versions

  $ untimed ../../../bin/main.exe debian --order=tool --native amd64 Packages ordapp
  packages (3):
    ordapp:amd64 1
    orddep:amd64 1
    ordy:amd64 1
  encoded solution: 5 core nodes (10 lookups)
  loaded: 176 names, 176 versions

A selector the solution is committed to is not yet a package it installs.
selcommon depends on selbase, which selutils provides, so its selector is
entailed before seldep's selutils | selbase is decided; apt reaches seldep's
clause first, takes selutils, and selutils then provides selbase:

  $ untimed ../../../bin/main.exe debian --order=pubgrub --native amd64 Packages selapp
  packages (4):
    selapp:amd64 1
    selcommon:amd64 1
    seldep:amd64 1
    selutils:amd64 1
  encoded solution: 6 core nodes (11 lookups)
  loaded: 176 names, 176 versions

  $ untimed ../../../bin/main.exe debian --order=tool --native amd64 Packages selapp
  packages (4):
    selapp:amd64 1
    selcommon:amd64 1
    seldep:amd64 1
    selutils:amd64 1
  encoded solution: 6 core nodes (11 lookups)
  loaded: 176 names, 176 versions

Nor is a name a conflict has reached: its range still admits ⊥.  botcfl
conflicts with botx (<< 2), which leaves botx at 2 or ⊥, and botdep's
boty | botx takes its leftmost:

  $ untimed ../../../bin/main.exe debian --order=pubgrub --native amd64 Packages botapp
  packages (4):
    botapp:amd64 1
    botcfl:amd64 1
    botdep:amd64 1
    boty:amd64 1
  encoded solution: 5 core nodes (8 lookups)
  loaded: 176 names, 176 versions

  $ untimed ../../../bin/main.exe debian --order=tool --native amd64 Packages botapp
  packages (4):
    botapp:amd64 1
    botcfl:amd64 1
    botdep:amd64 1
    boty:amd64 1
  encoded solution: 5 core nodes (8 lookups)
  loaded: 176 names, 176 versions

In the tool order, the shadow of apt's work heap decides which Recommends is
taken first, and the heap's ties fall to push order, which is apt's
propagation order: a package's dependencies are queued when its clause is
found unit, behind everything queued before, not when the package is first
named as an alternative.  hgoal names hgui as an alternative before hopengl
requires it, so hgui's Recommends (htheme -> hsysd, providing hsysusers) is
pushed after hglib's (hdbus: hadduser | hsysusers), and hdbus pops first,
taking hadduser before hsysd arrives, as apt does:

  $ untimed ../../../bin/main.exe debian --order=tool --native amd64 Packages hgoal
  packages (9):
    hadduser:amd64 1
    hcore:amd64 1
    hdbus:amd64 1
    hglib:amd64 1
    hgoal:amd64 1
    hgui:amd64 1
    hopengl:amd64 1
    hsysd:amd64 1
    htheme:amd64 1
  encoded solution: 13 core nodes (24 lookups)
  loaded: 176 names, 176 versions

apt rejects a package the moment a hard clause of its loses its last
solution, and the rejection cascades: kgui conflicts with kgui-gles, so
kquick-gles (which needs it) is rejected, and by the time kcomp is reached
its kquick | kquick-gles is unit, so kquick is enqueued behind kcomp rather
than left as a work item for after the queue.  kquick's Recommends (krq ->
ksysd, providing ksysusers) is then pushed before that of kcore, five
dependencies deep (krc: kadduser | ksysusers), and krc finds ksysusers
installed:

  $ untimed ../../../bin/main.exe debian --order=tool --native amd64 Packages kgoal
  packages (16):
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
  encoded solution: 22 core nodes (41 lookups)
  loaded: 176 names, 176 versions

The watch lists are read from the field text, folded or not: jgoal is kgoal
with jquick-gles's Depends folded, its first name on a continuation line,
and the rejection still reaches jquick-gles:

  $ untimed ../../../bin/main.exe debian --order=tool --native amd64 Packages jgoal
  packages (16):
    jc1:amd64 1
    jc2:amd64 1
    jc3:amd64 1
    jc4:amd64 1
    jc5:amd64 1
    jcomp:amd64 1
    jcore:amd64 1
    jgoal:amd64 1
    jgui:amd64 1
    jmid:amd64 1
    jmid2:amd64 1
    jmid3:amd64 1
    jquick:amd64 1
    jrc:amd64 1
    jrq:amd64 1
    jsysd:amd64 1
  encoded solution: 22 core nodes (41 lookups)
  loaded: 176 names, 176 versions

apt counts a clause's solutions as the entries of its target's provides
list and versions (AllTargets, pkgcache.cc).  Its cache drops a Provides of
the package's own name, except through the every-architecture path a
Multi-Arch: foreign package's Provides take, so mself, foreign, is two
solutions of ma's Recommends mself | mnone, and nself, not foreign, one.
A two-solution item ranks behind mb's one-solution mc, which pops first and
brings in my, and mself's mx | my then finds my installed; the one-solution
items tie, and na's, pushed first, pops first:

  $ untimed ../../../bin/main.exe debian --order=tool --native amd64 Packages mgoal
  packages (6):
    ma:amd64 1
    mb:amd64 1
    mc:amd64 1
    mgoal:amd64 1
    mself:amd64 1
    my:amd64 1
  encoded solution: 10 core nodes (20 lookups)
  loaded: 176 names, 176 versions

  $ untimed ../../../bin/main.exe debian --order=tool --native amd64 Packages ngoal
  packages (7):
    na:amd64 1
    nb:amd64 1
    nc:amd64 1
    ngoal:amd64 1
    nself:amd64 1
    nx:amd64 1
    ny:amd64 1
  encoded solution: 11 core nodes (21 lookups)
  loaded: 176 names, 176 versions

A conflict on an explicit :arch names another architecture's package, one
apt's cache holds as an empty pseudo-package, so ca's Conflicts: cb:x32
does not reject ca when cb is installed, and cq's ca | cz takes its
leftmost:

  $ untimed ../../../bin/main.exe debian --order=tool --native amd64 Packages cgoal
  packages (4):
    ca:amd64 1
    cb:amd64 1
    cgoal:amd64 1
    cq:amd64 1
  encoded solution: 5 core nodes (9 lookups)
  loaded: 176 names, 176 versions

apt folds a second single-target dependency into an earlier one on the
same target when they share a solution, and takes the first undecided of
the intersection (RegisterClause, solver3.cc): dfoo (<< 3) has the real
dfoo and dbar's dfoo (= 2), dfoo (>= 2) has dbar's and dbaz's dfoo (= 3),
so the merged clause is unit at dbar, and the real dfoo, which each half
alone would have let a leftmost-first choice install, is never installed:

  $ untimed ../../../bin/main.exe debian --order=tool --native amd64 Packages dgoal
  packages (2):
    dbar:amd64 1
    dgoal:amd64 1
  encoded solution: 4 core nodes (7 lookups)
  loaded: 176 names, 176 versions

The fold narrows the depender's own clause, and only while the depender is
installed: rpa folds rfoo (<< 3) and rfoo (>= 2) down to rbar, then fails,
and rqa's rfoo (<< 3), unfolded, takes the real rfoo:

  $ untimed ../../../bin/main.exe debian --order=tool --native amd64 Packages rgoal
  packages (3):
    rfoo:amd64 1
    rgoal:amd64 1
    rqa:amd64 1
  encoded solution: 5 core nodes (18 lookups)
  loaded: 176 names, 176 versions

apt assigns a rejection the moment it is derived but propagates it only when
its turn in the queue comes, and a package is two literals: fp's Conflicts
rejects fx's version var during fp's wave, and fx's package var -- what an
unversioned, unprovided alternative reads -- only when that rejection pops,
after fq's wave has counted fx | fw as two live solutions.  A two-solution
Recommends ranks behind fo's one-solution fz, so fz is installed first, and
its conflict with fw leaves fq's Recommends with nothing:

  $ untimed ../../../bin/main.exe debian --order=tool --native amd64 Packages fgoal
  packages (5):
    fgoal:amd64 1
    fo:amd64 1
    fp:amd64 1
    fq:amd64 1
    fz:amd64 1
  encoded solution: 9 core nodes (17 lookups)
  loaded: 176 names, 176 versions

apt takes the first solution of an item that is still undecided (Solve,
solver3.cc), so a rejected one is never tried: gb's gv is queued as a
two-solution item, then ga's conflict rejects gq, whose loss rejects gr and
gv, and the item pops with gw its one solution left.  The answer is the
same either way; what trying the rejected gv first would cost is a
backjump, which the shadow heap's counters count:

  $ PACSHADOW=1 ../../../bin/main.exe debian --order=tool --native amd64 Packages ggoal 2>&1 | sed -E '/^(parse|solve) [0-9.]+s$/d; s/^PACSHADOW.* (backjump=[0-9]+).*/\1/'
  backjump=0
  packages (4):
    ga:amd64 1
    gb:amd64 1
    ggoal:amd64 1
    gw:amd64 1
  encoded solution: 6 core nodes (10 lookups)
  loaded: 176 names, 176 versions

apt's Pop rejects the choice it undoes, and the rejection stands as long as
the level below does, through any later Pop above it (Solver::Pop,
solver3.cc).  vgoal tries wa, which fails, then vb's vp, which fails too; by
the time vq's Recommends are counted, wa | wxc has one solution left, so it
pops ahead of wyd | wxc and wxc meets both:

  $ untimed ../../../bin/main.exe debian --order=tool --native amd64 Packages wgoal
  packages (3):
    wb:amd64 1
    wgoal:amd64 1
    wxc:amd64 1
  encoded solution: 6 core nodes (21 lookups)
  loaded: 176 names, 176 versions

  $ untimed ../../../bin/main.exe debian --order=tool --native amd64 Packages vgoal
  packages (4):
    vb:amd64 1
    vgoal:amd64 1
    vq:amd64 1
    wxc:amd64 1
  encoded solution: 8 core nodes (33 lookups)
  loaded: 176 names, 176 versions

A clause with an obsolete solution is worked on after every other clause of
its eagerness that is not unit (Work::operator<, the SatisfyObsolete group): obsp's source obssrc also
builds obsnew at the newer source version 2, so obsgoal's obsp | obsq waits
behind its obsq | obsr, which takes obsq, and obsp | obsq then finds obsq
installed.  obsgoal2 is the same with obsx, which nothing makes obsolete, and
its first clause goes first:

  $ untimed ../../../bin/main.exe debian --order=tool --native amd64 Packages obsgoal
  packages (2):
    obsgoal:amd64 1
    obsq:amd64 1
  encoded solution: 4 core nodes (7 lookups)
  loaded: 176 names, 176 versions

  $ untimed ../../../bin/main.exe debian --order=tool --native amd64 Packages obsgoal2
  packages (3):
    obsgoal2:amd64 1
    obsq:amd64 1
    obsx:amd64 1
  encoded solution: 5 core nodes (8 lookups)
  loaded: 176 names, 176 versions

The tool order is the default.  PubGrub's own order decides obsgoal's
obsp | obsq first, and installs obsp too:

  $ untimed ../../../bin/main.exe debian --native amd64 Packages obsgoal
  packages (2):
    obsgoal:amd64 1
    obsq:amd64 1
  encoded solution: 4 core nodes (7 lookups)
  loaded: 176 names, 176 versions

  $ untimed ../../../bin/main.exe debian --order=pubgrub --native amd64 Packages obsgoal
  packages (3):
    obsgoal:amd64 1
    obsp:amd64 1
    obsq:amd64 1
  encoded solution: 5 core nodes (8 lookups)
  loaded: 176 names, 176 versions

apt's solver never leaves the candidate version (APT::Solver::Strict-Pinning,
on by default), which with no pins is the newest.  pinv 2 needs pinnone,
which nothing provides, and apt refuses pinapp rather than fall back to
pinv 1; with Strict-Pinning off it takes pinv 1:

  $ untimed ../../../bin/main.exe debian --order=pubgrub --native amd64 Packages pinapp
  unsatisfiable:
  Because pinapp:amd64 1 -> pinv:amd64 2 and pinv:amd64 2 -> pinnone:amd64 ∅, pinapp:amd64 (-∞, ⊥) is forbidden..
  And because root -> pinapp:amd64 1, version solving failed.
  loaded: 176 names, 176 versions
  [1]

  $ untimed ../../../bin/main.exe debian --order=pubgrub --native amd64 --no-strict-pinning Packages pinapp
  packages (2):
    pinapp:amd64 1
    pinv:amd64 1
  encoded solution: 2 core nodes (5 lookups)
  loaded: 176 names, 182 versions

  $ untimed ../../../bin/main.exe debian --order=tool --native amd64 Packages pinapp
  unsatisfiable:
  Because pinapp:amd64 1 -> pinv:amd64 2 and pinv:amd64 2 -> pinnone:amd64 ∅, pinapp:amd64 (-∞, ⊥) is forbidden..
  And because root -> pinapp:amd64 1, version solving failed.
  loaded: 176 names, 176 versions
  [1]

  $ untimed ../../../bin/main.exe debian --order=tool --native amd64 --no-strict-pinning Packages pinapp
  packages (2):
    pinapp:amd64 1
    pinv:amd64 1
  encoded solution: 2 core nodes (5 lookups)
  loaded: 176 names, 182 versions

apt refuses too where a dependency's range misses the candidate, however
installable an older version is: pinok 2 installs, and pinrange asks for
pinok (<< 2):

  $ untimed ../../../bin/main.exe debian --order=pubgrub --native amd64 Packages pinrange
  unsatisfiable:
  Because pinrange:amd64 1 -> pinok:amd64 ∅ and root -> pinrange:amd64 1, version solving failed..
  loaded: 176 names, 176 versions
  [1]

  $ untimed ../../../bin/main.exe debian --order=pubgrub --native amd64 --no-strict-pinning Packages pinrange
  packages (2):
    pinok:amd64 1
    pinrange:amd64 1
  encoded solution: 2 core nodes (3 lookups)
  loaded: 176 names, 182 versions

A query is a list of packages, as apt-get install takes it, and an element
may name a version, NAME=VERSION.  That version becomes the package's
candidate, so Strict-Pinning keeps it rather than the newest: pinv=1 makes
pinapp installable, and so does pinok=1 pinrange:

  $ untimed ../../../bin/main.exe debian --order=pubgrub --native amd64 Packages pinapp pinv=1
  packages (2):
    pinapp:amd64 1
    pinv:amd64 1
  encoded solution: 2 core nodes (3 lookups)
  loaded: 176 names, 176 versions

  $ untimed ../../../bin/main.exe debian --order=tool --native amd64 Packages pinapp pinv=1
  packages (2):
    pinapp:amd64 1
    pinv:amd64 1
  encoded solution: 2 core nodes (3 lookups)
  loaded: 176 names, 176 versions

  $ untimed ../../../bin/main.exe debian --order=pubgrub --native amd64 Packages pinrange pinok=1
  packages (2):
    pinok:amd64 1
    pinrange:amd64 1
  encoded solution: 2 core nodes (3 lookups)
  loaded: 176 names, 176 versions

  $ untimed ../../../bin/main.exe debian --order=pubgrub --native amd64 Packages app prioapp
  packages (5):
    app:amd64 1
    lib:amd64 1
    prioapp:amd64 1
    prov1:amd64 1
    zprio:amd64 1
  encoded solution: 8 core nodes (13 lookups)
  loaded: 176 names, 176 versions

Of two elements naming one package the later wins, as apt sets the
candidate once per element, in order:

  $ untimed ../../../bin/main.exe debian --order=pubgrub --native amd64 Packages pinapp pinv=2 pinv=1
  packages (2):
    pinapp:amd64 1
    pinv:amd64 1
  encoded solution: 2 core nodes (3 lookups)
  loaded: 176 names, 176 versions

  $ untimed ../../../bin/main.exe debian --order=pubgrub --native amd64 Packages pinapp pinv=1 pinv=2
  unsatisfiable:
  Because pinv:amd64 2 -> pinnone:amd64 ∅ and root -> pinv:amd64 2, version solving failed..
  loaded: 176 names, 176 versions
  [1]

The version is matched as apt's pkgVersionMatch does, the first of the
package's versions, newest first, that is the string, or matches it as a
glob; candidate and newest name the newest.  An arch:all stanza is the
native package's version, so pinmix=1 reaches the amd64 stanza:

  $ untimed ../../../bin/main.exe debian --order=pubgrub --native amd64 Packages 'pinok=1*'
  packages (1):
    pinok:amd64 1
  encoded solution: 1 core nodes (1 lookups)
  loaded: 176 names, 176 versions

  $ untimed ../../../bin/main.exe debian --order=pubgrub --native amd64 Packages 'pinv=*'
  unsatisfiable:
  Because pinv:amd64 2 -> pinnone:amd64 ∅ and root -> pinv:amd64 2, version solving failed..
  loaded: 176 names, 176 versions
  [1]

  $ untimed ../../../bin/main.exe debian --order=pubgrub --native amd64 Packages pinv=candidate
  unsatisfiable:
  Because pinv:amd64 2 -> pinnone:amd64 ∅ and root -> pinv:amd64 2, version solving failed..
  loaded: 176 names, 176 versions
  [1]

  $ untimed ../../../bin/main.exe debian --order=pubgrub --native amd64 Packages pinmix:amd64=1
  packages (1):
    pinmix:amd64 1
  encoded solution: 1 core nodes (1 lookups)
  loaded: 176 names, 176 versions

The glob is the pattern less its trailing '*', so 1.*2* reaches 1.2 and
not the newer 1.23; failing every version, a version whose package provides
itself at a matching version is taken; and candidate and newest read the
same after '/':

  $ untimed ../../../bin/main.exe debian --order=pubgrub --native amd64 Packages 'pinglob=1.*2*'
  packages (1):
    pinglob:amd64 1.2
  encoded solution: 1 core nodes (1 lookups)
  loaded: 176 names, 176 versions

  $ untimed ../../../bin/main.exe debian --order=pubgrub --native amd64 Packages 'pinglob=1.2*'
  packages (1):
    pinglob:amd64 1.23
  encoded solution: 1 core nodes (1 lookups)
  loaded: 176 names, 176 versions

  $ untimed ../../../bin/main.exe debian --order=pubgrub --native amd64 Packages pinself=5
  packages (1):
    pinself:amd64 1
  encoded solution: 1 core nodes (1 lookups)
  loaded: 176 names, 176 versions

  $ untimed ../../../bin/main.exe debian --order=pubgrub --native amd64 Packages pinok/newest
  packages (1):
    pinok:amd64 2
  encoded solution: 1 core nodes (1 lookups)
  loaded: 176 names, 176 versions

  $ untimed ../../../bin/main.exe debian --order=pubgrub --native amd64 Packages pinv/candidate
  unsatisfiable:
  Because pinv:amd64 2 -> pinnone:amd64 ∅ and root -> pinv:amd64 2, version solving failed..
  loaded: 176 names, 176 versions
  [1]

A version no stanza matches refuses the query, as does installed, there
being no installed version, and a release: NAME/RELEASE is matched against
Release files, which pac does not read, except for the release *, which
matches every version.  apt refuses these before it solves, with the
cacheset's own message (CacheSetHelper::canNotGetVersion), so they are
refusals and not unsatisfiable queries:

  $ ../../../bin/main.exe debian --order=pubgrub --native amd64 Packages pinv=3
  error: Version '3' for 'pinv' was not found
  [2]

  $ ../../../bin/main.exe debian --order=pubgrub --native amd64 Packages pinv=installed
  error: Can't select installed version from package pinv as it is not installed
  [2]

  $ ../../../bin/main.exe debian --order=pubgrub --native amd64 Packages pinv/stable
  error: Release 'stable' for 'pinv' was not found
  [2]

  $ ../../../bin/main.exe debian --order=pubgrub --native amd64 Packages.multiarch xunq=2
  error: Version '2' for 'xunq:i386' was not found
  [2]

  $ untimed ../../../bin/main.exe debian --order=pubgrub --native amd64 Packages 'pinok/*'
  packages (1):
    pinok:amd64 2
  encoded solution: 1 core nodes (1 lookups)
  loaded: 176 names, 176 versions

apt holds an arch:all stanza under the native architecture's package, so
pinmix 2 (all), which needs pinnone, is the candidate over pinmix 1 (amd64);
and of two stanzas at one version, apt keeps the first read:

  $ untimed ../../../bin/main.exe debian --order=pubgrub --native amd64 Packages pinmix
  unsatisfiable:
  Because pinmix:amd64 2 -> pinnone:amd64 ∅ and root -> pinmix:amd64 2, version solving failed..
  loaded: 176 names, 176 versions
  [1]

  $ untimed ../../../bin/main.exe debian --order=pubgrub --native amd64 Packages pindup
  packages (1):
    pindup:amd64 1
  encoded solution: 1 core nodes (1 lookups)
  loaded: 176 names, 176 versions

The first stanza is kept with Strict-Pinning off too, Provides and all: the
dupp that provides dupvirt is the second read, so apt refuses dupgoal, and
the dupr that does is the first, so dupgoal3 installs it.  An arch:all
stanza is a version of its own to apt (Version::All), so the arch:all dupq
still provides dupvirt2 beside its amd64 twin:

  $ untimed ../../../bin/main.exe debian --order=pubgrub --native amd64 --no-strict-pinning Packages dupgoal
  unsatisfiable:
  Because dupgoal:amd64 1 -> dupvirt:amd64 ∅ and root -> dupgoal:amd64 1, version solving failed..
  loaded: 176 names, 182 versions
  [1]

  $ untimed ../../../bin/main.exe debian --order=pubgrub --native amd64 --no-strict-pinning Packages dupgoal3
  packages (2):
    dupgoal3:amd64 1
    dupr:amd64 1
  encoded solution: 3 core nodes (4 lookups)
  loaded: 176 names, 182 versions

  $ untimed ../../../bin/main.exe debian --order=pubgrub --native amd64 --no-strict-pinning Packages dupgoal2
  packages (2):
    dupgoal2:amd64 1
    dupq:amd64 1
  encoded solution: 3 core nodes (4 lookups)
  loaded: 176 names, 182 versions

With a second architecture configured, apt satisfies an atom qualified
with an explicit architecture b only with b's own package, or with a
Provides one of b's packages declares: a Multi-Arch: foreign package of
another architecture meets an unqualified atom, but never a qualified one
("if a dependency has an explicit arch-qualifier then the value foreign is
ignored", deb-control(5)).  apt, with i386 configured beside amd64, refuses
xdep, whose xfor:i386 only the foreign xfor:amd64 could meet, while it
meets the unqualified xfor of xunq:i386:

  $ untimed ../../../bin/main.exe debian --order=pubgrub --native amd64 Packages.multiarch xdep
  unsatisfiable:
  Because xdep:amd64 1 -> xfor:<i386> ∅ and root -> xdep:amd64 1, version solving failed..
  loaded: 17 names, 18 versions
  [1]

  $ untimed ../../../bin/main.exe debian --order=pubgrub --native amd64 Packages.multiarch xunq:i386
  packages (2):
    xfor:amd64 1
    xunq:i386 1
  encoded solution: 3 core nodes (4 lookups)
  loaded: 17 names, 18 versions

An unqualified name in a query is the native package if there is one with
a version, and otherwise another architecture's (FindPreferredPkg,
pkgcache.cc): xunq exists only at i386:

  $ untimed ../../../bin/main.exe debian --order=pubgrub --native amd64 Packages.multiarch xunq
  packages (2):
    xfor:amd64 1
    xunq:i386 1
  encoded solution: 3 core nodes (4 lookups)
  loaded: 17 names, 18 versions

:native is an explicit qualifier of the native architecture: xnat:i386
needs xforn:native, and xforn is foreign but only at i386:

  $ untimed ../../../bin/main.exe debian --order=pubgrub --native amd64 Packages.multiarch xnat:i386
  unsatisfiable:
  Because xnat:i386 1 -> xforn:<amd64> ∅ and root -> xnat:i386 1, version solving failed..
  loaded: 17 names, 18 versions
  [1]

A declared Provides meets an explicit qualifier from its own architecture
alone: the foreign xvprov:amd64 does not meet xvdep's xvirt:i386, while
xvprov2:i386 meets xvok's xvirt2:i386; and where b's own package exists it
is taken, as xfor2:i386 is for xboth:

  $ untimed ../../../bin/main.exe debian --order=pubgrub --native amd64 Packages.multiarch xvdep
  unsatisfiable:
  Because xvdep:amd64 1 -> xvirt:<i386> ∅ and root -> xvdep:amd64 1, version solving failed..
  loaded: 17 names, 18 versions
  [1]

  $ untimed ../../../bin/main.exe debian --order=pubgrub --native amd64 Packages.multiarch xvok
  packages (2):
    xvok:amd64 1
    xvprov2:i386 1
  encoded solution: 3 core nodes (4 lookups)
  loaded: 17 names, 18 versions

  $ untimed ../../../bin/main.exe debian --order=tool --native amd64 Packages.multiarch xvok
  packages (2):
    xvok:amd64 1
    xvprov2:i386 1
  encoded solution: 3 core nodes (4 lookups)
  loaded: 17 names, 18 versions

  $ untimed ../../../bin/main.exe debian --order=pubgrub --native amd64 Packages.multiarch xboth
  packages (2):
    xboth:amd64 1
    xfor2:i386 1
  encoded solution: 4 core nodes (6 lookups)
  loaded: 17 names, 18 versions

A Conflicts or Breaks on pkg:b is apt's negative on the same
pseudo-package, so it reaches what the atom would meet as a dependency:
xcfl's Conflicts: xfc:i386 spares the foreign xfc:amd64 it depends on, and
xcfl2's xvc:i386 the foreign xpc:amd64 providing xvc, while xcfl3's
xvc3:i386 excludes the xpc3:i386 it needs:

  $ untimed ../../../bin/main.exe debian --order=pubgrub --native amd64 Packages.multiarch xcfl
  packages (2):
    xcfl:amd64 1
    xfc:amd64 1
  encoded solution: 3 core nodes (5 lookups)
  loaded: 17 names, 18 versions

  $ untimed ../../../bin/main.exe debian --order=tool --native amd64 Packages.multiarch xcfl2
  packages (2):
    xcfl2:amd64 1
    xpc:amd64 1
  encoded solution: 3 core nodes (5 lookups)
  loaded: 17 names, 18 versions

  $ untimed ../../../bin/main.exe debian --order=pubgrub --native amd64 Packages.multiarch xcfl3
  unsatisfiable:
  Because <sel xpc3:<i386> (T)> ref:xpc3:i386=1 -> xpc3:i386 1 and xcfl3:amd64 1 -> xpc3:i386 ⊥, xcfl3:amd64 (-∞, ⊥) or <sel xpc3:<i386> (T)> * is forbidden..
  And because xcfl3:amd64 1 -> <sel xpc3:<i386> (T)> ref:xpc3:i386=1 and root -> xcfl3:amd64 1, version solving failed.
  loaded: 17 names, 18 versions
  [1]

A query is not a relationship: apt-get's command line takes a name with no
version of its own to the one package providing it (tryVirtualPackage,
apt-private/private-cacheset.cc), and a Multi-Arch: foreign package
provides itself to every architecture, so apt-get install xfor:i386
installs xfor:amd64:

  $ untimed ../../../bin/main.exe debian --order=pubgrub --native amd64 Packages.multiarch xfor:i386
  packages (1):
    xfor:amd64 1
  encoded solution: 1 core nodes (1 lookups)
  loaded: 17 names, 18 versions

Provides admits only "=" (Policy 7.5).  apt ignores any other Provides with a
warning and keeps the rest of the stanza; so does pac, counting what it
dropped:

  $ untimed ../../../bin/main.exe debian --order=pubgrub --native amd64 Packages.provides bvgoal2
  packages (2):
    bvgoal2:amd64 1
    bvprov2:amd64 1
  encoded solution: 3 core nodes (4 lookups)
  loaded: 5 names, 5 versions
  parser dropped 2 declarations

  $ untimed ../../../bin/main.exe debian --order=pubgrub --native amd64 Packages.provides bvgoal
  unsatisfiable:
  Because bvgoal:amd64 1 -> bvirt:amd64 ∅ and root -> bvgoal:amd64 1, version solving failed..
  loaded: 5 names, 5 versions
  parser dropped 2 declarations
  [1]

apt keeps 1.0 and 1.00 as two versions, which compare equal, and NAME=VERSION
matches the string (pkgVersionMatch::MatchVer), so exv=1.00 is the stanza
without exv 1.0's missing dependency, and exv=1.0 the one with it:

  $ untimed ../../../bin/main.exe debian --native amd64 Packages.versions exv=1.00
  packages (1):
    exv:amd64 1.00
  encoded solution: 1 core nodes (1 lookups)
  loaded: 7 names, 7 versions

  $ untimed ../../../bin/main.exe debian --native amd64 Packages.versions exv=1.0
  unsatisfiable:
  Because exv:amd64 1.0 -> exnone:amd64 ∅ and root -> exv:amd64 1.0, version solving failed..
  loaded: 7 names, 7 versions
  [1]

An epoch is compared as dpkg's digit runs are, however long, and never
read into a machine integer:

  $ untimed ../../../bin/main.exe debian --native amd64 Packages.versions epgoal
  packages (2):
    epgoal:amd64 1
    epv:amd64 99999999999999999999:1
  encoded solution: 2 core nodes (3 lookups)
  loaded: 7 names, 7 versions

Two alternatives the calculus identifies, eqa (>= 1.0) and eqa (>= 1.00),
are one, so the clause is a single dependency on eqa: the shadow of apt's
queue enqueues eqa at once rather than push a work item for a clause name
PubGrub never offers, which would part the two when it popped ahead of
eqy | eqz:

  $ PACSHADOW=1 ../../../bin/main.exe debian --order=tool --native amd64 Packages.versions eqgoal 2>&1 | sed -E '/^(parse|solve) [0-9.]+s$/d; s/^PACSHADOW.* (desync=[0-9]+).*/\1/'
  desync=0
  packages (3):
    eqa:amd64 1.0
    eqgoal:amd64 1
    eqy:amd64 1
  encoded solution: 4 core nodes (6 lookups)
  loaded: 7 names, 7 versions

An arch:all stanza and its native twin at one version are one version here,
with both stanzas' Provides in the per-package view too.  With
Strict-Pinning on, the first read is the candidate and the twin is gone;
off, the tool order's solution count finds each of twvirt and twvirt2
provided by twin and takes it, as PubGrub's own order does:

  $ untimed ../../../bin/main.exe debian --order=tool --no-strict-pinning --native amd64 Packages.twin twgoal
  packages (2):
    twgoal:amd64 1
    twin:amd64 1
  encoded solution: 4 core nodes (6 lookups)
  loaded: 4 names, 4 versions

  $ untimed ../../../bin/main.exe debian --order=tool --no-strict-pinning --native amd64 Packages.twin twgoal2
  packages (2):
    twgoal2:amd64 1
    twin:amd64 1
  encoded solution: 4 core nodes (6 lookups)
  loaded: 4 names, 4 versions

  $ untimed ../../../bin/main.exe debian --order=pubgrub --no-strict-pinning --native amd64 Packages.twin twgoal
  packages (2):
    twgoal:amd64 1
    twin:amd64 1
  encoded solution: 4 core nodes (6 lookups)
  loaded: 4 names, 4 versions

An index that cannot be read is a read error, not a refused query:

  $ ../../../bin/main.exe debian nope/Packages app
  error: nope/Packages: No such file or directory
  [3]

A name apt cannot locate at all, one only referred to or provided by no
candidate, and one several packages provide, are apt's errors before it
solves:

  $ ../../../bin/main.exe debian Packages app nosuchpkg
  error: Unable to locate package nosuchpkg
  [2]
  $ ../../../bin/main.exe debian Packages nosuchpkg:i386
  error: Unable to locate package nosuchpkg:i386
  [2]
  $ ../../../bin/main.exe debian Packages nosuchpkg=1
  error: Unable to locate package nosuchpkg
  [2]
  $ ../../../bin/main.exe debian Packages pinnone
  error: Package 'pinnone' has no installation candidate
  [2]
  $ ../../../bin/main.exe debian Packages dupvirt
  error: Package 'dupvirt' has no installation candidate
  [2]
  $ ../../../bin/main.exe debian Packages virt
  error: Package 'virt' has no installation candidate
  [2]

while a name one package alone provides selects that package, as apt's
"Note, selecting 'hsysd' instead of 'hsysusers'" does:

  $ untimed ../../../bin/main.exe debian --order=pubgrub Packages hsysusers
  packages (1):
    hsysd:amd64 1
  encoded solution: 1 core nodes (1 lookups)
  loaded: 176 names, 176 versions
