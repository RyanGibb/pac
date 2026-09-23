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
cfld depends on cflb (= 1) and cflc, whichever order the solver reaches them:

  $ ../../../src/main.exe debian --native amd64 cfld Packages | sed -E '/^(parse|solve) [0-9.]+s$/d'
  unsatisfiable:
  Because cflc:amd64 1 -> cfla:amd64 1 and cfla:amd64 1 -> cflb:amd64 ⊥, cflc:amd64 (-∞, ⊥) requires cflb:amd64 ⊥.
  And because cfld:amd64 1 -> cflb:amd64 1, cfld:amd64 (-∞, ⊥) or cflc:amd64 (-∞, ⊥) is forbidden.
  And because cfld:amd64 1 -> cflc:amd64 1 and root -> cfld:amd64 1, version solving failed.

Absence is a version of the encoding, not an installation: cflc alone
decides cflb to ⊥, and the answer lists what is present.

  $ ../../../src/main.exe debian --native amd64 cflc Packages | sed -E '/^(parse|solve) [0-9.]+s$/d'
  cfla:amd64 1
  cflc:amd64 1
