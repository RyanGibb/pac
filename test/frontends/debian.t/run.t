  $ ../../../src/main.exe debian --native amd64 app Packages
  app:amd64 1
  lib:amd64 1
  prov2:amd64 1

A relationship field may be folded over several lines (Policy 5.1); the
newline is not part of the atom that follows it:

  $ ../../../src/main.exe debian --native amd64 folded Packages
  folded:amd64 1
  lib:amd64 1
  zzz:amd64 1

Provides makes an alias for a name, not the name itself: a real package is
preferred over anything claiming its name.  altlib alone would not
discriminate -- it sorts before lib, so the referent ordering hides the
question; zzlib sorts after it and does not:

  $ ../../../src/main.exe debian --native amd64 realdep Packages
  lib:amd64 1
  realdep:amd64 1

Recommends are installed by default, as under apt's APT::Install-Recommends,
and the leftmost alternative is preferred as in a Depends clause:

  $ ../../../src/main.exe debian --native amd64 softpair Packages
  softa:amd64 1
  softpair:amd64 1

  $ ../../../src/main.exe debian --native amd64 --no-install-recommends softpair Packages
  softpair:amd64 1

A one-alternative Recommends still gets its gadget: unlike a Depends clause,
which is inlined below two alternatives, the escape is the whole point of the
encoding and there is no cardinality test to skip it:

  $ ../../../src/main.exe debian --native amd64 softone Packages
  softlib:amd64 1
  softone:amd64 1

An unsatisfiable Recommends is not an error.  softconf recommends softnope,
which conflicts with the softkeep it depends on; the solve succeeds by taking
the escape, and softnope is absent:

  $ ../../../src/main.exe debian --native amd64 softconf Packages
  softconf:amd64 1
  softkeep:amd64 1

  $ ../../../src/main.exe debian --mono --native amd64 softconf Packages
  softconf:amd64 1
  softkeep:amd64 1

The escape sorts below every alternative, so it is reached only once they have
all failed: softalt recommends softnope | softb, and softnope is ruled out by
the same conflict, so softb is installed rather than nothing:

  $ ../../../src/main.exe debian --native amd64 softalt Packages
  softalt:amd64 1
  softb:amd64 1
  softkeep:amd64 1
