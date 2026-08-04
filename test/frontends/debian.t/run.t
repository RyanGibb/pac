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
