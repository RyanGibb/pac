  $ ../../../src/main.exe cargo index a | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root a 1.0.0
  crates (6):
    a 1.0.0
    b 1.0.0 [default]
    c 1.0.0 [default]
    d 1.0.0 [a,default]
    d 2.0.0 [b,default]
    f 1.0.0 [c,d,default]
  encoded solution: 61 core nodes (6 crate versions encoded)
  selections: 6
  loaded: 5 crates, 6 versions

A requirement admits a prerelease only when one of its own comparators
names a prerelease at the same release core.  p publishes 1.0.0 and the
newer 1.0.1-alpha, and ^1.0.0 names no prerelease, so it takes 1.0.0;
q publishes 1.0.0-alpha.1 alone, which ^1.0.0-alpha reaches.

  $ ../../../src/main.exe cargo index g | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root g 1.0.0
  crates (3):
    g 1.0.0
    p 1.0.0 [default]
    q 1.0.0-alpha.1 [default]
  encoded solution: 15 core nodes (4 crate versions encoded)
  selections: 2
  loaded: 3 crates, 4 versions

A dev-dependency participates only from the root crate.  k declares m both
as an optional normal dependency and as a dev-dependency; from root h, k is
not the root, so neither row installs m -- the optional one is never
activated and the dev one does not participate.

  $ ../../../src/main.exe cargo index h | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root h 1.0.0
  crates (2):
    h 1.0.0
    k 1.0.0 [default]
  encoded solution: 9 core nodes (2 crate versions encoded)
  selections: 1
  loaded: 3 crates, 3 versions

Crates are parsed as the solver first asks for them, so a link's declarers
can be discovered after the link has been asked about.  x 1.0.0 and z 1.0.0
both claim links=foo, so they cannot coexist; x is reached from the root's
own rows but z only through y, and links:foo is decided while x alone is
known.  z must still be admitted once it arrives -- the answer is the older,
link-free x beside z, not a rejection of z against a version set fixed
without it.

  $ ../../../src/main.exe cargo index r | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root r 1.0.0
  crates (4):
    r 1.0.0
    x 0.9.0 [default]
    y 1.0.2 [default]
    z 1.0.0 [default]
  encoded solution: 23 core nodes (7 crate versions encoded)
  selections: 3
  loaded: 4 crates, 7 versions
