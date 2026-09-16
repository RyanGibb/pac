  $ ../../../src/main.exe cargo index a | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root a 1.0.0
  crates (6):
    a 1.0.0
    b 1.0.0 [default]
    c 1.0.0 [default]
    d 1.0.0 [a,default]
    d 2.0.0 [b,default]
    f 1.0.0 [c,d,default]
  encoded solution: 24 core nodes (6 crate versions encoded)
  parent edges: 6
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
  encoded solution: 8 core nodes (4 crate versions encoded)
  parent edges: 2
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
  encoded solution: 5 core nodes (2 crate versions encoded)
  parent edges: 1
  loaded: 3 crates, 3 versions

From root k itself the same two rows both matter: the mandatory dev row
installs m even though nothing activates the optional normal row sharing
its alias.  The two stay separate slots -- conjoined, the dev row's
non-optionality would bind on every depender, which is the h case above.

  $ ../../../src/main.exe cargo index k | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root k 1.0.0
  crates (2):
    k 1.0.0
    m 1.0.0 [default]
  encoded solution: 5 core nodes (2 crate versions encoded)
  parent edges: 1
  loaded: 2 crates, 2 versions

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
  encoded solution: 12 core nodes (7 crate versions encoded)
  parent edges: 3
  loaded: 4 crates, 7 versions

A weak feature entry resolves as the strong one.  u's default feature
enables cap, whose only entry is "w?/extra", and w is optional and named
nowhere else; cargo's resolver activates such an entry unconditionally and
narrows it only in a later pass over the fixed resolution, so that w keeps
its place in the lock as --features varies, and w is installed with extra.

  $ ../../../src/main.exe cargo index s | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root s 1.0.0
  crates (3):
    s 1.0.0
    u 1.0.0 [cap,default]
    w 1.0.0 [default,extra]
  encoded solution: 11 core nodes (3 crate versions encoded)
  parent edges: 2
  loaded: 3 crates, 3 versions

Resolver v3's one effect on version selection: a candidate whose declared
MSRV the configured toolchain does not satisfy ranks below every candidate
it does, and newest-first still decides within each class.  d1 publishes
1.0.0 with rust-version 1.60 and 1.1.0 with 1.80; under a 1.70 toolchain
m1 takes the older 1.0.0.

  $ ../../../src/main.exe cargo index m1 --rust-version 1.70 | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root m1 1.0.0 for rust 1.70
  crates (2):
    d1 1.0.0 [default]
    m1 1.0.0
  encoded solution: 5 core nodes (3 crate versions encoded)
  parent edges: 1
  loaded: 2 crates, 3 versions

With no toolchain configured the preference is off, as it is in cargo when
the rust-versions list is empty, and the same index takes the newest.

  $ ../../../src/main.exe cargo index m1 | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root m1 1.0.0
  crates (2):
    d1 1.1.0 [default]
    m1 1.0.0
  encoded solution: 5 core nodes (3 crate versions encoded)
  parent edges: 1
  loaded: 2 crates, 3 versions

A crate declaring no MSRV is compatible with every toolchain rather than
with none: msrv_compat_count returns the full count when a summary carries
no rust-version.  d2 publishes 1.0.0 needing 1.90, 1.1.0 declaring nothing
and 1.2.0 needing 1.95, so under 1.70 the field-less 1.1.0 wins -- neither
the newest nor the oldest, which no other reading of the missing field
would give.

  $ ../../../src/main.exe cargo index m2 --rust-version 1.70 | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root m2 1.0.0 for rust 1.70
  crates (2):
    d2 1.1.0 [default]
    m2 1.0.0
  encoded solution: 5 core nodes (4 crate versions encoded)
  parent edges: 1
  loaded: 2 crates, 4 versions

  $ ../../../src/main.exe cargo index m2 | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root m2 1.0.0
  crates (2):
    d2 1.2.0 [default]
    m2 1.0.0
  encoded solution: 5 core nodes (4 crate versions encoded)
  parent edges: 1
  loaded: 2 crates, 4 versions

This is a preference and not a constraint.  m3 requires ^2 of d3, whose
only version in range is 2.0.0 needing 1.90; the MSRV-compatible 1.0.0 is
out of range, so 2.0.0 is taken rather than the solve failing.

  $ ../../../src/main.exe cargo index m3 --rust-version 1.70 | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root m3 1.0.0 for rust 1.70
  crates (2):
    d3 2.0.0 [default]
    m3 1.0.0
  encoded solution: 5 core nodes (3 crate versions encoded)
  parent edges: 1
  loaded: 2 crates, 3 versions
