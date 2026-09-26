A query is a root Cargo.toml, as cargo has no other.  Most cases below
root a crate of the index through the manifest it was published with,
manifests/<crate>.toml, so the root's own dev-dependencies and features
are in play.

  $ ../../../bin/main.exe cargo index manifests/a.toml | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root a 1.0.0
  packages (6):
    a 1.0.0
    b 1.0.0
    c 1.0.0
    d 1.0.0 [a,f]
    d 2.0.0 [b,f]
    f 1.0.0 [c,d]
  encoded solution: 27 core nodes (27 lookups)
  loaded: 5 names, 6 versions

A requirement admits a prerelease only when one of its own comparators
names a prerelease at the same release core.  p publishes 1.0.0 and the
newer 1.0.1-alpha, and ^1.0.0 names no prerelease, so it takes 1.0.0;
q publishes 1.0.0-alpha.1 alone, which ^1.0.0-alpha reaches.

  $ ../../../bin/main.exe cargo index manifests/g.toml | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root g 1.0.0
  packages (3):
    g 1.0.0
    p 1.0.0
    q 1.0.0-alpha.1
  encoded solution: 9 core nodes (10 lookups)
  loaded: 3 names, 4 versions

A dev-dependency participates only from the root crate.  k declares m both
as an optional normal dependency and as a dev-dependency; from root h, k is
not the root, so neither record installs m -- the optional one is never
activated and the dev one does not participate.

  $ ../../../bin/main.exe cargo index manifests/h.toml | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root h 1.0.0
  packages (2):
    h 1.0.0
    k 1.0.0
  encoded solution: 6 core nodes (6 lookups)
  loaded: 3 names, 3 versions

From root k itself the same two records both matter.  With no features
named the root gets every feature it declares, which is the lockfile
resolve: the implicit feature of the optional m is among them, so that
record activates as well and each of the two binds m through its own
slot, two parent edges onto the one installed crate.

  $ ../../../bin/main.exe cargo index manifests/k.toml | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root k 1.0.0
  packages (2):
    k 1.0.0 [m]
    m 1.0.0
  encoded solution: 8 core nodes (8 lookups)
  loaded: 2 names, 2 versions

Naming features instead resolves afresh with those features and, as in
cargo, the root's default, and
under default alone nothing activates the optional normal record: the
mandatory dev record installs m by itself.  The two stay
separate slots -- conjoined, the dev record's non-optionality would bind
on every depender, which is the h case above.

  $ ../../../bin/main.exe cargo index manifests/k.toml --features "" | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root k 1.0.0 with default features
  packages (2):
    k 1.0.0
    m 1.0.0
  encoded solution: 5 core nodes (5 lookups)
  loaded: 2 names, 2 versions

Crates are parsed as the solver first asks for them, so a link's declarers
can be discovered after the link has been asked about.  x 1.0.0 and z 1.0.0
both claim links=foo, so they cannot coexist; x is reached from the root's
own records but z only through y, and links:foo is decided while x alone is
known.  z must still be admitted once it arrives -- the answer is the older,
link-free x beside z, not a rejection of z against a version set fixed
without it.

  $ ../../../bin/main.exe cargo index manifests/r.toml | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root r 1.0.0
  packages (4):
    r 1.0.0
    x 0.9.0
    y 1.0.2
    z 1.0.0
  encoded solution: 13 core nodes (20 lookups)
  loaded: 4 names, 7 versions

The root's own links key excludes as a dependency's does.  rl claims
links=foo, so x 1.0.0, which claims it too, is out and x 0.9.0 is taken.

  $ ../../../bin/main.exe cargo index manifests/rl.toml | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root rl 1.0.0
  packages (2):
    rl 1.0.0
    x 0.9.0
  encoded solution: 7 core nodes (8 lookups)
  loaded: 2 names, 3 versions

A weak feature entry resolves as the strong one.  u's default feature
enables cap, whose only entry is "w?/extra", and w is optional and named
nowhere else; cargo's resolver activates such an entry unconditionally and
narrows it only in a later pass over the fixed resolution, so that w keeps
its place in the lock as --features varies, and w is installed with extra.

  $ ../../../bin/main.exe cargo index manifests/s.toml | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root s 1.0.0
  packages (3):
    s 1.0.0
    u 1.0.0 [cap,default]
    w 1.0.0 [extra]
  encoded solution: 12 core nodes (12 lookups)
  loaded: 3 names, 3 versions

Resolver v3's one effect on version selection: a candidate whose declared
MSRV the configured toolchain does not satisfy ranks below every candidate
it does, and newest-first still decides within each of the two.  d1 publishes
1.0.0 with rust-version 1.60 and 1.1.0 with 1.80; under a 1.70 toolchain
m1 takes the older 1.0.0.

  $ ../../../bin/main.exe cargo index manifests/m1.toml --rust-version 1.70 | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root m1 1.0.0 for rust 1.70
  packages (2):
    d1 1.0.0
    m1 1.0.0
  encoded solution: 6 core nodes (7 lookups)
  loaded: 2 names, 3 versions

With no toolchain configured the preference is off, as it is in cargo when
the rust-versions list is empty, and the same index takes the newest.

  $ ../../../bin/main.exe cargo index manifests/m1.toml | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root m1 1.0.0
  packages (2):
    d1 1.1.0
    m1 1.0.0
  encoded solution: 6 core nodes (7 lookups)
  loaded: 2 names, 3 versions

A crate declaring no MSRV is compatible with every toolchain rather than
with none: msrv_compat_count returns the full count when a summary carries
no rust-version.  d2 publishes 1.0.0 needing 1.90, 1.1.0 declaring nothing
and 1.2.0 needing 1.95, so under 1.70 the field-less 1.1.0 wins -- neither
the newest nor the oldest, which no other reading of the missing field
would give.

  $ ../../../bin/main.exe cargo index manifests/m2.toml --rust-version 1.70 | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root m2 1.0.0 for rust 1.70
  packages (2):
    d2 1.1.0
    m2 1.0.0
  encoded solution: 6 core nodes (7 lookups)
  loaded: 2 names, 4 versions

  $ ../../../bin/main.exe cargo index manifests/m2.toml | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root m2 1.0.0
  packages (2):
    d2 1.2.0
    m2 1.0.0
  encoded solution: 6 core nodes (7 lookups)
  loaded: 2 names, 4 versions

This is a preference and not a constraint.  m3 requires ^2 of d3, whose
only version in range is 2.0.0 needing 1.90; the MSRV-compatible 1.0.0 is
out of range, so 2.0.0 is taken rather than the solve failing.

  $ ../../../bin/main.exe cargo index manifests/m3.toml --rust-version 1.70 | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root m3 1.0.0 for rust 1.70
  packages (2):
    d3 2.0.0
    m3 1.0.0
  encoded solution: 6 core nodes (6 lookups)
  loaded: 2 names, 3 versions

One alias declared twice is two dependencies, not one.  t names e in
[dependencies] at ^0.2 and again under [target.'cfg(windows)'.dependencies]
at ^0.1; cargo's identity for a dependency is the manifest site that
declared it -- the target section, the kind table, and the key inside it --
so the two are separate rows of the summary and both resolve, giving a
lockfile with e 0.1.0 beside e 0.2.0.

  $ ../../../bin/main.exe cargo index manifests/t.toml | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root t 1.0.0
  packages (3):
    e 0.1.0
    e 0.2.0
    t 1.0.0
  encoded solution: 9 core nodes (9 lookups)
  loaded: 2 names, 3 versions

Two sites may also share an alias while naming different crates, since
package = renames the target and the cross-table check constrains only the
source registry.  rn's x is e under [dependencies] and w under
[target.'cfg(windows)'.dependencies], and both are installed.

  $ ../../../bin/main.exe cargo index manifests/rn.toml | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root rn 1.0.0
  packages (3):
    e 0.2.0
    rn 1.0.0
    w 1.0.0
  encoded solution: 9 core nodes (9 lookups)
  loaded: 3 names, 4 versions

A crate's feature set is the one cargo's version resolver records for it
(Resolve::features, what `cargo metadata --all-features` prints), and two of that
resolver's rules are about names it adds on its own.  A crate declaring no
default feature gets none -- cargo's handle_default requires the key -- so
a depender's default-features request lands on nothing, and every crate in
this index but u shows no default at all.  And a strong a/feat entry over
an optional dependency a also enables the feature named a when the crate
has one (dep_cache.rs, require_dep_feature): ir asks i for net alone, net
is "o/extra" over the optional o, whose implicit feature o exists, so i is
resolved with o on:

  $ ../../../bin/main.exe cargo index manifests/ir.toml | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root ir 1.0.0
  packages (3):
    i 1.0.0 [net,o]
    ir 1.0.0
    o 1.0.0 [extra]
  encoded solution: 12 core nodes (12 lookups)
  loaded: 3 names, 3 versions

Where dep:o names the dependency there is no implicit feature o to enable,
and i3 is resolved with net alone:

  $ ../../../bin/main.exe cargo index manifests/ir3.toml | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root ir3 1.0.0
  packages (3):
    i3 1.0.0 [net]
    ir3 1.0.0
    o 1.0.0 [extra]
  encoded solution: 11 core nodes (11 lookups)
  loaded: 3 names, 3 versions

Which of two crates keeps its newest version, when one pins the other, is
settled by the order cargo activates them in (core/resolver/mod.rs,
activate_deps_loop).  cp 0.1.7 pins ga to =0.14.7 where 0.1.6 takes ^0.14.4.
pa declares ga before cp, both with two candidates, and cargo takes a
crate's dependencies fewest candidates first and in declaration order
between equals: ga is activated at 0.14.9, cp 0.1.7 then fails on its pin,
and cp falls back to 0.1.6.

  $ ../../../bin/main.exe cargo index manifests/oa.toml | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root oa 1.0.0
  packages (4):
    cp 0.1.6
    ga 0.14.9
    oa 1.0.0
    pa 1.0.0
  encoded solution: 13 core nodes (16 lookups)
  loaded: 4 names, 6 versions

pb declares zp, a copy of cp, first, so zp 0.1.7 is activated first and its
pin, with one candidate, is taken before pb's own ^0.14 of ga.

  $ ../../../bin/main.exe cargo index manifests/ob.toml | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root ob 1.0.0
  packages (4):
    ga 0.14.7
    ob 1.0.0
    pb 1.0.0
    zp 0.1.7
  encoded solution: 13 core nodes (16 lookups)
  loaded: 4 names, 6 versions

The root's own dependencies are read from its manifest, whose tables cargo
keys by name, so oc's zp-then-ga reaches the resolver as ga-then-zp.

  $ ../../../bin/main.exe cargo index manifests/oc.toml | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root oc 1.0.0
  packages (3):
    ga 0.14.9
    oc 1.0.0
    zp 0.1.6
  encoded solution: 10 core nodes (13 lookups)
  loaded: 3 names, 5 versions

Resolver v3 ranks the candidate versions of a dependency, not their
granularity classes (version_prefs.rs, sort_summaries), and skips a
candidate whose granularity class is already activated at another version
(RemainingCandidates::next).
ms activates sk 0.5.10 through its pin; mq's >=0.5, <0.7 then meets the
compatible 0.5.9, which that activation rules out, and takes the newest of
the rest, 0.6.5, although it needs a newer Rust than 1.70.

  $ ../../../bin/main.exe cargo index manifests/ms.toml --rust-version 1.70 | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root ms 1.0.0 for rust 1.70
  packages (4):
    mq 1.0.0
    ms 1.0.0
    sk 0.5.10
    sk 0.6.5
  encoded solution: 12 core nodes (14 lookups)
  loaded: 3 names, 5 versions

mu pins sl to 0.6.5, which needs 1.80, so mt's range skips the compatible
0.6.4 of that granularity class and takes the compatible 0.5.9 of the
older one.

  $ ../../../bin/main.exe cargo index manifests/mu.toml --rust-version 1.70 | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root mu 1.0.0 for rust 1.70
  packages (4):
    mt 1.0.0
    mu 1.0.0
    sl 0.5.9
    sl 0.6.5
  encoded solution: 12 core nodes (14 lookups)
  loaded: 3 names, 5 versions

A candidate one of whose mandatory dependencies has no valid candidate
left is passed over, as cargo passes it over after activating it and
failing at once on that dependency.  dz pins sp to 1.0.0, and each zk pins
sp to its own version, so zk's newest two are dead on arrival: the solve
takes zk 1.0.0 without a single conflict, where learning it would cost
one per version, since each version's slot is its own name.

  $ ../../../bin/main.exe cargo index manifests/dz.toml | grep -E '^  (sp|zk) '
    sp 1.0.0
    zk 1.0.0
  $ ../../../bin/main.exe cargo index manifests/dz.toml --debug | grep -c '^conflict resolution'
  0
  [1]

The dependency can die a step further down.  Each zj past 1.0.0 pins ae
0.10.3, whose own range for sb misses the 2.6.1 dy pins, so a zj taking
ae has one candidate for it and that candidate is dead: the chain of
forced candidates is followed, and zj 1.0.0 is again reached without a
conflict.

  $ ../../../bin/main.exe cargo index manifests/dy.toml | grep -E '^  (ae|sb|zj) '
    sb 2.6.1
    zj 1.0.0
  $ ../../../bin/main.exe cargo index manifests/dy.toml --debug | grep -c '^conflict resolution'
  0
  [1]

And the dependency that dies can be an optional one the features asked of
the candidate turn on.  dx asks tr for url, which in tr 1.1.0 enables sb
at a range the pinned 2.6.1 misses, so tr 1.0.0 is taken, again without a
conflict.

  $ ../../../bin/main.exe cargo index manifests/dx.toml | grep -E '^  (sb|tr) '
    sb 2.6.1
    tr 1.0.0 [url]
  $ ../../../bin/main.exe cargo index manifests/dx.toml --debug | grep -c '^conflict resolution'
  0
  [1]

A dependency with several valid candidates dies when every one of them
does.  xw 1.1.0 needs zv, and each zv needs sb at a range the pinned 2.6.1
misses, so xw 1.1.0 is passed over for 1.0.0, again without a conflict.

  $ ../../../bin/main.exe cargo index manifests/dw.toml | grep -E '^  (sb|xw|zv) '
    sb 2.6.1
    xw 1.0.0
  $ ../../../bin/main.exe cargo index manifests/dw.toml --debug | grep -c '^conflict resolution'
  0
  [1]

Where every candidate is dead the versions can only be refuted, one per
backjump, and cargo's order reaches the dependency again after each only
behind everything queued ahead of it.  dv takes sb 2.6.1 before t1, t2 and
t3, and only then zj, whose versions both need ae 0.10.3 and so sb below
2.5.  Refuting it costs whole replays of the queue, not the answer: cargo,
backtracking into its saved frame, lands on sb 2.4.1 too.
zj 1.1.0 and 1.2.0 are one granularity class declaring ae alike, so they
share one slot, and the conflict learned against it refutes both at once.

  $ ../../../bin/main.exe cargo index manifests/dv.toml | grep -E '^  (ae|sb|zj) '
    ae 0.10.3
    sb 2.4.1
    zj 1.2.0
  $ ../../../bin/main.exe cargo index manifests/dv.toml --debug | grep -c '^deciding on'
  72

A root Cargo.toml of its own.  app takes s under [dependencies], e under
the key x through package = "e", the optional i with its default
features off, m as a dev-dependency, and e again for cfg(windows); its
feature net asks i for net.  The lock enables every root feature, so i
comes in through net, with o behind i's own net, and e is locked at both
0.1.0 (for x) and 0.2.0.

  $ ../../../bin/main.exe cargo index manifests/app.toml --print-parents | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root app 0.1.0
  packages (9):
    app 0.1.0 [default,i,net]
    e 0.1.0
    e 0.2.0
    i 1.0.0 [net,o]
    m 1.0.0
    o 1.0.0 [extra]
    s 1.0.0
    u 1.0.0 [cap,default]
    w 1.0.0 [extra]
  parent edges (8):
    app 0.1.0 -> e(e) 0.2.0
    app 0.1.0 -> i(i) 1.0.0
    app 0.1.0 -> m(m) 1.0.0
    app 0.1.0 -> s(s) 1.0.0
    app 0.1.0 -> x(e) 0.1.0
    i 1.0.0 -> o(o) 1.0.0
    s 1.0.0 -> u(u) 1.0.0
    u 1.0.0 -> w(w) 1.0.0
  encoded solution: 36 core nodes (36 lookups)
  loaded: 8 names, 8 versions

A dev-dependency that depends back on the root reaches the root's own
name and version through the registry.  The model has one node there;
cargo keeps two packages, the path root and the registry's b, unless a
[patch] maps the name to the root, so pac refuses the first manifest and
answers the second.

  $ ../../../bin/main.exe cargo index manifests/selfdep.toml > /dev/null
  error: the answer reaches b 1.0.0 through the registry, which cargo keeps apart from the root unless [patch.crates-io] maps b to it with { path = "." }
  [2]
  $ ../../../bin/main.exe cargo index manifests/selfpatch.toml --print-parents | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root b 1.0.0
  packages (6):
    a 1.0.0
    b 1.0.0
    c 1.0.0
    d 1.0.0 [a,f]
    d 2.0.0 [b,f]
    f 1.0.0 [c,d]
  parent edges (7):
    a 1.0.0 -> b(b) 1.0.0
    a 1.0.0 -> c(c) 1.0.0
    b 1.0.0 -> a(a) 1.0.0
    b 1.0.0 -> d(d) 1.0.0
    c 1.0.0 -> d(d) 2.0.0
    d 1.0.0 -> f(f) 1.0.0
    d 2.0.0 -> f(f) 1.0.0
  encoded solution: 28 core nodes (28 lookups)
  loaded: 5 names, 6 versions

Sources and patches the model does not cover are refused rather than
dropped:

  $ ../../../bin/main.exe cargo index manifests/pathdep.toml
  error: dependencies.m: a path source is not a registry crate, and only the registry is modelled
  [2]
  $ ../../../bin/main.exe cargo index manifests/otherpatch.toml
  error: [patch.crates-io] m: the only patch modelled maps the root's own name to the root, { path = "." }
  [2]

An index entry whose feature table cargo's build_feature_map refuses is
never a candidate, so cargo takes 1.0.0 of each of fa (dep:o/extra), fb
(o/extra/z) and fc (a feature naming neither a feature nor a dependency):

  $ ../../../bin/main.exe cargo index manifests/fm.toml | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root fm 1.0.0
  packages (4):
    fa 1.0.0
    fb 1.0.0
    fc 1.0.0
    fm 1.0.0
  encoded solution: 12 core nodes (12 lookups)
  loaded: 4 names, 3 versions
  parser dropped 3 declarations

The manifest is TOML, which cargo refuses where a header defines a table
dotted keys already made, an integer has a leading zero, or an escape
names a surrogate rather than a Unicode scalar value:

  $ ../../../bin/main.exe cargo index manifests/tomldot.toml
  error: manifests/tomldot.toml: line 13: table "dependencies.b" defined twice
  [2]
  $ ../../../bin/main.exe cargo index manifests/tomlint.toml
  error: manifests/tomlint.toml: line 7: bad value "0_1"
  [2]
  $ ../../../bin/main.exe cargo index manifests/tomlesc.toml
  error: manifests/tomlesc.toml: line 5: bad \u escape
  [2]

while dotted keys over one table, a sub-table header under them, and
numbers TOML allows all read:

  $ ../../../bin/main.exe cargo index manifests/tomlok.toml | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root tomlok 1.0.0
  packages (4):
    b 1.0.0
    d 1.0.0 [a,f]
    f 1.0.0 [c]
    tomlok 1.0.0
  encoded solution: 16 core nodes (16 lookups)
  loaded: 4 names, 4 versions

A version component is a u64 in cargo's semver, so tv's timestamp-style
1.0.1234567890 and 1.0.1234567891 are two versions, and ^1 takes the
newer, as cargo does.

  $ ../../../bin/main.exe cargo index manifests/vt.toml | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root vt 1.0.0
  packages (2):
    tv 1.0.1234567891
    vt 1.0.0
  encoded solution: 6 core nodes (7 lookups)
  loaded: 2 names, 2 versions

Two versions that differ only in build metadata are two packages to cargo,
whose PackageId compares the whole semver::Version, and the semver crate's
order breaks their precedence tie on the build identifiers, while a
requirement matches on precedence alone.  So =1.0.0 and <=1.0.0 admit both
of bm's and bp's, and each name takes the greater: 1.0.0+b over 1.0.0+a,
1.0.0+1 over 1.0.0, 1.0.0+x over the numeric 1.0.0+10, and 1.0.0+10 over
1.0.0+9.  bf's 1.0.0+b needs a crate the index lacks, so bf falls back to
1.0.0+a.  cargo 1.97 locks the same six:

  $ ../../../bin/main.exe cargo index manifests/bmeta.toml | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root bmeta 1.0.0
  packages (6):
    bf 1.0.0+a
    bm 1.0.0+b
    bmeta 1.0.0
    bn 1.0.0+x
    bo 1.0.0+10
    bp 1.0.0+1
  encoded solution: 18 core nodes (23 lookups)
  loaded: 7 names, 10 versions

cargo skips an index line it cannot deserialize, so a line that is JSON
but not an object is dropped and counted, and so is a version one of
whose dependencies is not an object, or has no name: nb's 1.1.0 and 1.2.0
are out, and cargo, like pac, locks 1.0.0.

  $ ../../../bin/main.exe cargo index manifests/nbr.toml | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root nbr 1.0.0
  packages (2):
    nb 1.0.0
    nbr 1.0.0
  encoded solution: 6 core nodes (6 lookups)
  loaded: 2 names, 1 versions
  parser dropped 4 declarations

--features keeps the root's default unless --no-default-features drops
it, as cargo's CliFeatures does, and an empty --features names nothing
rather than everything.  fd's default enables net, which asks the
optional i for net.

  $ ../../../bin/main.exe cargo index manifests/fd.toml | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root fd 1.0.0
  packages (3):
    fd 1.0.0 [default,i,net,plain]
    i 1.0.0 [net,o]
    o 1.0.0 [extra]
  encoded solution: 17 core nodes (17 lookups)
  loaded: 3 names, 2 versions
  $ ../../../bin/main.exe cargo index manifests/fd.toml -F "" | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root fd 1.0.0 with default features
  packages (3):
    fd 1.0.0 [default,i,net]
    i 1.0.0 [net,o]
    o 1.0.0 [extra]
  encoded solution: 16 core nodes (16 lookups)
  loaded: 3 names, 2 versions
  $ ../../../bin/main.exe cargo index manifests/fd.toml --no-default-features | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root fd 1.0.0 with no features
  packages (1):
    fd 1.0.0
  encoded solution: 2 core nodes (2 lookups)
  loaded: 2 names, 1 versions
  $ ../../../bin/main.exe cargo index manifests/fd.toml --no-default-features -F plain | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root fd 1.0.0 with features plain and no default feature
  packages (1):
    fd 1.0.0 [plain]
  encoded solution: 3 core nodes (3 lookups)
  loaded: 2 names, 1 versions

A requirement cargo cannot parse is refused, not read as "*":

  $ ../../../bin/main.exe cargo index manifests/badreq.toml
  error: failed to parse the version requirement `abc` for dependency `i`
  [2]

The order is cargo's unless --order=pubgrub leaves it to PubGrub, whose
answer is a resolution too, though not always the one cargo locks: under
PubGrub's own order oa keeps cp's newest, 0.1.7, and ga at its pin.

  $ ../../../bin/main.exe cargo index manifests/oa.toml --order=pubgrub | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root oa 1.0.0
  packages (4):
    cp 0.1.7
    ga 0.14.7
    oa 1.0.0
    pa 1.0.0
  encoded solution: 13 core nodes (16 lookups)
  loaded: 4 names, 6 versions

--order=random picks the next name and the version to try uniformly, from
a generator seeded by --seed: the same seed gives the same answer, and
another seed may give another, a resolution all the same:

  $ seed0() { ../../../bin/main.exe cargo index manifests/oa.toml --order=random --seed 0 | sed -E '/^(parse|solve) [0-9.]+s$/d'; }; [ "$(seed0)" = "$(seed0)" ] && seed0
  root oa 1.0.0
  packages (4):
    cp 0.1.6
    ga 0.14.9
    oa 1.0.0
    pa 1.0.0
  encoded solution: 13 core nodes (16 lookups)
  loaded: 4 names, 6 versions
  $ ../../../bin/main.exe cargo index manifests/oa.toml --order=random --seed 4 | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root oa 1.0.0
  packages (4):
    cp 0.1.7
    ga 0.14.7
    oa 1.0.0
    pa 1.0.0
  encoded solution: 13 core nodes (16 lookups)
  loaded: 4 names, 6 versions

cargo's lock records a crate's dependencies as the versions they resolved
to, and reading it back locks each declaration to the first of those, in
version order, that its requirement admits (core/registry.rs, lock).  stk
declares wsy twice, under two cfgs, with one requirement, so whatever the
order, the two are one version, with both declarations' features:

  $ for s in 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15; do ../../../bin/main.exe cargo index manifests/st.toml --order=random --seed $s | grep -c '^  wsy '; done | sort | uniq -c
       16 1

  $ ../../../bin/main.exe cargo index manifests/st.toml --print-parents | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root st 1.0.0
  packages (3):
    st 1.0.0
    stk 0.1.0
    wsy 0.61.0 [a,b]
  parent edges (2):
    st 1.0.0 -> stk(stk) 0.1.0
    stk 0.1.0 -> wsy(wsy) 0.61.0
  encoded solution: 11 core nodes (12 lookups)
  loaded: 3 names, 3 versions

The root's dev-dependencies are active beside its normal ones, so a
dev-dependency with the requirement of a normal one is the same
declaration to the lock:

  $ for s in 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15; do ../../../bin/main.exe cargo index manifests/st2.toml --order=random --seed $s | grep -c '^  wsy '; done | sort | uniq -c
       16 1

The root's feature table passes the checks an index entry's does
(build_feature_map), or cargo refuses the manifest:

  $ ../../../bin/main.exe cargo index manifests/rfm.toml
  error: manifests/rfm.toml: [features] is not a table cargo accepts: every entry names a feature, an optional dependency (dep:), or a dependency's feature
  [2]
  $ ../../../bin/main.exe cargo index manifests/rfm2.toml
  error: manifests/rfm2.toml: [features] is not a table cargo accepts: every entry names a feature, an optional dependency (dep:), or a dependency's feature
  [2]

A feature --features names must be the root's, and a version must be one:

  $ ../../../bin/main.exe cargo index manifests/fd.toml -F nope
  error: the package `fd v1.0.0` does not have the feature `nope`
  [2]
  $ ../../../bin/main.exe cargo index manifests/fd.toml -F i/net
  error: --features i/net: a dependency's feature on the command line is not modelled
  [2]
  $ ../../../bin/main.exe cargo index manifests/m1.toml --rust-version 1.x
  error: --rust-version 1.x is not a version like "1.32" or "1.32.0"
  [2]
  $ ../../../bin/main.exe cargo index manifests/rv.toml
  error: package.rust-version "1.70-beta" is not a version like "1.32"
  [2]

The root's version is a whole semver version, as cargo reads it, less
the whitespace around it:

  $ for v in 1.x 1.0 01.0.0 1.0.0-01 1.0.0- 1.0.0+a..b 18446744073709551616.0.0 ' 1.0.0 ' 1.0.0+001 18446744073709551615.0.0; do
  >   printf '[package]\nname = "vt"\nversion = "%s"\n' "$v" > v.toml
  >   ../../../bin/main.exe cargo index v.toml > out; s=$?; grep '^root' out; echo "[$s]"
  > done
  error: package.version "1.x" is not a semver version like "1.2.3"
  [2]
  error: package.version "1.0" is not a semver version like "1.2.3"
  [2]
  error: package.version "01.0.0" is not a semver version like "1.2.3"
  [2]
  error: package.version "1.0.0-01" is not a semver version like "1.2.3"
  [2]
  error: package.version "1.0.0-" is not a semver version like "1.2.3"
  [2]
  error: package.version "1.0.0+a..b" is not a semver version like "1.2.3"
  [2]
  error: package.version "18446744073709551616.0.0" is not a semver version like "1.2.3"
  [2]
  root vt 1.0.0
  [0]
  root vt 1.0.0+001
  [0]
  root vt 18446744073709551615.0.0
  [0]

The whitespace cargo trims is Rust's (str::trim, which strips Unicode
White_Space): a vertical tab, a no-break space and an ideographic space go
with it, while a zero-width space, which is no White_Space, stays and makes
the version one cargo refuses, as cargo 1.97 does:

  $ for v in '\u000B1.0.0' ' 1.0.0　' '​1.0.0'; do
  >   printf '[package]\nname = "vt"\nversion = "%s"\n' "$v" > v.toml
  >   ../../../bin/main.exe cargo index v.toml > out; s=$?; grep '^root' out; echo "[$s]"
  > done
  root vt 1.0.0
  [0]
  root vt 1.0.0
  [0]
  error: package.version "\226\128\1391.0.0" is not a semver version like "1.2.3"
  [2]
  $ printf '[package]\nname = "vt"\nversion = "1.x"\n' > v.toml
  $ ../../../bin/main.exe cargo index v.toml
  error: package.version "1.x" is not a semver version like "1.2.3"
  [2]

Its name is one cargo accepts, and a dependency's is too, though a
non-ASCII name, which no crates.io crate has, is refused unread:

  $ for n in 'a b' 1a -a a.b a:b a::b '' _a a-b café; do
  >   printf '[package]\nname = "%s"\nversion = "1.0.0"\n' "$n" > n.toml
  >   ../../../bin/main.exe cargo index n.toml > out; s=$?; grep '^root' out; echo "[$s]"
  > done
  error: invalid character ` ` in package name: `a b`, characters must be Unicode XID characters (numbers, `-`, `_`, or most letters)
  [2]
  error: invalid character `1` in package name: `1a`, the name cannot start with a digit
  [2]
  error: invalid character `-` in package name: `-a`, the first character must be a Unicode XID start character (most letters or `_`)
  [2]
  error: invalid character `.` in package name: `a.b`, characters must be Unicode XID characters (numbers, `-`, `_`, or most letters)
  [2]
  error: invalid character `:` in package name: `a:b`, characters must be Unicode XID characters (numbers, `-`, `_`, or most letters)
  [2]
  error: package name `a::b` needs the unstable open-namespaces feature, which is not modelled
  [2]
  error: package name cannot be empty
  [2]
  root _a 1.0.0
  [0]
  root a-b 1.0.0
  [0]
  error: package name `café`: a non-ASCII name is not modelled
  [2]
  $ printf '[package]\nname = "a b"\nversion = "1.0.0"\n' > n.toml
  $ ../../../bin/main.exe cargo index n.toml
  error: invalid character ` ` in package name: `a b`, characters must be Unicode XID characters (numbers, `-`, `_`, or most letters)
  [2]
  $ printf '[package]\nname = "vt"\nversion = "1.0.0"\n[dependencies]\n"a b" = "1"\n' > d.toml
  $ ../../../bin/main.exe cargo index d.toml
  error: invalid character ` ` in package name: `a b`, characters must be Unicode XID characters (numbers, `-`, `_`, or most letters)
  [2]
  $ printf '[package]\nname = "vt"\nversion = "1.0.0"\n[dependencies]\nx = { version = "1", package = "1a" }\n' > d.toml
  $ ../../../bin/main.exe cargo index d.toml
  error: invalid character `1` in package name: `1a`, the name cannot start with a digit
  [2]

A dependency of the root on a crate the index does not have is cargo's
error before any version is chosen, whatever its kind, so pac refuses it
with cargo 1.97's words.  One further down the graph fails only the version
declaring it, as bf's 1.0.0+b above does:

  $ printf '[package]\nname = "vt"\nversion = "1.0.0"\n[dependencies]\na = "1"\n[dev-dependencies]\nnx = "1"\n' > d.toml
  $ ../../../bin/main.exe cargo index d.toml
  root vt 1.0.0
  error: no matching package named `nx` found
  [2]

An index or a manifest that cannot be read is a read error, not a refused
query:

  $ ../../../bin/main.exe cargo nope manifests/a.toml
  error: nope: No such file or directory
  [3]
  $ ../../../bin/main.exe cargo manifests/a.toml manifests/a.toml
  error: manifests/a.toml: Not a directory
  [3]
  $ ../../../bin/main.exe cargo index manifests/nope.toml
  error: manifests/nope.toml: No such file or directory
  [3]
  $ ../../../bin/main.exe cargo index manifests
  error: manifests: Is a directory
  [3]
