A query is a root Cargo.toml, as cargo has no other.  Most cases below
root a crate of the index through the manifest it was published with,
manifests/<crate>.toml, so the root's own dev-dependencies and features
are in play.

  $ ../../../src/main.exe cargo index manifests/a.toml | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root a 1.0.0
  crates (6):
    a 1.0.0
    b 1.0.0
    c 1.0.0
    d 1.0.0 [a,f]
    d 2.0.0 [b,f]
    f 1.0.0 [c,d]
  encoded solution: 27 core nodes (6 crate versions encoded)
  parent edges: 6
  loaded: 5 crates, 6 versions

A requirement admits a prerelease only when one of its own comparators
names a prerelease at the same release core.  p publishes 1.0.0 and the
newer 1.0.1-alpha, and ^1.0.0 names no prerelease, so it takes 1.0.0;
q publishes 1.0.0-alpha.1 alone, which ^1.0.0-alpha reaches.

  $ ../../../src/main.exe cargo index manifests/g.toml | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root g 1.0.0
  crates (3):
    g 1.0.0
    p 1.0.0
    q 1.0.0-alpha.1
  encoded solution: 9 core nodes (4 crate versions encoded)
  parent edges: 2
  loaded: 3 crates, 4 versions

A dev-dependency participates only from the root crate.  k declares m both
as an optional normal dependency and as a dev-dependency; from root h, k is
not the root, so neither record installs m -- the optional one is never
activated and the dev one does not participate.

  $ ../../../src/main.exe cargo index manifests/h.toml | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root h 1.0.0
  crates (2):
    h 1.0.0
    k 1.0.0
  encoded solution: 6 core nodes (2 crate versions encoded)
  parent edges: 1
  loaded: 3 crates, 3 versions

From root k itself the same two records both matter.  With no features
named the root gets every feature it declares, which is the lockfile
resolve: the implicit feature of the optional m is among them, so that
record activates as well and each of the two binds m through its own
slot, two parent edges onto the one installed crate.

  $ ../../../src/main.exe cargo index manifests/k.toml | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root k 1.0.0
  crates (2):
    k 1.0.0 [m]
    m 1.0.0
  encoded solution: 8 core nodes (2 crate versions encoded)
  parent edges: 2
  loaded: 2 crates, 2 versions

Naming features instead resolves afresh with exactly those features, and
under default alone nothing activates the optional normal record: the
mandatory dev record installs m by itself.  The two stay
separate slots -- conjoined, the dev record's non-optionality would bind
on every depender, which is the h case above.

  $ ../../../src/main.exe cargo index manifests/k.toml --features default | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root k 1.0.0 with features default
  crates (2):
    k 1.0.0
    m 1.0.0
  encoded solution: 6 core nodes (2 crate versions encoded)
  parent edges: 1
  loaded: 2 crates, 2 versions

Crates are parsed as the solver first asks for them, so a link's declarers
can be discovered after the link has been asked about.  x 1.0.0 and z 1.0.0
both claim links=foo, so they cannot coexist; x is reached from the root's
own records but z only through y, and links:foo is decided while x alone is
known.  z must still be admitted once it arrives -- the answer is the older,
link-free x beside z, not a rejection of z against a version set fixed
without it.

  $ ../../../src/main.exe cargo index manifests/r.toml | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root r 1.0.0
  crates (4):
    r 1.0.0
    x 0.9.0
    y 1.0.2
    z 1.0.0
  encoded solution: 13 core nodes (7 crate versions encoded)
  parent edges: 3
  loaded: 4 crates, 7 versions

The root's own links key excludes as a dependency's does.  rl claims
links=foo, so x 1.0.0, which claims it too, is out and x 0.9.0 is taken.

  $ ../../../src/main.exe cargo index manifests/rl.toml | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root rl 1.0.0
  crates (2):
    rl 1.0.0
    x 0.9.0
  encoded solution: 7 core nodes (3 crate versions encoded)
  parent edges: 1
  loaded: 2 crates, 3 versions

A weak feature entry resolves as the strong one.  u's default feature
enables cap, whose only entry is "w?/extra", and w is optional and named
nowhere else; cargo's resolver activates such an entry unconditionally and
narrows it only in a later pass over the fixed resolution, so that w keeps
its place in the lock as --features varies, and w is installed with extra.

  $ ../../../src/main.exe cargo index manifests/s.toml | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root s 1.0.0
  crates (3):
    s 1.0.0
    u 1.0.0 [cap,default]
    w 1.0.0 [extra]
  encoded solution: 12 core nodes (3 crate versions encoded)
  parent edges: 2
  loaded: 3 crates, 3 versions

Resolver v3's one effect on version selection: a candidate whose declared
MSRV the configured toolchain does not satisfy ranks below every candidate
it does, and newest-first still decides within each class.  d1 publishes
1.0.0 with rust-version 1.60 and 1.1.0 with 1.80; under a 1.70 toolchain
m1 takes the older 1.0.0.

  $ ../../../src/main.exe cargo index manifests/m1.toml --rust-version 1.70 | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root m1 1.0.0 for rust 1.70
  crates (2):
    d1 1.0.0
    m1 1.0.0
  encoded solution: 6 core nodes (3 crate versions encoded)
  parent edges: 1
  loaded: 2 crates, 3 versions

With no toolchain configured the preference is off, as it is in cargo when
the rust-versions list is empty, and the same index takes the newest.

  $ ../../../src/main.exe cargo index manifests/m1.toml | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root m1 1.0.0
  crates (2):
    d1 1.1.0
    m1 1.0.0
  encoded solution: 6 core nodes (3 crate versions encoded)
  parent edges: 1
  loaded: 2 crates, 3 versions

A crate declaring no MSRV is compatible with every toolchain rather than
with none: msrv_compat_count returns the full count when a summary carries
no rust-version.  d2 publishes 1.0.0 needing 1.90, 1.1.0 declaring nothing
and 1.2.0 needing 1.95, so under 1.70 the field-less 1.1.0 wins -- neither
the newest nor the oldest, which no other reading of the missing field
would give.

  $ ../../../src/main.exe cargo index manifests/m2.toml --rust-version 1.70 | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root m2 1.0.0 for rust 1.70
  crates (2):
    d2 1.1.0
    m2 1.0.0
  encoded solution: 6 core nodes (4 crate versions encoded)
  parent edges: 1
  loaded: 2 crates, 4 versions

  $ ../../../src/main.exe cargo index manifests/m2.toml | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root m2 1.0.0
  crates (2):
    d2 1.2.0
    m2 1.0.0
  encoded solution: 6 core nodes (4 crate versions encoded)
  parent edges: 1
  loaded: 2 crates, 4 versions

This is a preference and not a constraint.  m3 requires ^2 of d3, whose
only version in range is 2.0.0 needing 1.90; the MSRV-compatible 1.0.0 is
out of range, so 2.0.0 is taken rather than the solve failing.

  $ ../../../src/main.exe cargo index manifests/m3.toml --rust-version 1.70 | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root m3 1.0.0 for rust 1.70
  crates (2):
    d3 2.0.0
    m3 1.0.0
  encoded solution: 6 core nodes (3 crate versions encoded)
  parent edges: 1
  loaded: 2 crates, 3 versions

One alias declared twice is two dependencies, not one.  t names e in
[dependencies] at ^0.2 and again under [target.'cfg(windows)'.dependencies]
at ^0.1; cargo's identity for a dependency is the manifest site that
declared it -- the target section, the kind table, and the key inside it --
so the two are separate rows of the summary and both resolve, giving a
lockfile with e 0.1.0 beside e 0.2.0.

  $ ../../../src/main.exe cargo index manifests/t.toml | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root t 1.0.0
  crates (3):
    e 0.1.0
    e 0.2.0
    t 1.0.0
  encoded solution: 9 core nodes (3 crate versions encoded)
  parent edges: 2
  loaded: 2 crates, 3 versions

Two sites may also share an alias while naming different crates, since
package = renames the target and the cross-table check constrains only the
source registry.  rn's x is e under [dependencies] and w under
[target.'cfg(windows)'.dependencies], and both are installed.

  $ ../../../src/main.exe cargo index manifests/rn.toml | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root rn 1.0.0
  crates (3):
    e 0.2.0
    rn 1.0.0
    w 1.0.0
  encoded solution: 9 core nodes (4 crate versions encoded)
  parent edges: 2
  loaded: 3 crates, 4 versions

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

  $ ../../../src/main.exe cargo index manifests/ir.toml | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root ir 1.0.0
  crates (3):
    i 1.0.0 [net,o]
    ir 1.0.0
    o 1.0.0 [extra]
  encoded solution: 12 core nodes (3 crate versions encoded)
  parent edges: 2
  loaded: 3 crates, 3 versions

Where dep:o names the dependency there is no implicit feature o to enable,
and i3 is resolved with net alone:

  $ ../../../src/main.exe cargo index manifests/ir3.toml | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root ir3 1.0.0
  crates (3):
    i3 1.0.0 [net]
    ir3 1.0.0
    o 1.0.0 [extra]
  encoded solution: 11 core nodes (3 crate versions encoded)
  parent edges: 2
  loaded: 3 crates, 3 versions

Which of two crates keeps its newest version, when one pins the other, is
settled by the order cargo activates them in (core/resolver/mod.rs,
activate_deps_loop).  cp 0.1.7 pins ga to =0.14.7 where 0.1.6 takes ^0.14.4.
pa declares ga before cp, both with two candidates, and cargo takes a
crate's dependencies fewest candidates first and in declaration order
between equals: ga is activated at 0.14.9, cp 0.1.7 then fails on its pin,
and cp falls back to 0.1.6.

  $ ../../../src/main.exe cargo index manifests/oa.toml | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root oa 1.0.0
  crates (4):
    cp 0.1.6
    ga 0.14.9
    oa 1.0.0
    pa 1.0.0
  encoded solution: 13 core nodes (6 crate versions encoded)
  parent edges: 4
  loaded: 4 crates, 6 versions

pb declares zp, a copy of cp, first, so zp 0.1.7 is activated first and its
pin, with one candidate, is taken before pb's own ^0.14 of ga.

  $ ../../../src/main.exe cargo index manifests/ob.toml | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root ob 1.0.0
  crates (4):
    ga 0.14.7
    ob 1.0.0
    pb 1.0.0
    zp 0.1.7
  encoded solution: 13 core nodes (6 crate versions encoded)
  parent edges: 4
  loaded: 4 crates, 6 versions

The root's own dependencies are read from its manifest, whose tables cargo
keys by name, so oc's zp-then-ga reaches the resolver as ga-then-zp.

  $ ../../../src/main.exe cargo index manifests/oc.toml | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root oc 1.0.0
  crates (3):
    ga 0.14.9
    oc 1.0.0
    zp 0.1.6
  encoded solution: 10 core nodes (5 crate versions encoded)
  parent edges: 3
  loaded: 3 crates, 5 versions

Resolver v3 ranks the candidate versions of a dependency, not their
classes (version_prefs.rs, sort_summaries), and skips a candidate whose
class is already activated at another version (RemainingCandidates::next).
ms activates sk 0.5.10 through its pin; mq's >=0.5, <0.7 then meets the
compatible 0.5.9, which that activation rules out, and takes the newest of
the rest, 0.6.5, although it needs a newer Rust than 1.70.

  $ ../../../src/main.exe cargo index manifests/ms.toml --rust-version 1.70 | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root ms 1.0.0 for rust 1.70
  crates (4):
    mq 1.0.0
    ms 1.0.0
    sk 0.5.10
    sk 0.6.5
  encoded solution: 12 core nodes (5 crate versions encoded)
  parent edges: 3
  loaded: 3 crates, 5 versions

mu pins sl to 0.6.5, which needs 1.80, so mt's range skips the compatible
0.6.4 of that class and takes the compatible 0.5.9 of the older one.

  $ ../../../src/main.exe cargo index manifests/mu.toml --rust-version 1.70 | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root mu 1.0.0 for rust 1.70
  crates (4):
    mt 1.0.0
    mu 1.0.0
    sl 0.5.9
    sl 0.6.5
  encoded solution: 12 core nodes (5 crate versions encoded)
  parent edges: 3
  loaded: 3 crates, 5 versions

A candidate one of whose mandatory dependencies has no valid candidate
left is passed over, as cargo passes it over after activating it and
failing at once on that dependency.  dz pins sp to 1.0.0, and each zk pins
sp to its own version, so zk's newest two are dead on arrival: the solve
takes zk 1.0.0 without a single conflict, where learning it would cost
one per version, since each version's slot is its own name.

  $ ../../../src/main.exe cargo index manifests/dz.toml | grep -E '^  (sp|zk) '
    sp 1.0.0
    zk 1.0.0
  $ ../../../src/main.exe cargo index manifests/dz.toml --debug | grep -c '^conflict resolution'
  0
  [1]

The dependency can die a step further down.  Each zj past 1.0.0 pins ae
0.10.3, whose own range for sb misses the 2.6.1 dy pins, so a zj taking
ae has one candidate for it and that candidate is dead: the chain of
forced candidates is followed, and zj 1.0.0 is again reached without a
conflict.

  $ ../../../src/main.exe cargo index manifests/dy.toml | grep -E '^  (ae|sb|zj) '
    sb 2.6.1
    zj 1.0.0
  $ ../../../src/main.exe cargo index manifests/dy.toml --debug | grep -c '^conflict resolution'
  0
  [1]

And the dependency that dies can be an optional one the features asked of
the candidate turn on.  dx asks tr for url, which in tr 1.1.0 enables sb
at a range the pinned 2.6.1 misses, so tr 1.0.0 is taken, again without a
conflict.

  $ ../../../src/main.exe cargo index manifests/dx.toml | grep -E '^  (sb|tr) '
    sb 2.6.1
    tr 1.0.0 [url]
  $ ../../../src/main.exe cargo index manifests/dx.toml --debug | grep -c '^conflict resolution'
  0
  [1]

A dependency with several valid candidates dies when every one of them
does.  xw 1.1.0 needs zv, and each zv needs sb at a range the pinned 2.6.1
misses, so xw 1.1.0 is passed over for 1.0.0, again without a conflict.

  $ ../../../src/main.exe cargo index manifests/dw.toml | grep -E '^  (sb|xw|zv) '
    sb 2.6.1
    xw 1.0.0
  $ ../../../src/main.exe cargo index manifests/dw.toml --debug | grep -c '^conflict resolution'
  0
  [1]

Where every candidate is dead the versions can only be refuted, one per
backjump, and cargo's order reaches the dependency again after each only
behind everything queued ahead of it.  dv takes sb 2.6.1 before t1, t2 and
t3, and only then zj, whose versions both need ae 0.10.3 and so sb below
2.5.  Refuting it costs whole replays of the queue, not the answer: cargo,
backtracking into its saved frame, lands on sb 2.4.1 too.
zj 1.1.0 and 1.2.0 are one class declaring ae alike, so they share one
slot, and the conflict learned against it refutes both at once.

  $ ../../../src/main.exe cargo index manifests/dv.toml | grep -E '^  (ae|sb|zj) '
    ae 0.10.3
    sb 2.4.1
    zj 1.2.0
  $ ../../../src/main.exe cargo index manifests/dv.toml --debug | grep -c '^deciding on'
  72

A root Cargo.toml of its own.  app takes s under [dependencies], e under
the key x through package = "e", the optional i with its default
features off, m as a dev-dependency, and e again for cfg(windows); its
feature net asks i for net.  The lock enables every root feature, so i
comes in through net, with o behind i's own net, and e is locked at both
0.1.0 (for x) and 0.2.0.

  $ ../../../src/main.exe cargo index manifests/app.toml --print-parents | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root app 0.1.0
  crates (9):
    app 0.1.0 [default,i,net]
    e 0.1.0
    e 0.2.0
    i 1.0.0 [net,o]
    m 1.0.0
    o 1.0.0 [extra]
    s 1.0.0
    u 1.0.0 [cap,default]
    w 1.0.0 [extra]
  encoded solution: 36 core nodes (9 crate versions encoded)
  parent edges: 8
  parent-edges:
    app 0.1.0 -> e(e) 0.2.0
    app 0.1.0 -> i(i) 1.0.0
    app 0.1.0 -> m(m) 1.0.0
    app 0.1.0 -> s(s) 1.0.0
    app 0.1.0 -> x(e) 0.1.0
    i 1.0.0 -> o(o) 1.0.0
    s 1.0.0 -> u(u) 1.0.0
    u 1.0.0 -> w(w) 1.0.0
  loaded: 8 crates, 8 versions

A dev-dependency that depends back on the root reaches the root's own
name and version through the registry.  The model has one node there;
cargo keeps two packages, the path root and the registry's b, unless a
[patch] maps the name to the root, so pac refuses the first manifest and
answers the second.

  $ ../../../src/main.exe cargo index manifests/selfdep.toml > /dev/null
  error: the answer reaches b 1.0.0 through the registry, which cargo keeps apart from the root unless [patch.crates-io] maps b to it with { path = "." }
  [2]
  $ ../../../src/main.exe cargo index manifests/selfpatch.toml --print-parents | sed -E '/^(parse|solve) [0-9.]+s$/d'
  root b 1.0.0
  crates (6):
    a 1.0.0
    b 1.0.0
    c 1.0.0
    d 1.0.0 [a,f]
    d 2.0.0 [b,f]
    f 1.0.0 [c,d]
  encoded solution: 28 core nodes (6 crate versions encoded)
  parent edges: 7
  parent-edges:
    a 1.0.0 -> b(b) 1.0.0
    a 1.0.0 -> c(c) 1.0.0
    b 1.0.0 -> a(a) 1.0.0
    b 1.0.0 -> d(d) 1.0.0
    c 1.0.0 -> d(d) 2.0.0
    d 1.0.0 -> f(f) 1.0.0
    d 2.0.0 -> f(f) 1.0.0
  loaded: 5 crates, 6 versions

Sources and patches the model does not cover are refused rather than
dropped:

  $ ../../../src/main.exe cargo index manifests/pathdep.toml
  error: dependencies.m: a path source is not a registry crate, and only the registry is modelled
  [2]
  $ ../../../src/main.exe cargo index manifests/otherpatch.toml
  error: [patch.crates-io] m: the only patch modelled maps the root's own name to the root, { path = "." }
  [2]
