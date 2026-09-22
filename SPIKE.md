# Spike: apk's undocumented bare-provides clauses, with support

This branch is evidence, not a proposal for main.  It asks whether the
calculus can match what apk does, beyond what `apk-package(5)` documents,
when it selects an unversioned `p:` provide whose owner has no `k:`.

## What apk does

`is_provider_auto_selectable` (`solver.c:339-345`) accepts such a provider
once its owner's own name has a requirer.  A package selected for another
reason also satisfies the bare name: `assign_name` gives it every name it
provides.  That covers selection through a versioned provide and through
its own install_if.  Main encodes only the documented rule (`k:` ≠ 0, or
the world names the owner).

Read as a check on the final set, the wider rule overreaches.  For world
`pv-user`, the set `{pv-user, pv-prov, pv-both}` passes it, because
`pv-both` depends on `pv-prov`.  apk refuses that query, and `apk fix`
rejects the same set as installed state.  `pv-both` is there only to act
as a requirer.

## What was tried

`theories/Alpine.v`, `IsResolution`:

- `MatchReq` (positive dependencies) accepts a bare provider `q` when
  `AutoSelectable I S q` holds.  That means one of: `k:` ≠ 0; the root or
  a package in S depends positively on `q`'s own name; the same for a name
  `q` provides with a version; or `q`'s own install_if conditions hold in S.
- `res_support`: every package in S ∩ `inst_supp` is `Supported`.  The
  root offers it, a package in S has a positive dependency it offers, or
  its own install_if holds.  "Offers" means by name and version, by a
  versioned provide, or by a bare provide with `k:` ≠ 0.  This is the
  local (Clark completion) form.  Packages that only lead to each other
  still pass: loops are not excluded.

The encoding needs no new machinery:

- Each bare provider's alternatives are `q` alone, or `r ∧ q` per
  requirer `r`, or `conditions ∧ q` per install_if rule (`selectableAlts`).
- A package in `inst_supp` depends on the disjunction of its supporters
  (`supportForm`).  That disjunction is empty (an empty version set) when
  nothing can lead to the package, and absent when the world or a vacuous
  rule already does.

For `pv-user`, with `inst_supp ⊇ {pv-both, pv-mid}`:

- `pv-user` depends on `pv-virt`, encoded as `(pv-both ∧ pv-prov) ∨ (pv-mid ∧ pv-prov) ∨ pv-virt∅`.
- `pv-both` depends on its supporters, which are empty, so it gets `pv-both∅`.
- `pv-mid` likewise gets `pv-mid∅`.

The result is unsatisfiable, as in apk.

`inst_supp` is data the frontend chooses:

- **Restricted (the default):** the requirers and install_if-condition
  providers that could make a provider without `k:` selectable, closed
  under "could lead to", i.e. reverse dependencies and the condition
  providers of their install_if.  On this snapshot that is one package,
  `nagios-plugins-all`.
- **`PAC_SUPPORT_ALL=1`:** every package.

Soundness and completeness hold for any `inst_supp`.  That the restricted
set is enough to stop a requirer being added only to serve is argued, not
proved.  A supporter demanded of a member is a reverse dependency or a
condition provider of it, so it is a member too.  Every other package
enters S only through a dependency or trigger of something already there.

## What it showed

- **Fixture `test/frontends/alpine.t/BARE`:**
  - `pv-prov pv-user`, `pv-both`, `pv-user pv-mid`, `al-user` and
    `ii-anchor ii-user` install what apk installs.
  - `pv-user` and `ii-user` are unsatisfiable, as in apk.
  - Loops: `cy-user` installs `{cy-prov, cy-user, cy-x}`, as apk does.
    `c2-user` installs `{c2-a, c2-user, c2-x}`, which apk refuses (the
    `c2`/`cy` inconsistency is apk's own).
- **Proofs:** `alpine_soundness`, `alpine_completeness`,
  `dependees_lookupOrig/Root/Prov`, `versions_lookupName` and the new
  `selectableAlts_lookup` all go through.  `dune build @axioms`:
  261/261 axiom-free.
- **Correspondence and validity:** 59/59 and 59/59 with the restricted
  `inst_supp`, and the same with `PAC_SUPPORT_ALL` (validity is the
  installed-state `apk fix` check).
- **Timings** (iphito, 59 goals, 8 in parallel, sum of per-goal solve
  times):

  | encoding | total solve | worst goal | answers |
  |---|---|---|---|
  | documented rule | 0.44 s | 0.03 s | — |
  | support, restricted `inst_supp` | 0.72 s | 0.04 s | unchanged |
  | support, every package (`PAC_SUPPORT_ALL`) | 2545 s | 47.9 s (gvim) | unchanged |

  With every package, each goal whose solution contains `musl` without
  the world naming it pays about 45 s.  `musl` has 2152 supporters in this
  index; `perl` has 438, `pkgconf` 398, `libstdc++` 330, and 3634 of the
  5542 packages have none.  A disjunction's synthetic package is named by
  all of its alternatives, so every set operation on the 2152 edges out of
  it compares that name structurally, which makes the cost quadratic in
  the width.  Measured on `dhcpcd`, `musl` alone takes: `reduceDeps` 1.0 s,
  `reduceReal` 8.1 s, and the driver's edge and version bookkeeping 13 s,
  plus PubGrub over a 2152-version name.

## Reproduce

- Fixture:

      dune build @runtest

  `test/frontends/alpine.t/run.t` holds the stanzas.
- Axioms:

      dune build @axioms

- Sweeps: inside `nix develop path:<abs>/nix`, run
  `eval/alpine/setup.sh <root>`, then:

      APKROOT=<root> eval/alpine/sweep.sh <exe> <tag>
      APKROOT=<root> eval/alpine/valid.sh <exe> <tag>

  Set `PAC_SUPPORT_ALL=1` for the unrestricted encoding.
- Timings: run `main.exe alpine repos/alpine/APKINDEX <goal>` and read its
  `solve` line.
