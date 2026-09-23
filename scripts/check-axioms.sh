#!/usr/bin/env sh
# Every reduction product and every theorem the artifact claims must be
# axiom-free: the products are what extraction compiles, and a theorem
# resting on an Admitted lemma would be a claim nothing backs.  The audit
# list below is the only thing to edit when a theorem is added; the
# expected count is derived from it.
#
# Names are qualified through the nat instantiations: Smoke.v supplies
# one per functor, Npm.v supplies its own (NpmS) since Smoke.v has none,
# and Semver has no instance of its own because Cargo Includes it, so its
# range language is audited through Cgo.
set -e
# Resolved before the cd below, since dune passes it relative to the
# directory the action runs in.
theories=$(cd "${PAC_THEORIES:-.}" && pwd)
cd "${PAC_ROOT:-$(dirname "$0")/..}"
[ -n "${PAC_THEORIES:-}" ] || theories="$PWD/_build/default/theories"

command -v coqtop >/dev/null 2>&1 || {
  echo "FAIL: coqtop not on PATH (eval \$(opam env) first)"; exit 1; }


names=$(sed -e 's/#.*//' -e '/^[[:space:]]*$/d' <<'LIST'
# core: merge and its resolution characterisation
C.Merge.merge
C.Merge.merge_functionalInName
C.Merge.merge_resolution_iff
C.Merge.mergedVS
C.dependees
C.versions

# versions: the version-formula reduction and its glue
Ver.Reduction.Lookup.dependees_lookup
Ver.Reduction.Lookup.reduce_glue
Ver.Reduction.Lookup.versions_lookup
Ver.Reduction.reduce
Ver.Reduction.version_formula_correct

# conflicts
Cfl.Reduction.Lookup.dependees_lookupOrig
Cfl.Reduction.Lookup.dependees_lookupSynthetic
Cfl.Reduction.Lookup.versions_lookupOrig
Cfl.Reduction.Lookup.versions_lookupSynthetic
Cfl.Reduction.conflictResolution
Cfl.Reduction.conflict_completeness
Cfl.Reduction.conflict_soundness
Cfl.Reduction.reduce
Cfl.Reduction.reduceDeps
Cfl.Reduction.reduceReal

# concurrent versions
Conc.Reduction.Lookup.dependees_lookupGranular
Conc.Reduction.Lookup.dependees_lookupGranularGran
Conc.Reduction.Lookup.dependees_lookupIntermediate
Conc.Reduction.Lookup.dependees_lookupIntermediateOrig
Conc.Reduction.Lookup.versions_lookupGranular
Conc.Reduction.Lookup.versions_lookupIntermediate
Conc.Reduction.concurrentResolution
Conc.Reduction.concurrent_completeness
Conc.Reduction.concurrent_soundness
Conc.Reduction.reduceDeps
Conc.Reduction.reduceDepsDirect
Conc.Reduction.reduceDepsEmpty
Conc.Reduction.reduceDepsSplitEntry
Conc.Reduction.reduceDepsSplitFanout
Conc.Reduction.reduceReal

# peer dependencies
Peer.Reduction.Lookup.dependees_lookupGranular
Peer.Reduction.Lookup.dependees_lookupIntermediate
Peer.Reduction.Lookup.dependees_lookupIntermediateGran
Peer.Reduction.Lookup.versions_lookupGranular
Peer.Reduction.Lookup.versions_lookupIntermediate
Peer.Reduction.peer_completeness
Peer.Reduction.peer_soundness
Peer.Reduction.reduceDeps
Peer.Reduction.reduceDepsDepToInt
Peer.Reduction.reduceDepsIntToDep
Peer.Reduction.reduceDepsPeer
Peer.Reduction.reduceReal
Peer.Reduction.reduceRealIntermediate
Peer.Reduction.reduceRealPeer

# dependency visibility
Vis.Reduction.Lookup.depBlocks
Vis.Reduction.Lookup.dependees_lookupAgreement
Vis.Reduction.Lookup.dependees_lookupIntermediate
Vis.Reduction.Lookup.dependees_lookupOccurrence
Vis.Reduction.Lookup.versions_lookupAgreement
Vis.Reduction.Lookup.versions_lookupIntermediate
Vis.Reduction.Lookup.versions_lookupOccurrence
Vis.Reduction.reduceDeps
Vis.Reduction.reduceDepsIntToAgr
Vis.Reduction.reduceDepsIntToOcc
Vis.Reduction.reduceDepsOccToInt
Vis.Reduction.reduceDepsSelf
Vis.Reduction.reduceReal
Vis.Reduction.reduceRealAgreement
Vis.Reduction.reduceRealIntermediate
Vis.Reduction.reduceRealOccurrence
Vis.Reduction.visibility_completeness
Vis.Reduction.visibility_soundness

# features
Feat.Reduction.Lookup.dependees_lookupFeatPkg
Feat.Reduction.Lookup.dependees_lookupOrig
Feat.Reduction.Lookup.versions_lookupFeatPkg
Feat.Reduction.Lookup.versions_lookupOrig
Feat.Reduction.feature_completeness
Feat.Reduction.feature_soundness
Feat.Reduction.reduceDeps
Feat.Reduction.reduceReal

# virtual packages
Virt.Reduction.Lookup.dependees_lookupOrig
Virt.Reduction.Lookup.dependees_lookupSelector
Virt.Reduction.Lookup.versions_lookupOrig
Virt.Reduction.Lookup.versions_lookupSelector
Virt.Reduction.reduceDeps
Virt.Reduction.reduceReal
Virt.Reduction.selectorVersions
Virt.Reduction.virtual_completeness
Virt.Reduction.virtual_soundness

# package formulas
PkgF.Reduction.Lookup.dependees_lookupDisjunct
PkgF.Reduction.Lookup.dependees_lookupNegDep
PkgF.Reduction.Lookup.dependees_lookupOrig
PkgF.Reduction.Lookup.subInstanceOrig
PkgF.Reduction.Lookup.versions_lookupDisjunct
PkgF.Reduction.Lookup.versions_lookupNegDep
PkgF.Reduction.Lookup.versions_lookupOrig
PkgF.Reduction.package_formula_completeness
PkgF.Reduction.package_formula_soundness
PkgF.Reduction.reduceDeps
PkgF.Reduction.reduceReal

# variable formulas
VarF.Reduction.Lookup.dependees_lookupDisjunct
VarF.Reduction.Lookup.dependees_lookupNegDep
VarF.Reduction.Lookup.dependees_lookupOrig
VarF.Reduction.Lookup.dependees_lookupVar
VarF.Reduction.Lookup.subInstanceOrig
VarF.Reduction.Lookup.versions_lookupDisjunct
VarF.Reduction.Lookup.versions_lookupNegDep
VarF.Reduction.Lookup.versions_lookupOrig
VarF.Reduction.Lookup.versions_lookupVar
VarF.Reduction.extractAssignment
VarF.Reduction.reduceDeps
VarF.Reduction.reduceReal
VarF.Reduction.variable_formula_completeness
VarF.Reduction.variable_formula_soundness

# features composed with concurrency
FC.Reduction.Lookup.dependees_lookupGranularFeatPkg
FC.Reduction.Lookup.dependees_lookupGranularOrig
FC.Reduction.Lookup.dependees_lookupIntermediate
FC.Reduction.Lookup.dependees_lookupIntermediateA
FC.Reduction.Lookup.dependees_lookupIntermediateF
FC.Reduction.feature_concurrent_completeness
FC.Reduction.feature_concurrent_soundness
FC.Reduction.reduceDeps
FC.Reduction.reduceReal

# debian
Deb.Lookup.dependees_lookupDisjunct
Deb.Lookup.dependees_lookupGuard
Deb.Lookup.dependees_lookupOrig
Deb.Lookup.dependees_lookupSelector
Deb.Lookup.dependees_lookupSelectorAgree
Deb.Lookup.dependees_lookupSoft
Deb.Lookup.versions_lookupDisjunct
Deb.Lookup.versions_lookupGuard
Deb.Lookup.versions_lookupOrig
Deb.Lookup.versions_lookupSelector
Deb.Lookup.versions_lookupSelectorAgree
Deb.Lookup.versions_lookupSoft
Deb.debianResolution_coreResolution
Deb.debian_completeness
Deb.debian_soundness
Deb.dependees
Deb.matchb
Deb.reduceDeps
Deb.reduceReal
Deb.versions
Deb.versionsDisj
Deb.versionsSoft

# debian multiarch
DMA.Lookup.dependees_lookupDisjunctMA
DMA.Lookup.dependees_lookupGuardMA
DMA.Lookup.dependees_lookupOrigMA
DMA.Lookup.dependees_lookupSelectorAgreeMA
DMA.Lookup.dependees_lookupSelectorMA
DMA.Lookup.dependees_lookupSelectorRecMA
DMA.Lookup.dependees_lookupSoftMA
DMA.Lookup.versions_lookupDisjunctMA
DMA.Lookup.versions_lookupGuardMA
DMA.Lookup.versions_lookupGuardMA_pseudo
DMA.Lookup.versions_lookupOrigMA
DMA.Lookup.versions_lookupOrigMA_pseudo
DMA.Lookup.versions_lookupSelectorAgreeMA
DMA.Lookup.versions_lookupSelectorMA
DMA.Lookup.versions_lookupSelectorRecMA
DMA.Lookup.versions_lookupSoftMA
DMA.debian_ma_completeness
DMA.debian_ma_core_completeness
DMA.debian_ma_core_soundness
DMA.debian_ma_soundness
DMA.multiarchResolution_core
DMA.multiarchResolution_reduceReal
DMA.reduceAtom
DMA.reduceClause
DMA.reduceConf
DMA.reduceConfEntry
DMA.reduceDeps
DMA.reduceProv
DMA.reduceProvEntry
DMA.reduceRec
DMA.reduceReal

# opam
Op.depextsOf
Op.mem_depextsOf
Op.Reduction.clsForms
Op.Reduction.clsPkgs
Op.Reduction.clsSel
Op.Reduction.clsVersions
Op.Reduction.decodeS
Op.Reduction.dependees
Op.Reduction.dependeesBy
Op.Reduction.dependees_lookupReal
Op.Reduction.dependees_lookupRoot
Op.Reduction.encR
Op.Reduction.encodeOF
Op.Reduction.opam_completeness
Op.Reduction.opam_soundness
Op.Reduction.rootPkg
Op.Reduction.srcVersions
Op.Reduction.transD
Op.Reduction.transR
Op.Reduction.transS
Op.Reduction.versSetBy
Op.Reduction.versions
Op.Reduction.versions_lookupCls
Op.Reduction.versions_lookupReal

# cargo, and the semver range language it Includes
Cgo.Lookup.claimants
Cgo.Lookup.dependees_lookup
Cgo.Lookup.dependees_lookupCrate
Cgo.Lookup.dependees_lookupCrateSub
Cgo.Lookup.dependees_lookupDecision
Cgo.Lookup.dependees_lookupDecisionSub
Cgo.Lookup.dependees_lookupFeatP
Cgo.Lookup.dependees_lookupFeatPSub
Cgo.Lookup.dependees_lookupInert
Cgo.Lookup.dependees_lookupRoot
Cgo.Lookup.dependees_lookupRootSub
Cgo.Lookup.dependees_lookupSlot
Cgo.Lookup.dependees_lookupSlotSub
Cgo.Lookup.dependees_lookupSub
Cgo.Lookup.fdefFibre
Cgo.Lookup.owner
Cgo.Lookup.reads
Cgo.Lookup.realPreimage
Cgo.Lookup.supportPreimage
Cgo.Lookup.versions_lookupCrate
Cgo.Lookup.versions_lookupCrateSub
Cgo.Lookup.versions_lookupDecision
Cgo.Lookup.versions_lookupDecisionSub
Cgo.Lookup.versions_lookupFeatP
Cgo.Lookup.versions_lookupFeatPSub
Cgo.Lookup.versions_lookupLink
Cgo.Lookup.versions_lookupLinkSub
Cgo.Lookup.versions_lookupRoot
Cgo.Lookup.versions_lookupRootSub
Cgo.Lookup.versions_lookupSlot
Cgo.Lookup.versions_lookupSlotSub
Cgo.cargo_completeness
Cgo.cargo_soundness
Cgo.coreRes
Cgo.csAdmits
Cgo.csHolds
Cgo.decodeFS
Cgo.decodeParents
Cgo.decodeS
Cgo.dependees
Cgo.evalReq
Cgo.rangeEval
Cgo.rgHolds
Cgo.srcVersions
Cgo.transDeps
Cgo.transReal
Cgo.versions

# alpine
Alp.Reduction.Lookup.dependees_lookupOrig
Alp.Reduction.Lookup.dependees_lookupProv
Alp.Reduction.Lookup.dependees_lookupRoot
Alp.Reduction.Lookup.versions_lookupName
Alp.Reduction.alpine_completeness
Alp.Reduction.alpine_soundness
Alp.Reduction.attachAt
Alp.Reduction.dependees
Alp.Reduction.encReq
Alp.Reduction.installIfFibre
Alp.Reduction.installIfForm
Alp.Reduction.matchPos_attachAt
Alp.Reduction.match_req_decode
Alp.Reduction.match_req_transS
Alp.Reduction.rootPkg
Alp.Reduction.transD
Alp.Reduction.transR
Alp.Reduction.versions

# npm
NpmS.Reduction.Lookup.dependees_lookupGran
NpmS.Reduction.Lookup.dependees_lookupInt
NpmS.Reduction.Lookup.versions_lookupGran
NpmS.Reduction.Lookup.versions_lookupInt
NpmS.Reduction.dependees
NpmS.Reduction.npm_completeness
NpmS.Reduction.npm_soundness
NpmS.Reduction.peer_installed
NpmS.Reduction.transD
NpmS.Reduction.transR
NpmS.Reduction.transRoot
NpmS.Reduction.versions
NpmS.rootPkg
LIST
)

expected=$(printf '%s\n' "$names" | grep -c .)

# An installed copy under _opam is on coqtop's default load path and goes
# stale; an absolute -R is what keeps this reading the build tree.
out=$({ printf 'From PackageCalculus Require Import Smoke Npm.\n'
        printf '%s\n' "$names" | sed -e 's/^/Print Assumptions /' \
                                      -e 's/$/./'; } \
      | coqtop -q -R "$theories" PackageCalculus 2>&1)

if printf '%s\n' "$out" | grep -q 'Error'; then
  printf '%s\n' "$out" | grep -A3 'Error'
  echo "FAIL: a name in the audit list no longer resolves"
  exit 1
fi

closed=$(printf '%s\n' "$out" | grep -c 'Closed under the global context' \
         || true)
echo "axiom-free: $closed/$expected"

if [ "$closed" -ne "$expected" ]; then
  # Print Assumptions emits one block per name, in order, so the block's
  # position in the output is the name that failed.
  tmp=$(mktemp)
  printf '%s\n' "$names" > "$tmp"
  printf '%s\n' "$out" \
    | awk 'NR==FNR { n[++k] = $0; next }
           /Closed under the global context/ { i++; next }
           /Axioms:/ { i++; print "NOT CLOSED: " n[i] }' "$tmp" -
  rm -f "$tmp"
  printf '%s\n' "$out" | grep -A4 'Axioms:'
  echo "FAIL: a product or theorem depends on an axiom"
  exit 1
fi
echo ok
