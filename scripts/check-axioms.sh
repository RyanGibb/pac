#!/usr/bin/env sh
# Every reduction product and every theorem the artifact claims must be
# axiom-free: the products are what extraction compiles, and a theorem
# resting on an Admitted lemma would be a claim nothing backs.  The audit
# list below is the only thing to edit when a theorem is added; the
# expected count is derived from it.
#
# Names are qualified through the nat instantiations Smoke.v supplies, one
# per functor.  Semver has no instance of its own because Cargo Includes
# it, so its range language is audited through Smoke's Cargo.
set -e
# Resolved before the cd below, since dune passes it relative to the
# directory the action runs in.
theories=
[ -z "${PAC_THEORIES:-}" ] || theories=$(cd "$PAC_THEORIES" && pwd)
cd "${PAC_ROOT:-$(dirname "$0")/..}"
[ -n "$theories" ] || theories="$PWD/_build/default/theories"

command -v coqtop >/dev/null 2>&1 || {
  echo "FAIL: coqtop not on PATH (eval \$(opam env) first)"; exit 1; }


names=$(sed -e 's/#.*//' -e '/^[[:space:]]*$/d' <<'LIST'
Core.Merge.merge
Core.Merge.merge_functionalInName
Core.Merge.merge_resolution_iff
Core.Merge.mergedVS
Core.check
Core.check_agree
Core.check_iff
Core.check_iff_sets
Core.check_resolution
Core.check_spec
Core.dependees
Core.namePreimage
Core.versions

Complexity.Encoding.satEncoding
Complexity.Encoding.sat_encoding_completeness
Complexity.Encoding.sat_encoding_soundness
Complexity.Reduction.assignment
Complexity.Reduction.coreResolution
Complexity.Reduction.reduceDeps
Complexity.Reduction.reduceDeps_functionalInName
Complexity.Reduction.reduceReal
Complexity.Reduction.three_sat_completeness
Complexity.Reduction.three_sat_correct
Complexity.Reduction.three_sat_soundness

VersionFormula.Reduction.Lookup.dependees_lookup
VersionFormula.Reduction.Lookup.reduce_glue
VersionFormula.Reduction.Lookup.versions_lookup
VersionFormula.Reduction.reduce
VersionFormula.Reduction.version_formula_correct

Conflict.Reduction.Lookup.dependees_lookupAbsent
Conflict.Reduction.Lookup.dependees_lookupOrig
Conflict.Reduction.Lookup.versions_lookupOrig
Conflict.Reduction.conflictResolution
Conflict.Reduction.conflict_completeness
Conflict.Reduction.conflict_retraction
Conflict.Reduction.conflict_soundness
Conflict.Reduction.reduceDeps
Conflict.Reduction.reduceReal

ConflictClass.Reduction.Lookup.classRelAt
ConflictClass.Reduction.Lookup.dependees_lookupClass
ConflictClass.Reduction.Lookup.dependees_lookupOrig
ConflictClass.Reduction.Lookup.inClass
ConflictClass.Reduction.Lookup.versions_lookupClass
ConflictClass.Reduction.Lookup.versions_lookupOrig
ConflictClass.Reduction.classPkgs
ConflictClass.Reduction.conflictClassResolution
ConflictClass.Reduction.conflict_class_completeness
ConflictClass.Reduction.conflict_class_retraction
ConflictClass.Reduction.conflict_class_soundness
ConflictClass.Reduction.coreResolution
ConflictClass.Reduction.reduceDeps
ConflictClass.Reduction.reduceReal

Concurrent.Reduction.Lookup.dependees_lookupGranular
Concurrent.Reduction.Lookup.dependees_lookupGranularGran
Concurrent.Reduction.Lookup.dependees_lookupIntermediate
Concurrent.Reduction.Lookup.dependees_lookupIntermediateOrig
Concurrent.Reduction.Lookup.versions_lookupGranular
Concurrent.Reduction.Lookup.versions_lookupIntermediate
Concurrent.Reduction.concurrentResolution
Concurrent.Reduction.concurrent_completeness
Concurrent.Reduction.concurrent_retraction
Concurrent.Reduction.concurrent_soundness
Concurrent.Reduction.reduceDeps
Concurrent.Reduction.reduceDepsDirect
Concurrent.Reduction.reduceDepsEmpty
Concurrent.Reduction.reduceDepsSplitEntry
Concurrent.Reduction.reduceDepsSplitFanout
Concurrent.Reduction.reduceReal

PeerDependency.Reduction.Lookup.dependees_lookupGranular
PeerDependency.Reduction.Lookup.dependees_lookupIntermediate
PeerDependency.Reduction.Lookup.dependees_lookupIntermediateGran
PeerDependency.Reduction.Lookup.versions_lookupGranular
PeerDependency.Reduction.Lookup.versions_lookupIntermediate
PeerDependency.Reduction.peer_completeness
PeerDependency.Reduction.peer_retraction
PeerDependency.Reduction.peer_soundness
PeerDependency.Reduction.reduceDeps
PeerDependency.Reduction.reduceDepsDepToInt
PeerDependency.Reduction.reduceDepsIntToDep
PeerDependency.Reduction.reduceDepsPeer
PeerDependency.Reduction.reduceReal
PeerDependency.Reduction.reduceRealIntermediate
PeerDependency.Reduction.reduceRealPeer

Visibility.Reduction.Lookup.dependees_lookupAgreement
Visibility.Reduction.Lookup.dependees_lookupIntermediate
Visibility.Reduction.Lookup.dependees_lookupOccurrence
Visibility.Reduction.Lookup.versions_lookupAgreement
Visibility.Reduction.Lookup.versions_lookupIntermediate
Visibility.Reduction.Lookup.versions_lookupOccurrence
Visibility.Reduction.reduceDeps
Visibility.Reduction.reduceDepsIntToAgr
Visibility.Reduction.reduceDepsIntToOcc
Visibility.Reduction.reduceDepsOccToInt
Visibility.Reduction.reduceDepsSelf
Visibility.Reduction.reduceReal
Visibility.Reduction.reduceRealAgreement
Visibility.Reduction.reduceRealIntermediate
Visibility.Reduction.reduceRealOccurrence
Visibility.Reduction.visibility_completeness
Visibility.Reduction.visibility_retraction
Visibility.Reduction.visibility_soundness

Placement.index
Placement.mem_reachable
Placement.reachable
Placement.reachableBy
Placement.reachableBy_reachable
Placement.reaches_parented
Placement.reaches_restriction
Placement.walk
Placement.walkIx
Placement.walkIx_index
Placement.Reduction.Lookup.dependees_lookupAbsent
Placement.Reduction.Lookup.dependees_lookupLoc
Placement.Reduction.Lookup.dependees_lookupRoot
Placement.Reduction.Lookup.dependees_lookupWalk
Placement.Reduction.Lookup.versions_lookupLoc
Placement.Reduction.Lookup.versions_lookupRoot
Placement.Reduction.Lookup.versions_lookupWalk
Placement.Reduction.coreResolution
Placement.Reduction.dependees
Placement.Reduction.lookup_resolution
Placement.Reduction.placementResolution
Placement.Reduction.placement_completeness
Placement.Reduction.placement_retraction
Placement.Reduction.placement_soundness
Placement.Reduction.reached_reduceReal
Placement.Reduction.reduceDeps
Placement.Reduction.reduceReal
Placement.Reduction.versions

Feature.Reduction.Lookup.dependees_lookupFeatPkg
Feature.Reduction.Lookup.dependees_lookupOrig
Feature.Reduction.Lookup.versions_lookupFeatPkg
Feature.Reduction.Lookup.versions_lookupOrig
Feature.Reduction.feature_completeness
Feature.Reduction.feature_retraction
Feature.Reduction.feature_soundness
Feature.Reduction.reduceDeps
Feature.Reduction.reduceReal

Virtual.Reduction.Lookup.dependees_lookupOrig
Virtual.Reduction.Lookup.dependees_lookupSelector
Virtual.Reduction.Lookup.versions_lookupOrig
Virtual.Reduction.Lookup.versions_lookupSelector
Virtual.Reduction.reduceDeps
Virtual.Reduction.reduceReal
Virtual.Reduction.selectorVersions
Virtual.Reduction.virtual_completeness
Virtual.Reduction.virtual_retraction
Virtual.Reduction.virtual_soundness

PackageFormula.Reduction.Lookup.dependees_lookupAbsent
PackageFormula.Reduction.Lookup.dependees_lookupDisjunct
PackageFormula.Reduction.Lookup.dependees_lookupDisjunctBy
PackageFormula.Reduction.Lookup.dependees_lookupOrig
PackageFormula.Reduction.Lookup.dependees_lookupOrigBy
PackageFormula.Reduction.Lookup.versions_lookupDisjunct
PackageFormula.Reduction.Lookup.versions_lookupOrig
PackageFormula.Reduction.Lookup.versions_lookupOrigPresent
PackageFormula.Reduction.formula_calculus_completeness
PackageFormula.Reduction.package_formula_retraction
PackageFormula.Reduction.package_formula_soundness
PackageFormula.Reduction.reduceDeps
PackageFormula.Reduction.reduceDepsBy
PackageFormula.Reduction.reduceReal
PackageFormula.package_formula_completeness

VariableFormula.Reduction.Lookup.dependees_lookupAbsent
VariableFormula.Reduction.Lookup.dependees_lookupDisjunct
VariableFormula.Reduction.Lookup.dependees_lookupDisjunctBy
VariableFormula.Reduction.Lookup.dependees_lookupOrig
VariableFormula.Reduction.Lookup.dependees_lookupOrigBy
VariableFormula.Reduction.Lookup.dependees_lookupVar
VariableFormula.Reduction.Lookup.versions_lookupDisjunct
VariableFormula.Reduction.Lookup.versions_lookupOrig
VariableFormula.Reduction.Lookup.versions_lookupVar
VariableFormula.Reduction.assignment
VariableFormula.Reduction.reduceDeps
VariableFormula.Reduction.reduceDepsBy
VariableFormula.Reduction.reduceReal
VariableFormula.Reduction.variable_formula_completeness
VariableFormula.Reduction.variable_formula_retraction
VariableFormula.Reduction.variable_formula_soundness

ConcurrentFeature.Reduction.Lookup.dependees_lookupGranularFeatPkg
ConcurrentFeature.Reduction.Lookup.dependees_lookupGranularOrig
ConcurrentFeature.Reduction.Lookup.dependees_lookupIntermediate
ConcurrentFeature.Reduction.Lookup.dependees_lookupIntermediateA
ConcurrentFeature.Reduction.Lookup.dependees_lookupIntermediateF
ConcurrentFeature.Reduction.Lookup.versions_lookupGranularFeatPkg
ConcurrentFeature.Reduction.Lookup.versions_lookupGranularOrig
ConcurrentFeature.Reduction.Lookup.versions_lookupIntermediate
ConcurrentFeature.Reduction.Lookup.versions_lookupIntermediateA
ConcurrentFeature.Reduction.Lookup.versions_lookupIntermediateF
ConcurrentFeature.Reduction.concurrent_feature_completeness
ConcurrentFeature.Reduction.concurrent_feature_retraction
ConcurrentFeature.Reduction.concurrent_feature_soundness
ConcurrentFeature.Reduction.reduceDeps
ConcurrentFeature.Reduction.reduceReal

Debian.Reduction.Lookup.dependees_lookupAbsent
Debian.Reduction.Lookup.dependees_lookupDisjunct
Debian.Reduction.Lookup.dependees_lookupOrig
Debian.Reduction.Lookup.dependees_lookupSelector
Debian.Reduction.Lookup.dependees_lookupSoft
Debian.Reduction.Lookup.versions_lookupDisjunct
Debian.Reduction.Lookup.versions_lookupOrig
Debian.Reduction.Lookup.versions_lookupSelector
Debian.Reduction.Lookup.versions_lookupSoft
Debian.Reduction.debian_completeness
Debian.Reduction.debian_retraction
Debian.Reduction.debian_soundness
Debian.Reduction.dependees
Debian.Reduction.matchb_nodeFibre
Debian.Reduction.reduceDeps
Debian.Reduction.reduceReal
Debian.Reduction.versions
Debian.Reduction.versionsDisj
Debian.Reduction.versionsSoft
Debian.matchb

MultiarchDebian.Reduction.Lookup.dependees_lookupDisjunct
MultiarchDebian.Reduction.Lookup.dependees_lookupOrig
MultiarchDebian.Reduction.Lookup.dependees_lookupSelector
MultiarchDebian.Reduction.Lookup.dependees_lookupSoft
MultiarchDebian.Reduction.Lookup.versions_lookupOrig
MultiarchDebian.Reduction.Lookup.versions_lookupOrig_pseudo
MultiarchDebian.Reduction.Lookup.versions_lookupSelector
MultiarchDebian.Reduction.Lookup.versions_lookupSoft
MultiarchDebian.Reduction.debian_ma_completeness
MultiarchDebian.Reduction.debian_ma_core_completeness
MultiarchDebian.Reduction.debian_ma_core_retraction
MultiarchDebian.Reduction.debian_ma_core_soundness
MultiarchDebian.Reduction.debian_ma_retraction
MultiarchDebian.Reduction.debian_ma_soundness
MultiarchDebian.Reduction.declConfOf
MultiarchDebian.Reduction.declProvOf
MultiarchDebian.Reduction.reduceAtom
MultiarchDebian.Reduction.reduceClause
MultiarchDebian.Reduction.reduceConf
MultiarchDebian.Reduction.reduceDeps
MultiarchDebian.Reduction.reduceInst
MultiarchDebian.Reduction.reduceProv
MultiarchDebian.Reduction.reduceReal
MultiarchDebian.Reduction.reduceRec

Opam.Reduction.Lookup.clsVersions_reduceReal
Opam.Reduction.Lookup.declarers
Opam.Reduction.Lookup.dependeesBy_lookupOrig
Opam.Reduction.Lookup.dependees_lookupClassCore
Opam.Reduction.Lookup.dependees_lookupDisjunctCore
Opam.Reduction.Lookup.dependees_lookupOrig
Opam.Reduction.Lookup.dependees_lookupOrigCore
Opam.Reduction.Lookup.dependees_lookupRoot
Opam.Reduction.Lookup.dependees_lookupRootCore
Opam.Reduction.Lookup.versions_class_mono
Opam.Reduction.Lookup.versions_lookupClass
Opam.Reduction.Lookup.versions_lookupClassCore
Opam.Reduction.Lookup.versions_lookupOrig
Opam.Reduction.Lookup.versions_lookupOrigCore
Opam.Reduction.Lookup.versions_lookupRootCore
Opam.Reduction.clsForms
Opam.Reduction.clsPkgs
Opam.Reduction.clsSel
Opam.Reduction.clsVersions
Opam.Reduction.coreResolution
Opam.Reduction.dependees
Opam.Reduction.dependeesBy
Opam.Reduction.encR
Opam.Reduction.encodeOF
Opam.Reduction.opamResolution
Opam.Reduction.opam_completeness
Opam.Reduction.opam_core_completeness
Opam.Reduction.opam_core_retraction
Opam.Reduction.opam_core_soundness
Opam.Reduction.opam_retraction
Opam.Reduction.opam_soundness
Opam.Reduction.reduceDeps
Opam.Reduction.reduceReal
Opam.Reduction.rootPkg
Opam.Reduction.srcVersions
Opam.Reduction.versSetBy
Opam.Reduction.versions
Opam.depextsOf
Opam.mem_depextsOf

Cargo.Reduction.Lookup.claimants
Cargo.Reduction.Lookup.dependees_lookupDecision
Cargo.Reduction.Lookup.dependees_lookupFeatP
Cargo.Reduction.Lookup.dependees_lookupGranular
Cargo.Reduction.Lookup.dependees_lookupRoot
Cargo.Reduction.Lookup.dependees_lookupSlot
Cargo.Reduction.Lookup.dependees_reduceDeps
Cargo.Reduction.Lookup.dependees_reduceDepsInert
Cargo.Reduction.Lookup.fdefFibre
Cargo.Reduction.Lookup.reads
Cargo.Reduction.Lookup.supportAt
Cargo.Reduction.Lookup.versions_cls_mono
Cargo.Reduction.Lookup.versions_lookupCls
Cargo.Reduction.Lookup.versions_lookupDecision
Cargo.Reduction.Lookup.versions_lookupFeatP
Cargo.Reduction.Lookup.versions_lookupGranular
Cargo.Reduction.Lookup.versions_lookupRoot
Cargo.Reduction.Lookup.versions_lookupSlot
Cargo.Reduction.Lookup.versions_reduceRealCls
Cargo.Reduction.Lookup.versions_reduceRealDecision
Cargo.Reduction.Lookup.versions_reduceRealFeatP
Cargo.Reduction.Lookup.versions_reduceRealGranular
Cargo.Reduction.Lookup.versions_reduceRealRoot
Cargo.Reduction.Lookup.versions_reduceRealSlot
Cargo.Reduction.cargoResolution
Cargo.Reduction.cargo_completeness
Cargo.Reduction.cargo_retraction
Cargo.Reduction.cargo_soundness
Cargo.Reduction.coreResolution
Cargo.Reduction.dependees
Cargo.Reduction.dependeesBy
Cargo.Reduction.evalReq
Cargo.Reduction.evalReqBy
Cargo.Reduction.features
Cargo.Reduction.linkRel
Cargo.Reduction.parents
Cargo.Reduction.reduceDeps
Cargo.Reduction.reduceReal
Cargo.Reduction.versions
Cargo.Reduction.versions_cls_reduceReal
Cargo.csAdmits
Cargo.csHolds
Cargo.rangeEval
Cargo.rgHolds

Alpine.Reduction.Lookup.dependees_lookupDisjunctCore
Alpine.Reduction.Lookup.dependees_lookupOrig
Alpine.Reduction.Lookup.dependees_lookupOrigCore
Alpine.Reduction.Lookup.dependees_lookupProv
Alpine.Reduction.Lookup.dependees_lookupProvCore
Alpine.Reduction.Lookup.dependees_lookupRoot
Alpine.Reduction.Lookup.dependees_lookupRootCore
Alpine.Reduction.Lookup.versions_lookupOrig
Alpine.Reduction.Lookup.versions_lookupOrigCore
Alpine.Reduction.Lookup.versions_lookupRootCore
Alpine.Reduction.alpine_completeness
Alpine.Reduction.alpine_core_completeness
Alpine.Reduction.alpine_core_retraction
Alpine.Reduction.alpine_core_soundness
Alpine.Reduction.alpine_retraction
Alpine.Reduction.alpine_soundness
Alpine.Reduction.attachAt
Alpine.Reduction.dependees
Alpine.Reduction.encReq
Alpine.Reduction.installIfFibre
Alpine.Reduction.installIfForm
Alpine.Reduction.match_attachAt
Alpine.Reduction.reduceDeps
Alpine.Reduction.reduceReal
Alpine.Reduction.req_coreResolution
Alpine.Reduction.req_decode
Alpine.Reduction.rootPkg
Alpine.Reduction.versions

Npm.Reduction.Lookup.dependees_lookupDesc
Npm.Reduction.Lookup.dependees_lookupGranular
Npm.Reduction.Lookup.dependees_lookupIntermediate
Npm.Reduction.Lookup.dependees_lookupLink
Npm.Reduction.Lookup.dependees_lookupSight
Npm.Reduction.Lookup.versions_lookupDesc
Npm.Reduction.Lookup.versions_lookupGranular
Npm.Reduction.Lookup.versions_intermediate_mono
Npm.Reduction.Lookup.versions_lookupIntermediate
Npm.Reduction.Lookup.versions_lookupLink
Npm.Reduction.Lookup.versions_lookupSight
Npm.Reduction.dependees
Npm.Reduction.dependees_reducedNames
Npm.Reduction.embedRoot
Npm.Reduction.lookup_resolution
Npm.Reduction.npm_completeness
Npm.Reduction.npm_retraction
Npm.Reduction.npm_soundness
Npm.Reduction.peer_installed
Npm.Reduction.reached_reduceReal
Npm.Reduction.reduceDeps
Npm.Reduction.reduceReal
Npm.Reduction.sight
Npm.Reduction.versions
Npm.rootPkg

NpmPlacement.Reduction.Lookup.dependees_lookupAbsent
NpmPlacement.Reduction.Lookup.dependees_lookupOcc
NpmPlacement.Reduction.Lookup.dependees_lookupRoot
NpmPlacement.Reduction.Lookup.dependees_lookupWalk
NpmPlacement.Reduction.Lookup.edgeAtom
NpmPlacement.Reduction.Lookup.occAtoms_parts
NpmPlacement.Reduction.Lookup.versions_lookupLoc
NpmPlacement.Reduction.Lookup.versions_lookupLoc_sub
NpmPlacement.Reduction.Lookup.versions_lookupWalk
NpmPlacement.Reduction.Lookup.versions_lookupWalk_sub
NpmPlacement.Reduction.npm_placement_completeness
NpmPlacement.Reduction.npm_placement_retraction
NpmPlacement.Reduction.npm_placement_soundness
NpmPlacement.Reduction.npm_placement_soundness_of
NpmPlacement.Reduction.reachableOf
NpmPlacement.Reduction.reachableOf_reachable
NpmPlacement.Reduction.reduceDeps
NpmPlacement.Reduction.reduceReal
NpmPlacement.Reduction.tr
NpmPlacement.Reduction.tr_resolution
NpmPlacement.edgesOf
NpmPlacement.edgesOfBy
LIST
)

expected=$(printf '%s\n' "$names" | grep -c .)

# An installed copy under _opam is on coqtop's default load path and goes
# stale; an absolute -R is what keeps this reading the build tree.
out=$({ printf 'From PackageCalculus Require Import Smoke.\n'
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
