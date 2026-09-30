#!/usr/bin/env sh
# Every reduction product and every theorem the artifact claims must be
# axiom-free: the products are what extraction compiles, and a theorem
# resting on an Admitted lemma would be a claim nothing backs.  The audit
# list below is the only thing to edit when a theorem is added; the
# expected count is derived from it.
#
# Names are qualified through the nat instantiations Smoke.v supplies, one
# per functor.  Semver has no instance of its own because Cargo Includes
# it, so its range language is audited through Cgo.
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
C.Merge.merge
C.Merge.merge_functionalInName
C.Merge.merge_resolution_iff
C.Merge.mergedVS
C.dependees
C.namePreimage
C.versions

Cx.Encoding.satEncoding
Cx.Encoding.sat_encoding_completeness
Cx.Encoding.sat_encoding_soundness
Cx.Reduction.assignment
Cx.Reduction.coreResolution
Cx.Reduction.reduceDeps
Cx.Reduction.reduceDeps_functionalInName
Cx.Reduction.reduceReal
Cx.Reduction.three_sat_completeness
Cx.Reduction.three_sat_correct
Cx.Reduction.three_sat_soundness

Ver.Reduction.Lookup.dependees_lookup
Ver.Reduction.Lookup.reduce_glue
Ver.Reduction.Lookup.versions_lookup
Ver.Reduction.reduce
Ver.Reduction.version_formula_correct

Cfl.Reduction.Lookup.dependees_lookupAbsent
Cfl.Reduction.Lookup.dependees_lookupOrig
Cfl.Reduction.Lookup.versions_lookupOrig
Cfl.Reduction.conflictResolution
Cfl.Reduction.conflict_completeness
Cfl.Reduction.conflict_retraction
Cfl.Reduction.conflict_soundness
Cfl.Reduction.reduceDeps
Cfl.Reduction.reduceReal

Cls.Reduction.Lookup.classRelAt
Cls.Reduction.Lookup.dependees_lookupClass
Cls.Reduction.Lookup.dependees_lookupOrig
Cls.Reduction.Lookup.inClass
Cls.Reduction.Lookup.versions_lookupClass
Cls.Reduction.Lookup.versions_lookupOrig
Cls.Reduction.classPkgs
Cls.Reduction.conflictClassResolution
Cls.Reduction.conflict_class_completeness
Cls.Reduction.conflict_class_retraction
Cls.Reduction.conflict_class_soundness
Cls.Reduction.coreResolution
Cls.Reduction.reduceDeps
Cls.Reduction.reduceReal

Conc.Reduction.Lookup.dependees_lookupGranular
Conc.Reduction.Lookup.dependees_lookupGranularGran
Conc.Reduction.Lookup.dependees_lookupIntermediate
Conc.Reduction.Lookup.dependees_lookupIntermediateOrig
Conc.Reduction.Lookup.versions_lookupGranular
Conc.Reduction.Lookup.versions_lookupIntermediate
Conc.Reduction.concurrentResolution
Conc.Reduction.concurrent_completeness
Conc.Reduction.concurrent_retraction
Conc.Reduction.concurrent_soundness
Conc.Reduction.reduceDeps
Conc.Reduction.reduceDepsDirect
Conc.Reduction.reduceDepsEmpty
Conc.Reduction.reduceDepsSplitEntry
Conc.Reduction.reduceDepsSplitFanout
Conc.Reduction.reduceReal

Peer.Reduction.Lookup.dependees_lookupGranular
Peer.Reduction.Lookup.dependees_lookupIntermediate
Peer.Reduction.Lookup.dependees_lookupIntermediateGran
Peer.Reduction.Lookup.versions_lookupGranular
Peer.Reduction.Lookup.versions_lookupIntermediate
Peer.Reduction.peer_completeness
Peer.Reduction.peer_retraction
Peer.Reduction.peer_soundness
Peer.Reduction.reduceDeps
Peer.Reduction.reduceDepsDepToInt
Peer.Reduction.reduceDepsIntToDep
Peer.Reduction.reduceDepsPeer
Peer.Reduction.reduceReal
Peer.Reduction.reduceRealIntermediate
Peer.Reduction.reduceRealPeer

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
Vis.Reduction.visibility_retraction
Vis.Reduction.visibility_soundness

Plc.mem_reachable
Plc.reachable
Plc.reaches_parented
Plc.reaches_restriction
Plc.walk
Plc.Reduction.Lookup.dependees_lookupAbsent
Plc.Reduction.Lookup.dependees_lookupLoc
Plc.Reduction.Lookup.dependees_lookupRoot
Plc.Reduction.Lookup.dependees_lookupWalk
Plc.Reduction.Lookup.versions_lookupLoc
Plc.Reduction.Lookup.versions_lookupRoot
Plc.Reduction.Lookup.versions_lookupWalk
Plc.Reduction.coreResolution
Plc.Reduction.dependees
Plc.Reduction.lookup_resolution
Plc.Reduction.placementResolution
Plc.Reduction.placement_completeness
Plc.Reduction.placement_retraction
Plc.Reduction.placement_soundness
Plc.Reduction.reached_reduceReal
Plc.Reduction.reduceDeps
Plc.Reduction.reduceReal
Plc.Reduction.versions

Feat.Reduction.Lookup.dependees_lookupFeatPkg
Feat.Reduction.Lookup.dependees_lookupOrig
Feat.Reduction.Lookup.versions_lookupFeatPkg
Feat.Reduction.Lookup.versions_lookupOrig
Feat.Reduction.feature_completeness
Feat.Reduction.feature_retraction
Feat.Reduction.feature_soundness
Feat.Reduction.reduceDeps
Feat.Reduction.reduceReal

Virt.Reduction.Lookup.dependees_lookupOrig
Virt.Reduction.Lookup.dependees_lookupSelector
Virt.Reduction.Lookup.versions_lookupOrig
Virt.Reduction.Lookup.versions_lookupSelector
Virt.Reduction.reduceDeps
Virt.Reduction.reduceReal
Virt.Reduction.selectorVersions
Virt.Reduction.virtual_completeness
Virt.Reduction.virtual_retraction
Virt.Reduction.virtual_soundness

PkgF.Reduction.Lookup.dependees_lookupAbsent
PkgF.Reduction.Lookup.dependees_lookupDisjunct
PkgF.Reduction.Lookup.dependees_lookupDisjunctBy
PkgF.Reduction.Lookup.dependees_lookupOrig
PkgF.Reduction.Lookup.dependees_lookupOrigBy
PkgF.Reduction.Lookup.versions_lookupDisjunct
PkgF.Reduction.Lookup.versions_lookupOrig
PkgF.Reduction.Lookup.versions_lookupOrigPresent
PkgF.Reduction.formula_calculus_completeness
PkgF.Reduction.package_formula_retraction
PkgF.Reduction.package_formula_soundness
PkgF.Reduction.reduceDeps
PkgF.Reduction.reduceDepsBy
PkgF.Reduction.reduceReal
PkgF.package_formula_completeness

VarF.Reduction.Lookup.dependees_lookupAbsent
VarF.Reduction.Lookup.dependees_lookupDisjunct
VarF.Reduction.Lookup.dependees_lookupDisjunctBy
VarF.Reduction.Lookup.dependees_lookupOrig
VarF.Reduction.Lookup.dependees_lookupOrigBy
VarF.Reduction.Lookup.dependees_lookupVar
VarF.Reduction.Lookup.versions_lookupDisjunct
VarF.Reduction.Lookup.versions_lookupOrig
VarF.Reduction.Lookup.versions_lookupVar
VarF.Reduction.assignment
VarF.Reduction.reduceDeps
VarF.Reduction.reduceDepsBy
VarF.Reduction.reduceReal
VarF.Reduction.variable_formula_completeness
VarF.Reduction.variable_formula_retraction
VarF.Reduction.variable_formula_soundness

FC.Reduction.Lookup.dependees_lookupGranularFeatPkg
FC.Reduction.Lookup.dependees_lookupGranularOrig
FC.Reduction.Lookup.dependees_lookupIntermediate
FC.Reduction.Lookup.dependees_lookupIntermediateA
FC.Reduction.Lookup.dependees_lookupIntermediateF
FC.Reduction.Lookup.versions_lookupGranularFeatPkg
FC.Reduction.Lookup.versions_lookupGranularOrig
FC.Reduction.Lookup.versions_lookupIntermediate
FC.Reduction.Lookup.versions_lookupIntermediateA
FC.Reduction.Lookup.versions_lookupIntermediateF
FC.Reduction.feature_concurrent_completeness
FC.Reduction.feature_concurrent_retraction
FC.Reduction.feature_concurrent_soundness
FC.Reduction.reduceDeps
FC.Reduction.reduceReal

Deb.Reduction.Lookup.dependees_lookupAbsent
Deb.Reduction.Lookup.dependees_lookupDisjunct
Deb.Reduction.Lookup.dependees_lookupOrig
Deb.Reduction.Lookup.dependees_lookupSelector
Deb.Reduction.Lookup.dependees_lookupSelectorAgree
Deb.Reduction.Lookup.dependees_lookupSoft
Deb.Reduction.Lookup.reachable_instNames
Deb.Reduction.Lookup.versions_lookupDisjunct
Deb.Reduction.Lookup.versions_lookupOrig
Deb.Reduction.Lookup.versions_lookupSelector
Deb.Reduction.Lookup.versions_lookupSelectorAgree
Deb.Reduction.Lookup.versions_lookupSoft
Deb.Reduction.debian_completeness
Deb.Reduction.debian_retraction
Deb.Reduction.debian_soundness
Deb.Reduction.dependees
Deb.Reduction.matchb_nodeFibre
Deb.Reduction.reduceDeps
Deb.Reduction.reduceReal
Deb.Reduction.versions
Deb.Reduction.versionsDisj
Deb.Reduction.versionsSoft
Deb.matchb

DMA.Reduction.Lookup.dependees_lookupDisjunct
DMA.Reduction.Lookup.dependees_lookupOrig
DMA.Reduction.Lookup.dependees_lookupSelector
DMA.Reduction.Lookup.dependees_lookupSelectorAgree
DMA.Reduction.Lookup.dependees_lookupSelectorRec
DMA.Reduction.Lookup.dependees_lookupSoft
DMA.Reduction.Lookup.versions_lookupOrig
DMA.Reduction.Lookup.versions_lookupOrig_pseudo
DMA.Reduction.Lookup.versions_lookupSelector
DMA.Reduction.Lookup.versions_lookupSelectorAgree
DMA.Reduction.Lookup.versions_lookupSelectorRec
DMA.Reduction.Lookup.versions_lookupSoft
DMA.Reduction.debian_ma_completeness
DMA.Reduction.debian_ma_core_completeness
DMA.Reduction.debian_ma_core_retraction
DMA.Reduction.debian_ma_core_soundness
DMA.Reduction.debian_ma_retraction
DMA.Reduction.debian_ma_soundness
DMA.Reduction.reduceAtom
DMA.Reduction.reduceClause
DMA.Reduction.reduceConf
DMA.Reduction.reduceConfEntry
DMA.Reduction.reduceDeps
DMA.Reduction.reduceInst
DMA.Reduction.reduceProv
DMA.Reduction.reduceProvEntry
DMA.Reduction.reduceReal
DMA.Reduction.reduceRec

Op.Reduction.Lookup.clsVersions_reduceReal
Op.Reduction.Lookup.declarers
Op.Reduction.Lookup.dependeesBy_lookupOrig
Op.Reduction.Lookup.dependees_lookupClassCore
Op.Reduction.Lookup.dependees_lookupDisjunctCore
Op.Reduction.Lookup.dependees_lookupOrig
Op.Reduction.Lookup.dependees_lookupOrigCore
Op.Reduction.Lookup.dependees_lookupRoot
Op.Reduction.Lookup.dependees_lookupRootCore
Op.Reduction.Lookup.versions_class_mono
Op.Reduction.Lookup.versions_lookupClass
Op.Reduction.Lookup.versions_lookupClassCore
Op.Reduction.Lookup.versions_lookupOrig
Op.Reduction.Lookup.versions_lookupOrigCore
Op.Reduction.Lookup.versions_lookupRootCore
Op.Reduction.clsForms
Op.Reduction.clsPkgs
Op.Reduction.clsSel
Op.Reduction.clsVersions
Op.Reduction.coreResolution
Op.Reduction.dependees
Op.Reduction.dependeesBy
Op.Reduction.encR
Op.Reduction.encodeOF
Op.Reduction.opamResolution
Op.Reduction.opam_completeness
Op.Reduction.opam_core_completeness
Op.Reduction.opam_core_retraction
Op.Reduction.opam_core_soundness
Op.Reduction.opam_retraction
Op.Reduction.opam_soundness
Op.Reduction.reduceDeps
Op.Reduction.reduceReal
Op.Reduction.rootPkg
Op.Reduction.srcVersions
Op.Reduction.versSetBy
Op.Reduction.versions
Op.depextsOf
Op.mem_depextsOf

Cgo.Reduction.Lookup.claimants
Cgo.Reduction.Lookup.decision_declines
Cgo.Reduction.Lookup.dependees_lookupCrate
Cgo.Reduction.Lookup.dependees_lookupDecision
Cgo.Reduction.Lookup.dependees_lookupFeatP
Cgo.Reduction.Lookup.dependees_lookupRoot
Cgo.Reduction.Lookup.dependees_lookupSlot
Cgo.Reduction.Lookup.dependees_reduceDeps
Cgo.Reduction.Lookup.dependees_reduceDepsInert
Cgo.Reduction.Lookup.fdefFibre
Cgo.Reduction.Lookup.reads
Cgo.Reduction.Lookup.slot_declines
Cgo.Reduction.Lookup.supportAt
Cgo.Reduction.Lookup.versions_link_mono
Cgo.Reduction.Lookup.versions_lookupCrate
Cgo.Reduction.Lookup.versions_lookupDecision
Cgo.Reduction.Lookup.versions_lookupFeatP
Cgo.Reduction.Lookup.versions_lookupLink
Cgo.Reduction.Lookup.versions_lookupRoot
Cgo.Reduction.Lookup.versions_lookupSlot
Cgo.Reduction.Lookup.versions_reduceRealCrate
Cgo.Reduction.Lookup.versions_reduceRealDecision
Cgo.Reduction.Lookup.versions_reduceRealFeatP
Cgo.Reduction.Lookup.versions_reduceRealLink
Cgo.Reduction.Lookup.versions_reduceRealRoot
Cgo.Reduction.Lookup.versions_reduceRealSlot
Cgo.Reduction.cargoResolution
Cgo.Reduction.cargo_completeness
Cgo.Reduction.cargo_retraction
Cgo.Reduction.cargo_soundness
Cgo.Reduction.coreResolution
Cgo.Reduction.dependees
Cgo.Reduction.dependeesBy
Cgo.Reduction.evalReq
Cgo.Reduction.evalReqBy
Cgo.Reduction.features
Cgo.Reduction.linkRel
Cgo.Reduction.parents
Cgo.Reduction.reduceDeps
Cgo.Reduction.reduceReal
Cgo.Reduction.versions
Cgo.Reduction.versions_link_reduceReal
Cgo.csAdmits
Cgo.csHolds
Cgo.rangeEval
Cgo.rgHolds

Alp.Reduction.Lookup.dependees_lookupDisjunctCore
Alp.Reduction.Lookup.dependees_lookupOrig
Alp.Reduction.Lookup.dependees_lookupOrigCore
Alp.Reduction.Lookup.dependees_lookupProv
Alp.Reduction.Lookup.dependees_lookupProvCore
Alp.Reduction.Lookup.dependees_lookupRoot
Alp.Reduction.Lookup.dependees_lookupRootCore
Alp.Reduction.Lookup.versions_lookupOrig
Alp.Reduction.Lookup.versions_lookupOrigCore
Alp.Reduction.Lookup.versions_lookupRootCore
Alp.Reduction.alpine_completeness
Alp.Reduction.alpine_core_completeness
Alp.Reduction.alpine_core_retraction
Alp.Reduction.alpine_core_soundness
Alp.Reduction.alpine_retraction
Alp.Reduction.alpine_soundness
Alp.Reduction.attachAt
Alp.Reduction.dependees
Alp.Reduction.encReq
Alp.Reduction.installIfFibre
Alp.Reduction.installIfForm
Alp.Reduction.matchPos_attachAt
Alp.Reduction.match_req_coreResolution
Alp.Reduction.match_req_decode
Alp.Reduction.reduceDeps
Alp.Reduction.reduceReal
Alp.Reduction.rootPkg
Alp.Reduction.versions

NpmS.Reduction.Lookup.dependees_lookupDesc
NpmS.Reduction.Lookup.dependees_lookupGranular
NpmS.Reduction.Lookup.dependees_lookupIntermediate
NpmS.Reduction.Lookup.dependees_lookupLink
NpmS.Reduction.Lookup.dependees_lookupSight
NpmS.Reduction.Lookup.versions_lookupDesc
NpmS.Reduction.Lookup.versions_lookupGranular
NpmS.Reduction.Lookup.versions_intermediate_mono
NpmS.Reduction.Lookup.versions_lookupIntermediate
NpmS.Reduction.Lookup.versions_lookupLink
NpmS.Reduction.Lookup.versions_lookupSight
NpmS.Reduction.dependees
NpmS.Reduction.dependees_reducedNames
NpmS.Reduction.embedRoot
NpmS.Reduction.lookup_resolution
NpmS.Reduction.npm_completeness
NpmS.Reduction.npm_retraction
NpmS.Reduction.npm_soundness
NpmS.Reduction.peer_installed
NpmS.Reduction.reached_reduceReal
NpmS.Reduction.reduceDeps
NpmS.Reduction.reduceReal
NpmS.Reduction.sight
NpmS.Reduction.versions
NpmS.rootPkg

NplS.Reduction.Lookup.dependees_lookupAbsent
NplS.Reduction.Lookup.dependees_lookupOcc
NplS.Reduction.Lookup.dependees_lookupRoot
NplS.Reduction.Lookup.dependees_lookupWalk
NplS.Reduction.Lookup.edgeAtom
NplS.Reduction.Lookup.occAtoms_parts
NplS.Reduction.Lookup.versions_lookupLoc
NplS.Reduction.Lookup.versions_lookupLoc_sub
NplS.Reduction.Lookup.versions_lookupWalk
NplS.Reduction.Lookup.versions_lookupWalk_sub
NplS.Reduction.npm_placement_completeness
NplS.Reduction.npm_placement_retraction
NplS.Reduction.npm_placement_soundness
NplS.Reduction.reduceDeps
NplS.Reduction.reduceReal
NplS.Reduction.tr
NplS.Reduction.tr_resolution
NplS.edgesOf
NplS.edgesOfBy
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
