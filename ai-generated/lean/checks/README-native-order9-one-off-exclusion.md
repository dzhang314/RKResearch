# Native ordered ERK order-nine one-off exclusion

This additive source-only delta is against the unchanged reviewed
`RKResearch` definitions at commit `91f4ab1bac096ddf81781ca1b81ab5afbb3c55a5`.
It contains 21 new canonical `RKCert.ReviewedNative` leaves and checked
test evidence. It makes no changes to the earlier graded, paid-forward,
terminal rank, good-prime, or reviewed human sources.

## Exact scope

Import `RKCert.ReviewedNative.OrderNineOneOffExclusion`.

* `RKResearch.Certified.Graded.OneOff.order9_one_off_impossible` excludes
  a strictly lower physical `Fin 12` matrix A with reviewed
  `RKResearch.HasOrder 9 A b` and `(offKnots A).card = 1`.
* `RKResearch.Certified.Graded.OneOff.explicit_order_nine_one_off_at_least_thirteen`
  proves `13 ≤ s` for any stage count under the same one-off premise.
* The field assumptions are `[Field K] [LinearOrder K] [IsStrictOrderedRing K]`;
  no weight, abscissa, distinct-row or rank premises remain.
* This completes only the **one-off branch** of the strongest existing p9
  lower endpoint. The native multi-off census is not part of this packet,
  so the arbitrary-tableau native numerical bound is not claimed here.

The proof establishes the original-coordinate sixth and seventh rows,
independence of the earlier evaluations, the two true doubled fibres,
the terminal unit profile, and two further new on clocks. The native
reflected primitive budget and anchored reverse two-node gain force the
grade-six profile. The two chronological tail actions are exact on all
twelve coordinates, and the reviewed reflected moment interface closes
the two scalar cubic/quartic terminal cases.

## Existing scalar arithmetic and genuine native interfaces

The checked `RKCert.Paired.OneOff.endpoint_nonzero` supplies only the
integer coefficient nondegeneracy of the endpoint curve; it uses no
stage or order input. The final adapter imports the established
`RKCert.ERKOrderNineOneOffTailCubic` module and calls only scalar facts:
`RKCert.Paired.OneOff.cubic_tail_mass`,
`RKCert.Paired.OneOff.four_root_tail_hankel`, and
`RKCert.Paired.reflected_collision_scalar`. That existing scalar
interface has legacy transitive imports; no legacy tableau predicate,
order conversion, or physical proof adapter is called in this delta.
The equality of the two scalar integration operators is established
coefficient by coefficient, not by mapping a tree. Ordered scalar
proofs and endpoint grids are consumed from already checked artifacts.

The exact H48 good-prime theorem
`RKCert.CompactResidue.sixOn_atlas_impossible` is the separate scalar
seam for the **multi-off** branch; it is neither called nor replayed here.

## Pinned build and exact prerequisite packets

* Lean v4.36.0 `611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9` and
  Mathlib v4.36.0 `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`.
* `rk-native-order9-paid-maximal-chart-91f4ab1b-20261124.zip`,
  SHA-256 `03edd960ae4cbff6a30c357fef44fc724f4425b672dc669f7b540f43a3d583a3`,
  including the earlier prerequisites that it pins.
* Original checked ordered p9 closure
  `rk-erk-order9-ordered-complete-delta-20261124.zip`, SHA-256
  `f428f9397a393b890d1161d502a892a12f8595e71e16fa94205252318114d9ec`,
  solely for the scalar interfaces above and their declared imports.
* Native `RKCert.ReviewedNative.OrderedNodalGain` and
  `RKCert.ReviewedNative.ClockBlockDetection`, and the existing
  tree-independent `RKCert.NodalHermiteRank` / `RKCert.NodalPrimitive`.
  The shared native sources are included in this commit.

From `ai-generated/lean`, build the named endpoint and apply the audit:

```sh
lake build RKCert.ReviewedNative.OrderNineOneOffExclusion
lake env lean checks/NativeOrderNineTailAudit.lean
```

The audit checks 26 named declarations, including four scalar dependencies,
and applies the endpoint to a reviewed tableau. The added leaves compiled
without warnings and reported only the standard axioms.
