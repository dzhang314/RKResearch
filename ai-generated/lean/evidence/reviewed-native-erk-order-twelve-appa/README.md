# Native ERK order-12 Appendix A

**Checked result.** Over every characteristic-zero field, actual reviewed order 12 on a strictly lower triangular tableau of at most 17 stages forces the original one-dimensional first reverse flag to escape the reflected clock. The ninth tree grade therefore escapes its clock image, and the tenth tree grade occupies the entire original stage space. These theorems do **not** assert the final 18-stage bound.

Entry points under `RKResearch.Certified.Graded.ERK12`:

- `back_one_noninvariant`: no reflective clock invariance of the actual `back A b 1` on the saturated candidate;
- `saturated_e9_escape`: the corresponding physical forward clock escape at tree grade nine;
- `actual_e10_top`: `treeSpace A 10 = ⊤`, from just original strict triangularity, native `HasOrder A b 12`, and `s ≤ 17`.

The physical reverse proof uses the greatest original stage having both nonzero reflected clock and nonzero weight. The first potentially nonzero quadratic residual there cannot vanish by strict transposed causality. An invariant reverse line would then be supported on a single nonzero reflected clock. The next three paid reverse levels give exact rows in the same line-plus-head chart. Their coefficients are fixed at the chronological pivot. The native causal two-node argument changes the feature by a multiple of the localized residual and forces its support into two nonzero clock blocks, while actual reflected moments guarantee a live stage outside any four chosen clocks. This yields the needed contradiction without assuming distinct nodes or nonzero weights throughout.

## Remaining forward boundary

The immediately dependent forward step is the full head staircase through the exact T7/T8/T9/T10 spaces: this packet offers the missing ninth-grade escape and the top-space conclusion, not that staircase or its exclusions. In the audited legacy proof, grade-two and grade-three core admission restrict the head length; the surviving forward cases are `(head length, dim F4) = (2,3), (2,4), (3,4)`. Those restrictions and their finite polynomial/chronological contradictions have not been checked natively here. The prior general native 17-stage floor is unchanged.

## Provenance and validation

The human tree type, matrix weight Φ, and HasOrder are from `91f4ab1bac096ddf81781ca1b81ab5afbb3c55a5`. The earlier sealed native cap-to-T9 packet is SHA-256 `b32cda77522f3f7f3f1e42f4814b33af05c587c1dad6c703ec5fb791dc665b2f`. The two-node recurrence consumes the already checked **tree-free** `RKCert.ReverseTwoNodeScalars` unchanged, source SHA-256 `ad4389d3e1f914e9e3ce4a9f6a0686fa3a1cb278a7e716228e47f9a83d3887c9`. Neither the old RK order predicate nor any conversion enters this closure. No scalar certificate was regenerated or recompiled.

All four new modules built warning-free and separately passed kernel replay (Lean/Mathlib v4.36.0, Mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`); the independent consumer checks both clock escapes and the original-stage top conclusion. Only the standard `propext`, `Classical.choice`, and `Quot.sound` axioms were reported. All new Lean object files were staged in temporary storage, and the archive contains source and audit evidence only.

With the native prerequisites and cached tree-free scalar module present in the pinned `ai-generated/lean` package:

```sh
lake build RKCert.ReviewedNative.ERKOrderTwelveAppendixA
lake env lean AuditReviewedNativeERKOrderTwelveAppendixA.lean
for mod in ReverseTwoNodeNative ERKOrderTwelveReverseLocalized ERKOrderTwelveReverseRows ERKOrderTwelveAppendixA; do
  lake env leanchecker --verbose "RKCert.ReviewedNative.$mod"
done
```
