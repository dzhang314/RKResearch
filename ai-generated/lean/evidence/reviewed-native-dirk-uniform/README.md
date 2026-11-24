# Native unrestricted DIRK stage floor

For a lower triangular tableau of order `p ≥ 6` over **any nontrivial commutative ring**, the original number of stages is at least **p + ⌊(p−1)/2⌋ − 3**. In particular, orders 7, 8, 9, 10 and 11 require at least **7, 8, 10, 11 and 13 stages** respectively. The result imposes no common or nonzero diagonal, positive or individually nonzero weights, distinct stage nodes, characteristic-zero or real-order hypothesis.

- `RKResearch.HasOrder.dirk_uniform_stages`: uniform ring theorem from the human `HasOrder` predicate and `A.IsLowerTriangular`.
- `RKResearch.HasOrder.dirk_order_seven_stages`, `RKResearch.HasOrder.dirk_order_eight_stages`: direct numerical corollaries.
- `RKResearch.HasOrder.dirk_uniform_floor_le_stages`: all-order version, with the small cases supplied by the already reviewed native results.
- `RKResearch.dirkUniformFloor_through_twenty`: checked numerical regression on the complete arbitrary-ring DIRK column (orders 0 through 20): `[0,1,1,2,3,4,5,7,8,10,11,13,14,16,17,19,20,22,23,25,26]`.

These are necessary stage counts, not existence statements. The unrestricted-ring column agrees with the stronger characteristic-zero and ordered columns through order 11; their later improvements are not asserted here.

## Why the extra stage is necessary

At forward degree `q ≥ 2` with `2q+1 ≤ p`, the native clock/defect decomposition gives `dim T_q = q+1 + dim F_q`. The DIRK forward flag gives `dim F_q ≥ q−2`, with an extra dimension if C(2) fails. At reverse level `n ≥ 1` with `q+n+2 ≤ p`, the all-monomial physical flag lies in the annihilator of `T_q`. Any plateau from level 1 would trap both D(2) and D(3) in an invariant subspace and hence the reflected clock target, contradicting its paid nonzero pairing. Thus the reverse rank is at least `n−1` plus the rank at level 1.

If the forward flag does not earn the extra dimension and the first reverse space is zero, C(2), D(1) and D(2) vanish. C(2) forces the first physical row to vanish over the field. At the last nonzero weight, the combination D(2) − 2(1−c)D(1) equals the nonzero weight times (1−c)², so its node equals one. Every row of the reverse flag vanishes on the closed tail starting there. Yet that live coordinate does not belong to `T_q`: a polynomial representing it modulo defects would have zero constant term at the physical origin and nonzero constant moments through degree q, contrary to the native shifted Cauchy test. The reverse flag therefore loses one dimension inside the annihilator. In all cases `2q+n−1 ≤ s`; take `q=⌊(p−1)/2⌋` and `n=p−q−2`. Reviewed maximal-ideal transport gives the unrestricted commutative-ring result.

## Verification and provenance

The two new proof modules and the independent consumer use only the reviewed human `RKResearch.FiniteRootedTree` / `RKResearch.OrderConditions` definitions and native proof modules. No old order predicate, old tree, compatibility bridge or heavy replay is imported. Human sources were read from commit `91f4ab1bac096ddf81781ca1b81ab5afbb3c55a5`. The direct earlier order-six dependency is the reviewed archive `be8d41d7ec3a01284985e6488ad6f65ac6618572c693e92a0b75173daf4522d4`. Exact source fingerprints for the transitive local inputs are listed in `source-inputs.sha256`.

Lean v4.36.0 and the matching Mathlib v4.36.0 checkout (`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`) were used. The two new modules compile without warnings. The independent consumer checks actual uses of the all-order and numerical APIs. The only proof axioms reported are `propext`, `Classical.choice`, and `Quot.sound`; the numerical regression has no axioms. Both new modules separately passed kernel replay.

Place the source delta on top of the native dependencies, then from the repository's `ai-generated/lean` project:

```sh
lake build RKCert.ReviewedNative.DIRKReverseGrowth RKCert.ReviewedNative.DIRKUniform
lake env lean AuditReviewedNativeDIRKUniform.lean
lake env leanchecker --verbose RKCert.ReviewedNative.DIRKReverseGrowth
lake env leanchecker --verbose RKCert.ReviewedNative.DIRKUniform
```
