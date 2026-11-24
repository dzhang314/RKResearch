# Native DIRK lower bound at order six

Every lower triangular, order-six Runge–Kutta tableau over a nontrivial commutative ring has at least **five original stages**. This is a lower bound, not an existence or sharpness claim. The diagonal can vary and can vanish; no positivity, realness, distinct nodes, unit weights, or trimming are used.

The user-facing theorem is `RKResearch.HasOrder.dirk_order_six_stages`. Its field version is `RKResearch.HasOrder.dirk_order_six_stages_field`. The independent consumer also checks arbitrary `p ≥ 6`.

**Proof.** Over a field, let Fⱼ be the true grade-j homogeneous defect span. Native DIRK strict growth gives `finrank F₃ ≥ 1`, or at least 2 if the quadratic defect is nonzero. In the latter case, the three clock columns of degrees 0, 1, and 2 separate from F₃: the three paid scalar probes give an invertible 3-by-3 Cauchy system. Three columns plus two defect dimensions need five physical coordinates.

If the quadratic defect is zero, lower triangularity gives the first diagonal entry squared equal to zero. The first physical row therefore vanishes over a field. All positive-grade tree differences vanish on that row, so the row itself detects the constant coefficient. The same three shifted Cauchy moments now separate **four** clock columns (degrees 0 through 3) from F₃. Four columns plus one defect again need five coordinates. The existing reviewed maximal-ideal transport gives the nontrivial commutative-ring statement, including nonreduced and positive-characteristic rings.

The common forward argument is stated at general even midpoint: a field tableau with paid order at least 2m, m ≥ 2, has at least 2m − 1 physical stages. This is not asserted to be the full published high-order DIRK bound. No reverse-count result or grade-six surplus is used.

**Source basis.** Human `RKResearch.FiniteRootedTree` and `RKResearch.OrderConditions` from commit `91f4ab1bac096ddf81781ca1b81ab5afbb3c55a5`; direct generated imports `RKCert.ReviewedNative.DIRKSmall`, `RKCert.ReviewedNative.DIRKForwardRank`, and `RKCert.ReviewedNative.GradedSeparation`. The full list of checked source dependencies is in `source-inputs.sha256` (paths relative to the repository). No legacy tree, legacy order predicate, or compatibility bridge is imported. The legacy `RKCert.UniformDIRK` was consulted only to locate the prior numerical endpoint.

**Recheck** from the repository's `ai-generated/lean` project with the pinned Lean/Mathlib 4.36 dependencies:

```sh
lake build RKCert.ReviewedNative.DIRKOrderSix
lake env lean AuditReviewedNativeDIRKOrderSix.lean
lake env leanchecker --verbose RKCert.ReviewedNative.DIRKOrderSix
```
