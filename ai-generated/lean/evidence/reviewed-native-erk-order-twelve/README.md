# Native ERK order-12 equality chart through grade nine

This is a **structural milestone, not** the 18-stage exclusion. Over a characteristic-zero field, exact reviewed order 12 on a strictly lower triangular tableau with at most 17 original stages forces:

- exactly 17 stages, `dim F₅=5`, `dim F₆=6`, `dim T₆=13`;
- zero first reverse seed and exact ranks 0 through 4 for the ordinary and all-monomial reverse flags (the two flags agree at each of these levels);
- a nonzero last *physical* weight at clock one, its coordinate column in `T₆`, and all actual `F₅` and `F₆` vectors zero there;
- an intrinsic single head of initial length at least two, extending to the seven-dimensional terminal-zero grade-seven cut;
- exact `dim T₇=14`, `dim T₈=15`, and `dim T₉=16`; their annihilators are the original reverse flags at levels 3, 2, and 1 respectively.

The fields of these conclusions are consumed by the next reverse and forward chart lemmas in the prior audited ERK12 proof. The unresolved native inputs are the final rank-one reverse escape (for `T₁₀ = ⊤`) and the finite head exclusions. The existing 18-stage legacy certificate is not used as a premise.

## Method

The published native grade-five surplus, native paid rank interval, and measured even midpoint budget force exact forward and reverse payment. Reviewed prefix invariance rules out a zero weight on the last original coordinate by the native 17-stage lower bound; no prefix replaces the tableau in any conclusion. Pairing the live coordinate with an actual grade-five defect uses the paid product relation and makes the last row zero on `F₅`; the genuine single clock step gives the same fact on `F₆`.

`coeff_separated_two_endpoints` is reusable over **any field** at its paid cutoffs. Actual zero at the origin and at the indicated node one eliminates the constant and last clock coefficients, so only n ordinary moments are needed for degree n+1. Scaling the remaining rows gives the same shifted native Cauchy test. This replaces an order-specific coefficient decoder without rerunning any scalar arithmetic table.

At the physical last row, the zero-at-terminal part of `F₇` has rank at most seven by this separation; the next clock escape fills it exactly. Then `T₇` is that cut plus the seven degree-six clock columns. The published native reverse Hermite gains give the next two clock escapes and exact ranks through `T₉`. They do not yet discharge the more delicate rank-one case.

## Check

Human `FiniteRootedTree`, Φ, and HasOrder from `91f4ab1bac096ddf81781ca1b81ab5afbb3c55a5`. No old order predicate, old tree or compatibility conversion is imported. No heavyweight scalar certificates were generated or rerun. The only local non-ReviewedNative imports are the existing tree-free OneEscape, NodalPrimitive and NodalHermiteRank lemmas.

Three warning-free scoped builds and three targeted kernel replays passed on Lean/Mathlib 4.36.0 (Mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`); the independent consumer starts from the actual order and stage cap. Proof axioms are only `propext`, `Classical.choice`, and `Quot.sound`.

With the checked native prerequisites present in the pinned `ai-generated/lean` package:

```sh
lake build RKCert.ReviewedNative.ERKOrderTwelveSaturation RKCert.ReviewedNative.TwoEndpointClockSeparation RKCert.ReviewedNative.ERKOrderTwelveTerminalBand
lake env lean AuditReviewedNativeERKOrderTwelveBand.lean
for mod in ERKOrderTwelveSaturation TwoEndpointClockSeparation ERKOrderTwelveTerminalBand; do
  lake env leanchecker --verbose "RKCert.ReviewedNative.$mod"
done
```
