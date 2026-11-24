# Native uniform explicit Runge–Kutta stage floor

For a strictly lower triangular order-p tableau over **any nontrivial commutative ring**,

```text
max(p, ⌈3p/2⌉ − 2) ≤ number of original stages.
```

The Lean statement is `RKResearch.HasOrder.erk_uniform_stages` with the exact natural-number expression `max p ((3*p+1)/2-2)`. It agrees with the existing uniform arbitrary-ring lower-bound column, not the stronger characteristic-zero or ordered endpoints in some higher orders. No positivity, distinctness, or nonzero individual weight or node is assumed. No tableau is trimmed in the statement. This is a lower bound, not an existence claim.

`erkUniformFloor_through_twenty` checks the full published column, with order zero prepended:

```text
[0,1,2,3,4,6,7,9,10,12,13,15,16,18,19,21,22,24,25,27,28]
```

## Reusable midpoint budgets

Write F_q for the true degree-q defect space and T_q for the tree space of the actual reviewed tableau.

- At paid even order 2q, the genuine zero first row detects the constant coefficient. Shifted Cauchy moments separate the other q clock coefficients from F_q. Thus `dim T_q = q+1+dim F_q`; the reverse flag contributes q−2 plus its actual seed rank. The even budget is `2q−1+dim F_q+dim(back 0) ≤ s` for q≥2.
- At paid odd order 2q+1, the native reverse endpoint lemma uses either a nonzero initial adjoint seed or the original last-live coordinate as its extra dimension. The odd budget is `2q+1+dim F_q ≤ s` for q≥1. Any proved surplus beyond q−1 in F_q increases the physical lower bound directly; no particular order-specific surplus is used.
- Native explicit causal growth always gives `dim F_q ≥ q−1` at these paid midpoints. The chain tree gives `p ≤ s` over the coefficient ring itself. The new native strict-lower coefficient specialization keeps the entire diagonal zero while transporting HasOrder to a residue field.

The optional `ERKEvenHorizon` module makes equality usable. If q≥2, order 2q is paid, and the original tableau has at most 3q−2 stages, it has exactly 3q−2 stages, `dim F_q=q−1`, and `dim T_q=2q`. The first reverse seed is zero, the paid flags have exact ranks, and the top reverse space is the full annihilator of T_q. The last *physical* weight is live and its node is one; its coordinate column belongs to T_q. An auxiliary strict prefix is used only to contradict a zero last weight, not as the tableau in the statement.

## Provenance and verification

The human tree type, matrix weights Φ and HasOrder come from `91f4ab1bac096ddf81781ca1b81ab5afbb3c55a5`. This delta imports only native proof modules and Mathlib, not the old order predicate, old tree, any translation, or specialized order-9/15/17 proof. The legacy `RKCert.UniformERK` was consulted only to identify the exact published numerical target. Exact source inputs are fingerprinted in `source-inputs.sha256`.

Both new modules built without warnings and separately passed kernel replay using Lean/Mathlib v4.36.0 (Mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`). The independent consumer checks the original ring and field signatures, even saturation, odd surplus, low endpoints, and finite examples over `ZMod 77` and `ZMod 23`. Checked proof axioms are limited to `propext`, `Classical.choice`, and `Quot.sound`; the numerical regression has no axioms.

With the verified native prerequisites present in the pinned `ai-generated/lean` project:

```sh
lake build RKCert.ReviewedNative.ERKUniform RKCert.ReviewedNative.ERKEvenHorizon
lake env lean AuditReviewedNativeERKUniform.lean
lake env leanchecker --verbose RKCert.ReviewedNative.ERKUniform
lake env leanchecker --verbose RKCert.ReviewedNative.ERKEvenHorizon
```
