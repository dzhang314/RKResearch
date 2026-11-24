# Native logarithmic ERK stage floor

Over any **characteristic-zero commutative ring**, a strictly lower triangular order-p tableau with p≥10 uses at least

```
((3*p+1)/2) - 1 + Nat.log 2 (p/10)
```

original stages (natural division). The human-facing theorem is `RKResearch.HasOrder.erk_logarithmic_stages`. The independent consumer checks the 30-stage endpoint at order 20 and 61 and 122 stages at orders 40 and 80. There are no assumptions on signs, distinct nodes, individual weights or reducedness. The stronger, separate ordered order-20 bound is not asserted.

The core `erk_doubling_rank_surplus` proves `dim F_(2j) ≥ dim F_j+j+1` for the actual defect flag whenever j≥5 and 4j≤p. A flat band would give an intrinsic head and an unpaid top clock power by the independently checked `NativeFlatClockHead` theorem. The outgoing Hermite gain forces a head of length at least two. The native head-fibre argument makes the invariant core closed under products and selects a physical disjoint representative. All paid squares force that head to agree on its support with a polynomial of degree ≤ j−1. Two chronological first-unmatched rows supply the incompatible primitive tests at two distinct nonzero physical clocks. The scalar Jacobi proof now uses the native Cauchy kernel and does not import the old order-dependent CauchyKnots path.

Starting at the known grade-five rank, every paid dyadic doubling adds a dimension beyond unit growth. The existing rank interval and midpoint budgets convert these to physical stages, and strict characteristic-zero coefficient transfer gives the ring statement. No order-15 or order-17 stage-specific result is used in this proof.

Human inputs: `91f4ab1bac096ddf81781ca1b81ab5afbb3c55a5`. No old tree, order predicate, or conversion is imported. The existing native grade-five count archive is `6a27edb23ca8a1f40205f5b90be536350d977b1854f3d4d0ca24549c0efe68a6`; the independently staged `NativeFlatClockHead.lean` is `82ff550301902a235ab6897921a668647c29727414d61788da01275d0b56f952`. Additional differently named local dependencies are the already reviewed tree-free OneEscape, NodalPrimitive and NodalHermiteRank modules.

All four new modules compiled warning-free and individually passed kernel replay on Lean/Mathlib v4.36.0 (Mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`). The independent consumer passed over both fields and rings; the axioms are only `propext`, `Classical.choice`, and `Quot.sound`.

With the checked prerequisites present, from the pinned `ai-generated/lean` package:

```sh
lake build RKCert.ReviewedNative.JacobiTwoKnot RKCert.ReviewedNative.ERKHeadContrast RKCert.ReviewedNative.ERKDoublingHead RKCert.ReviewedNative.ERKLogarithmic
lake env lean AuditReviewedNativeERKLogarithmic.lean
for mod in JacobiTwoKnot ERKHeadContrast ERKDoublingHead ERKLogarithmic; do
  lake env leanchecker --verbose "RKCert.ReviewedNative.$mod"
done
```
