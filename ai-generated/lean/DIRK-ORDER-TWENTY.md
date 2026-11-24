# Order twenty needs at least twenty-nine original stages

Pinned Lean/Mathlib v4.36.0. The public unconditional theorems in RKCert.DirkOrder20TwentyNine are RKCert.Paired.dirk_order20_twenty_nine_charZero_field and RKCert.dirk_order20_twenty_nine_charZero_ring. Input: an arbitrary lower-triangular s-stage array with all-tree order at least p and 20≤p. Conclusion: 29≤s. No ordering, positivity, clock convention, nonzero weight, endpoint prescription, field closure or stage-removal assumption is imposed on the source array. This improves the earlier specifically named 28-stage intermediate theorems without redefining them.

The 28-row chart has a genuine last stage and exact full/terminal-zero marked flags. If any F10 defect survives there, F9+CF9 is the exact terminal-zero hyperplane. Its F5 products and F4-containing invariant core contradict the prior two-case paid H9 obstruction. Thus all F10 defects vanish at that actual endpoint; polynomial right-endpoint separation then forces C(2), the zero initial row and dim F10=10. The endpoint difference minus the genuine weighted Legendre derivative annihilates E10, forcing clock values at every clean b-active physical coordinate onto the eleven-point Lobatto grid. No assertion about arbitrary inactive clocks is used.

For generic horizon H and full marked coverage, zero net mass on each occupied cubic fiber places its diagonal orbit inside the final, constant-tree marked space, not necessarily inside the small high-information marked space. The true incoming Hermite gain at level j then requires at least j−2+floor(j/2) distinct sites. At order 20 the additional moment budget forces at least eighteen physically nonzero cubic coordinates even in signed cancellations. The clean grid has room for at most ten sites *minus* the dimension of the common zero coordinate space.

A grade-five numerator extracted from an actual defect would have two distinct, nonzero clean pivots paying the original 3+2 primitive tests. One original-quadrature omitted Lobatto knot supplies a zero. A 3×3 determinant after solving the three first-site equations rules this out: the remaining homogeneous degree-seven determinant is nonzero on all 990 ordered distinct triples modulo the proved split prime 15727. The finite tables are checked by the Lean kernel; the integral specialization acts only on a fixed polynomial's roots, never on arbitrary RK coefficients. This proves F5 is annihilated by both coordinatewise tests, costing at least four dimensions by the native incoming Hermite gain. At least five Lobatto knots are now genuinely omitted: the genuine one-port sextic with two primitives therefore vanishes by the separately certified 2772-case sextic gate. This places F6 in a clock-invariant subspace of F10, contradicting the original grade-six escape. Base change is used only to split the one fixed polynomial for cardinal counting.

The [sextic test](FIXED-LOBATTO-SEXTIC.md) and the two Python arithmetic replays are separate evidence; the Lean proof has no Python dependency. With pinned Lean and Mathlib v4.36.0:
```sh
lake build RKCert.DirkOrder20TwentyNine
lake env lean AuditDirk20.lean
lake env lean AuditSexticFixed.lean
lake env leanchecker RKCert.DirkOrder20TwentyNine
```
