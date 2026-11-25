# Two reusable order-certificate lemmas

The denominator-cleared order transport works over commutative
semirings with left-regular mapped scales. It reuses the reviewed
`map_Φ` and retains the unit version and sparse checker signatures.

The exterior sign-switch cost is exactly the minimum degree of a
polynomial positive on the open unit interval and with nonpositive
products at all exterior sites with nonzero weights. The lower-bound
proof only needs one positive interior anchor. This sharpens the piece
of the signed quadrature test that controls the exterior, not an
unconditional stage-count bound.

Both modules compiled at pinned Lean/Mathlib 4.36.0, were individually
kernel-replayed, and passed the accompanying typed audits. Five named
axiom queries reported only the standard axioms. The existing
`BooleDIRK56` consumer also elaborated after the checker change.
This is targeted verification, not a clean whole-repository or
cross-version build.
