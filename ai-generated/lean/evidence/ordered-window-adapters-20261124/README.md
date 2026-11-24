# Ordered sign-window adapters for ERK orders 16 and 19

`HasAlternationsOn.add_open` joins two ordered open-interval witnesses without losing any sign changes. The proof extracts one sample in each nonzero sign run. When the signs on either side of the join agree, it discards the first sample of the right witness. The distinction between actual alternating samples and a count on a grid gives the same bound over every ordered field.

For order 16, `Moments.shape` proves the exact degree, interiority and simplicity of the two actual pivots, and the odd-reflection identity for their product with the contrast polynomial. It uses global orthogonality against the positive weight (X(1-X)), not a fixed table of Jacobi roots. The residual identities give the denominator-free scalar comparisons needed in the decreasing-order case.

For order 19, `width29_zero_opposed_windows` extracts the full six groups of local polynomial observations (12 equations) and the nine or eight global observations at the original 29 stages. It requires only strict explicitness, the reviewed `HasOrder 19` predicate and a zero first reverse seed. Together with the previously checked nonzero branch and native stage padding, `ordered_erk19_stage_floor30_of_zero_scalar` proves the 30-stage conclusion **conditional on the scalar opposed-window exclusion**. That scalar exclusion is [proved in prose](../../../lower-bounds/conditional/erk_order19_zero_first_seed_opposed_windows_20261124.md), but is not yet a Lean theorem in this packet.

The 12 modules were checked and individually kernel-replayed on Lean 4.36.0 with its matching Mathlib. The four source audits use only the standard Lean axioms. No new unconditional stage-bound certificate is asserted.
