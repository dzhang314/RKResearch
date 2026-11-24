# Order 17: tiny reverse support and three-pivot moments

The tableau results use the reviewed predicate `HasOrder 17 A b`.
For a strictly lower triangular width-26 tableau over an ordered field
with nonzero first reverse seed, the ninth defect space has dimension
ten and is the sum of the eighth defect space and its image under
multiplication by the nodes. When the seed has at most two supported
reflected clocks, the local frame yields a hidden subspace of dimension
four or five that is invariant under multiplication by the nodes. In the
rank-five case, the physical producer gives a vector supported at exactly
four clocks, with the same nonzero rows as its witness. Every vector in
the ninth defect space vanishes on those rows.

Separately, opposed three-, two-, and one-moment tests at three distinct
interior pivots force a nonzero polynomial to have degree at least six,
under the stated degree budget and positivity of the two base weights.
The typed audit specializes the weights to X and 1. This proof uses only
single-weight sign tests and addition across open intervals.

These certificates do not assert the full native order-17 bound. They do
not supply the rank-four physical census or the whole-block moment
identities connecting the rank-five producer to the scalar result.

All seven modules compiled and were individually kernel-replayed on Lean
4.36.0 with its pinned Mathlib. The three audits check 15 named
declarations and found only standard axioms.
