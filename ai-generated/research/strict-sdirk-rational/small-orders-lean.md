# Lean checks of the rational strict SDIRK minima

The [exact three-stage order-three and four-stage order-four tableaux](small-orders.md)
and their lower bounds now have Lean proofs on the reviewed `RKResearch.HasOrder`
predicate. The lower bounds apply even to rational common diagonal zero.

`RKResearch.Certified.rational_strictSDIRK_three_minima` and
`RKResearch.Certified.rational_strictSDIRK_four_minima` give both least
stage counts: attaining the stated order and attaining exactly that order.
The existence proofs use integer coefficients scaled by common denominators.
The lower proofs reduce only the scalar polynomial after justifying
its rational denominator, not the whole tableau modulo five.

All five modules compiled and independently replayed with Lean 4.36.0.
The typed audits passed, and the axiom reports list only standard Lean axioms.
