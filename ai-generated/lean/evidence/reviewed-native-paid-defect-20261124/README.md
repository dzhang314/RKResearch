# Suffix order from single primitive defects

The generic sufficiency theorem applies to a Runge–Kutta tableau over
any characteristic-zero field, with zero weights on the prefix stages.
It gives the reviewed predicate `HasOrder p A b` from suffix quadrature,
vanishing low-order primitive defects and cancellation of eligible short
words in one remaining primitive defect. If defects start at tree size
`q + 1` and `p - 1 < 2 * (q + 1)`, no product of two defects appears
within the order budget. The theorem does not assume a donor rank,
triangularity, or any order condition on the prefix alone. It is not an
existence certificate for an eleven-stage SDIRK method of order eight.

The separate characteristic-zero scalar module excludes a nonzero
degree-at-most-six polynomial vanishing at the origin when the paid
forward 4+3 primitive moments hold at two distinct nonzero clocks. It
factors out X and uses the existing quintic theorem. The typed audit
takes the integral notation used in the order-17 no-origin branch;
deriving those inputs from tableau geometry is separate.

Both modules compiled and were individually kernel-replayed on Lean
4.36.0 and pinned Mathlib. The audits reported only standard axioms.
