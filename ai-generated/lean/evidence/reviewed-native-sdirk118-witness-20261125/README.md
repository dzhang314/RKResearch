# Eleven-stage strict SDIRK, order at least eight

The closed theorem `exists_real_strict_sdirk11_hasOrder8` gives an 11-by-11
lower triangular real tableau, a real weight vector, and a positive
constant diagonal. It proves the reviewed `RKResearch.HasOrder 8 A b`
directly. The theorem has no sign, rank, order, or tableau hypotheses.
It does not assert exact order eight or stage minimality. This formalizes
the existing 11-stage upper endpoint.

The proof uses three small real root brackets, checks the six rational
interval outputs and the five positive Bernstein tables in Lean, binds
the literal forward and reverse rows, and contracts a pair of equal
stage values to get eleven stages. The real root bracket uses only
ordered completeness, not a topology package. A separate
[coefficient-field proof](../../../upper-bounds/real-algebraic/sdirk11_order8_literal_coefficient_field_20261125.md)
shows that the same explicit formulas give coefficients in an extension
of the rationals of degree at most 12. The field degree is not kernel
formalized here.

All 24 added Lean modules elaborated on Lean 4.36.0 and Mathlib
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842` against the reviewed dependency
bank. `leanchecker` independently replayed the endpoint, quadratic
signs, Bernstein tables, affine signs and literal reverse producer.
The typed audit confirms the endpoint signature and only the standard
axioms `propext`, `Classical.choice`, and `Quot.sound`.
The computations use kernel `decide`, not native axioms.
No clean whole-repository build or additional version is claimed.
