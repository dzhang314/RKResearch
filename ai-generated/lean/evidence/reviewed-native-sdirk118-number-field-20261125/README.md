# The eleven-stage method over a field of degree at most twelve

The theorem `exists_strict_sdirk11_hasOrder8_over_field_degree_le_twelve`
proves existence over a finite intermediate field of ℝ over ℚ with
degree at most 12. It uses the same literal tableau as the real
witness: the lift is entrywise and maps back exactly to the real
coefficients. Common diagonal positivity, lower triangularity, and
the reviewed `HasOrder 8 A b` are preserved. The proof does not assert
that the degree is exactly 12 or that it is the smallest coefficient field.

The three monic equations have degrees 3, 2, and 2. Their minimal
polynomials can only have smaller degrees. The proof multiplies the
three simple-extension degree bounds without recomputing the earlier
numerical sign certificates.

The separate `CommonDiagonalStageFloor` module transports existing
branch bounds for tableaux with one common diagonal over a nontrivial
commutative ring. A nonunit diagonal gives an explicit residue-field
method, while a nonnilpotent one survives in a field and gives the
nonsingular quadratic lower bound. When neither condition is assumed,
the minimum applies; characteristic zero also gives seven stages at
order six without a diagonal assumption beyond being common.

The seven added modules compiled and replayed separately on
Lean/Mathlib 4.36.0 with the verified reviewed dependency bank. Both
typed audits report only the standard axioms. This is targeted
verification and not a clean whole-repository or cross-version build.
