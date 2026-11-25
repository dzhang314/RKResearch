# Signed quadrature without a fixed degree cutoff

Over any ordered field, the formal integral of a nonzero polynomial square times endpoint powers is strictly positive. The proof lowers degree by an exact weighted integration-by-parts identity. The same holds after multiplication by finitely many affine factors whose endpoint values are nonnegative and not both zero.

For a reviewed Runge–Kutta tableau of order `p`, group the actual output weights at equal abscissae. If `t` is the number of nonzero groups, `e` the number at or outside the endpoints, and `n` the number of negative interior groups, the theorem gives `p + e + 2*n ≤ 2*t`. The exterior sign-switch variant chooses fewer factors: on each side it counts the changes in grouped signs, starting from a negative sign at the interior boundary. It proves `p ≤ 2*m + k_left + k_right`, where `m` counts positive interior groups. Neither result assumes the individual weights are positive or claims a new stage bound for a particular RK class.

The new modules and existing grouping prerequisite were compiled and independently replayed with Lean and Mathlib 4.36.0 on the ec3d reviewed foundation. The two typed audit files use the reviewed order predicate and the actual grouped weights. This is a targeted check against the verified project dependency bank.
