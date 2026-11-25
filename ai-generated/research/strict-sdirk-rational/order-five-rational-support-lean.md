# Lean proof of the order-five rational quadrature support bound

The [four-site lower bound](order-five.md#at-least-four-distinct-sites-carry-quadrature-weight)
now has a native Lean proof. The theorem
`RKResearch.HasOrder.four_le_activeQuadratureSites_of_rat` requires only
that the abscissae with nonzero aggregate quadrature weight are rational
casts in a characteristic-zero field. Unweighted sites can be arbitrary,
weights can be signed, and no triangularity is required.

The proof groups coincident abscissae and uses the reviewed quadrature
conditions. The arithmetic argument clears the discriminant to an integer
that is divisible by three but not by nine; it cannot be a rational square.
The two source files compiled and independently replayed in Lean 4.36.0.
The typed audit reports only the standard axioms.
