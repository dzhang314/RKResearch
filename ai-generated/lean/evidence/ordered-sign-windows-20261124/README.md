# Ordered-field sign tests for polynomial moments

The common proof uses the [19-node positive rational rule](../../../lower-bounds/conditional/positive_rational_rule_degree19_20261124.json). Lean checks exactness through degree 19, including affine changes of interval and reflection. These identities are algebraic and need no integration theory over the coefficient field.

Over an ordered field, `grid_variation_of_positive_moments` gives one sign change for each paid moment against a single positive weight. Its separator adds a linear factor only when two successive nonzero samples have opposite signs. `grid_variation_of_monotone_ratio` gives two changes from two positive weights with strictly monotone ratio. `HasAlternationsOn.le_natDegree` bounds any strictly ordered sample witness by the degree of its polynomial. It uses Lagrange interpolation, so it does not infer a root between two samples.

The separate ERK16 adapter `width24_strong_centered_moments` constructs the six local and seven global scalar moments from the reviewed order conditions and the strong-three geometry. The two scalar exclusions are still documented [in prose](../../../lower-bounds/conditional/README.md); this packet makes no new stage-count claim.

All eight modules were rebuilt and individually kernel-replayed on Lean 4.36.0 with the matching Mathlib pin. The rebuild list includes five audit sources. No other version was checked in this pass.
