# Clock-one width and finite signed-moment tools

`full_whole_clock_one_suffix_width_debit` proves a width estimate for explicit methods satisfying the reviewed `HasOrder p A b`. It assumes a zero first seed, equality of the primitive reverse space with the full annihilator, and that the complete group of live stages with abscissa one is a terminal live suffix. Writing q = n + 1, an order of at least 2q and zero total mass of that group imply at least 3q + 1 stages for q ≥ 6. For q ≥ 8, equality also determines the two live stages in the suffix and the ranks listed in the theorem. This is conditional; it does not strengthen an unconditional stage bound.

The other modules provide a scalar-cokernel cancellation criterion, signed two-point moment elimination, a Gaussian comparison for a finite grid, and a sign bracket for a stopped signed moment identity on a finite grid. The last three work over an ordered field. They do not require an embedding into the reals or an analytic integral.

The sources use Lean 4.36.0 and Mathlib 4.36.0 (Mathlib commit `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`). The order below starts after the existing imports have been built. The named theorem axiom report lists only the standard Lean axioms.
