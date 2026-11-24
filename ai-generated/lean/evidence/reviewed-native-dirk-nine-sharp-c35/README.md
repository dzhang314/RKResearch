# Sharp reviewed-native DIRK order nine

Ten is the minimum number of physical stages of ordinary DIRK for classical order at least nine over both the reals and the real algebraic numbers. The Lean endpoint does not assert failure of order ten.

The archived Lobatto tableau has a genuine zero first row. Lean interprets
its exact coefficients at the bracketed root of the monic quartic
x^4 − 147x² + 3087 and the positive root y² = 7. The stage and weight
denominators are 87572016 and 120. These are ordinary lower triangular
DIRK theorems, not strict SDIRK, rational-existence, or stability results.

The public names in RKResearch.Certified are
dirk_order_nine_isLeast_real, dirk_order_nine_isLeast_realAlgebraic,
and dirk_order_nine_isLeast_of_roots. The native order predicate has
the reviewed order-first interface HasOrder 9 A b.

The shared CanonicalStageMemo proves coverage by the actual constructors.
There are 486 weighted identities and grade labels, 790 checked
constructor joins, and 200 sparse matrix derivatives. The packet
uses the reviewed finite order conditions and the already checked
uniform DIRK lower bound, which evaluates to 10 at order nine.
No Python check is trusted by the Lean proof.

The independent replay reconstructs the archived exact tableau and
matches all 100 literal matrix entries and ten literal output weights.
It checks the 486 unordered order conditions, in addition to the
native Lean check of all reviewed tree constructors.

## Reproducing the checks

Use Lean and Mathlib at the revisions in result.json. Set LEAN_PATH
to the approved c35 foundations and the pinned Mathlib libraries,
with an isolated empty output directory. Build these source files in
rebuild-order.txt order, one module at a time, using lean -j1 -M 3000,
then run the supplied audit consumers. No old packet object was
reused. This release is source-only; build hashes are receipts.
