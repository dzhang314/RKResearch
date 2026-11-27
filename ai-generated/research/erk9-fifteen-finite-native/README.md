# Native fifteen-stage exact ERK9 in finite characteristic

The [two rational coefficient charts](../erk9-fifteen-local-portfolio/README.md)
also give **one exact fifteen-stage ERK9 over each nontrivial commutative
ring of finite characteristic that inverts \(9!\)**. The ambient ring
need not be finite, reduced, local or a field.

**Lean endpoint:**
RKResearch.Certified.ERK9FifteenLocalRing.exists_exact_finite_characteristic.
In the theorem, a natural-number characteristic is supplied as CharP R p
with \(p\ne 0\). The theorem produces a strictly lower \(15\times 15\)
matrix \(A\) and a weight vector \(\boldsymbol b\) with HasOrder 9 and
not HasOrder 10.

The two literal common denominators \(D_1,D_2\) generate the unit ideal
because their integer Bézout value divides \((9!)^3\). The scalar
\(D_1\) has an idempotent positive power \(e\) in \(\mathbb Z/p\);
the proof finds such a power by repetition in this finite monoid.
The same power is idempotent after casting into \(R\). Scalar \(D_1\)
is invertible on the \(e\)-part, and \(D_2\) on the \(1-e\)-part:
there \(D_1\) is nilpotent so the complementary Bézout equation
makes \(D_2\) invertible. Denote the supported inverse scales by
\(d_1,d_2\).

The two tableaux are first evaluated with \(d_1,d_2\) as their scales,
then added. A generic lemma shows that projecting by an idempotent
before evaluating any ordinary rooted-tree condition is the same as
projecting its result. Each order condition through nine thus holds
on both complementary parts. Order ten would force \(5e=0\) by the
first chart's tenth bush, hence \(e=0\) as \(5\) is a unit; the second
chart's certified pair of tenth defects then gives a contradiction.

Two more general endpoints are available in the same namespace:
- **exists_exact_if_scalar_power_idempotent** over any nontrivial
  factorial-unit commutative ring with an idempotent positive power
  of \(D_1\);
- **exists_exact_of_projected_scales**, the underlying gluing theorem
  for given supported inverse scales.

This adds all finite-characteristic factorial-unit rings to the scope
of the [native local-ring result](../erk9-fifteen-local-native/README.md).
It does not supply a single universal tableau over \(\mathbb Z[1/210]\)
or handle arbitrary characteristic-zero nonlocal rings.

Replay from ai-generated/lean with matching Mathlib and both literal
witness packets present:

    lake build +RKCert.ReviewedNative.ERK9FifteenFiniteCharacteristic

Checked on Lean 4.36.0. The closed endpoint's axiom audit reports
only propext, Classical.choice and Quot.sound.
