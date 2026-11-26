# One quadratic stage residual in explicit Runge–Kutta methods

Three results have different scopes:

1. A [dense chart width bound](SINGLE-DEFECT-CROSS-ORDER-FLOOR.md): if the quadratic stage residual is supported at one coordinate, a chart that recovers the derivative polynomials through tree size \(m\ge6\) needs at least \(2m-1\) stages. The [eleven-row argument](SINGLE-SECOND-ROW-DEFECT-SIX-LOWER-BOUND.md) gives the key chronological restriction; an [alternative eleven-row construction](REPAIRED-ELEVEN-ROW-DENSE-SIX.md) attains the bound at size six.
2. A [six-stage order-five classification over fields](ORDER-FIVE-MINIMAL-DEFECT-FIELD-THRESHOLD.md): with one quadratic stage residual coordinate and three independent pure defects through size five, the ordinary method exists exactly when \(-15\) is a square. The [literal witnesses](EXPLICIT-FIELD-WITNESSES.md) include a conjugate pair over the complex numbers and a tableau over \(\mathbb F_{17}\), with an [exact verifier](verify-f17.py). The classification does not exclude six-stage real methods outside these restrictions.
3. A [determinantal extension to commutative rings](DETERMINANTAL-RING-CRITERION.md): require vanishing \(4\times4\) minors of the pure defect matrix, rather than only bounding the ranks in residue fields. The argument reduces the possible failure of an exact clock identity to a square-zero element and lifts the square root of \(-15\) by one explicit correction.

The [causal rank formula](CAUSAL-NEXT-DEFECT-RANK.md) describes how new pure probes consume defect rank. The results here are algebraic proofs and exact examples, not Lean certificates.
