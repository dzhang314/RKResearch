# Lean proof of the literal twenty-one-stage midpoint tableau

This end-to-end Lean/Mathlib 4.36.0 certificate proves
the literal order-twelve midpoint witness over the rationals
and its specialization to arbitrary nonzero commutative rings.
It does not certify the sharper separate twenty-stage
factorial-localized tableau.

Module order under the ordinary RKCert reviewed namespace:

1. DIRK12Midpoint21Data
2. DIRK12Midpoint21Checks
3. DIRK12Midpoint21Flags
4. DIRK12Midpoint21Rings

The data is regenerated from the literal twenty-one-stage
JSON, including the even-step-power primitive coefficients.
The checks verify the actual stage nodes, branch constants,
eleven true matrix reads, every paid silent monomial, all
twelve scalar powers, and the ordinal integer tall trace.
The flag theorem uses the span of the actual generator
vectors \(\mathbf h^{2k}\mathbf c^j\) at grade \(2k+j\);
within-branch constancy gives the structural commutation.
The ordinary rooted-tree implication then follows directly
from the existing reviewed sufficient-flag theorem.

No flag-basis denominator is imposed on the target ring.
The twelve ordinary tree identities are first transferred
to literal integer matrix and weight numerators by
homogeneity and rational cast injectivity. The generic
reviewed scaled-moment bridge then sends the integer
identities to any ring that inverts the actual scales.
At the thirteenth tall tree, the separately checked
integer recurrence gives the normalized defect with
equation \(1024\,\delta=-231\). Thus the defect is a unit
in every nonzero ring inverting \(12!\); the two first
physical diagonals are distinct there as well.

Use the final theorem
\(\texttt{RKResearch.Certified.DIRK12Midpoint21.exists\_exact\_factorial}\)
for existence, and
\(\texttt{RKResearch.Certified.DIRK12Midpoint21.exists\_exact\_iff\_factorial\_unit}\)
for the corresponding width-21 existence equivalence. The
converse follows from the order-twelve tall tree, independent
of the construction.

The [toolchain transcript](lean-4.36.0.txt) reports only
\(\texttt{propext}\), \(\texttt{Classical.choice}\) and
\(\texttt{Quot.sound}\) for the endpoint theorems. All
computed checks use kernel decisions, not native-compilation
axioms. This Mathlib proof was checked on the explicitly
pinned Lean 4.36.0 release; it has not been replayed against
matching dependencies for other Lean releases.
