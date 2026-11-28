# Kernel-checked fixed-q 29-adic scalar inputs

This is a scalar proof packet, separate from the already-checked fixed
modulus tableau and the [unbounded mathematical order result](README.md).
It formalizes the actual raw two-row head solve at the fixed choices
\(g=6,\ R=15,\ d=26\). There is no assertion here of full rooted-tree
order for a tableau over the 29-adic integers.

In the namespace **RKResearch.Certified.ERK10FixedQ29Adic**:

- **decic_residue**, **decic_derivative_residue**, and
  **decic_leading_residue** check the literal published \(P\):
  \(P(2)=0\), \(P'(2)=16\), and leading coefficient \(25\), in
  \(\mathbb F_{29}\). The evaluation and derivative use an integer
  Horner jet proved to agree with Mathlib's polynomial evaluation.
- **avg_integer_moments** checks a 10-point integer quadrature
  for \(I(x^j)=1/(j+1)\) through degree nine. Its support is
  \(0,\ldots,9\), with common denominator \(7257600\).
  The integral formulas of this scalar solve have degree at most
  nine, so they can be evaluated by this exact quadrature.
  **map_avg** and the formula-specific map lemmas prove compatibility
  with any ring homomorphism reflecting units. Inverse means the
  inverse of an actual ring unit at the selected point, not an
  unqualified division operation.
- **head_residue** and **head_derivative_residue** check the true
  symmetric head coefficients \(s_h=2,\ p_h=17\) modulo 29,
  the ordered residues \(a=11,\ b=20\), and derivatives \(20,9\).
- **paidHead_of_residue** proves actual uncancelled denominators
  are units whenever \(c\) has residue 2: \(2,3,5,c\), the quadrature
  denominator, the three tail solves, \(T_3(0)\), the head determinant,
  and \(C_\nu\). The last six residues in this list are
  \(27,27,24,4,14,9\).
- **scalar_existence** composes the two simple-root lift operations
  for any unit-reflecting homomorphism to \(\mathbb F_{29}\) with
  that lifting property. It produces the decic root \(c\), the ordered
  head roots \(a,b=s_h-a\), the three exact tail residues \(22,7,27\)
  for \(h,f,e\), and all the paid guards above.

At this stage **scalar_existence** takes simple-root lifting as an
explicit premise. The actual 29-adic application of Hensel's lemma
is a separate module. The exact origin identity linking the decic
to the vanishing cofactor, the late contact at \(h\), the quartic
remainder proportionality plus host value, the remaining physical
pivots and decoder, and the final rooted-order argument are not part
of this three-module release.

Lean/Mathlib 4.36.0 checked these modules with standard axioms only.
The [audit](lean-scalars-4.36-audit.txt) preserves all entries. A
full dependency build on other Lean versions is not claimed.

From the repository root:

    cd ai-generated/lean
    lake build +RKCert.ReviewedNative.ERK10FixedQ29AdicResidues:olean

Check the source manifest from the repository root:

    sha256sum -c ai-generated/research/erk10-fifteen-fixedq-29adic/lean-scalars-sha256.txt
