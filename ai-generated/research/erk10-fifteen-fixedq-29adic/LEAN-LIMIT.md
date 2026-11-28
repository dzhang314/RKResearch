# Unbounded native scalar Hensel in the inverse-limit model

The proof uses the ordinary inverse-limit ring
\[
  \mathcal Z_{29}
  =\varprojlim_{n\ge0}\mathbb Z/(29^{n+1}),
\]
implemented as the subring of compatible coordinates, with
the literal canonical reduction maps between moduli. It does
not import the analytic p-adic construction, nor claim a Lean
isomorphism with Mathlib's analytic type.

The following endpoints are in namespace
**RKResearch.Certified.ERK10FixedQ29Adic.Digits**:

- **step** lifts a root of a polynomial by one digit, even when
  the polynomial has coefficients in the higher modulus. It uses
  the first-order polynomial expansion and the fact that the
  higher square of the digit increment is zero.
- **lift_compatible** iterates this for any compatible family of
  polynomials with a simple root in the base residue field.
- **simpleLift_limit** and **unique_of_simple_residue** give
  existence and uniqueness in \(\mathcal Z_{29}\). Its projection
  to \(\mathbb F_{29}\) reflects units: if the first coordinate is
  a unit, coordinatewise inverses are compatible and give an
  inverse in the limit ring.
- **scalar_existence_limit** uses the [literal scalar solve](LEAN-SCALARS.md)
  and [exact origin identity](LEAN-ORIGIN.md). It gives one
  \(c\) with the specified decic and the true origin residual zero,
  the ordered roots \(a,b=s_h-a\) of the actual head quadratic,
  the exact six residues \(c,a,b,h,f,e=2,11,20,22,7,27\),
  and all uncancelled scalar-head guard units.
  This is a point in the infinite compatible ring itself, not
  an inference from finitely many replays.

## What remains for the full Lean tableau endpoint

The existing [unbounded mathematical order proof](README.md) is
stronger than this native scalar theorem. The following exact
obligations remain:

1. For the cardinal polynomial \(\widetilde\mu\bmod D_7\) and
   \(q_1\) built from its two literal \(f,g\) phase values, prove
   the third phase identity at \(h\).
2. Prove the seven polynomial-coefficient equalities
   \(E_i B_0=B_i E_0\) over the scalar coefficient ring, where
   \(E=(\widetilde\mu U_0-y(1-y)q_1)\bmod D_7\) and
   \(B=(\widetilde\mu T_4)\bmod D_7\).
   The exact residue is \(B_0=4\pmod{29}\), so the constant
   coefficient is an appropriate fixed unit pivot. With
   \(\sigma=-E_0/B_0\), certify \(U=U_0+\sigma T_4\) and
   \(U(R)=-1\). The latter follows from the definition of \(U_0\)
   and the vanishing \(T_4(R)=0\).
3. Prove the remaining actual cardinal, pair and physical pivot
   conditions, the weighted and marked pairings, and the
   triangular decoder with its original guards. For example,
   the seven cardinal residues at \(a,b,d,e,f,g,h\) are
   \(7,6,11,21,14,24,9\), all nonzero. These finite residue
   checks can pay inversions, but cannot replace the exact
   algebraic identities in steps 1–2.
4. Connect the resulting literal matrix \(A\) and
   \(\boldsymbol b\) to the actual rooted-order predicate and
   next-tree unit, then transfer that full theorem through each
   projection. No full order statement is made by these modules.

Lean/Mathlib 4.36.0 checked the native proof; the
[complete axiom audit](lean-limit-4.36-audit.txt) lists standard
axioms only. No four-release dependency build is claimed.

From the repository root:

    cd ai-generated/lean
    lake build +RKCert.ReviewedNative.ERK10FixedQ29AdicLimit:olean

To verify this extension after the scalar and origin packets,
run from the repository root:

    sha256sum -c ai-generated/research/erk10-fifteen-fixedq-29adic/lean-limit-sha256.txt
