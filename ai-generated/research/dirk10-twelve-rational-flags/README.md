# Compact native flag replay of the twelve-stage rational DIRK10

This is an independent native certificate for the
[already literal twelve-stage tableau](../dirk10-twelve-rational-three-ports/tableau.json)
from the [Jacobi-correction construction](../dirk10-twelve-rational-three-ports/README.md).
It is not a second claimed tableau and does not duplicate the construction.
The reviewed mathematical lower bound over \(\mathbb Q\) is
[separate](../causal-profile-reduction/dirk-order10-rational-lower-twelve.md);
the complete stage minimum over \(\mathbb Q\) is not a single native theorem.

The Lean conclusions are \(A\) lower triangular, \(\mathtt{HasOrder}\ 10\ A\ b\),
and not \(\mathtt{HasOrder}\ 11\ A\ b\), for the very same literal rational
entries. The order theorem is
`RKResearch.Certified.DIRK10RationalTwelveFlagReplay.order_ten` and the
bundled existence theorem in that namespace is `exists_exact`.
The factorial-scaled eleventh-star residual is \(1/2488320\).
No native-code arithmetic oracle, numerical solve, or assumed rank enters
this proof.

## Compact certificate and why it works

The stand-alone standard-library Python generator takes the literal JSON
and computes exact echelon rows in homogeneous grades 0 through 9, with
respective sizes \(0,0,0,1,2,4,6,8,9,10\). The frame of a grade is a
submodule spanned by these literal rational vectors, not an assumed
complete basis of all defects. Pivot-coordinate projection is only a
candidate span witness: Lean verifies its pointwise equality with the
required vector in every closed case.

The generic [rational bridge](../../lean/RKCert/ReviewedNative/RationalFlagReplay.lean)
then proves that the frame closes under the next tableau action, the next
clock multiplier, each paid componentwise product, and each paid monomial
primitive defect. The actual output row kills the frame at every paid
grade and has the exact clock moments. The reviewed
`SufficientGradedFlags.hasOrder` theorem inducts on the actual binary
rooted-tree constructors, so the certificate does not assume that a
Python enumerator covered all roots. All finite scalar checks use
`decide +kernel`.

## Ring specialization

The separately named native
[`DIRK10RationalTwelveFlagRings`](../../lean/RKCert/ReviewedNative/DIRK10RationalTwelveFlagRings.lean)
module recovers integer numerator moment equations from the established
rational theorem, using injectivity into \(\mathbb Q\) and the reviewed
homogeneity of \(\Phi_t\). For a tree of size \(n\), the common numerator
scaling is \(D^n\): \(n-1\) matrix factors and one output factor.
In a target commutative ring, if \(D\) is a unit, take a right inverse of
\(D\), multiply all numerators by it, and cancel the mapped \(D^n\).
No denominators from the row reduction are added to the target assumptions.

The common literal denominator is
\[
 D=101588047290852467338246934187117072000
  =2^7 3^5 5^3 7\cdot11\cdot17^2\cdot19\cdot151\cdot173\cdot607
    \cdot653\cdot1063\cdot1499\cdot1553^3.
\]
The lifted integer star equality is
\(2488320(\gamma(t)b_{\rm num}^\mathsf{T}\Phi_t(A_{\rm num})-D^{11})
 =D^{11}\).
If order eleven held after specialization, its left side would be zero
while the right side is a unit. `exists_exact_of_unit` therefore certifies
the exact upper bound in every nontrivial commutative ring paying this
literal \(D\). It does not assert that \(D\) must be a unit for every way
to attain order ten in twelve stages, or extend the rational lower bound
to coefficient fields in which eleven stages could exist.

## Reproduction

Run from `ai-generated/lean`, with the reviewed root and pinned Mathlib:

```sh
lake build RKCert.ReviewedNative.DIRK10RationalTwelveFlagRings
lake env lean AuditReviewedNativeDIRK10RationalTwelveFlagReplay.lean
```

The typed upper proof plus ring specialization was replayed on the pinned
Lean 4.36.0 package. To regenerate the compact arithmetic source, use
`generate-flags.py` with the literal JSON path followed by the
`RKCert/ReviewedNative` output directory. The denominator transport and
generic bridge are maintained separately rather than generated.
The shipped `make-portable-audit.py` extracts just the literal matrices,
basis and pivots from the generated `...FlagReplayData.lean` into a
stand-alone Lean Core arithmetic replay. It does not try to replace
Mathlib or the typed native order proof.

The stand-alone arithmetic replay passed on **4.34.1, 4.35.0, 4.36.0,
and 4.37.0-rc1**, using only those compilers' standard core libraries.
The logs distinguish this portability check from the full native
typed proof, which uses the pinned project and Mathlib at 4.36.0.
The input tableau SHA-256 is
`5577dfeb4762a82046c98432757b6a5840b7caf1170dbcdbf74c8973f6d4785a`.
