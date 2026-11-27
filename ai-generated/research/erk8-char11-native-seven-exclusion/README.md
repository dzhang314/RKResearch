# Native exclusion of the ERK8 seven-off branch in characteristic 11

The checked theorem **RKResearch.Certified.Graded.ERK8CharEleven.no_seven_off_char11**
takes an original strictly explicit tableau on \(\mathrm{Fin}\,10\), the
reviewed HasOrder at eight, and \(11=0\) in its coefficient field. It
rules out seven distinct off clocks without supplying the number of
clean clocks, an early chart, assumed roots, or any scalar profile.
This applies to every field of characteristic 11, including arbitrary
extensions.

This is a branch exclusion, **not a stage-floor theorem**. The one-,
four-, and five-off alternatives still need their own native closures.
The existing [mathematical characteristic-11 proof](../erk-eight-char11/README.md)
is not being replaced or expanded in mathematical scope.

## Native proof chain

1. **ERK8CharElevenHighEarlySetup** earns the clean anchors at physical
   origin, center, and terminal from the original 7/3 census. The
   early off-clock count proves that the center is at least row 4.
   Before the center, \(A[(Xq)(\boldsymbol c)]\) equals
   \(A(\boldsymbol c\,\boldsymbol g)/\theta\) by strict causality and the
   fitted off head \(\theta q\), where \(q=X^2-X+8\). Its two grade-four
   receipts force a common degree-two multiple of \(q\) to match the
   primitive on earlier off clocks. The difference is a nonzero
   degree-four polynomial since the primitive has nonzero remainder
   \(3+9X\) modulo \(q\). Thus the center is row 4 or row 5.
2. **ERK8CharElevenHighEarlyFour** earns the clean incoming coefficient
   \(A_{4,0}=-1\) from the actual pure \(q\) action. For the first
   three off hull \(N_3=X^3-sX^2+tX-r\), the next paid pure action
   gives \(I(N_3)(6)=-N_3(0)\), hence \(5-6s+7t-7r=0\).
   This pins \(N_3\bmod q\) to a nonzero multiple of \(1-X\).
3. **ERK8CharElevenHighSentinel** adds a degree-one off correction to
   the pure sentinel \(X(X-6)(X+8)\). Its physical vector vanishes at
   each row before row 5, so its \(A\)-image vanishes through row 5.
   Comparing the nonzero remainder \(10+7X\) of that paid primitive
   with the actual four-off hull forces \(c_5=2\). This produces all
   three receipts for the earlier [native late endgame](../erk8-char11-native-high-tail/README.md),
   closing the row-four-center branch.
4. **ERK8CharElevenEarlyNewton** earns the actual top-coefficient
   equations at \(m=3,4\). For each input power, only the \(m-1\)
   literal preceding off rows are interpolated. Strict causality gives
   the matching physical \(A\)-images on the first \(m\) off rows
   without requiring an interpolation value at the current row.
   The paid low-degree defect profiles kill the low polynomial part
   under the top-coefficient functional.
5. **ERK8CharElevenEarlyMeasures** and **ERK8CharElevenEarlyFiveScalars**
   verify the rest of the row-five-center reduction. The actual
   four-off hull has the remainder \(3+9X\), up to a nonzero scale
   from step 1. Only the measurements of the hull and of \(X\) times
   the hull, together with the quadratic recurrences, are needed to
   determine the leading-coefficient ratios. The physical fourth
   off clock must be \(-1\), and the third-row equations give the
   two-clock quotient ratio 4. No augmented determinant is assumed.
6. **ERK8CharElevenHighExclusion** derives the two scalar equations for
   the literal off clocks and invokes the earlier checked
   [impossible_first_clean_five_prefix](../../lean/RKCert/ReviewedNative/ERK8CharElevenScalar.lean).
   This closes row 5 and hence completes the unconditional seven-off
   exclusion.

The same entry module also proves **order8_paid_only_one_four_or_five_off**:
over any field, the literal width-ten order-eight tableau has one off
clock, or four off and five clean, or five off and five clean with
\(11=0\). Under \(11=0\) and no root of \(q\) in the coefficient field,
**order8_char11_nonsplit_forces_one_off** leaves just the singleton-off
case. Neither corollary excludes that case.

## Reproduction

From the certificate package:

    cd ai-generated/lean
    lake build +RKCert.ReviewedNative.ERK8CharElevenHighExclusion

All seven new source modules were checked serially on Lean 4.36.0 with
Mathlib fc4f59e577feb1a4956671bc04ac18aaaf8cd842. The
[Lean log](lean-4.36-audit.txt) records only standard axioms
propext, Classical.choice, and Quot.sound; the
[source digests](source-sha256.txt) bind the checked source bytes.
Compatibility with additional Lean releases has not been measured
for this packet.
