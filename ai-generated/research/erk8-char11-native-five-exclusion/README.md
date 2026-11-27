# Native exclusion of the ERK8 five-off branch in characteristic 11

**RKResearch.Certified.Graded.ERK8CharEleven.no_five_off_char11**
takes only a strict original \(\mathrm{Fin}\,10\) tableau, the reviewed
HasOrder at eight, and \(11=0\) in its coefficient field. It excludes five
distinct off clocks over every such field, including arbitrary
extensions. It does not take a clean support count, an origin/sentinel
chart, numerical root locations, weights, or a reverse profile as input.

Together with the [native seven-off exclusion](../erk8-char11-native-seven-exclusion/README.md)
and the existing paid census, **order8_paid_only_one_or_four_off**
shows over every field that a literal width-ten order-eight tableau has
one off clock, or four off clocks and exactly five clean clocks. This is
a **census, not a stage floor**. The native exclusion of the remaining
one-/four-off alternatives is separate work. The full mathematical proof
is still in the [characteristic-11 note](../erk-eight-char11/README.md).

## Early physical producer

- **FiveEarlyPrefix** derives five clean clocks from the native paid
  census, earns the actual first center, and bounds its physical
  index to 4 or 5 via \(I(Xq)\bmod q=3+9X\), where
  \(q=X^2-X+8\).
- **FiveEarlyNewton**, **FiveEarlyMeasures**, **FiveEarlyFiveScalars**,
  and **FiveEarlyFiveExclusion** apply the literal three/four-node
  Newton adapter to the five-off prefix. The paid predecessor
  interpolation and hull measurements earn the existing scalar
  contradiction when the center is physical row 5.
- **FiveEarlyFour** earns \(A_{4,0}=-1\) and the first-three hull
  \(N_3\bmod q\propto1-X\) from the two paid pure primitive actions
  on the actual first clean row.
- **FiveEarlySentinel** shows that physical row 5 cannot be a
  clean root of \(q\). The pure sentinel plus its grade-four
  off-column correction would yield a zero primitive there, but
  its linear remainder \(10+7X\) does not vanish at a root of \(q\).
  It then forces physical row 5 to be off at clock 2 and gives the
  actual first-four off hull \(N_4\bmod q\propto6+2X\).
  These are additive five-off prefix adapters; the previously
  frozen seven-off modules and audit are unchanged.

## Dual cofactor and literal scalar endgame

- **FiveGeometry** obtains two actual late quadratic clean stages
  \(x<z\) and seven distinct bulk clocks. The bulk consists of all
  physical rows except \(0,4,9\), not an identified-clock tableau.
- **FiveProfile** earns all arbitrary values on the three anchors
  plus degree-at-most-five evaluations on the seven bulk clocks.
  The nine independent profile coordinates saturate the paid \(E_5\)
  cap. **FiveCofactor** proves that the reciprocal nodal
  cofactors on the bulk clocks, extended by zero at the anchors,
  span the actual \(E_5\) row annihilator. This is not obtained
  from the identically zero output-weighted quadratic defect.
- **FiveWeights** proves that the two actual clean weights are equal
  and nonzero by the two paid moments of \(L_0=X(X-6)(X-1)\) and
  \(XL_0\), rather than assuming or solving for a weight vector.
  **FiveLatePlacement** uses the nonzero first reflected cofactor
  multiple to force \(z=8\). The other clean root \(x\) is therefore
  at row 6 or 7; no affine second reflected profile is needed.
- **FiveTailPhysical** tests the original tableau with the actual
  grade-four masked \(\boldsymbol v=N_4(\boldsymbol c)\) on bulk
  rows and zero on anchors. The cofactor pairing with
  \(A\boldsymbol v\) balances its two late coordinates. The
  two earned reflected measurements are then the literal scalar
  equations consumed in **FiveTailScalar**.
- For \(x=6\), those equations produce the
  [impossible_four_late](../../lean/RKCert/ReviewedNative/ERK8CharElevenScalar.lean)
  scalar identity. For \(x=7\), they force the remaining off
  clock at row 6 to repeat the off clock 2 at row 5 by
  **fifth_off_eq_two** in the same scalar module. Both arguments
  preserve the actual physical off tags.

## Reproduction and scope

From the certificate package:

    cd ai-generated/lean
    lake build +RKCert.ReviewedNative.ERK8CharElevenFiveExclusion

The [serial Lean audit](lean-4.36-audit.txt) and
[exact source digests](source-sha256.txt) are for the fifteen additive
modules, checked on Lean 4.36.0 with Mathlib
fc4f59e577feb1a4956671bc04ac18aaaf8cd842. The audited declarations
depend only on the standard axioms propext, Classical.choice, and
Quot.sound. No other release has been measured for this packet.
