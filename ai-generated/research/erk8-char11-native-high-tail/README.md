# Native seven-off ERK8 endgame from the early chart

Lean now closes the late characteristic-11 seven-off argument, from the
literal strict \(\mathrm{Fin}\,10\) tableau and its early chart. This is
not yet an unconditional native seven-off exclusion or a native stage
floor. The complete mathematical argument is in the
[characteristic-11 note](../erk-eight-char11/README.md).

## Exact inputs and endpoint

The endpoint is **RKResearch.Certified.Graded.ERK8CharEleven.seven_off_contradiction_of_early_chart**.
It assumes the reviewed HasOrder at eight, strictness, \(11=0\), seven
distinct off clocks and three distinct clean clocks. Here
\(q=X^2-X+8\). It additionally assumes these three physical early-chart
receipts:

1. **HighPhysicalTail** supplies the physical last three off rows
   \(f<u<v\), with any later clean row after \(f\) at clock 1.
2. The hull \(N_4\) of the four earlier off clocks satisfies
   \(N_4=\beta(6+2X)+qV\), \(\beta\ne0\).
3. The clock 2 belongs to those four earlier off clocks, not the last
   three.

There are no supplied assumptions about a reflected-row value,
rank-equality profile, output-weight sign, nonzero tail measurement,
root splitting, or numerical ordering of clocks. The contradiction
derives \(c_f=2\) from the actual tableau and uses receipt 3.

## Proof chain

- **ERK8CharElevenTailSupport** constructs a grade-four column equal
  to the evaluations of \(N_4\) on the off rows and zero on clean rows.
  A degree-two clean-only correction is formed by Lagrange interpolation;
  the physical column \(\boldsymbol v\) and its action by \(A\) do not
  arise from merging coincident clocks.
- **ERK8CharElevenReflectedTail** proves **seven_off_paid_reflected_tail**.
  The two paid reflected tests of \(\boldsymbol v\) and the paid mixed
  pairing of \(\boldsymbol g\) with \(A\boldsymbol v\) give the exact
  two-receiver balance and tail equation. This bypasses a separate
  identification of the full grade-four and grade-five annihilators.
  **seven_off_paid_tail_product_of_ratio** consumes the measured
  nonzero ratio to derive \(c_u c_v=8\) using the published scalar
  theorem **high_tail_product**.
- **ERK8CharElevenHighHull** proves **seven_off_paid_hull_remainder**
  with no early-chart assumptions. The actual quadrature of
  \(L_0=X(X-6)(X-1)\) is zero and its clean contribution vanishes.
  The earned nonzero off weights give a zero top coefficient for the
  interpolant of \(L_0/q\). Thus the literal seven-clock hull has a
  nonzero remainder proportional to \(L_0\bmod q=4+3X\).
- **ERK8CharElevenTailMoments** proves
  **seven_off_paid_tail_hull_remainder** and
  **highTail_moments_of_hull_remainder**. Cancelling \(6+2X\) modulo
  \(q\) gives the last-three remainder \(\delta(1+7X)\), with
  \(\delta\ne0\). The two quotient measurements give
  \(\mathcal B_2=-\delta^{-1}\ne0\) and \(2\mathcal B_3=\mathcal B_2\)
  in the normalization that removes the common weight scale \(\lambda\).
- **ERK8CharElevenHighEndgame** proves **high_fifth_clock_of_hull**
  by extracting two coefficients in the unique linear remainder.
  Together with **high_fifth_eq_two** this forces \(c_f=2\), and the
  complete conditional endpoint follows.

The existing scalar consumers are in
[ERK8CharElevenScalar.lean](../../lean/RKCert/ReviewedNative/ERK8CharElevenScalar.lean);
the completed [physical head and weight adapters](../erk8-char11-native-head/README.md)
are the only new prerequisites beyond the previously reviewed modules.

## Remaining early producer

The three early receipts have mathematical proofs, but are not earned
by this Lean packet. A shorter route to their mechanization is available.
When the first center is physical row 4, the actual paid primitive of
\(q\) gives \(A_{4,0}=I(q)(6)/q(0)=-1\), because the defect term from all
earlier off rows vanishes there. Applying the same row to the first
three off hull \(N_3=X^3-s X^2+t X-r\) gives
\(I(N_3)(6)=-N_3(0)\), or \(5-6s+7t-7r=0\). This forces
\(N_3\bmod q\) proportional to \(1-X\); the sentinel in the
[mathematical proof](../erk-eight-char11/README.md) then fixes the
fourth off clock at 2 and gives the early hull receipt.

If four consecutive off rows precede the first center, the actual
\(A[(Xq)(\boldsymbol c)]\) and \(A(\boldsymbol c\,\boldsymbol g)\)
already show that their degree-four hull is proportional to
\(I(Xq)\bmod q=3+9X\), without the augmented determinant calculation.
As the remainder is nonzero, five such consecutive prior off rows
are impossible by the polynomial root bound. The first-center-at-5
contradiction still needs the three/four-node native causal Newton
coefficient argument. These comments describe source-level shortcuts,
not additional kernel-checked statements.

## Reproduction

From the certificate package:

    cd ai-generated/lean
    lake build +RKCert.ReviewedNative.ERK8CharElevenHighEndgame

A serial replay of all five new sources passed on Lean 4.36.0 with
Mathlib fc4f59e577feb1a4956671bc04ac18aaaf8cd842. The
[Lean log](lean-4.36-audit.txt) prints seven endpoints, each with only
the standard axioms propext, Classical.choice, and Quot.sound. The
[source digests](source-sha256.txt) bind exactly the checked files.
No other Lean release is claimed by this replay.
