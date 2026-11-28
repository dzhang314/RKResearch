# Two S,D,D prefixes at singleton endpoints in the affine seven-clock graph

Assume an all-dirty strict ten-stage SDIRK tableau of ordinary order at least eight over a characteristic-zero field has exactly seven different clocks, with nonconstant affine singleton residual graph \(R\). The earlier [one-double-end exclusion](../sdirk-eight-all-dirty-seven-affine-one-double-end/README.md) forces both endpoint clocks to be singleton. Use S for a singleton clock and D for a doubled clock. This packet proves that the two actual ends **cannot both start S,D,D**. Combined with the [two-singleton-prefix exclusion](../sdirk-eight-all-dirty-seven-affine-two-singletons/README.md), exactly one of the two actual opening prefixes must have type S,D,D. The other prefix is still allowed S,S,D or S,D,S. This is not yet a full affine graph or ten-stage exclusion. Signed weights are allowed throughout.

## Ordered-pair geometry

Normalize the diagonal to one and write \(\ell=1/\gamma\) for the interval length. Use dimensionless centered coordinate \(v=(2x-\ell)/\ell\). Let the physical terminal have coordinate \(e=(\ell-2)/\ell\), the first \(-e\), and the graph zero \(s\). The three D labels are exactly the three simple roots of \(K(v,s;1)\) from the [affine Christoffel formula](../sdirk-eight-all-dirty-seven-affine-openers/README.md). Their cubic leading coefficient is \(-35J_3(s)\ne0\). There cannot be two opposite D labels: if \(v,-v\) were both D, the odd/even parities of \(J_3,J_4\) and the nonzero ratio \(J_3(s)/J_4(s)\) would give a common zero of both consecutive modes. This also forbids a D label at zero.

Name the two actual forward D clocks (physical rows 2,3) \(\alpha,\beta\), and write \(\chi\) for the third D label. In original centered coordinates the reverse D clocks are an ordered pair \(\rho,\sigma\) of two of these three, with their slot order supplied by the reverse end. The exact clock phases require:
\[
 \begin{array}{c|cc}
  &\text{arithmetic A}&\text{star S}\\\hline
  \text{forward }e&\beta-2\alpha&(2-\alpha-\beta)/4\\
  \text{reverse }e&2\rho-\sigma&(2+\rho+\sigma)/4 .
 \end{array}
\]
The signs in the second row come from reversing the actual dimensionless coordinates, not from assuming a symmetric tableau. Reversing the whole method allows the phase-pair cases A/A, A/S, S/S. Try all six directed selections of the reverse pair. With both phases A and the same two labels, the same ordering forces \(e=0\) (impossible as the two endpoints are singleton) and the swapped ordering forces \(\alpha+\beta=0\) (impossible opposite D labels). With both star phases and the same label pair, either order forces \(\alpha+\beta=0\). No A/S shared-pair case is discarded.

## Exact six-permutation projection

Equating the two expressions for \(4e\) gives one exact linear condition
\[
                 c+w_0\alpha+w_1\beta+w_2\chi=0
\]
for each remaining directed placement. Write \(L,M,T\) for the leading, negative quadratic, and linear coefficients of \(K\); the D-label sum is \(M/L\) and sum of pair products \(T/L\). Let \(a=w_0-w_2,\ b=w_1-w_2\) and \(z_\alpha=L(a\alpha+c)+w_2M\). At fixed first D clock \(\alpha\), the product of the two linear conditions obtained by assigning either of the other two clocks to \(\beta\), multiplied by \(L^2\), is
\[
       z_\alpha^2
           +b z_\alpha(M-L\alpha)+b^2L(T-\alpha M+L\alpha^2).
\]
This uses the genuine sum and product of the other two roots, so a repeated-label artefact \(\alpha=\beta\) is not introduced. The resultant of this quadratic in \(\alpha\) with \(K(\alpha,s;1)\) is the six-permutation norm up to a power of the known nonzero leading factor. Its only irreducible factors other than \(s\) and \(5s^2-3\) have degrees 8, 12, or 18. The two listed guard factors are excluded by \(J_3(s)\ne0\). No assumption \(s\notin\{\alpha,\beta,\chi\}\) is made.

In each exact projected field, a polynomial gcd gives the allowed first D labels. If \(b\ne0\), the linear equation recovers \(\beta\), and \(\chi\) is fixed by the sum. If \(b=0\), \(\alpha\) is fixed and the remaining two D clocks are recovered from their quadratic. Every irreducible quadratic is retained as an exact field extension with both orientations checked. The code verifies every reconstructed D root and distinctness, the root-sum and phase relation, and all actual arithmetic/star denominator and endpoint guards. There are twenty forward/reverse placements after factoring and reconstructing, six for A/A, six for A/S, and eight for S/S (counting the two assignments in each quadratic tower).

## Actual quartic fits

The first singleton is known at \(x=1\) with residual \(1/2\), so in uncentered normalized clock
\[
 R(x)=\frac{x-1+a_0}{2a_0},\qquad
 a_0=-(e+s)/(1-e),\quad b_0=(s-e)/(1-e).
\]
The reverse residual scale is \(\lambda=2R(\ell-1)=-b_0/a_0\), nonzero from the last singleton. The actual second- and third-row residuals in each orientation follow from the known literal formula, with reverse residuals converted by \(\lambda\). A repeated clock between the two prefixes must still use different physical pairs; the exact guard forbids shared residuals there. Off-graph D residuals and all other explicit guards are checked.

Put \(C=A_2+B R\). At the two actual singleton endpoints its values are \(L_4/R\), so
\[
 C=C_0+t(x-1)(x-(\ell-1))
\]
where \(C_0\) is the interpolating line. For each of the four actual D pairs, the quartic equation \(U=0\) is the exact affine condition
\[
   g(g-R(x))B
     +g(x-1)(x-(\ell-1))t=L_4(x-\ell/2)-gC_0(x).
\]
The code tests the four equations simultaneously. It does not assume any determinant nonzero; rank-zero and rank-one cases are retained if consistent, and \(B=0\) is disallowed as required by the original complete intersection. Every placement is rejected. No trace or fourth read is needed.

## Replay and scope

Run `python check_both_sdd.py` with SymPy 1.14 and python-flint 0.8 (the sibling `exact_support.py` handles the checked quadratic field arithmetic). The [Lean scalar companion](../../lean/RKCert/Research/SDIRKEightDirtySevenAffineTwoDoublePrefixes.lean) records the cleared norm identity and terminal-pair scalar equations only; these scalar identities check on Lean/Mathlib 4.36.0. The exact projective and chronological exclusion is the paper argument and replay. There is no finite-characteristic result.
