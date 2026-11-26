# The explicit stage bound for weighted rooted order

**Theorem.** Let \(m\ge0\), \(r\ge13\), and let a field have \((m+r)!\ne0\). Suppose a strictly lower triangular tableau has an actual row \(\boldsymbol\beta\) exact on all rooted stage profiles through tree size \(r\) for
\[
                  \ell_m(P)\coloneqq\frac1{m!}\int_0^1(1-X)^mP(X)\,dX .
\]
The integral is evaluation of a formal primitive; no ordering or topology is needed. The literal prefix ending at the last nonzero coefficient of \(\boldsymbol\beta\) has at least \(\lceil3r/2\rceil\) stages. The row need not arise as a tap of a pre-existing ordinary method, provided its weighted rooted tests hold.

This extends the [odd explicit stage bound](06-ODD-EXPLICIT-STAGE-BOUND.md) from the ordinary integral to weighted rooted order, and then to even orders. The [order-eleven refinement](08-ORDER-ELEVEN-THRESHOLD.md) lowers the effective-order threshold to 11. This is a mathematical proof, not a Lean certificate.

## Weighted words and the forward and reverse flags

The actual \(E_g,F_g\), clock \(C\), diagonal \(Y=I-C\) and commutator \(D=CA-AC-A^2\) are unchanged. A weighted exact row still annihilates every pure \(F_g\) within its budget. The formal identity \(XJ-JX=J^2\) gives the same zero tests on \(D\mathbf v\).

For a vector \(\mathbf v\in E_g\), exactness gives
\[
 \boldsymbol\beta A^aY^hA^b\cdot\mathbf v
   = \frac{(m+a+h)!}{(m+a)!}\,
       \boldsymbol\beta A^{a+b+h}\cdot\mathbf v
                  \qquad(a+b+h\le r-1-g).
\]
Indeed \(\ell_m(JP)=\ell_{m+1}(P)\) and \(\ell_m((1-X)^hP)=(m+h)!\ell_{m+h}(P)/m!\). This supplies the complete paid word premise of the penultimate-tap proof f5986589…, which never otherwise uses an underlying ordinary row. A final coordinate at clock 1 adjoined to the spaces is killed by \(A,Y\) and every positive word, just as in that proof.

For odd \(r=2d+1\), \(d\ge6\), suppose the prefix ending at the last actual \(\boldsymbol\beta\)-read has \(3d+1\) stages. Fewer are already excluded by the old paid weighted grade-five floor. Define
\[
 \mathbf h_1\coloneqq(m+1)\boldsymbol\beta A-\boldsymbol\beta Y,
 \qquad
 \mathbf h_2\coloneqq(m+2)\boldsymbol\beta YA-\boldsymbol\beta Y^2.
\]
The weighted words make the reverse flag with these seeds vanish on \(E_g\) in the identical degrees. A row plateau would contain \(\boldsymbol\beta Y\) by the nilpotent \(A Y^\dagger\) argument, contradicting \(\boldsymbol\beta Y\cdot\mathbf1=1/[m!(m+2)]\ne0\). Separation through \(d\) uses the Gram with weight \(X(1-X)^m\); the old weighted grade-five proof gives \(\dim F_d\ge d\). The final clock is 1 if \(\mathbf h_1=0\). At clock 1 the final basis vector cannot belong to \(E_d\): subtracting its \(d+1\) clock-moment equations gives the Gram with weight \(X(1-X)^{m+1}\) on its possible model divided by \(X\). The Gram budgets are at most \((m+r)!\). This also forces the final clock to be different from 1 if \(\mathbf h_1\ne0\), since otherwise that extra basis vector would add one rank to the already full reverse and forward count.

Augmenting by the last basis vector only when \(\mathbf h_1=0\) therefore again leaves one available rank increment per degree. The penultimate \(\boldsymbol\beta A^{d-1}\) vanishes on the actual late vectors through degree \(d\). The bare localized cutoff and descending Vandermonde argument of MAXIMAL-ODD-CLOCK-DELAY.md apply: the moments \(\boldsymbol\beta Y^h A^j\) differ from \(\boldsymbol\beta A^{h+j}\) by a paid nonzero factorial. Therefore the augmented closure delay is at least \(d-1\) and its exact reverse flags are the same. The dual flag identification in REVERSE-CLOCK-CHARTS.md uses only these ranks and is independent of \(m\). Its optional identity \(\mathbf h_2=-\mathbf bD\) was specific to \(m=0\); it is not used here.

The early-prefix obstruction also transfers. If all positive tap rows factor on \(E_d\) through the first \(2d\) coordinates, they give actual prefix outputs \(\ell_{m+1},\ldots,\ell_{m+d}\) on all degree-\(d\) profiles. Their simultaneous reads separate those profiles by the weight \(X(1-X)^{m+1}\) Gram and the literal origin. Their span consists of reads against \((1-X)^{m+1}\) times a polynomial of degree at most \(d-1\), up to scalar normalization. The Gram with weight \((1-X)^{m+1}\) supplies a combination equal to the ordinary integral through degree \(d-1\). The ordinary order-\(d\) prefix has \(d-1\) pure dimensions through degree \(d-1\), by the unrestricted size-six floor and strict growth. The increase to degree \(d\) is still strict because the actual shift-one read of \(\mathbf c\) is \(1/(m+3)!\ne0\), contradicting any pure \(A,C\)-invariant plateau as in the ordinary argument. Then \(2d+1\) independent directions would fit in only \(2d\) coordinates. This supplies the genuinely late positive tap.

## Actual terminal Newton action and reweighting

The physical tail filling uses the same distinct-clock Vandermonde. For a localized late vector at a nonendpoint clock, the weighted penultimate tap is a paid nonzero factorial multiple of \((1-\theta)^{d-1}\boldsymbol\beta\) there, so its output vanishes. Therefore an actual late positive tap forces a nonzero detector read and fills every available detector position. The Newton vectors \(\mathbf v_j\) are constructed from the actual detector coordinates with the same denominators \(\lambda_i\nu'(c_i)\); there is no global singleton clock condition.

In the one-detector branch with nonzero first residual take terminal output \(\boldsymbol\zeta\coloneqq\boldsymbol\beta\), weight shift \(M=m\) and \(L=d\). In the augmented branch take \(\boldsymbol\zeta\coloneqq\boldsymbol\beta A\), shift \(M=m+1\) and \(L=d-1\); the added final coordinate does not contribute. In both cases \(M+L=m+d\), and the last actual \(\boldsymbol\zeta\)-read at the detector terminal site is nonzero:
\[
 \lambda_t=
 \begin{cases}
       -\zeta_t y_L,&\mathbf h_1\ne0,\\
       -(m+1)\zeta_t y_L,&\mathbf h_1=0 .
 \end{cases}
\]
For the second formula all later coefficients of \(\boldsymbol\beta Y\) are zero at the detector terminal site, and \(\boldsymbol\beta Y=(m+1)\boldsymbol\beta A\).

The no-missing-shift proof uses the word identity at weight \(M\) and the old stage floor for the next actual weighted tap \(\boldsymbol\zeta A\). The first word is \(y_j\gamma_j=(1+(M+1)\alpha_j)\gamma_{j+1}\). A zero shift followed by a positive-length visible run contradicts the paid single-\(Y\) test. Any trailing-zero profile with a nonzero run would have at most one entry in that run by the distinct clocks. It would put the last actual read of \(\boldsymbol\zeta A\) no later than row \(2d+1\), below its old paid stage floor \(3d-1\) or \(3d-2\). The penultimate of \(\boldsymbol\zeta\) in both cases is the original \(\boldsymbol\beta A^{d-1}\). Exactly as in the ordinary proof it gives
\[
                         \alpha_j=-\frac1{m+d-j}.
\]
The commutator coefficient \(\alpha_j-\alpha_{j+1}-\alpha_j\alpha_{j+1}\) is zero, while \(\alpha_j(y_j-y_{j+1})\ne0\). Purity therefore forces the intermediate terminal reads to vanish. The last \(L\) ratios \(\zeta_i/\lambda_i\) are constant by Lagrange and Vandermonde, allowing all those coordinates to be removed by adding a multiple of \(\boldsymbol\lambda\). This preserves the \(\ell_M\) exactness through size \(2d\) in the first branch and \(2d-1\) in the augmented branch. Both require a prefix larger than \(2d+1\) by the old weighted floor.

In the invariant terminal hyperplane branch the last lifted vector satisfies \((m+1)\beta_s\omega=y_L\gamma_L\) instead of the unweighted equality. The paid nonzero factor \(m+1\) does not affect the deduction. If \(\omega\ne0\), the same single-\(Y\) test forces every earlier shift nonzero and then yields a nonzero forbidden penultimate tap. If \(\omega=0\), the last nonzero positive tap and the last nonzero read require two different endpoint clocks in one detector tail, again impossible. Thus no odd equality tableau survives.

For even effective order \(r=2d+2\ge14\), the actual row \(\boldsymbol\beta A\) is exact for \(\ell_{m+1}\) through size \(2d+1\). Its final contributing index is at least \(3d+2\) by the odd case, but is strictly earlier than the last contributing index of \(\boldsymbol\beta\). This gives \(3d+3=\lceil3r/2\rceil\), completing the weighted theorem. For an ordinary explicit tableau over a nonzero commutative unital ring, use the paid residue-field specialization of e73766c3… to obtain the stage lower bound without requiring the coefficient ring to contain the rationals.
