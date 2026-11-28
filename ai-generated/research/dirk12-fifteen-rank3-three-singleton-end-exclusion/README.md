# DIRK12/15: the remaining four-cancelling-pair chronology is impossible

On the ordinary real order-twelve fifteen-stage \(C(2), f_5=3\) face, **there cannot be four distinct active cubic dirty labels**. The [four-active-label census](../dirk12-fifteen-rank3-four-active-cubic/README.md) excludes the four noncancelling triples and reduces the alternative to four genuine cancelling pairs. The [end-run reduction](../dirk12-fifteen-rank3-four-singleton-end-exclusion/README.md) leaves exactly three singleton dirty labels before the first interior clean row and exactly three after the last interior clean row. The remaining two central physical dirty stages are excluded below, regardless of their individual positions. This is not an unrestricted fifteen-stage exclusion; the real interval remains **15–16**. All other open label counts and weighted-invisible cases are distinct.

Use the notation of the end-run reduction. In particular \(H\) is the monic hull of the four distinct dirty labels, \(P\in P_3\) is the nonzero polynomial taking values \(h_z\) on those labels, and \(L(S)=\sum_z S(z)/(h_zH'(z))\) is the genuine dirty barycentric functional on \(P_5\). The clean clocks in physical order are \((0,\gamma_1,\ldots,\gamma_5,1)\). The two actual \(6+5=11\) cuts and the forward/reverse grade-four clean-supported profiles give
\[
 L=sL_+(\mathbf x)+tL_-(\mathbf x),\qquad
 a(\mathbf x)s+b(\mathbf x)t=c(\mathbf x)s+d(\mathbf x)t=0
\]
with \(\mathbf x\ne0\), \(st\ne0\), and \((a,b)\) having no simultaneous projective zero. Thus \(e=ad-bc=0\), and we may use the representative \(s=b(\mathbf x),\,t=-a(\mathbf x)\). This rescales \(L\) by a nonzero constant. Clock ratios and the two monic hull coefficients below do not change under that scaling; replacing \(P\) by the corresponding nonzero Hankel cofactor representative only rescales the final gates.

For all 120 fixed clean permutations the coefficient of \(x_0^4\) in \(e\) is nonzero, by the exact arithmetic below. Hence \(x_1\ne0\) at a projective solution, and we may put \(\mathbf x=(q,1)\). Write \(\mu_j=L(X^j)\) for the canonical scaled moments in this representative. Operations below are evaluated in the finite coefficient algebra defined by the single degree-four equation \(e(q,1)=0\); no unknown DIRK coefficients are reduced modulo a prime.

## The two actual missing labels are functions of the clean chronology

For the first interior clean forward row at \(u=\gamma_1\), exactly one of the four dirty labels, say \(w_f\), is absent from its prefix. At a clean row the aggregate physical tap \(g_z\) to both rows of label \(z\) satisfies
\[
             \sum_z g_z h_z=\sum_z z g_z h_z=0
\]
because \(A\mathbf h\) and \(A(C\mathbf h)\) are genuine grade-four and grade-five pure states and vanish there. These are the actual taps, with zero used for a missing stage. The two barycentric probes give the full two-dimensional annihilator on four labels, so \(g_z=(\alpha+\delta z)/(h_zH'(z))\). As \(g_{w_f}=0\), this simplifies to \(g_z=\delta(z-w_f)/(h_zH'(z))\).

Put \(V=X(X-u)\), \(I_j=\int_0^u V(X)X^j\,dX\), and \(v_j=L(VX^j)\). The genuine scalar primitive on each \(VX^j\), \(j=0,1,2\), is exact at this clean row: its degree-five error lies in the actual \(F_5=\mathbf h P_2(\mathbf c)\). Since \(V\) kills the origin and the row itself, and there are no other clean stages in its prefix, this gives \(I_j=\delta(v_{j+1}-w_fv_j)\). A nonzero rescaling of \(L\) simply rescales \(\delta\) inversely. In particular \(\delta\ne0\) since \(I_0\ne0\). Eliminating it from the first two identities gives
\[
                 w_f=\frac{I_0v_2-I_1v_1}{I_0v_1-I_1v_0}.
\]
The denominator is a verified unit on the whole fixed quartic algebra, not an assumption about a pivot chosen from an unknown tableau.

For the first clean row in reverse physical chronology the same computation uses \(\widehat N=\beta^{-1}A^{\mathsf T}\beta\), \(V=(X-\gamma_5)(X-1)\) and \(I_j=\int_{\gamma_5}^{1} V(X)X^j\,dX\). Use the actual pure weighted reverse grades four and five, whose normalized coordinates are \(\mathbf hP_1,\mathbf hP_2\). This recovers its missing label \(w_r\) with a separately verified unit denominator. The arithmetic also verifies \(w_f-w_r\) a unit, so the case of the same label missing from both end runs is excluded. Within each end run the three present labels are already known distinct. The derivation allows the missing label or any present label to share a clock with any clean stage, including 0 or 1.

## The true monic dirty hull is fixed

The four labels are distinct and include \(w_f,w_r\), so write
\[
     H=(X-w_f)(X-w_r)Q,\qquad Q=X^2+q_1X+q_0 .
\]
Set \(n_i=L(X^i(X-w_f)(X-w_r))\), \(0\le i\le3\). The exact vanishings \(L(H)=L(XH)=0\) are justified by pointwise vanishing on all dirty labels. Their two-by-two determinant \(\Delta=n_0n_2-n_1^2\) is another verified unit, giving the only possible values
\[
 q_0=\frac{n_1n_3-n_2^2}{\Delta},\qquad
 q_1=\frac{n_1n_2-n_0n_3}{\Delta}.
\]
No extra condition on the two uncovered roots was imposed.

## A grade-four primitive obstruction on the three actual dirty stages

Use either physical direction. Write \(o=0\), \(w=w_f\), \(J_{\mathrm{dir}}=J\) for forward; write \(o=1\), \(w=w_r\), \(J_{\mathrm{dir}}=J^*\) for reverse. The three started labels are exactly the roots of \(H_3=H/(X-w)\), a genuine monic cubic. The scalar degree-three profile
\[
                       S=H_3(o)P-P(o)H_3
\]
supplies the **actual** grade-three vector \(S(\mathbf c)-H_3(o)\mathbf h\). It vanishes through the three dirty end stages, inclusively: at the literal origin \(S(o)=0\) and \(\mathbf h=0\); at the three started labels \(H_3(z)=0,\ P(z)=h_z\). This use of the mask involves no division by \(H_3(o)\) or \(P(o)\). If either factor, or the entire scalar mask, happens to vanish, the same necessary equation holds.

Chronological application of the true primitive is zero on these three dirt rows. Its grade-four pure error lies in \(\mathbf hP_1(\mathbf c)\), or in that same normalized space for the true reverse flag. Consequently \((J_{\mathrm{dir}}S)(z)/h_z\) agrees with an affine polynomial at the three distinct started labels. At those labels \(H'(z)=(z-w)H_3'(z)\). The point \(w\) contributes zero to \(L\) on a multiple of \(X-w\). The three-node barycentric annihilation of affine polynomials therefore gives the necessary equation
\[
                      L((X-w)J_{\mathrm{dir}}S)=0 .
\]
All scalar degrees are at most five. The \(3\times4\) dirty Hankel matrix of the moments has rank three, as already proved against the Vandermonde factors. Its signed three-column minors give a nonzero scalar multiple of \(P\), so the equation remains valid with that cofactor polynomial. The fixed arithmetic verifies that its left-hand side is a unit in the entire quartic coefficient algebra, separately in either direction. This is the contradiction.

## Exact fixed-grid replays

The Python checker independently reconstructs all values from the monomial primitive definitions in the preceding packet. At \(1013\) each of the 120 ordered Lobatto grids verifies:

1. the \(x_0^4\) coefficient guard for \(e\);
2. the two missing-clock denominator units and the difference unit;
3. the remaining monic quadratic moment determinant unit;
4. both independent grade-four contradiction units.

For the transfer, use the same prime of the fixed real Lobatto splitting field as in the [prior packet](../dirk12-fifteen-rank3-four-singleton-end-exclusion/README.md). All initial coefficients are in the local ring at that prime, including the rational and distinct-root denominator units. The leading guard permits normalization to a monic quartic, and its quotient is free on \(1,q,q^2,q^3\), with no assumption of irreducibility or square-freeness. A checked modular multiplication matrix of full rank has determinant a unit in the local ring. Its inverse lifts by the adjugate, so each quotient division in the checker is legit in characteristic zero, in the same order. For a real candidate, evaluation at its root \(q\) sends every such unit to a nonzero real number. A final unit therefore cannot be zero as forced by the actual tableau. Neither the unknown \(q\) nor any unknown dirty clock or tableau coefficient has been reduced.

    python3 -B check.py

The analytical implications from actual rooted order, including the exclusion of the four cancelling pairs, are mathematical. They are not an end-to-end native Lean stage-lower theorem.

An independent replay also matched all 720 quotient inversions to polynomial extended Euclidean inversion over \(\mathbb F_{1013}\).
