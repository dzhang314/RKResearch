# Coprime eight-active reverse-star exclusion

At strict SDIRK8 with ten stages over a characteristic-zero field, take the [eight-active reverse-silent chart](../sdirk-eight-silent-one-eight-reverse-vanish/README.md). The sole nonzero quadratic defect is at the weight-zero physical first row. Exactly eight ordinarily active physical stages have distinct clocks; both literal fronts are active and the other silent has actual \(w_4=0\). The active cubic profile is \(h_i=L_4(c_i)/Q(c_i)\) in a fixed normalization, with \(Q=T/\sigma\) affine. This packet excludes nonconstant \(Q\) coprime to \(L_4\) when the actual live rear three stages are in the reverse star phase. It includes all possible Gauss tail pegs. Reverse arithmetic is separate; the unrestricted interval stays **10–11**.

Use normalized time \(Y=c_i/\gamma\) for literal front constraints, with literal front clocks \(A_0,B_0\) and their actual nonzero normalized cubic defects \(H_a,H_b\). Write the two affine denominator versions \(Q(Y)=q_0+q_1Y\) and \(q(X)=\gamma q_0+q_1X\), their coefficients determined by the literal front values. No active clock is a root of \(q\), since such a root would also be a root of \(L_4\). In particular \(T(c_i)\ne0\) at every active clock, and the actual reverse reads \(w_i\ne0\) there. Thus a Gauss active clock has \(h_i=0\) and is a root of the nonzero affine reverse multiplier \(P_1\). There can be at most one such clock; neither nonzero-defect literal front is Gauss.

## Centered tail and exact fifth projection

Put \(x=1-\gamma\), \(v=u-1\), \(k=2-v^2\), \(m=x-\gamma\), \(c=m-\gamma v\), \(d=m+\gamma v\). The actual reflected ratios are \(w_{10}/b_{10}=-\gamma^2\) and \(w_9/b_9=w_8/b_8=-\gamma^2k\). The affine \(P_1\) and these ratios give the cleared star equation
\[
 (1-v)L_4(c)q(d)q(x)-(1+v)L_4(d)q(c)q(x)
       +2v(2-v^2)L_4(x)q(c)q(d)=0 .
\]
It is valid even when an active tail defect is zero. After exact division by the forbidden collision factor \(v(v^2-1)\), it is \(a(\gamma)+b(\gamma)v^2=0\). Both coefficients have degree fourteen, and their exact gcd is one in each literal front phase, so \(b(\gamma)\ne0\). The symmetry preserves both signs of \(v\).

The shape of the nonzero affine \(P_1\) is determined by its terminal value and the mean of the two nonterminal values. In terms of the scaled cubic defects \(f=L_4/q\), it is
\[
 (X-m) k f(x)+(x-X)(f(c)+f(d))/2 .
\]
The exact computation clears \(q(x)q(c)q(d)\) and uses \(\beta=bv\) with \(\beta^2=-ab\) for the symmetric sums. It clears a positive power of \(b\) as a nonzero scalar, without evaluating \(v\) or ordering its roots. The scaled nodal polynomial of the five occupied pegs is
\[
 (X-\gamma A_0)(X-\gamma B_0)(X-x)\{b(X-m)^2+a\gamma^2\}.
\]

Suppose first none of the three tail pegs is Gauss. The [eight-site nodal identity](../sdirk-eight-silent-one-eight-reverse-vanish/README.md) gives \(D\bmod L_4\) proportional to \(-P_1 q^2 W_{L_4}^{-1}\bmod L_4\), where \(D\) is the eight-site monic nodal polynomial. Divide out the five known distinct pegs to leave a monic cubic. Modulo monic \(L_4\), multiplication by the scaled five-peg polynomial is invertible because no peg is Gauss. Its four-column adjugate applied to the right-hand remainder gives the missing cubic up to a nonzero scale. The exact replay checks the matrix equation for those coordinates. It does not divide by individual fitted clock values in the exact projection.

The actual fifth is one of those three missing active clocks. Apply the literal fifth cross elimination with actual normalized \(h_5=L_4(\gamma Y)/Q(Y)\), clearing \(Q\). The two padded earlier roots \(A_0,B_0\) divide out exactly and are forbidden by actual distinctness. The resultant with the normalized missing cubic gives the exact diagonal projection. Polynomial content is removed only through exact factors corresponding to \(\gamma=0\), the forbidden zero leading gap coefficient, the constant/shared-root \(Q\) loci, actual vanished denominator or Legendre values at known pegs, the nonzero nodal multiplication determinant, or actual collisions among the five physical pegs. More explicitly, \(a,a+b,a+2b\) are guarded by the forbidden \(v^2=0,1,2\); \(b(z-m)^2+a\gamma^2\), \(z=\gamma A_0,\gamma B_0,x\), is guarded by literal distinctness; and \(q_1\) and the homogeneous Legendre evaluation at its pole are nonzero by the coprime hypothesis. Any unguarded content is retained. The final square-free projection has degree 27 in each front phase. There is no degree drop removed from a reduced projection alone.

## Separate Gauss-tail contact

A Gauss tail is not a shared root of \(Q\) and \(L_4\). Here \(T,w_i,b_i\) are nonzero at the Gauss clock, its true \(h_i=0\), and it is a root \(r\) of \(P_1\). No Gaussian weight is assumed, and no atom is subtracted from the scalar quadrature. The factor \(L_4(x)L_4(c)L_4(d)\) with the same centered substitution projects the diagonal into a guarded degree-40 equation in each front phase. The normalized fifth equation is genuinely cubic there; its leading coefficient has exact gcd one with the diagonal projection.

Keep each of the three possible literal tail contacts in the full monic centered-gap fiber, imposing its actual polynomial equation \(L_4(r)=0\). Deflate \(L_4\) and \(D\) by \(X-r\); the exact nodal remainder \(P_1q^2 W_{L_4}^{-1}\bmod L_4\) also vanishes at \(r\) and is deflated. Now retain the fifth as an additional known node, adjoining all its roots from the literal cubic. Apart from \(r\), there are four known ordinary pegs plus the actual fifth, none Gauss by uniqueness of the root of \(P_1\). Multiplying by their five-factor polynomial modulo \(L_4/(X-r)\) and taking its adjugate yields the missing nonhole quadratic up to scale. Only this congruence is used, not a Gaussian weight or a reduced diagonal approximation.

## Literal sixth gate in every mode

At actual normalized fifth clock \(y\), the literal \(\tau_4\) read gives \(Jz+U=0\), with \(z=c_4/\gamma\) the unknown actual silent fourth clock. Multiply by \(Q(y)\) to get the cleared coefficients \(J,U\); this is a true nonzero denominator before reduction but is not inverted. The other earlier information remains the actual interpolated \(H_4(z)\), not an extrapolated active defect at \(z\).

For candidate actual sixth clock \(Y\), let \(F_3=(X-A_0)(X-B_0)(X-z)\) mark its actual fifth tap, and let \(H_2\) interpolate the three actual predecessor defects at \(A_0,B_0,z\). The first four normalized strict scalar moments after removal of the stage-one feed are determined by its true \(h_6=L_4(\gamma Y)/Q(Y)\) and its literal pure-four line. In those moments the marked scalar sum is the tap to physical fifth times \(F_3(y)\). The difference between the required \(Ah\) strict read and the \(H_2\) read is the same tap times \(h_5-H_2(y)\). Cross multiplication, after clearing both fifth and sixth \(Q\)'s, gives a polynomial \(R_0(Y)+z R_1(Y)+z^2 R_2(Y)=0\). This remains valid if the fourth and fifth clocks coincide. Then the necessary sixth polynomial is \(J^2 R_0-JU R_1+U^2 R_2\), with no inverse or case deletion at \(J=0\). The existing [Lean cleared substitution](../../lean/RKCert/ReviewedNative/SDIRK8CoprimeReversePole.lean) checks this identity.

In the no-Gauss case, adjoin the actual fifth as a common root of the monic missing cubic and the literal fifth scalar equation, removing that actual factor to leave a monic quadratic containing actual sixth. In the Gauss case the adjugate already supplies a scaled quadratic after including fifth. The sixth resultant is a unit in all finite components; the latter Gauss test uses a padded Sylvester matrix and never divides by the scaled quadratic's leading coefficient in reduction.

## Replay

Install sympy==1.14.0 and python-flint==0.9.0 and run **python3 check_eight_coprime_star.py** in this repository proof directory. The no-Gauss modes use \((1103,161)\) and \((1097,345)\) for the two front phases; the Gauss tests use \((1097,345)\) for both. In the no-Gauss modes the monic diagonal and missing-cubic unit pivots are checked before passing to all residue common-root fibers. In the Gauss modes all available signed centered-gap roots and literal fifth roots are retained by monic finite-algebra tests, with a separate check at every literal contact. Counts are 6 and 1 no-Gauss fifth components, 11 and 21 Gauss-tail orientations. Thus the unit results lift over the corresponding characteristic-zero coefficient field without reducing an unknown tableau. The earlier cleared substitution is already verified in Lean. The tableau saturation, scalar projections, and finite replay are source-level.

The [Lean scalar companion](../../lean/RKCert/ReviewedNative/SDIRK8EightActiveCenteredStar.lean) is checked on Lean/Mathlib 4.36.0; the [axiom audit](lean-audit-4.36.0.txt) reports standard axioms only. The scope remains the displayed scalar algebra rather than the full chart.
