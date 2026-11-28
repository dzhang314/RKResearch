# Coprime shared literal balance with active arithmetic eighth

This is the [detected seven-distinct active strict SDIRK8 chart](../sdirk-eight-silent-one-seven-distinct-anchors/README.md) at ten stages over a characteristic-zero field. Only the individually weight-zero first row has nonzero quadratic residual, \(k\ne0\), and \(Q\) is affine nonconstant and coprime to \(L_4\). Exactly one literal front is active. The silent literal and physical stage six or seven share their actual clock \(z\), with nonzero aggregate reverse weight. Eighth is active with its arithmetic clock. Fourth and fifth are active, and individual silent defects are not transported. The [active-star proof](../sdirk-eight-silent-one-seven-distinct-coprime-shared-star/README.md) treats the analogous star placement.

## Actual arithmetic tail and nodal diagonal

Write \(\boldsymbol h=N\boldsymbol g,\ \boldsymbol w=\boldsymbol b^{\mathsf T}M\), \(N=A-\gamma I,\ M=CA-AC-A^2\). Let \(a,b\) be the normalized active and silent literals; \(z=\gamma b\). Put \(x=1-\gamma,\ c=x-\gamma u,\ d=x-2\gamma u,\ k=1+2u-u^2\). At active sites \(w_i/b_i\) is proportional to \(L_4(c_i)/(q(c_i)(c_i-z))\). Set
\[
 \mathcal A=(x-z)L_4(c),\qquad \mathcal B=k(c-z)L_4(x),\qquad
 F=(\mathcal A-\mathcal B)/u .
\]
The division is exact zero-gap padding. Ninth pins the actual affine shape up to physical scale: use \(q(X)=\gamma\mathcal B-F(X-x)\), so \(q(x)=\gamma\mathcal B\), \(q(c)=\gamma\mathcal A\), and \(q(d)=\gamma(2\mathcal A-\mathcal B)\) since \(d=2c-x\). The actual arithmetic eighth factor law \(Hk_d=-kT\) then gives
\[
 R_{\mathrm{raw}}=H(x-z)L_4(d)(c-z)+T(d-z)(2\mathcal A-\mathcal B)=0,
 \qquad H=-2+u+4u^2-u^3,\quad T=4u^3-12u^2+3u+2.
\]
The common canceled factor is \(\gamma k L_4(x)\ne0\). Removing exact forbidden powers of \(u\) and \(\gamma\) leaves degree five in \(u\).

With \(P(Y)=h_aq(\gamma a)L_4(\gamma Y)\), \(Q_0(Y)=L_4(\gamma a)q(\gamma Y)\), actual fourth \(s\) satisfies the padded \(\Phi=(Q_0H_4-P)/(Y-a)=0\). The [actual 5-peg nodal determinant](../sdirk-eight-silent-one-seven-distinct-coprime-shared-star/README.md) on \(\gamma a,x,c,d,\gamma s\) is \(D_5(s)=0\); its Newton divided-difference form removes only the actual nonzero Vandermonde. Let \(J=\operatorname{Res}_s(\Phi,D_5)\), keeping coefficient content as explicit diagonal factors. The projected diagonal \(\operatorname{Res}_u(R,J)\) is computed by exact pseudo-remainder and a fraction-free Sylvester determinant over \(\mathbb Q(t)\), \(2t^2=1\). Deflate only the exact redundant pseudo-remainder leading power; keep the true leading-zero factor. The deflated raw degree is 670 before recorded content/leading factors, and guarded diagonal degree is 557. Only \(\gamma,\ x-z,\ L_4(x),\ L_4(\gamma a),\ x-\gamma a\) are stripped as nonzero diagonal guards.

## Exact deletion of forbidden Gauss tail roots, not their entire diagonals

An actual ordinary active \(c\) or \(d\) cannot have \(L_4=0\). Compute the exact diagonal resultants \(\operatorname{Res}_u(R,L_4(c))\) and \(\operatorname{Res}_u(R,L_4(d))\); after the true diagonal guards, the distinct-root degrees are 36 each. Intersect their union with the main projection **exactly**. Rational norm factorization over the quadratic coefficient field and exact intersections give components of degrees \(4,32,20\), and also degree 12 for a star literal front. Removing their support from the main diagonal yields a degree-301 complement for star front and degree 313 for arithmetic front. The affected 68 or 56 diagonal degrees are **retained as separate branches**, not dropped.

On each affected exact diagonal quotient, pseudo-gcd \(R(u)\) with each forbidden \(L_4(c)\), \(L_4(d)\). Split by exact leading coefficients if a pivot is a zero divisor. Divide only common \(u\)-factors, with exact zero pseudo-remainder and leading unit, so any other \(u\) at the same diagonal survives. The retained gap degrees are three or four there. On the unaffected complement, keep the actual degree-five and lowered degree-four branches of \(R\). This eliminates the spurious Gauss-tail contacts **before** selecting or computing any reduced fiber.

## Pole-free actual fifth

The polynomial \(D_5(Y)\) is the normalized evaluation determinant when its fifth peg is \(\gamma Y\); it vanishes at **any** ordinary active \(Y\) distinct from the four known ordinary pegs. In particular it vanishes at actual fourth and fifth. Divide by \(Y-s\); the remainder is \(D_5(s)\), and the quotient is another necessary polynomial for actual fifth, since those active clocks differ. This gives the missing quadratic condition without evaluating the rational pole functional or inverting an unknown moment determinant.

In each reduced diagonal component impose both exact gap equations \(R,J\) by their complete gap gcd. Over that finite algebra use a verified unit leading coefficient of \(\Phi\), \(D_5\), or a linear combination of them to retain an entire fourth quotient. Both actual fourth equations are still imposed separately as residuals. This choice can be made locally at each maximal ideal of the finite diagonal/gap algebra; its monic fourth quotient is finite there. The numeric leading inverse is explicitly verified by multiplication. Actual fifth satisfies both literal pure reads with earlier padded factors \(y-a,y-s\), as in the paired packets. Its two padded resultants with the \(D_5\) quotient, their mutual resultant, and both fourth equations generate the unit ideal. No individual silent value or pole denominator is inverted.

## Verification

Run `python3 check_coprime_shared_arithmetic.py` in the repository sibling proof tree with `sympy==1.14.0` and `python-flint==0.9.0`. The runner lists all finite six-clock, literal and later helper paths. It checks all four complete modes after exact diagonal/gap guards and genuine leading-degree splits, retaining every reduced component. Use \((1103,t-161)\) for final finite arithmetic, with the other cited primes only for exact degree-preserving coprimality. At any possible characteristic-zero solution the finite diagonal/gap coefficient prime lies in some maximal ideal over the chosen local residue; the tested local monic fourth quotient contradicts that solution. No reduction of an actual tableau or removal based on a residue coincidence is assumed.

The [native Lean file](../../lean/RKCert/ReviewedNative/SDIRK8ArithmeticAffineTail.lean) kernel-checks the arithmetic third affine reading and cleared tail normalization on Lean/Mathlib 4.36.0. The saturation, projection and literal finite arithmetic remain separate source-level certificates. This is a scoped placement, not an unrestricted advance of the **10–11** interval.
