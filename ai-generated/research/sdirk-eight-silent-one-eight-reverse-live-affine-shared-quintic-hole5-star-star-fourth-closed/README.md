# Regular corrected ordinary hole5, star front and true star rear, actual silent fourth

In the [genuine affine shared-quintic ordinary-hole chart](../sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole-literal-closed/README.md), exclude early rank two, star front and ordinarily weighted star rear with the other ordinarily silent but reverse-live physical row \(\zeta=4\). The nine distinct sites consist of eight ordinarily weighted sites and the actual reverse-live clock \(z=c_4\). Only first quadratic defect is nonzero, and the first stage is ordinarily and reversely silent. The ordinary fifth \(r=c_5\) is the common root of affine \(T\) and quintic \(S\), with true \(h_5=0\) and \(H(r)\ne0\) for the continued quartic \(H=(S/T)/\gamma^3\). The field has characteristic zero; no ordering is used. The [regular literal silent 2/3 companion](../sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole5-star-star-literal-closed/README.md) and [complete early rank-loss packet](../sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole5-rank-closed/README.md) are separate.

The true now reverse-live fourth is not the hole: \(z=\gamma s\) and actual \(H_4(s)=H(\gamma s)\). The homogeneous \(H_N=\Delta H=\alpha_N L_4+\beta_NK_3\) has actual two-literal anchors \(a=\gamma A,b=\gamma B\). As in the literal companion,
\[
  J=(\Delta H_4(s)-H_N(\gamma s))/((s-A)(s-B))=0,\qquad
  (Y^3-9Y^2+18Y-6)(3s-2Y-1)=0,\quad Y=r/\gamma .
\]
The first identity is not a rule for ordinary weights at stage four: it is the true cubic-residual value there. \(s=A,B\) are forbidden by ninth-site distinctness, not by whether their ordinary weights vanish. There is still no fake fifth pad.

At the star tail use the same actual centered \(F(w),E(w;z),O(w;z)\), \(w=(u-1)^2\). The coefficient \(F_1=140\alpha_N\gamma^4\ne0\) is independent of \(z\); both \(E,O\) are affine in \(z\). The cleared exact centered-odd condition, treating \(s\) now as a literal fourth clock rather than a gap variable, is
\[
 U(\gamma,Y,s)=\bigl[F_1 O_0(\gamma s)-F_0O_1(\gamma s)\bigr]/\gamma=0 .
\]
It is affine in \(s\). No leading \(s\)-coefficient of \(U\) is divided.

* For \(s=(2Y+1)/3\), substitute this in \(J,U\), removing only \(\gamma\) from \(J\) as in the companion. Take the exact padded \(Y\)-resultant of degrees 5 and 7. The raw diagonal degree is 139. Divide only true factors \(\gamma^{30}\beta_N^6\), with \(\beta_N=\Delta b_rH(r)\ne0\). The retained degree 85 splits once by \(L(\gamma)=120\gamma^3-60\gamma^2+12\gamma-1\). Before any finite reduction, specialize the complete two \(Y\)-polynomials modulo \(L\) into degrees 4 and 6. The resulting cubic diagonal fiber has no common \(Y\). Keep all degree-82 diagonal outside this locus.
* For \(Y^3-9Y^2+18Y-6=0\), take the padded \(s\)-resultant of \(J,U\) whether or not either leading coefficient drops. Remove only \(\gamma^4\); the retained polynomial has bidegree \((15,46)\) in \((Y,\gamma)\). Its exact resultant with the monic cubic in \(Y\) leaves degree 138 in \(\gamma\), without deletions. Keep \(J(s)=0\) in the \(s\)-fiber.

The true known ordinary nonhole pegs are now \(a,b,x,c,d\), **not \(z=c_4\)**. Their \(E_5\) gives \(D_7=E_5R_2\), with true monic quadratic. Use the three signed coefficient rows of \(H_NW_{X^jE_5}^{I_\#}-X^jE_5W_{H_N}^{I_\#}\), \(I_\#=H_N(r)I-\beta_N\mathrm{ev}_r\), and fourth actual terminal row from \(b_9=b_{10}\ne0\) as in the [five-peg derivation](../sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole4-middle-closed/README.md#signed-polynomial-determinant-from-five-true-nonhole-pegs). Their four minors must vanish.

At \((1129,t=203)\), keep all monic diagonal factors, then full \(Y\)-gcds with at least one full leading unit, the full cubic-branch \(J(s)\) quotient, and the full double cover \(v^2-w\). The final relation uses actual \(z=\gamma s\) and both signed terminal orientations. The centered comparisons and signed minors generate a unit on each remaining fiber. All **18** retained components pass (four degree-82 factors plus one cubic, and thirteen degree-138 factors). Unit lifts are finite and do not assume good reduction of the actual tableau.

Run `python3 check_eight_reverse_live_affine_shared_quintic_hole5_star_star_fourth.py` with `sympy==1.14.0`, `python-flint==0.9.0`, and the declared siblings. The [native scalar receipt](../../lean/RKCert/ReviewedNative/SDIRK8ReverseLiveAffineSharedQuinticHoleFiveStarFourth.lean) verifies the no-pivot quadratic/linear homogeneous elimination on Lean/Mathlib 4.36.0. Exact projections and finite unit tests are source-level. Other rear phases, other actual silent positions and other ordinary holes are separate; the global **10–11** bound is unchanged.
