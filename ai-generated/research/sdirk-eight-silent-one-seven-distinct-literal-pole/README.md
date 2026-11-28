# A literal silent clock at the coprime pole

Work in the [seven-distinct active profile](../sdirk-eight-silent-one-seven-distinct-anchors/README.md) at the strict SDIRK8 ten-stage floor over a characteristic-zero field. Only physical stage one has nonzero quadratic residual, and its ordinary weight is zero. There are seven distinct active clocks, the cubic defect is detected, the reverse factor \(k\ne0\), and the affine \(Q\) is nonconstant and coprime to \(L_4\). Assume there is **no extra clock with nonzero aggregate reverse weight**. This excludes every such case with at most one active literal front. It does not close the separate-aggregate chart or advance the unrestricted 10–11 interval.

Put \(\boldsymbol h=N\boldsymbol g,\ \boldsymbol w=\boldsymbol b^{\mathsf T}M\) for \(N=A-\gamma I,\ M=CA-AC-A^2\). On the seven active sites, the interpolant of \(D'(c_i)w_i\) is a nonzero constant, and the interpolant of \(D'(c_i)b_i h_i\) is proportional to \(q(c_i)\), with \(q\) the physical affine denominator. Thus the actual \(\boldsymbol h^{\mathsf T}B=\boldsymbol wP_1(C)\) has \(P_1\) proportional to \(q\). Both individually silent zero rows must have nonzero, opposite \(w\)'s at the pole \(z\), and distinct actual \(h\)'s. Otherwise the three paid \(\boldsymbol w C^j\boldsymbol h\) moments reduce to seven active nodes and interpolate the active \(h\)'s by a cubic, contradicting the coprime rational profile. The two literal front clocks are distinct; both cannot be silent.

Write \(a,b\) for the normalized active and silent literal clocks, respectively, and \(h_a\) for the actual normalized active defect. Necessarily \(z=\gamma b\) and
\[
  Q(Y)=(Y-b)L_4(\gamma a),\qquad
  P(Y)=h_a(a-b)L_4(\gamma Y),\qquad Q(Y)h(Y)=P(Y)
\]
on the active set. Physical fourth cannot repeat either earlier literal clock by the three-tap scalar measurement, so it is active. Each active pure-four read \(v\) is \(\ell_v(Y)h\) with affine \(\ell_v\), anchored by the literal \(a\) and the actual fourth \(s\). For \(v=Ah,\tau_4\), define \(X_v(s)\) by the exact polynomial division
\[
 (s-a)X_v(s)=v_4(s)-\ell_v(a)H_4(s).
\]

## The other silent is fifth

At \(b\) the actual literal fifth formulas are affine in the actual \(h_5\), with slope \(D_v(s)\). Their padded read at the literal \(h_b\) is exactly \(v_b\), by uniqueness of the three strict scalar moments at the distinct preceding clocks \(A_0,B_0,s\). The opposite nonzero actual \(w\)'s imply
\((v_5-v_b)=\ell_v(b)(h_5-h_b)\). The actual \(h\)'s differ, so \(D_v(s)=\ell_v(b)\). Therefore
\[
 H_4(s)(D_v(s)-\ell_v(a))=(b-a)X_v(s).
\]
The two resulting exact univariate polynomials are coprime in each front-phase/position orientation. This is a **difference** identity, not transport of individual silent defects.

## The other silent is later

Physical fifth is now an active ordinary clock. Write \(x=c_{10}=1-\gamma,\ c=c_9=x-\gamma u,\ k=1+2u-u^2\). At ordinary sites \(w_i/b_i\) is proportional to \(L_4(c_i)/(c_i-z)^2\). The ninth comparison gives
\[
 F_9=\bigl[L_4(c)(x-z)^2-kL_4(x)(c-z)^2\bigr]/u=0.
\]
The division is exact polynomial padding at the forbidden zero gap, not a numerically guessed factor. If eight is active, use \(d=x-\gamma(2-u)\) in the star phase or \(d=x-2\gamma u\) in arithmetic. In star the analogous raw polynomial at \(d\) is divided by \(u-2\); adding \(F_9\) allows an exact division by \(u-1\), since the two active tails cannot coincide. In arithmetic the cleared literal numerator is
\[
 H L_4(d)(x-z)^2+kT L_4(x)(d-z)^2,\quad
 H=-2+u+4u^2-u^3,\quad T=4u^3-12u^2+3u+2.
\]
Remove only its exact powers of the forbidden \(u\). If eight is silent, its nonzero individual \(w_8\) instead gives \(2(x-z)+\gamma k(u-2)=0\). Thus compatible methods lie in the exact diagonal resultant of \(F_9\) and the independent eighth polynomial.

The guarded diagonal degrees before squarefree decomposition are 22, 44, 17 for star, arithmetic, and silent eight. Removed diagonal factors evaluate to \(\gamma,\ x-z,\ L_4(z),\ L_4(x),\ L_4(\gamma a)\), or \(x-\gamma a\), all genuinely nonzero. Exact leading-coefficient gcds retain **both** degree-two and degree-three \(F_9\) branches when eight is active; the silent eighth branch has degree three. The other eighth polynomial is imposed without a leading division.

For active eight, four known ordinary pegs \(\gamma a,x,c,d\) leave exactly three distinct ordinary nodes. Multiply the signed rational functional by the four-peg nodal mask. Its first six moments form the exact \(3\times3\) Hankel/Cramer system for the missing cubic, with its coefficients cleared and its argument normalized by \(\gamma\). The actual fourth is a root of that cubic and of \(\Phi=(QH_4-P)/(Y-a)\), removing only the exact padded earlier occupied site. Their degree-\((3,3)\) Sylvester resultant is a unit in every surviving reduced tail fiber.

For silent eight, first retain the **entire** cubic \(\Phi\) for actual fourth. Its leading coefficient is a unit in those reduced tail fibers. Then the four ordinary pegs \(\gamma a,x,c,\gamma s\) give a cleared missing cubic containing actual fifth. Use separately the exact fifth strict scalar formulas for \(Ah,\tau_4\), whose constant and defect parts are \(V_0(y),D_v(s)h_5\). The necessary cleared read is
\[
 H_4(s)V_0(y)Q(y)
  +\bigl(H_4(s)(D_v(s)-\ell_v(a))-X_v(s)(y-a)\bigr)P(y)=0.
\]
After imposing \(\Phi=0\), its padded \(y-a\) factor is exact. Actual fifth is distinct from the active earlier \(a\). Test its two degree-\((3,4)\) padded Sylvester resultants against the cleared cubic. They jointly generate the unit ideal. No inverse of \(H_4(s)\), an unknown moment determinant, or an individual silent weight is used.

### Verification and lift

Run `python3 check_literal_shared_pole.py` in the sibling proof tree, with `sympy==1.14.0` and `python-flint==0.9.0`. The front slopes and diagonal projections are exact over \(\mathbb Q(t)\), \(2t^2=1\). The 12 late gates are finite quotient tests at the local prime \((1103,t-161)\): retain every exact diagonal and gap leading branch, normalize only after checking each leading coefficient is a reduced unit, and impose the eighth equation by the complete modular gcd. All irreducible reduced diagonal factors are visited. The only rational moment denominator beyond the fixed scalars is \(L_4(z)\), checked as a unit, along with \(\gamma\). No residue point with a chronology guard equal to zero is discarded. Use padded resultants even if an individual residual drops degree on reduction. Thus each tested ideal is the unit ideal in the relevant finite algebra over the local base, since its reduction has no maximal ideal containing the conditions. Passing to the fraction field proves the characteristic-zero exclusions. The unknown actual tableau is never assumed to admit reduction.

The [Lean file](../../lean/RKCert/ReviewedNative/SDIRK8LiteralSharedPole.lean) kernel-checks the literal shared-pole fourth cut and the denominator-clear fifth read on Lean/Mathlib 4.36.0. The saturation, exact polynomial inputs and finite arithmetic are separate source-level certificates.
