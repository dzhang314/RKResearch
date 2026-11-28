# Coprime extra aggregate shared by a literal silent and silent fifth

In the [strict SDIRK8 detected seven-distinct chart](../sdirk-eight-silent-one-seven-distinct-anchors/README.md) at ten stages, only the weight-zero physical first row has nonzero quadratic residual. Work over a characteristic-zero field, \(k\ne0\), and assume the affine \(Q\) is nonconstant and coprime to \(L_4\). Here exactly one literal front is active; the other is silent with clock \(z\), shared by physical silent fifth. Their combined reverse aggregate is nonzero. This is separate from the [paired silent-eighth chart](../sdirk-eight-silent-one-seven-distinct-coprime-shared-eighth/README.md) and from a sole individually transported literal.

Write \(\boldsymbol w=\boldsymbol b^{\mathsf T}M,\ \boldsymbol h=N\boldsymbol g\) for \(N=A-\gamma I,\ M=CA-AC-A^2\). Let \(a\) be the active literal normalized clock, \(b=z/\gamma\) the silent literal clock, and \(s\) the actual normalized fourth clock. Fourth and eighth are active. Fourth cannot repeat either earlier literal clock. Let \(H_4(s)\) be its literal cubic defect, nonzero by the active coprime profile, and \(h_a\ne0\) the active literal defect.

## Weighted virtual fifth, not an individual reading

For either pure-four read \(v=Ah,\tau_4\), denote the active affine slope by \(\ell_v\), anchored at the two actual active positions \(a,s\). The literal fifth formula at its actual clock \(b\) is affine in its actual defect. The earlier silent literal at that same clock has the exact padded formula, at its own actual defect, by uniqueness of the strict scalar taps with preceding clocks \(A_0,B_0,s\). Since the total reverse aggregate is nonzero, the **weighted virtual** fifth pure read at \(b\) has that same affine formula at the virtual defect \(H\). The [separate aggregate interpolation](../sdirk-eight-silent-one-seven-distinct-coprime/README.md) supplies \(H=L_4(\gamma b)/Q(b)\) and virtual pure read \(\ell_v(b)H\). Neither individual \(h\) is set to this \(H\).

Write the two cleared strict reads as
\[
 H_4(s)T_0(b,s)+T_1(b,s)H=0,\qquad
 H_4(s)A_0(b,s)+A_1(b,s)H=0,
\]
using the [literal fifth formulas](../sdirk-eight-silent-one-seven-distinct-gauss-root/README.md) and anchors \(a,s\). At the fixed literal \(b\) all four coefficients are polynomials in \(s\) over \(\mathbb Q(t)\), \(2t^2=1\), independent of \(\gamma\). Eliminate the unknown virtual \(H\) with the necessary \(T_0 A_1-A_0 T_1=0\). The exact fourth projection has degree one in the star-front modes and three in the arithmetic-front modes after removing only forbidden \(s=A_0,B_0\) and \(H_4(s)=0\) factors. Its exact gcd with \(T_1\) is one, and the joint gcd with \(T_0,A_0\) is one. Therefore the virtual \(H=-H_4(s)T_0/T_1\) is determined and nonzero on any candidate satisfying both reads. The exact field construction checks the actual inversions, not just those two gcds.

## Three affine readings pin the diagonal

The actual affine \(Q\) must simultaneously read
\[
 Q(a)=L_4(\gamma a)/h_a,\quad
 Q(s)=L_4(\gamma s)/H_4(s),\quad
 Q(b)=L_4(\gamma b)/H.
\]
Linearity gives \((s-b)Q(a)+(b-a)Q(s)+(a-s)Q(b)=0\). This is a quartic diagonal polynomial over the exact fourth-clock quotient, with unit leading coefficient after the displayed guard splits. Removed factors are only the nonzero strict diagonal, nonzero \(L_4\) at the two ordinary and the now nonzero virtual readings, and genuine terminal distinctness from the active literal, active fourth, and separate silent root. The actual \(Q\) itself is recovered from the two ordinary readings at \(a,s\).

Put \(x=1-\gamma,\ c=x-\gamma u,\ k=1+2u-u^2,\ q(X)=Q(X/\gamma)\). At the active sites \(w_i/b_i\) is proportional to \(L_4(c_i)/(q(c_i)(c_i-z))\). With \(z=\gamma b\), the exact ninth numerator is \((x-z)L_4(c)q(x)-k(c-z)L_4(x)q(c)\), divided only by its exact zero-gap padding. The corresponding active eighth is star or arithmetic, with \(d=x-\gamma(2-u)\) or \(x-2\gamma u\). Its comparison uses \(k\) or the cleared \(Hk_d=-kT\). In star remove the exact padded factors at eighth=terminal and eighth=ninth by the sum/division of the two tail quotients; in arithmetic remove only the exact zero-gap factor. The degree-\((3,2)\) or degree-\((3,6)\) padded tail resultant is a unit on the entire retained finite fourth/diagonal algebra. No individual silent weight or signed moment pivot is inverted.

## Replay

Run `python3 check_coprime_shared_fifth.py` with `sympy==1.14.0` and `python-flint==0.9.0` in the sibling proof tree. All 8 modes use \((1103,t-161)\) after the exact fourth, guard and diagonal splits. Every irreducible reduced fourth factor and full monic diagonal component is retained. Padded tail resultants avoid an assumed reduced tail leading degree. The standard local finite-unit argument lifts to characteristic zero without reducing an actual tableau. The [native Lean file](../../lean/RKCert/ReviewedNative/SDIRK8AffineThreeReads.lean) verifies the affine three-reading identity on Lean/Mathlib 4.36.0; the [weighted virtual read transport](../../lean/RKCert/ReviewedNative/SDIRK8VirtualFifthAtLiteralClock.lean) is separately native. The full saturation and exact arithmetic remain source-level.

Second physical silent at six or seven, no-active-literal and nonliteral-root coprime cases remain separate; no unconditional advance of the **10–11** interval is claimed.
