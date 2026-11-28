# The neighboring corrected moment operator always has full rank

**Scope.** In the ordered, all-live, half-clock two-carrier, seventeen-stage ERK11 equality chart with both seventh boundaries new, \(q=10,n=12\), both full plateau pairs and sole dormant physical 9 sharing the active outer singleton \(s=c_8\notin\{0,1,a,d\}\), assume \(K_0(a,b)\ne0\), \(b=1-d\). The [width and diagonal-pole packets](ERK11-NONZERO-TEN-TWELVE-NEIGHBOR-SINGLETON-DIAGONAL-POLE-EXIT.md) measure \(s,z,u,v\). The whole corrected three-row operator on all polynomials of degree at most four has rank three. This eliminates simultaneous rank loss of the five-column corrected moment block, **not** either individual fixed three-by-three determinant loss or either raw affine loss. It uses neither of those regular-fit pivots. The proof transfers under the same reflection; the \(K_0=0\) width curve is already [separately empty](ERK11-NONZERO-TEN-TWELVE-NEIGHBOR-K-ZERO-COMPLETE.md).

## Compact Jacobi projection of any lost row rank

In physical coordinates let \(\omega=X(1-X)(X-a)(X-d)\) and \(\rho=J_0/(uv)\). Loss of rank of the three maps \(\mathcal L_j(Q)=\int X^j\omega Q-\rho s^jQ(s)\), \(j=0,1,2\), gives a nonzero polynomial \(r\) of degree at most two whose coefficient combination annihilates all \(Q\) of degree at most four.

Use \(Q=(X-s)q\) with arbitrary \(q\) of degree at most three. The correction vanishes, so the nonzero polynomial
\[
 T=(X-a)(X-d)(X-s)r
\]
has degree at most five and is orthogonal to degrees at most three for the weight \(X(1-X)\). The dimension of this orthogonal complement is two: the degree-three rational Gram determinant is nonzero. It has the following two independently checked shifted Jacobi generators,
\[
 J_4=1-14X+56X^2-84X^3+42X^4,\qquad
 J_5=-1+20X-120X^2+300X^3-330X^4+132X^5.
\]
Thus all three \(2\times2\) minors of the evaluation rows \((J_4(y),J_5(y))\) at \(y=a,d,s\) vanish. The algebraic necessity does not assume a leading degree of \(r\) or divide by either generator value.

Substitute \(s=C_2/H\) in the last two minors by homogenizing with \(H^5\); use the known live clock differences and width factors to deflate them. The resulting bidegrees in \(a,b\) are \((4,4),(12,8),(8,12)\). The \(b\)-resultants of the first with each of the other two both have \(a\)-degree 80, and their common gcd is irreducible of degree 60. This gives a single exact \(a\)-field, regardless of any other moment or affine pivot loss.

The deterministic replay derives a linear subresultant of the first two input polynomials and obtains an exact \(b\) in the degree-60 \(a\)-field (represented by a polynomial of degree 59 in \(a\)); it verifies all three input polynomials vanish at that value and all named mixed-width guards remain live. At \((p,a,b)=(31,7,19)\) the monic degree-60 factor has a simple root, the first width polynomial retains its \(b\)-degree four with leading coefficient 16, and the **whole joint residue gcd** of the three width polynomials is \(b-19\). The first polynomial's derivative there is 27. Every exact candidate \(b\) at that \(a\) embedding is integral and reduces to 19, by the unit leading coefficient. Hensel uniqueness then makes it the exact reconstructed \(b\); the latter was verified to satisfy all three inputs. This does not treat a modulus as the tableau's coefficient field.

## Use both actual temporal rows, without assuming a sparse pivot live

The original flanks here use actual \(R_9\) on the left and actual \(L_7\) on the right. Both first derivative pairings are live, the former by the diagonal-pole exit and the latter by \(K_0\ne0\) as in the [original live-fit proof](ERK11-NONZERO-TEN-TWELVE-NEIGHBOR-K-LIVE-REGULAR-FINITE.md). Use the sparse shapes
\[
 Q=U_f\phi+W_f YB_0+T_f YB_1+A_f(B_0+tB_1),\qquad
 P=w[U_f+(T_f/t-W_f)(Y-h)]
\]
with their original physical temporal outer equations \([L_8,R_9]=0,[L_7,R_{10}]=0\). The right orientation is \(Y=1-X\). The shifted rank-one measure becomes its reflected form and has the same rank.

At the above width place the first two moment rows on the first two columns have pivots \(19,3\) on the left and right respectively. These pivots are units, so the counterfactual rank loss is exactly rank two. Solve those two rows for \(U_f,W_f\) in terms of \(T_f,A_f\) and \(tA_f\). Subtract from each temporal row the resulting combination of the two moment rows on the first two columns. The remaining coefficient on the **third fixed column is exactly zero**, not just zero modulo 31: the replay constructs each \(3\times3\) determinant on the first two corrected moments and one actual temporal row, on the first three columns. The deflated two width polynomials have bidegrees \((32,29),(44,39)\), with norms of degrees 244 and 332, and both evaluate to zero at the reconstructed exact \(b\) modulo the degree-60 \(a\)-polynomial. The rank-one determinant expansion uses at most one correction row and live width clearings. Thus the remaining temporal equations are exactly
\[
 A_f(\eta_0+\eta_1t)=0
\]
in both orientations. The last two coefficients reduce to \((18,13)\) on the left and \((5,6)\) on the right. In particular \(\eta_1\) is a unit on both sides.

Here \(A_f=0\) if and only if \(Q\) vanishes at the orientation's own endpoint, physical \(0\) or \(1\): all three fixed columns vanish at \(Y=0\), and \(tB_1(0)\ne0\). If that endpoint is nonzero, the actual product \(t=-\eta_0/\eta_1\) is measured, with residues 1 left and 25 right. If it is zero, \(A_f=0\) and no measurement or reduction of the unknown \(t\) is needed for the remaining \(Q\) line.

## All four endpoint masks fail

For each orientation the first two moment equations write the true shape as
\[
 Q=T_f Q_T+A_f(Q_{A0}+tQ_{A1}).
\]
When the endpoint vanishes retain only \(Q_T\); otherwise the true \(t\) has just been measured. The left coefficient vectors \(Q_T,Q_{A0}+tQ_{A1}\), and their right counterparts already moved back to physical \(X\), are the following, in increasing degree order modulo 31:
\[
 (0,1,22,21,12),\ (1,22,21,12,0);\qquad
 (18,9,22,14,30),\ (16,24,16,25,0).
\]
The actual \(Q\) is nonzero and proportional in the two orientations. For both endpoints zero the two retained vectors have rank two. If exactly one endpoint is zero the three retained vectors have rank three in either orientation. A unit full-column minor lifts from the residue, so none of these cases has a common nonzero \(Q\).

When both endpoints are nonzero, the comparison matrix on all four retained vectors (opposite sign on the right pair) has rank three modulo 31 and normalized kernel \((24,9,22,1)\). A true common nonzero \(Q\) forces exact rank at most three; the unit rank-three minor lifts, so the width-measured kernel can be normalized by its actual right \(A_f\) and reduces to that vector. Substitute into the two sparse \(P\) lines, using the measured and residue-live products. The oriented \(P\) lines are \((20,12),(29,28)\), whose required physical proportionality determinant is
\[
 20\cdot28+12(29+28)=4\bmod31,
\]
not zero. This uses only measured coefficient data, not reduction of arbitrary tableau states.

Finally, this proves rank three also for the actual **five-column** corrected moment matrix. The second slope in each orientation is live because with first slope live the seventh-row formula would otherwise force an extra clock equal to its own plateau. After factoring out \(Y-h\) from the last four columns, any dependence would give
\[
 Y(Y-w)(d_0+d_1Y)+[w\ell_0-(\ell_0-\ell_1)Y](e_0+e_1Y)=0 .
\]
Evaluation at \(0,w\) uses \(\ell_0,\ell_1\ne0\) to give \(e_0=e_1=0\), then \(d_0=d_1=0\). Thus the last four span precisely the degree-at-most-four polynomials divisible by \(Y-h\), and \(\phi(h)\ne0\) complements them.

The exact standalone replay uses python-flint 0.9.0 and SymPy 1.14.0, with no coefficient checkpoint or randomized search (reference wall time 3.806 seconds). The chronology and field-place inference are mathematical; no full Lean stage theorem is asserted. Individual fixed-moment and affine masks remain open on \(K_0\ne0\).
