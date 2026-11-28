# The dormant plateau alias has no right fixed-moment pivot loss

**Scope.** In the [sparse plateau-alias chart](ERK11-NONZERO-TEN-TWELVE-SPARSE-PLATEAU-ALIAS-ELIMINANT.md) with \(q=10,n=12\), both plateau pairs full and sole dormant physical 9 at \(\zeta=d\), this excludes the **right** fixed three-by-three moment-determinant mask. It is a separate calculation from the left moment mask. Reflection transfers it to the opposite plateau orientation. The field arithmetic is characteristic zero with the inherited ordered-width and mixed-moment guards. The two affine-pivot masks are still separate; no unrestricted stage interval changes.

## 1. Actual right determinant and exact width projection

Use the right reflected coordinate \(Y=1-X\), \(w=1-d\), opposite-width label \(1-a\), and \(h=w/2\). Its fifth-grade opposing row for these calculations is the actual physical \(L_7\), found from its two live left slope coefficients against \(R_9\). In particular the right-side calculation uses actual \([L_7,R_{11}]=[L_7,R_{10}]=0\), not a symmetric assumption about \(L_9\) or any reverse order-eleven statement. Let \(B_0,B_1\) be the fixed cubic and quadratic of the right calibrated hull \(B_0+tB_1\), and let \(\phi=Y^2(w-Y)\). The fixed right moment determinant \(\Delta_R\) uses the three columns \(\phi,YB_0,YB_1\) and the three shifted integrals against \(Y(1-Y)(Y-w)(Y-(1-a))\). The right fourth equation is the actual temporal outer row from physical \(R_{10}\), evaluated at \(1-c_{10}\).

With \(\mathcal D(a,d)\) the same central reciprocal diagonal, remove only powers of the already live geometry \(a,d,d-1,a-d\). The resultant in \(d\) against the right moment determinant has degree 138, with irreducible degrees and multiplicities \(1^8,3,3,12,12,100\). The degree-one factor is \(a\), forbidden by the front. The exact joint gcd of the width and mask equations in \(d\), over each of the four small nontrivial width fields, is monic linear. Its roots give the following exits:

* Both cubics, \(165a^3-180a^2+54a-4\) and \(110a^3-125a^2+39a-3\), give \(d=1\), a zero right width.
* The degree-12 factor of the [left initial-slope proof](ERK11-NONZERO-TEN-TWELVE-PLATEAU-ALIAS-LEFT-SLOPE-EXIT.md) gives both left derivative slopes zero.
* On the other degree-12 factor the exact width gives the forbidden \(x_D=x_N=0\) and zero variance, as in the [right initial-slope proof](ERK11-NONZERO-TEN-TWELVE-PLATEAU-ALIAS-RIGHT-SLOPE-EXIT.md). No reconstruction is attempted there.

## 2. The degree-100 factor: the actual right temporal row restores rank

Use the simple residue place \((p,a,d)=(31,12,5)\) of the monic irreducible degree-100 factor. The replay checks \(p\)-integrality of its coefficients, nonzero derivative at \(a=12\), a unit leading coefficient of \(\mathcal D\) in \(d\) (degree 13 retained), and the single linear gcd in \(d\) of the two input residues. As in the [left moment proof](ERK11-NONZERO-TEN-TWELVE-PLATEAU-ALIAS-LEFT-MOMENT-EXIT.md#1-exact-projection-and-finite-place-ingress), these checks give a Hensel embedding of the exact \(a\)-field; any actual \(d\) extends to it and is integral because it solves the unit-leading diagonal. Thus every candidate on the factor must reduce to the indicated \(d=5\). Only coefficients and justified width-shape ratios are reduced, not an arbitrary tableau.

For each orientation form the four actual sparse equations in \((U,W,T,A)\): three correctly reflected moment rows and its actual outer row. Their last column is affine in the true product parameter \(t\) of that orientation. Their full determinant is \(g_0+t g_1\) whether or not a fixed moment block is invertible. The replay checks the live width and row normalizations, then the two affine slopes \(g_1\), so \(t=-g_0/g_1\) gives true recovered products with residues \(t_L=4,t_R=25\). The left three moment rows give a live first-three-column pivot. The right first-three-column block has a live pivot using moment rows 0 and 1 plus the **actual temporal outer row**. Its residue determinant is \(7\). In particular \(A\) cannot vanish in either true nonzero kernel: the corresponding live pivot would force all four coordinates zero. Normalize \(A=1\) and reconstruct the two true affine first-pool lines using those pivots and the live \(t_L,t_R\).

The lines obtained are \((p_0,p_1)=(28,10)\), \((q_0,q_1)=(26,10)\bmod31\), with the right line still in \(Y\). They must be proportional after reflection to the same physical first pool. The exact projective criterion
\[
 p_0q_1+p_1(q_0+q_1)=0
\]
instead has residue \(20\bmod31\). This rules out the last width factor. It does not suppose the left fixed moment pivot live in an arbitrary right-loss chart: the exact small factors already exited, and the last factor has an explicit place where that pivot is a unit.

The standalone replay reconstructs the exact resultant, small quotient-field checks, the large factor's place and all local pivots. The companion Lean checks the explicit three-row minor, affine recovery and last projective obstruction as integer residues; the tableau and field-place arguments remain in the mathematical proof.

The [standalone exact replay](erk11-plateau-alias-right-moment-exit/replay_erk11_plateau_alias_right_moment_pivot.py) and [Lean scalar gates](../lean/RKCert/ReviewedNative/ERK11RightMomentFallbackGate.lean) were independently checked, the latter on all four targeted versions.
