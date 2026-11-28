
# Right nonshared fixed block: rank repair and five complete clock slices

**Scope.** In the ordered, all-live, seventeen-stage ERK11 neighboring singleton chart with \(q=10,n=12\), half-clock two carriers, both seventh boundaries new, full pairs of widths \(a\) and \(b=1-d\), and actual \(s=c_8=c_9\notin\{0,1,a,d\}\), consider the **nonshared right fixed-moment factor** of bidegree \((23,20)\). The central diagonal is live and \(K_0\ne0\); both actual second-pool endpoint values are assumed live (the earlier single- and double-endpoint exits cover the rest). This note excludes every point of that factor with \(a=1\), \(b=1\), \(a=b\), \(c_{10}=0\), or \(c_{10}=1\). It also gives a rank-free measurement of the right calibrated hull and the exact behavior of the temporal repair on the rest of that factor. **The remaining unequal-width, off-axis, nonendpoint-outer points are not excluded.** This does not change an unrestricted stage count.

The notation and the width, diagonal, and derivative-slope guards are those in the [neighboring width reduction](ERK11-NONZERO-TEN-TWELVE-NEIGHBOR-SINGLETON-WIDTH-REDUCTION.md), plus its diagonal, initial-slope, full-rank and individual-mask follow-ups. The [shared-factor exit](ERK11-NONZERO-TEN-TWELVE-NEIGHBOR-SHARED-FIXED-EXIT.md) removes \(E_L,E_R\). On the nonshared right factor, the original right fit uses actual \(L_7\) and the left fit actual \(R_9\). The actual right outer clock in the oriented variable \(Y=1-X\) is \(x=1-z,\ z=c_{10}\); the rank-one correction node is \(\sigma=1-s\), not \(x\).

## 1. The unordered right product is fixed even when the temporal repair loses rank

Use \(w=b\), \(h=w/2\), and both live derivative slopes \(\ell_0,\ell_1\) of actual \(L_7\) against the right anchored basis. Put
\[
 \phi=Y^2(w-Y),\quad B_0=Y(Y-w)(Y-h),\quad
 B_1=(Y-h)[w\ell_0-(\ell_0-\ell_1)Y].
\]
The actual sparse coefficients, of which \(A_f,B_f\) are **coordinates** and \(B_0,B_1\) are polynomials, satisfy
\[
 Q=U_f\phi+(W_fY+A_f)B_0+(T_fY+B_f)B_1,\qquad B_f=t_R A_f
\]
for the true product parameter \(t_R\ne0\). The five columns are a basis of the polynomials of degree at most four. The true corrected moment kernel \(K_3\) has dimension two. Since the actual own endpoint \(Q(0)\) (physical \(Q(1)\)) is live, the subspace \(K_3^0=K_3\cap\ker\operatorname{ev}_0\) is a line.

The three fixed columns are \(\phi,YB_0,YB_1\). Their moment block has rank two on this factor, so their span intersects \(K_3\) nontrivially. As the columns all vanish at zero, that intersection is exactly \(K_3^0\). Thus both sparse coordinates \(A_f,B_f\) vanish on that line. On any member of \(K_3\) with nonzero value at zero, both \(A_f,B_f\) are nonzero: on the physical \(Q\) this holds by \(B_f=t_R A_f\) and the live endpoint, and any other such member is its live multiple plus an element of \(K_3^0\). Consequently \(t_R=B_f/A_f\) is a **width-only ratio**, independent of the chosen live-endpoint member of \(K_3\). The monic unordered hull \(B_0+t_R B_1\) is therefore measured without fitting the right temporal row or inverting the lost three-by-three block. The argument assumes no leading coefficient of \(Q\) or of a cofactor. It also works at an exact intersection with another fixed moment loss.

Write any nonzero \(q_{\rm dead}\in K_3^0\) as \(Y r(Y)\), \(\deg r\le3\). From the fixed columns one reads
\(\ell_0 r(w)+\ell_1 r(0)=0\): \(\phi/Y\) and \(B_0\) vanish at both anchors, and \(B_1(0),B_1(w)\) are respectively \(-hw\ell_0,hw\ell_1\). Let \(\mathcal J_R\) be the true right outer linear functional and \(E(Y)\) its adjusted primal cubic as in the prior fit. The polynomial quotient formula for \(\mathcal J_R\) gives
\[
 \mathcal J_R(q_{\rm dead})
 = -w\ell_0 E(x)r(w)-w\ell_1 E(0)r(x)
 = w\ell_1\big(E(x)r(0)-E(0)r(x)\big).
\]
This formula is valid even at \(x=0\): the quotient by \(Y\) was polynomial before evaluation. If this scalar is live, subtract the unique multiple of \(q_{\rm dead}\) from any other member with live endpoint to get the actual shape line. If it is zero, an actual live-endpoint \(Q\) requires \(\mathcal J_R=0\) throughout \(K_3\), since \(Q,q_{\rm dead}\) are independent. In particular, at \(z=1\), \(x=0\) makes \(\mathcal J_R(q_{\rm dead})=0\) identically. This is a structural rank-loss criterion, not a division by a raw affine coefficient.

## 2. Three width lines

Let \(F_R(a,b)\) be the primitive irreducible \((23,20)\) factor of the exact right fixed determinant after removing only live width factors and its other irreducible \(E_R\), of bidegree \((21,21)\). The exact factorization is regenerated in the standalone replay.

* At \(a=1\), \(F_R(1,b)\) has degree 20, with irreducible factors of degrees 14 and 6. Their roots force, respectively, the original **left second derivative slope** and the cleared \(s-z\) factor to vanish, by exact univariate divisibility.
* At \(b=1\), \(F_R(a,1)\) is irreducible of degree 23. Its simple full-degree good place is \((p,a,b)=(17,8,1)\). The actual left full moment-plus-temporal matrix has rank four there, and its projective common \(Q\) has both endpoint coordinates live. Both bases invert with all needed quotient coefficients live. Their oriented first-pool lines are \((11,1)\) and \((8,16)\) in the normalization of the replay, giving the required physical projectivity determinant \(13\bmod17\), not zero.
* At \(a=b\), the degree-42 specialization is the forbidden \(a=0\) factor times one degree-41 irreducible factor. At its full-degree simple place \((19,7,7)\), the same valid coefficient calculation gives oriented lines \((1,3),(14,7)\) and determinant \(13\bmod19\).

On these lines the second width is determined by the first (or the single width variable in the \(a=1\) line); there is no second extension or hidden choice of a \(b\) root. Over the field of the indicated exact irreducible factor, a simple point of its integral polynomial at the chosen prime gives an embedding into the local field. All required nonzero minors and divisions are units at that place. Thus a residue nonzero mark is a contradiction to an **exact** zero in the width field, not a claim that arbitrary tableau coordinates reduce at that prime.

## 3. Two actual outer-clock endpoint slices

The mixed square-and-primitive moments measure \(z=z_N/z_D\) with \(z_D\ne0\). For \(z=0\) use the live-deflated numerator of \(z_N\); for \(z=1\) use the live-deflated \(z_N-z_D\). Denote these two polynomials by \(Z_0,Z_1\). Their bidegrees are \((4,4),(4,2)\). The exact \(b\)-resultants with \(F_R\) have degrees 168 and 124 in \(a\), with all factors as follows (degrees with multiplicities):
\[
 z=0:1^4,8^6,12,104,\qquad
 z=1:1^4,4,8^6,12,56 .
\]
Every actual affine width lies above a root of its indicated exact norm, regardless of degree losses in the specialized \(b\) equation. For the small factors, compute the actual polynomial gcd in \((\mathbb Q[a]/F)[b]\), using the specialized polynomials with their true degrees, not the generic leading terms. The following lists the entire nonconstant \(b\)-gcd and its exact saturation:

| clock | \(a\)-factor degree | joint gcd degree in \(b\) | exact guard exhausting it |
|---|---:|---:|---|
| \(z=0\) | 1 | 2 | \(a\) |
| \(z=0\) | 8 | 1 | \(H\) |
| \(z=0\) | 12 | 1 | \(z_D\) |
| \(z=1\) | 1 | 2 | \(a\) |
| \(z=1\) | 4 | 1 | cleared \(s-z\) |
| \(z=1\) | 8 | 2 | \(H\), with repeated removal |
| \(z=1\) | 12 | 1 | \(z_D\) |

For degree 104 at \(z=0\), take \((p,a,b)=(37,7,7)\). The \(a\)-polynomial has full degree and simple root, \(F_R(a,b)\) retains full \(b\)-degree 20, and the **whole** \(b\)-gcd with \(Z_0\) in that residue is \(b-7\). Its root is simple for \(F_R\). Every possible exact \(b\) is integral at the extending place by the unit leading coefficient; it reaches that single width root, and the simple Hensel lift of \(F_R\) fixes it. All normalizing guards are units. Reconstructing the actual profile from the unit left cofactor gives two first-pool lines \((32,12),(17,17)\), and the necessary physical projectivity instead equals \(27\bmod37\).

For degree 56 at \(z=1\) use the full simple place \((23,6,13)\), with the **whole** residue gcd \(b-13\) with \(Z_1\) and unit leading degree 20. The actual right four-row matrix has rank four at this place, hence exactly rank four over the width field. This is not a modular assertion that \(Q(1)=0\) implies an exact zero. The exact fixed-block rank is two and \(x=0\) makes the actual last row
\[
 (0,0,0,S_0(0),S_1(0)).
\]
The exact right fixed-block null vector with last two entries zero is therefore in the full kernel and spans it. Every actual \(Q\) must then have \(B_f=0\), forcing its exact right endpoint zero. This contradicts the actual endpoint-live assumption. No leading coefficient of \(Q\) is needed, and the right norm's small leading-drop fibers were retained above.

The deterministic Python replay uses python-flint 0.9.0. It reconstructs all polynomials and quotient-field tests without saved coefficients or numerical searches. The companion Lean verifies the two cleared scalar parts of the rank-repair law over arbitrary commutative rings. The anchored row geometry, the ordered width guards, and the algebraic field-place argument remain mathematical. The five exits hold over ordered fields, with characteristic-zero exact arithmetic once the inherited geometric guards are supplied.
