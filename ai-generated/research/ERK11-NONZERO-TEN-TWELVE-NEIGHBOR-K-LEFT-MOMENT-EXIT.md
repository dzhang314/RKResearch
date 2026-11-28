# The neighboring singular cross block has no left fixed-moment loss

**Scope.** In the [neighboring singleton original right-loss chart](ERK11-NONZERO-TEN-TWELVE-NEIGHBOR-SINGLETON-RIGHT-SLOPE.md), take the sole dormant physical 9 sharing the active singleton \(s=c_8\notin\{0,1,a,d\}\), with the fixed full-pair ordered ERK11 chronology. Assume the original right initial loss, equivalently \(K_0(a,b)=0\). Use actual \(R_9\) for the left fit and the already proved live alternative actual \(L_9\) for the right. This excludes the **left fixed three-by-three moment loss on this particular width curve**. It makes no claim for the same moment mask away from \(K_0=0\), or for the other fit masks or unrestricted stage count. Reflection gives the corresponding mirrored result.

## 1. Normalize only the calibrated hull slope, then clear the measured moment

The right-loss proof gives \([D_L^a-K_{10}D_L^0,R_9]=0\) on the actual \(K_0\) curve. The original first left slope is live, so its two hull slopes can be normalized to \(1,K_{10}\), with \(K_{00}=1\). This changes only the scale of the unordered product parameter. It multiplies the third fixed moment column \(XB_1\) by a live scalar and preserves its zero-pivot condition. Thus use
\[
 h=a/2,\quad B_0=X(X-a)(X-h),\quad
 B_1=(X-h)\bigl[a-(1-K_{10})X\bigr],\quad \phi=X^2(a-X).
\]
Here \(K_{10}\) uses \(N\) in the derivative matrix; the normalization comes from the actual curve, not a specialization of unrelated slopes. The proof of moment loss below always uses actual original \(R_9\) and its outer equation.

Use the measured width scalars from the right-loss note. In particular \(U=C_1 z_D-Hz_N,\ S=C_2 z_D-H z_N,\ B_N=(H-C_2)(C_2-dH)\), and the exact cleared diagonal coefficients \(\alpha',\beta'\) satisfy
\[
 u=-\frac{\alpha'}{H^3\beta'},\qquad
 v=\frac{J_0 B_N S}{H^3 U}.
\]
The diagonal-pole exit and \(u\ne0\) make \(\alpha',\beta'\) live. The rank-one moment weight is therefore \(\rho=J_0/(uv)=-H^6 U\beta'/(\alpha' B_N S)\). For the three fixed columns \(\phi,XB_0,XB_1\), write \(M^0\) for the three uncorrected \(\omega\)-moment rows. The exact corrected determinant is
\[
 \det M^0-\rho\sum_{j=0}^2 s^j\det\bigl(M^0 \text{ with row }j
                         \text{ replaced by the three column values at }s\bigr).
\]
All terms with at least two replaced rows vanish because both are proportional to the same evaluation row. In the sum, substitute \(s=C_2/H\) and multiply by \(H^6\) (all summands have \(s\)-degree at most six). This gives a polynomial width test after multiplying \(\det M^0\) by \(\alpha' B_N S\) and adding \(U\beta'\) times that homogeneous sum. The normalizing and clearing factors remain live in the actual chart.

The resulting left fixed moment polynomial has raw bidegree \((42,37)\) and live-deflated bidegree \((40,34)\) in \(a,b\). Its exact \(b\)-resultant with \(K_0\) has degree 222 in \(a\) and irreducible degrees and multiplicities \(12^2,12^2,66,108\). In the two exact degree-twelve fields the whole common-gcd in \(b\) is linear, and each value makes \(U=0\), contrary to the true mixed guard. The slope normalization above is the reason no spurious initial-slope component needs a width fit.

## 2. Complete exits of the two remaining width factors

For the degree-108 factor use the simple place \((p,a,b)=(19,9,6)\), and for degree 66 use \((41,33,22)\). In each case the monic exact \(a\)-factor has a simple residue; \(K_0\) retains full \(b\)-degree three, and the **entire** joint residue gcd in \(b\) of \(K_0\) and the left moment polynomial is linear. The Hensel embedding extends to the candidate \(b\), which is integral by the unit leading coefficient. All such candidates reduce to the indicated \(b\); no unknown tableau entry need be reduced. The replay checks all required width and actual row units.

* At degree 108, the original right fixed moment pivot and both full affine slopes are units. Restore the left pivot by its two lowest moment rows and the actual temporal outer row \([L_8,R_9]=0\). Their first-three-column minor is a unit, so the true nonzero kernel normalizes with last coordinate 1. Both products and first-pool lines are then measured. The residue lines are \((17,1),(9,2)\) in the oriented variables; their required physical projectivity determinant reduces to 7 modulo 19, not zero.
* At degree 66, use the guarded right shape fit with actual \(L_9\). Reflect its measured first- and second-pool lines to the physical coordinate, and calibrate their relative scale at the actual left half-clock so that \(Q(h)=P(h)f_L(h)\). The old left fit need not be pivotable. The **original**, uncompressed actual left outer contact at \(c_8=s\) then gives a necessary affine equation in \(t_L\) from that known response profile. Its coefficients are \(k_0=2,k_1=33\bmod41\), so \(t_L=31\) in the residue. At that \(t_L\) the three true left calibrated singleton hits have monic hull \(B_0+t_L B_1\) in its actual slope normalization. It must divide \(Q-P f_L\). Monic remainder commutes with reduction even if residue labels collide. The replay obtains \(18X^2+28X+29\), nonzero. This rejects a true width without using a constraint inferred solely from a vanished residue affine slope.

Thus all left fixed moment widths on \(K_0=0\) fail. The deterministic python-flint 0.9.0 replay took 1.186 seconds wall time on the reference host, with no external data. The companion Lean file checks the scalar terminal arithmetic; the actual-tableau and field-place arguments remain mathematical.
