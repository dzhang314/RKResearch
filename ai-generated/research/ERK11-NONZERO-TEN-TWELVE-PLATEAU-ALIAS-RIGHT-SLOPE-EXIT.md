# The dormant opposite-plateau alias has no zero right initial slope

**Scope.** In the [sparse ERK11 plateau-alias chart](ERK11-NONZERO-TEN-TWELVE-SPARSE-PLATEAU-ALIAS-ELIMINANT.md), take \(q=10,n=12\), both ordinary plateau pairs full, and sole dormant middle stage physical 9 at \(\zeta=d=1-b\). This excludes the second exceptional mask, the zero right initial inverse-Gram slope, after the full [left initial-slope exclusion](ERK11-NONZERO-TEN-TWELVE-PLATEAU-ALIAS-LEFT-SLOPE-EXIT.md). Reflection gives the corresponding orientations at \(\zeta=a\). The algebra uses an exact characteristic-zero width field; the mixed-pay nonvanishing and the earlier double-zero exit are inherited over ordered fields. The generic moment-pivot and affine-product rank drops are not excluded by this note, nor does an unrestricted stage interval change.

## 1. The actual two-support denominator cannot vanish

Let \(x=c_8,z=c_{10}\) and \(W=X^2(X-a)^2,\ V=(1-X)^2(X-d)^2\). Write \(V_L,V_R\) for the actual grade-four vectors with these models, and \(p=AV_L\) for the actual grade-five primitive with model \(P=JW\). The literal front restrictions are \(V_L|_{1,\ldots,7}=0,\ V_R|_{11,\ldots,17}=0\). Here \(V_R(9)=0\) because the middle row has zero response and its clock is \(d\). Consequently \(pV_R\) is supported only at physical 10, while \(V_LV_R\) is supported in physical \(\{8,10\}\). Define
\[
 H=\int PV,\qquad C_1=\int XPV,\qquad I_j=\int X^jWV\quad(0\le j\le2).
\]
The mixed grade 9 and 10 payments of \(pV_R\) and its clock multiple give \(Hz=C_1\). The grade 8, 9 and 10 payments of \(V_LV_R\) give the nodal identity
\[
 I_2-(x+z)I_1+xz I_0=0.
\]
No assumption that either numerical supported product is nonzero is needed in deriving these equations.

Define \(x_D=HI_1-C_1I_0,\ x_N=HI_2-C_1I_1\). Substitution in the nodal identity gives \(x_N=x x_D\). In fact,
\[
 H(I_0I_2-I_1^2)=(xI_0-I_1)x_D .
\]
Thus \(x_D=0\) would force \(x_N=0\) and zero variance, since \(H\ne0\). The Gram positivity for the nonzero polynomial squares on the mixed integration domains gives \(H>0\) and \(I_0I_2-I_1^2>0\) over an ordered field, as in the earlier two-support argument. The new scalar identity itself needs only a commutative ring; the field corollary uses nonzero \(H\) and variance, not an order. This is why clearing \(x_D\) in a width eliminant may produce a root which cannot carry even an actual middle clock.

## 2. The exact right-initial-slope list

After the left-mask theorem, the two left derivative slopes \(\ell_0,\ell_1\) against \(R_9\) are live. In the anchored degree-five duality use the live direction
\[
 L_7\ \propto\ \Phi_L=\ell_1D_L^0-\ell_0D_L^a .
\]
It is the actual left boundary row, obtained from its off-diagonal with the actual \(R_9\), a live multiple of \(r_d\). Write \(\rho_0=[\Phi_L,D_R^1],\ \rho_1=[\Phi_L,D_R^d]\) for the right initial and endpoint derivative slopes. The actual \(R_{11}\) is proportional to
\[
 (w-d)(y-d)D_R^1-(1-w)(1-y)D_R^d ,
 \qquad (w,y)=(c_{12},c_{11}).
\]
Here \(w,y\ne1\) by genuine chronology, so the coefficient of \(D_R^d\) is nonzero. Therefore \([L_7,R_{11}]=0\) and \(\rho_0=0\) imply \(\rho_1=0\). This step does not fit a rotated row or require nonzero right derivative slopes against \(L_9\).

Use the exact central reciprocal diagonal \(\mathcal D(a,d)=0\) of bidegree \((8,13)\) and the rational inverse Gram. Remove only the geometry factors \(a,d,d-1,a-d\) from the determinant and the two slope inputs. These are live: the widths are nonzero, the two full plateau labels are distinct, and \(d=0,\zeta=d\) is the previously excluded double-zero center. The common monic gcd of the two \(d\)-resultants has degree 27 and exactly three simple irreducible factors of degrees \(3,12,12\); the two individual resultant degrees are 63 and 87. Over each exact field \(\mathbb Q[a]/F\), the three input equations have a monic *linear* gcd in \(d\). In particular there is no lost vertical or positive-dimensional second-width fiber.

1. The cubic \(165a^3-180a^2+54a-4\) forces \(d=1\), a zero right width.
2. The first degree-twelve factor gives \(\ell_0=\ell_1=0\), already excluded by the left initial-slope theorem.
3. On the other factor, whose coefficients from degree 12 to degree 0 are
   \[
   \begin{gathered}
     164711250,-790614000,1680998550,-2086868850,1679022735,\\
     -918969660,349502948,-92707335,16964631,-2084400,163296,-7344,144 ,
   \end{gathered}
   \]
   exact evaluation at the linear \(d\)-root gives \(x_D=x_N=0\). The replay also checks zero Gram variance directly in this quotient field. These widths are already forbidden by §1, even though the left derivative slopes remain live on this component of the *cleared* equations.

Thus no actual right-slope-zero chart reaches an unordered-flank fit. Apparent free flank products on the third factor come only from the lost denominator, not from an unresolved exceptional tableau. The standalone replay constructs all moments and projections from exact rational polynomials, verifies the factorization, exact field gcds and terminal evaluations, and uses no finite-place ingress. The three companion Lean scalar checks do not formalize the actual mixed-grade bridge or the exact polynomial factorization.

The [standalone exact replay](erk11-plateau-alias-right-slope-exit/replay_erk11_plateau_alias_right_initial_slope.py) and [Lean scalar gates](../lean/RKCert/ReviewedNative/ERK11RightSlopeVarianceGate.lean) were independently checked, the latter on all four targeted versions.
