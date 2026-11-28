# A sparse explicit width eliminant for the unequal-width plateau alias

**Scope.** In the [finite-width dormant-center chart](ERK11-NONZERO-TEN-TWELVE-CENTRAL-ALIAS-FINITE-WIDTH.md), take the two full active plateau pairs, the sole dormant physical 9, and its clock \(\zeta=d\), the opposite plateau \(d=1-b\). This gives a practical explicit eliminant in \(a,d\) and exact projections of the six exceptional pivot masks, without assuming \(a=b\). The \(\zeta=a\) orientation is its reflection. The ordered mixed-moment guards from the earlier work are needed to measure \(c_8,c_{10}\) and the central row. With those guards supplied explicitly the new algebra is characteristic zero. The remaining candidates, including every mask intersection, are not excluded here. No unrestricted stage interval changes.

## 1. Use both calibrated extras without paying for an extra grade

Use the physical coordinate on the left; on the right, use the reflected coordinate \(Y=1-X\). In either orientation write \(w\) for the width, \(h=w/2\) for its own half-clock in that coordinate, and \(u,v\) for its two genuine calibrated extras. The actual front proof gives them distinct, nonzero, and different from \(w,h\). The left opposite row for this argument is **the actual physical \(R_9\)**, which at the dormant \(\zeta=d\) is a live multiple of \(r_d\). The right opposite row is **the actual physical \(L_7\)**, measured up to a live scalar by the row-7 derivative contact against \(R_9\). This second choice uses actual \([L_7,R_{10}]=0\) and does not require measuring the high-degree central amplitude for the right fit.

Let \(D_0,D_w\) be the two derivative rows on the orientation's anchored model space. Pair them against the chosen opposite row to get \(\ell_0,\ell_1\). On the left these are the pairings with \(r_d\). On the reverse side they are obtained from the already earned left row direction \(\Phi_L=\ell_1 D_0-\ell_0D_w\) against the two reflected derivative rows. If a first coefficient \(\ell_0=0\), its corresponding seventh-row off-diagonal forces \(\ell_1=0\), because both actual calibrated extras are nonzero. This is an exceptional width mode, not a division made in that case. Work first with the two first coefficients live.

The true seventh-row functional has coefficients \((w-u)(w-v),-uv\) at \(D_0,D_w\). Its off-diagonal therefore gives the **unordered** calibrated hull
\[
 B(X)=B_0(X)+tB_1(X),\qquad
 t=\frac{uv}{w\ell_0}\ne0,\qquad
 B_0=X(X-w)(X-h),\quad
 B_1=(X-h)\,[w\ell_0-(\ell_0-\ell_1)X].
\]
Indeed \((w-u)(w-v)\ell_0-uv\ell_1=0\) fixes the sum of the two extras to \(w+(\ell_0-\ell_1)t\). This is an exact physical seventh-row condition, not a model symmetry assumption about the order of the two extras.

Use \(x\) for the outer middle clock in that orientation (\(c_8\) on the left, \(1-c_{10}\) on the right), both already determined by the true mixed moments of the central alias. Let \(\mathscr P_w\) be the corresponding square-clock primitive. Pair the adjusted row model
\[
 d(s)=\mathscr P_w(w)\operatorname{ev}_s-\mathscr P_w(s)\operatorname{ev}_w
\]
against the chosen opposite row. Up to a live scalar, it is \(s(s-w)E(s)\) for a scalar cubic \(E\) of degree at most three. These two roots are exact because the anchored models vanish at their own origin and the plateau adjustment is literal. Write \(e_0=E(0)\). The correction to the adjusted actual row is a quadratic \(S(s)\) times its physical response. On the first six this is the same measured correction as in the symmetric proof. Pairing also at the genuine seventh-row hit adds the second extra: \(d(s)+f(s)S(s)=0\) at \(h,u,v\), with \(f=s^2(w-s)/w\). The seventh hit is paid because \([L_7,R_9]=0\) or \([L_7,R_{11}]=0\) respectively. Thus \(E-s S/w\) is a scalar multiple of \(B\). Evaluating at zero and using the true \(B(0)=-huv\ne0\) gives
\[
 B(0)S(X)=S_0(X)+tS_1(X),
\quad
 S_0=-w e_0(X-w)(X-h),\quad
 S_1=\frac{w}{X}\,[E(X)B_1(0)-e_0 B_1(X)] .
\]
The quotient by \(X\) is **polynomial** (the numerator has zero constant coefficient), so this evaluates even at an outer clock \(x=0\). There is no requirement that the two middle clocks or any unrelated clock stay distinct in a finite residue.

The exact grade-five off-diagonal at the eighth-row hit gives \(d(x)+F_x S(x)=0\) in that orientation. Here the adjusted primitive read is zero by strictness. Its actual first/second pool sample is \(Q(x)=P(x)F_x\), using \(P/\kappa\) and the reflected variable on the right. The scalar exchange
\[
 d(x)B(0)+f(x)(S_0(x)+tS_1(x))=x(x-w)e_0 B(x)
\]
follows by substitution and does not divide by \(x\). Write \(Q=P f+(A+BX)B(X)\). Multiplying the outer sample and canceling only the **actual** \(B(x)\ne0\) gives the necessary outer row
\[
 x(x-w)e_0 P(x)+(A+Bx)(S_0(x)+tS_1(x))=0 .
\]
The guard \(B(x)\ne0\) follows because the two active outer middle sites are genuine singleton labels, distinct from every calibrated active flank label in this both-full census. The resulting equation is polynomial and requires no extra modular exclusion if the guard collapses at a later place.

## 2. A sparse fixed moment block and an affine product equation

The true second interpolant \(Q\) is degree at most four, and the three **rank-zero** scalar moments \(\int X^j X(1-X)(X-a)(X-d)Q=0\) for \(j=0,1,2\) hold because the dormant clock is already a plateau label. They are used in each coordinate (the reflected weight is \(Y(1-Y)(Y-b)(Y-(1-a))\)). No degree-four leading or root condition on \(Q\) is required.

Replace \(P\) by its live scale \(P/w=U+C(X-h)\), write \(\phi=X^2(w-X)\), and let \(W=B-C,\ T=tB\) for the affine coefficient \(A+BX\) in the preceding fit. Then the two scalar identities are
\[
 \begin{split}
 Q&=U\phi+W X B_0+T X B_1+A(B_0+t B_1),\\
 0&=U\,w x(x-w)e_0+W xS_0(x)+T xS_1(x)+A(S_0(x)+tS_1(x)).
 \end{split}
\]
They use exactly \((X-h)\phi+X B_0=0\) and the displayed \(S_0\). Thus **only the \(A\) column depends on \(t\)**. There is an affine determinant, not a quartic in a chronologically chosen first extra. The companion Lean checks these transformations over a commutative ring.

Let \(M_*\) be the fixed three-by-three moments of the first three columns \(\phi,XB_0,XB_1\). Write \(\Delta=\det M_*\), and \(\mathbf c_0,\mathbf c_1\) for the negative Cramer vectors with last columns the moments of \(B_0,B_1\). In the regular chart \(\Delta\ne0\), every nonzero moment-kernel coefficient vector is proportional to \((\mathbf c_0+t\mathbf c_1,\Delta)\). Substitute it in the actual outer row to obtain the affine law \(g_0+t g_1=0\), after the live \(x\)-denominator raised to the third power clears all degrees of the outer entries. On \(g_1\ne0\), \(t=n/m\) where \(n=-g_0,\ m=g_1\). The code may remove a common factor from \(g_0,g_1\) only under the **raw** \(g_1\ne0\) guard.

For \(\mathbf c=m\mathbf c_0+n\mathbf c_1\), a polynomial numerator for the first-pool coefficient line in that coordinate is
\[
 p_1=m c_T-n c_W,\qquad p_0=n c_U-h p_1 .
\]
This retrieves the true \(P/w\) up to live scaling, since \(t P_1/w=T-tW\) and \(t P_0/w=tU-h(T-tW)\). Both recovered lines are nonzero in an actual regular layout; therefore exact polynomial common factors of their two entries can be canceled without losing a live candidate. Let the reduced left and right lines be \((p_0,p_1)\) and \((q_0,q_1)\), with the second still in \(Y=1-X\). The actual proportionality of the two first pools in **physical** coordinates gives the independent mark
\[
 \Pi(a,d)=p_0 q_1+p_1(q_0+q_1)=0 .
\]
This uses the genuine same \(P\) on both sides, not merely independent fitting of two affine denominators. The two recovered \(Q\) lines after reflecting to physical coordinates are **identically proportional as bivariate polynomial vectors**; the replay checks all their coefficient cross minors are zero. They are not counted as another cut.

## 3. Explicit degrees and all exceptional masks

The exact cleared line bidegrees in \((a,d)\) are \((25,26)\) and \((23,30)\). The first-pool mark has bidegree \((48,56)\) and no common polynomial factor with the genuine central diagonal \(\mathcal D(a,d)\) of bidegree \((8,13)\). In particular it is independent, unlike the 7–11 width slope identity. As a small separate check, at the coefficient specialization \(a=2\bmod19\) the two \(d\)-polynomials have unit gcd. This is not a width exclusion.

The six exceptional width masks are the two **raw first slope coefficients**, the two fixed moment determinants \(\Delta\), and the two **raw affine slopes** \(g_1\). If any vanishes, keep \(\mathcal D=0\) and that mask equation, without using the regular first-pool line. The first raw slope mask includes any common slope factor used when normalizing its two entries. The remaining common-factor removals are safe only once the relevant row, \(E\) with live first derivative, or first-pool line has been earned nonzero. Already live \(a,d,d-1,a-d\) factors can be removed from the guard masks (the double-zero central exclusion gives \(d\ne0\)). No other rank, pole or width exceptional case is dropped.

The exact \(d\)-resultant of \(\mathcal D,\Pi\) has degree **1060** in \(a\), with factor degrees and multiplicities \(1^{16},3^3,8^8,12^6,12^7,815^1\); the two degree-twelve factors are distinct. These are necessary regular width factors, not certified feasible or infeasible fibers. The \(d\)-resultants for the six exceptional masks are nonzero, of degrees **32, 63, 143, 138, 494, 422** in the order left slope, right slope, left moment pivot, right moment pivot, left affine slope, right affine slope. At \(a=2\bmod19\) all six mask polynomials also have unit gcd with the diagonal. Neither this place nor overlap of univariate resultant factors licenses discarding an exceptional \(d\)-fiber: its actual width still needs to solve the corresponding pair of bivariate equations. The archived coefficient gcd 1 of \(\mathcal D\) prevents a vertical width fiber even at all these mask roots.

The standalone replay optionally computes all seven exact resultants, and the adjacent Lean file checks the scalar sparse profile, outer transformation and proportionality identities. The written tableau and polynomial elimination ingress is mathematical. Reflection transfers the result to the other plateau alias without ordinary reverse order eleven.

The [full exact replay](erk11-sparse-plateau-alias-eliminant/replay_erk11_sparse_plateau_alias.py) takes `--full`; the [resultant-factor archive](erk11-sparse-plateau-alias-eliminant/optional-exact-factor-data) also has an [independent modular product check](erk11-sparse-plateau-alias-eliminant/verify_factor_data.py) at 103 and 107. The [four scalar Lean lemmas](../lean/RKCert/ReviewedNative/ERK11SparseFlankProfileGate.lean) passed 4.34.1, 4.35.0, 4.36.0 and 4.37.0-rc1.
