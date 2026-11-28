# Twelve active rows: symmetric-width central aliases are impossible

**Scope.** Continue the [two-pair twelve-active chart](ERK11-NONZERO-TEN-TWELVE-ACTIVE-TWO-PAIR-GATES.md) with \(q=10\), both plateau fifths active, and the sole dormant middle row at physical 9. Over an ordered field with **equal oriented widths** \(a=b\) (so \(d=1-a\)), its clock \(\zeta\) cannot lie in \(\{0,1,a,d\}\). The proof does not need ordinary reverse order eleven, any ghost-root or weight condition, or separation of \(\zeta\) from other unrelated labels. For unequal widths it gives a necessary exact width curve and flank system, not an exclusion. The full twelve-active chart and unrestricted stage interval remain open.

## 1. A reciprocal diagonal gives a width-only equation

Write \(\mathscr P=J V_a,\ \mathscr Q=\bar J V_b\) for the grade-five primitive models of the actual square-clock vectors \(V_L,V_R\). Use \(p=AV_L,\ r=A^\star V_R\) for their actual numerical lifts. Keep the true mixed scalar integrals \(H,C_1,C_2,J_0,I_0,I_1,I_2\) from the two-pair note. In particular \(J_0=b_9p_9r_9\), and the edges \(p_8=r_{10}=0\) are literal. Throughout write \([L,R]\) for the inverse anchored Gram pairing including its normalization: in the two natural monomial bases it is \(210\,L^\mathsf T N R\). Actual physical rows \(7,\ldots,11\) on the two sides have \([L_i,R_j]=\delta_{ij}/b_i\). Let \(\ell_y\) and \(r_y\) denote evaluation at the physical clock \(y\) in the anchored forward and reverse model spaces. They are distinct functionals from the numerical primitive \(r\).

The [dormant inverse-Gram row formula](ERK11-SIX-PAIR-DORMANT-INVERSE-GRAM-PORT.md) applies also to an aliased dormant **physical** row: \(L_9=\ell_\zeta+\eta\ell_a,\ R_9=r_\zeta+\eta^\star r_d\). It only uses \(F_9=s_9=0\) and the local fifth-grade pivot, not whether the clock is new. The scalar coefficients are measured by \(p_9,r_9\), using \(\mathscr P(a)=a^5/30,\ \mathscr Q(d)=b^5/30\), both live.

By reflection it suffices to consider \(\zeta=d\) and \(\zeta=0\). The double-zero alias is already excluded over ordered fields, so \(d\ne0\) in each of these two cases. Put \(x=c_8,z=c_{10}\). In both cases the central \(V_LV_R\) read vanishes, so \(I_2-(x+z)I_1+xzI_0=0\). Over an ordered field \(H,J_0,I_0>0\), \(0<C_i<H\), and the strict weighted variance \(I_0I_2-I_1^2>0\) ensure the following clock and primitive divisions are live. These are the inherited rational Gram arguments, not restrictions that all tableau weights have a sign.

* For \(\zeta=d\), the shifted \(pV_R\) contact gives \(z=C_1/H\). Then
\[
 x=x_N/x_D,\quad x_N=H I_2-C_1 I_1,\quad x_D=H I_1-C_1 I_0 .
\]
The exact \(V_Lr\) contact with clock mask \(C-x\) is \(C_2-xH=b_9r_9(d-x)V_a(d)\). Both \(x\ne d\) and \(V_a(d)\ne0\) are earned: \(x\) is a singleton active clock distinct from the full plateau; \(a\ne d\) and the double-zero exit gives \(d\ne0\). Put \(S=(d x_D-x_N)V_a(d)\), \(U=C_2x_D-Hx_N\). Then \(b_9r_9=U/S\), \(p_9=J_0 S/U\), and both \(S,U\) are live. Thus
\[
 \widehat L=U\mathscr P(a)\ell_d+
              (J_0S-U\mathscr P(d))\ell_a,\qquad \widehat R=r_d
\]
are live representative scalings of \(L_9,R_9\). Their actual reciprocal diagonal gives
\[
 [\widehat L,\widehat R]=S\,\mathscr P(a)\mathscr Q(d).
\]
Indeed \(L_9=\widehat L/(U\mathscr P(a))\) and \(R_9=(r_9/\mathscr Q(d))\widehat R\).

* For \(\zeta=0\), the shifted \(V_Lr\) contact gives \(x=C_2/H\); use
\[
 z=z_N/z_D,\quad z_N=H I_2-C_2 I_1,\quad z_D=H I_1-C_2 I_0 .
\]
The \(pV_R\) contact with \(C-z\) gives \(C_1-zH=-b_9p_9 z V_b(0)\), and \(V_b(0)=d^2\ne0\). If \(z=0\), the same equality contradicts \(C_1>0\). Put \(S=-z_N V_b(0)\), \(U=C_1z_D-Hz_N\), so \(b_9p_9=U/S\), \(r_9=J_0 S/U\), both \(S,U\) live. This time
\[
 \widehat L=\ell_a,\qquad
 \widehat R=U\mathscr Q(d)r_0+(J_0S-U\mathscr Q(0))r_d .
\]
The same cleared diagonal follows by exchanging the measured scales. Here \(L_9=(p_9/\mathscr P(a))\widehat L\) since \(\ell_0\) is zero.

All used shifted factors raise a grade-four vector to grade five. Thus the ordinary order-eleven mixed Gram pays every displayed product, without a reverse grade-five square. The diagonal equation is polynomial in \(a,d\). Its only removed factors in the exact replay are \(a^3d(d-1)(a-d)\) in the first case and \(ad(d-1)^3\) in the second, up to nonzero rational normalization. The genuine remaining width equations have bidegrees \((8,13)\) and \((10,8)\). Substituting \(d=1-a\) yields irreducible width polynomials of degrees **21** and **18**, respectively. The diagonal already removes the extraneous degree-six factor of the neighbor-only slope determinant; that determinant is not treated as an independent equation.

## 2. The live width fiber fixes the two seventh-row directions

On the anchored spaces denote the forward endpoint derivative rows by \(D_L^0,D_L^a\); denote their reflected counterparts, differentiated in \(Y=1-X\), by \(D_R^1,D_R^d\). The actual row 7 is a live multiple of
\[
 (a-u)(a-v)D_L^0-uv D_L^a,\qquad (u,v)=(c_6,c_7),
\]
and the row 11 of a live multiple of
\[
 (w-d)(y-d)D_R^1-(1-w)(1-y)D_R^d,\qquad (w,y)=(c_{12},c_{11}).
\]
These are the actual both-new [derivative contacts](ERK11-LIVE-TRIPLE-EIGHT-CLOCK-HANKEL.md#3-literal-derivative-contact-of-rows-7-and-11), not fitted differentiation matrices.

Put \((l_0,l_1)=([D_L^0,\widehat R],[D_L^a,\widehat R])\) and \((r_0,r_1)=([\widehat L,D_R^1],[\widehat L,D_R^d])\). Each pair is live, coefficientwise, on the selected symmetric exact width fibers: the arithmetic replay earns these units as width residue checks below. Thus the two row directions are
\[
 \Phi_L=l_1D_L^0-l_0D_L^a,\qquad \Phi_R=r_1D_R^1-r_0D_R^d .
\]
Their actual off-diagonals with central row 9 give \(v=N_L/D_L,\ y=N_R/D_R\), with
\[
\begin{aligned}
 D_L&=l_0(a-u)+l_1 u,& N_L&=l_0 a(a-u),\\
 D_R&=r_0(w-d)+r_1(1-w),& N_R&=r_0 d(w-d)+r_1(1-w).
\end{aligned}
\]
Actual denominators are live: in the first relation \(N_L\ne0\); in the second \(N_R-dD_R=r_1(1-w)(1-d)\ne0\). The replay uses these formulas only via polynomial hulls, so it does not discard a residue with a zero denominator in these last two fractions. Pairings may all be computed with \(N\) rather than \(210N\) when only zero or projective direction matters.

## 3. One-flank profile determinants of degree at most four

Use \(Q\) for the true second-response interpolant, not the primitive \(\mathscr Q\). Since \(\zeta\) is one of the pair/endpoint labels, the actual grade-eight mask of the grade-four \(T\) has zero reads. Thus
\[
 \int X^j X(1-X)(X-a)(X-d)Q=0,\qquad j=0,1,2 .
\]
No assumption about the degree or roots of \(Q\) is made. Define the measured nonplateau polynomials \(f_L=X^2(a-X)/a,\ f_R=(1-X)^2(X-d)/b\). Let \(P\) be the true first-response interpolant, and \(\widetilde P=P/\kappa\) with \(\kappa F\) the reflected physical response. At the calibrated left singleton labels \(h,u,v\) and the right \(e,w,y\), the exact response marks are respectively \(Q=P f_L\) and \(Q=\widetilde P f_R\). Hence
\[
 Q=P f_L+(A+BX)B_L(X)
   =\widetilde P f_R+(D+EX)B_R(X),
\quad
 B_L=(X-h)(X-u)(D_L X-N_L),\quad B_R=(X-e)(X-w)(D_R X-N_R).
\]
Both quotients after the three calibrated roots are affine, because \(\deg Q\le4,\ \deg P,\deg\widetilde P\le1\). Pivots were used only for the symbolic hull normalization; no root of \(Q\) is divided by.

The actual row 8 can be read without reconstructing its response. For the forward anchored models write
\[
 d_y=\mathscr P(a)\ell_y-\mathscr P(y)\ell_a .
\]
Subtracting the primitive evaluation direction makes the model vanish at \(a\). The two literal plateau reads then force the extra pure degree-five coefficient and the quadratic response correction's value at \(a\) to vanish. The remaining quadratic correction is determined by the zero readings at \(h,u\). Interpolation yields physical row 8 proportional, with live primitive scale, to
\[
 d_x+F_8 E_L(u)/\Delta_L(u),
\quad
\begin{cases}
 \Delta_L=(h-a)(u-a)(h-u) f_L(h)f_L(u),\\
 E_L=(x-a)\big[-(x-u)(u-a)f_L(u)d_h
                     +(x-h)(h-a)f_L(h)d_u\big].
\end{cases}
\]
This uses the actual zero \(p_8=0\); it does not assume the stage-8 response is calibrated. The reflected row 10 formula is identical with \(a,h,u,x,\ell,\mathscr P,f_L,F_8\) replaced by \(d,e,w,z,r,\mathscr Q,f_R,\kappa F_{10}\), using physical clock coordinates for the polynomial interpolation. All original \(\Delta\)'s are live by the real clock census.

For each of the two opposing row directions \(R_9,R_{11}\) use the scaled representatives \(\widehat R,\Phi_R\). Put \(f_j=[d_x,R_j]\), \(g_j=[E_L,R_j]\), so \(F_8g_j+\Delta_L f_j=0\). The three polynomials \(g_0,g_1,\Delta_L\) divide exactly by \(u(u-a)(u-h)\): the formula for \(E_L\) kills \(0,a\), and its two terms cancel at \(u=h\). The same holds on the right with \((w-1)(w-d)(w-e)\). Use bars for the respective exact quotients. The true outer sample \(Q(x)=P(x)F_8\) then gives two necessary **denominator-free** rows
\[
 P(x)(f_L(x)\bar g_j+\bar\Delta_L f_j)
          +(A+Bx)B_L(x)\bar g_j=0 .
\]
These remain constraints when a residue response pivot vanishes. There are analogous right rows with \(\widetilde P,D,E,B_R,z\) and opposite directions \(\widehat L,\Phi_L\).

For each flank, take the determinant of the three moment rows on its four coefficients and either outer row. The two determinants have degree at most six in \(u\) (or \(w\)): the last two moment columns have degree at most two; the first two outer entries degree at most two, the last two at most four. In the forward determinants \(u(u-a)\) divides **exactly**. At \(u=0\) or \(a\), \(B_L\) is a nonzero multiple of \(X(X-a)(X-h)\); with \(P=X-h\), take \(A+BX\) to make \(Q\) identically zero. Also \(\bar\Delta_L=0\) there, so this nonzero coefficient vector annihilates both possible outer rows as well as the moments. The same argument at \(w=1,d\), with \(\widetilde P=X-e\), gives exact removal of \((w-1)(w-d)\) on the right. These are literal forbidden width-side clocks, not merely modular collisions. The resulting degrees are at most four. No other root is dropped in the replay.

## 4. Exact degree-preserving lift and linear contradiction

For \(\zeta=d\), the width polynomial retains degree 21 at prime 19, with residue factor degrees \(2,4,4,11\). For \(\zeta=0\), it retains degree 18 at prime 29, with degrees \(7,11\). Width is algebraic and integral at the chosen place. The arithmetic checks the live width denominators, slope coefficients and directions at one Frobenius representative of every irreducible residue factor. This earns the needed exact width-side guards before choosing \(u,w\). In each fiber at least one determinant per side retains full degree four, so \(u,w\) are also algebraic and integral. The reduced gcd of the two determinants on each side is degree four and has four distinct roots in the chosen finite extension, giving exactly sixteen possible root tuples per width representative. **All** of them are checked, without assuming their labels remain distinct after reduction.

For each tuple, assemble the homogeneous eight-column system for the two pairs of linear coefficients of \(P,A+BX\) and \(\widetilde P,D+EX\). Use the three moment rows, two outer rows in each direction, and the five coefficient equalities between the two expressions for \(Q\). In each residue it either has rank eight, or rank seven with a one-dimensional kernel whose two first-pool linear rows are **not proportional**. An actual solution must instead have \(\widetilde P=P/\kappa\). A unit rank-eight minor rules out any solution over characteristic zero. In rank-seven residue, a unit seven-column pivot lifts: if a nonzero characteristic-zero kernel exists it is at most one-dimensional, and its generator can be normalized using the live reduced free coordinate to reduce to a nonzero kernel vector. The nonzero reduced determinant of its two first-pool lines contradicts actual proportionality. This argument concerns coefficient fields, so it does not reduce any unknown tableau weight or assume a root of \(Q\) remains live.

The actual proof works in characteristic zero whenever the initial mixed-moment pivots are nonzero; ordering is used to earn them and exclude the double-zero cases here. Reflection preserves the paid mixed chart and the pooled scalar equations (\(F\) only changes scale and the clock reflects), so the same ordered exclusions apply to \(\zeta=a,1\). The standalone exact replay uses python-flint, and the adjacent Lean file checks scalar clearing and proportionality over a commutative ring. The full RK and finite-place ingress remain mathematical.

See the [standalone replay](erk11-ten-twelve-symmetric-central-alias/replay_erk11_symmetric_central_alias.py), [exact output](erk11-ten-twelve-symmetric-central-alias/exact-replay.txt), and the [Lean scalar lemmas](../lean/RKCert/ReviewedNative/ERK11CentralAliasProfileGate.lean). The scalar checks passed on Lean 4.34.1, 4.35.0, 4.36.0 and 4.37.0-rc1.
