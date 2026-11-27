# All ordinary quadrature mass lies on quadratic-zero clocks at the strict SDIRK8 floor

**Result.** Let \(A,\boldsymbol b\) be a ten-stage strict SDIRK tableau of ordinary order at least eight over a characteristic-zero field. Put \(\boldsymbol c=A\boldsymbol1\), \(\boldsymbol g=A\boldsymbol c-\boldsymbol c^{\odot2}/2\), and \(U=\ker\operatorname{diag}(\boldsymbol g)\). If at least four physical rows satisfy \(g_i=0\), then, for every clock \(x\) and every \(q\ne0\),
\[
                          \sum_{i:\,c_i=x,\ g_i=q} b_i=0 .
\]
In particular all ordinary scalar quadrature is carried by the zero-residual rows, and [together with the earlier exclusions](../sdirk-eight-three-zero-silent/README.md) a zero-containing ten-stage method needs **at least four distinct quadratic-zero clocks**. This does not require each off-zero weight to vanish; canceled groups at equal \((c,g)\) can remain. Neither that remaining zero-containing case nor the zero-free case is ruled out here; the unrestricted interval is still **10–11**.

## 1. Active groups and scalar gates

Use the saturated flags \(E_j,F_j,W_j,Z_j\) and \(C=\operatorname{diag}(\boldsymbol c)\), \(G=\operatorname{diag}(\boldsymbol g)\), \(B=\operatorname{diag}(\boldsymbol b)\), \(M=CA-AC-A^2\), and \(N=A-\gamma I\). Write \(m=\dim U\), \(\ell=10-m\le6\), and \(d_j=\dim(E_j\cap U)\). The [support argument](../sdirk-eight-two-zero-line/README.md) gives
\[
 \dim(W_j\cap U_{\rm row})=m-d_{5-j},\qquad
 \operatorname{rank}(F_{j+2}|_U)=d_j.
\]
The second identity compares \(GE_j\subset F_{j+2}=ME_j\) with the restriction of \(M(E_j\cap U)\), injective by the principal triangular block. If any off-zero stage is active (has nonzero weight), \(E_2^{\mathsf T}B=W_2\), since ordinary probes detect its scalar trace and the active stage detects its pure line \(\langle\boldsymbol g\rangle\). In this situation the terminal stage is active and off-zero: \(b_{10}\ne0\) by trimming, and \(\boldsymbol b^{\mathsf T}G\) and \(\boldsymbol b^{\mathsf T}M\) span the same line \(Z_2\), with the latter's terminal coefficient \(-b_{10}\gamma^2\ne0\). By triangularity and \(D(1)\), \(c_1=\gamma\) and \(c_{10}=1-\gamma\).

First suppose there is a clock with nonzero ordinary off-zero aggregate. The paid \(\boldsymbol b^{\mathsf T} C^j\boldsymbol g=0,\ 0\le j\le5\), separate all off-zero groups (at most six); each active group needs at least two active rows. Three active groups would all be pairs, separated also by \(\boldsymbol b^{\mathsf T} C^jG^2\boldsymbol1=0,\ 0\le j\le2\). In a pair, subtract one residual times the first residual sum from the second to force equal residuals, and then the ordinary weights cancel. More than three active groups are impossible by their sizes. Thus there are at most two active off-zero clocks, and all three residual-power sums separate using \(C^jG^k\boldsymbol1\), \(j=0,1\), \(k=1,2,3\). At a group with nonzero ordinary aggregate, evaluating the at-most-cubic polynomial vanishing at its distinct nonzero residual values would contradict these sums unless there are at least four such values. Hence there is exactly one aggregate-active off-zero clock \(d\), with at least four different active residuals. If another active off-zero clock \(e\) exists, all six off-zero rows are active (four at \(d\), two at \(e\)); the latter pair cancels and has equal residual.

Ordinary quadrature needs at least four distinct sites by Hilbert rank. With exactly four, the monic nodal polynomial is orthogonal to degrees zero through three, so the sites are the roots of
\[
                         L(X)=70X^4-140X^3+90X^2-20X+1 .
\]
With five sites, if three known sites have product \(P(X)\), the monic quadratic for the other two has coefficient vector in the kernel of \([I(X^{i+j}P)]_{i,j=0}^2\), \(I(X^k)=1/(k+1)\). Thus that determinant vanishes. With five known sites and at most one other, the corresponding two-by-two Hankel determinant vanishes by using the product times the missing linear factor (or any factor if all sites are already listed). This test does not require all listed sites to have weight.

When only \(d\) is active off-zero, \(\boldsymbol b^{\mathsf T}(C-dI)\in W_1\) is supported on \(U\). Its right multiplication by \(A\) has profile \(J^*(X-d)\), where \(J^*p(X)=\int_X^1p(t)\,dt\), plus an element of \(Z_2=\langle\boldsymbol b^{\mathsf T}G\rangle\) vanishing on \(U\). Evaluate the latest nonzero coordinate of the supported row, of clock \(z\ne d\); it exists by scalar rank and reads only the diagonal. With \(\gamma=1-d\),
\[
                  (1-z^2)/2-d(1-z)-(1-d)(z-d)=0 .                  \tag{1}
\]
The [exact replay](check_mass.py) excludes this when both clocks are Gauss by a resultant and gcd. Its general roots are \(z=2d-1+v(1-d)\) with \(v^2=2\).

## 2. Two active off-zero clocks

The physical off-zero clocks are exactly \(d,e\), \(m=4\), and \(F_3=GE_1\) is clean on \(U\). The first two rows are off-zero: if \(g_2=0\), the [literal front identity](../clock-localized-tail/tied-stage-floor/FIRST-THREE-ROWS-AND-PHYSICAL-LEVEL-OBSTRUCTIONS.md) \((C-\gamma I)\boldsymbol g=(g_2/g_1)N\boldsymbol g\) would localize all off-zero rows at one clock. The first three clocks are pairwise distinct by the star/arithmetic argument (a coincident star clock would give a literal twin). Therefore row three is a zero; it is arithmetic because the star would keep \(g_3=g_2\ne0\). With gap \(u=(c_2-\gamma)/\gamma\),
\[
                  C_0(u)=4u^3-12u^2+3u+2=0,\qquad a=c_3=\gamma(1+2u).
\]
If the front and terminal clocks differ, the two clocks are \(\gamma,1-\gamma\), so \(\gamma=(2+u)^{-1}\) and \(d\) is either \(\gamma\) or \(1-\gamma\). If the front and terminal both equal \(e\), then \(e=\gamma=1/2\) and \(d=(1+u)/2\); if both equal \(d\), then \(d=\gamma=1/2\). All four possible values of \(d\) are non-Gauss, by exact gcd with \(C_0\).

Since there are only four zero rows, scalar rank now forces **five** distinct sites \(d\) and the four zero clocks, all active; otherwise \(d\) would either be among exactly four Gauss sites or, if its mass canceled against a zero row with the same clock, there would be at most three remaining sites. All ten weights are nonzero. The [full weighted reflection at saturation](../../lower-bounds/characteristic-zero/sdirk_saturated_weighted_mirror_duality_20261123.md) is legitimate, and the reverse quadratic residual is proportional to the forward one by the \(Z_2\) identity. When front and terminal coincide at \(1/2\), the reflected gap is \(-u\), impossible because \(C_0(u),C_0(-u)\) are coprime. Otherwise reflected gap equals \(u\), so the last zero clock is \(1-a\), distinct from \(a\) in this five-site case. The three known sites \(d,a,1-a\) give a nonzero nodal Hankel determinant modulo \(C_0\) for both values of \(d\), contradicting Section 1.

## 3. One active off-zero clock and at least two physical off-zero clocks

The \(W_2\) restriction to active off-zero rows has rank two, so \(d_3=m-2\). With at least three physical off-zero clocks, the \(E_2\) restriction has rank four: three polynomial directions and residual variation at \(d\). Hence \(d_2=0\), and \(F_4=GE_2\) vanishes on \(U\). The column \(L(\boldsymbol c)\) belongs to \(F_4=\operatorname{Ann}(W_3)\) by scalar orthogonality of \(L\) to degree-three profiles. Thus all zero clocks are Gauss, and ordinary quadrature applied to \(L\) forces \(d\) to be Gauss too, contradicting (1).

With exactly two physical off-zero clocks \(d,s\), all rows at \(s\) are silent. Restriction of \(E_2\) has rank three, so \(d_2=1\). The \(E_3\) restriction has rank three or four, since \(F_3=GE_1\), the two scalar sites give rank two, and \(g\) varies at \(d\). Hence \(m=4\) or \(m=5\). The first three again give \(C_0(u)=0\), and \(a=\gamma(1+2u)\) is the first zero. From \(c_{10}=d\) there are two possible front orientations: \(d=\gamma=1/2\) if \(c_1=d\), or \(\gamma=(2+u)^{-1},d=1-\gamma\) if \(c_1=s\). In either case \(d\) is not Gauss.

If there are at most four distinct zero clocks, the same scalar rank argument forces five ordinary sites \(d\) and four zeros, all distinct and aggregate-active. The latest supported zero \(z\) from (1) is distinct from \(a\) by a norm test in \(\mathbb Q[u,v]/(C_0,v^2-2)\). The five-site Hankel determinant for \(d,a,z\) has nonzero norm modulo \(C_0\) in both orientations. This is a contradiction.

Otherwise \(m=5\) and all five zero clocks are distinct. There is only one physical row at \(s\), since at least four rows at \(d\) are active. Every polynomial \(p\) of degree at most three with \(p(d)=0\) is the profile of a supported column \(p(\boldsymbol c)+H(\boldsymbol c)\odot\boldsymbol g\), with \(H\) affine chosen by \(H(d)=0,H(s)=-p(s)/g_s\). On \(U\) its values are \(p(c_i)\). The line \(F_4|_U\) is spanned by \(L(\boldsymbol c)|_U\), because five distinct clocks cannot all be Gauss. If \(z_2\) is the second chronological zero, then for \(p=(X-d)(X-a)\) and \(p=X(X-d)(X-a)\), literal application of \(A\) at the first two zeros sees only the diagonal since \(p(a)=0\). Its scalar profile is \(Jp(X)=\int_0^X p(t)\,dt\) plus that pure line. The necessary tests are
\[
 [\gamma p(z_2)-Jp(z_2)]L(a)-[\gamma p(a)-Jp(a)]L(z_2)=0 .
\]
Their gcd over the gap cubic quotient is exactly \(X-a\) in both orientations, contradicting distinctness. The replay checks the inverse coefficients needed by quotient Euclid.

## 4. One physical off-zero clock

This clock is \(d=\gamma=1/2\) since both endpoints are off-zero. On the off-zero rows \(E_3\) restricts to the span of \(\boldsymbol1,\boldsymbol g,\boldsymbol h\), where \(\boldsymbol h=N\boldsymbol g\); its rank is two or three. Since \(d_3=m-2\), we have \(m=5\) or \(m=6\); also \(d_2=2\). The second clock differs from \(d\), so \(g_2=0\). The first-three identities give the front zero clocks
\[
 1+\epsilon t,\quad 1-\epsilon t\quad\hbox{(star)},\qquad
 1+\epsilon t,\quad 3/2+2\epsilon t\quad\hbox{(arithmetic)},\qquad
 t^2=1/2,\quad\epsilon\in\{1,-1\}.
\]

The last three stages permit the same alternatives in reflected time even if earlier weights vanish. Indeed \(D(1)\) and full reverse rank give \(b_9\ne0,c_9\ne c_{10}\): a silent ninth stage would have no strict successor tap, and equal trailing clocks would make all reverse-word restrictions proportional there. The quadratic reverse word
\[
 \widehat{\boldsymbol w}=\boldsymbol b^{\mathsf T}(I-C)A
           -\tfrac12\boldsymbol b^{\mathsf T}(I-C)^2
           =-\tfrac12\boldsymbol b^{\mathsf T}M
\]
is proportional to \(\boldsymbol b^{\mathsf T}G\). If \(b_8=0\), its coordinate-eight equation and \(D(1)\) would kill both strict successor taps, because the ninth and tenth weights are nonzero and clocks differ. Every reverse word would then vanish in coordinate eight. Thus the last three stages are active, and their literal trailing block can be normalized by just those weights and reversed. Its row sums are the reflected clocks, and its quadratic residual there is proportional to the original one. Its second reflected stage is a zero, since \(c_9\ne c_{10}=d\); the [trailing three-clock alternatives](../../lower-bounds/characteristic-zero/sdirk_saturated_weighted_mirror_duality_20261123.md) give the same four choices for the reflected pair. The third is also a zero because its clock differs from \(d\).

These four prescribed zero clocks are all distinct and different from \(d\), by their rational parts front/back and \(t\notin\mathbb Q\). If there are at most five distinct zero clocks, the known five sites (four zeros and \(d\)) with at most one more must meet the two-by-two nodal Hankel test. The replay checks nonzero determinant norms in all sixteen cases. Hence \(m=6\), with six distinct zero clocks and exactly four active off-zero stages, having distinct residuals.

Now \(E_3\) restriction off \(U\) has rank two. A nonzero constant term of \(\boldsymbol h|_{\mathrm{off}}\) in \(\langle\boldsymbol1,\boldsymbol g\rangle\) would give, by subtracting a pure linear combination from \(\boldsymbol1\), a supported grade-three column of trace \(1\). Pairing it with the output forces the aggregate at \(d\) to vanish. Thus the constant term is zero, and \(h_1=0,g_1\ne0\) force \(\boldsymbol h|_{\mathrm{off}}=0\). The vector \(\boldsymbol h\) is pure and nonzero, since \(h_2=A_{21}g_1\ne0\). The pure column \(A\boldsymbol c^{\odot2}-\boldsymbol c^{\odot3}/3\) is \((4\gamma/3)\boldsymbol g+\lambda\boldsymbol h\) by the first row, and the second row gives \(\lambda=2/3\).

Write \(a=c_2,b=c_3\). If stage four were off-zero, \(h_4=0\) would kill its first strict tap. Its two other strict taps would sum to zero because \(c_4=\gamma\); their first clock moment would be \(g_4-g_1\ne0\), and their second moment \((4\gamma/3)(g_4-g_1)\) by the pure column. Their moment ratio is also \(a+b\), forcing \(a+b=2/3\), incompatible with both front choices. Thus the fourth row is zero at \(x\ne a,b\).

Its three strict taps \(q_1,q_2,q_3\) now satisfy
\[
 \begin{pmatrix}1&1&1\\\gamma&a&b\\\gamma^2-\lambda g_1&a^2&b^2\end{pmatrix}
 \begin{pmatrix}q_1\\q_2\\q_3\end{pmatrix}
 =\begin{pmatrix}x-\gamma\\x^2/2-\gamma x\\x^3/3-\gamma x^2\end{pmatrix},
 \qquad h_4=g_1q_1 .
\]
This system is invertible in both front choices modulo \(u^2-2u-1\). The two restrictions \(\boldsymbol h|_U,L(\boldsymbol c)|_U\) are independent on rows two and three by an exact determinant, so span \(F_4|_U\) of rank \(d_2=2\). For both \(C\boldsymbol h,A\boldsymbol h\), the coefficients in this span are fixed by rows two and three, and the fourth-row reads give two polynomials in \(x\). The replay computes their gcd as \((X-a)(X-b)\) in both front choices. This contradicts \(x\ne a,b\) and completes the ordinary off-zero aggregate exclusion.

## 5. Cancellation at fixed residual

We now know the ordinary off-zero aggregate at every clock is zero. For at most two active off-zero clocks, residual powers \(0,1,2,3\) all separate; Vandermonde gives zero aggregate at each distinct nonzero residual unless some clock \(d\) carries at least five distinct active residuals. Three active clocks are already canceled equal-residual pairs, as in Section 1.

A group with at least five distinct active residuals is the sole active off-zero clock. If there are six physical off-zero rows, at most one lies away from \(d\). The \(E_3\) restriction on these rows has rank at most three: if all share \(d\), use the scalar constant and the dimension-two pure space; otherwise \(F_3=GE_1\), giving rank at most two at \(d\) and at most one more. But the \(W_2\) active off-zero rank is two, forcing \(d_3=m-2=2\), which would require \(E_3\) restriction rank four. If there are five physical off-zero rows, all share \(d\) and \(\gamma=d=1/2\). The four pegged zeros of Section 4 and its two-by-two nodal obstruction already exclude \(m=5\), independently of the clock's ordinary aggregate. This proves the full cancellation assertion.

## Reproducibility

Run the [exact replay](check_mass.py) with Python and SymPy. It uses rational polynomials and quotient Euclid, not numerical roots or a characteristic test. The [Lean receipts](../../lean/RKCert/ReviewedNative/SDIRK8OffZeroMassReceipts.lean) check the two nodal Hankel implications, the active pair cancellation, and the three affine Gauss exclusions that also give a short independent route to the mixed-repeat three-clock obstruction. The receipts compiled on Lean/Mathlib 4.36.0 with only the standard axioms. The larger eliminations and tableau reductions are source-level, not a complete Lean nonexistence proof.
