# Rational cubic-defect reduction for the all-active half-diagonal endpoint pair

Use the [remaining half-diagonal chart](../sdirk-eight-half-equal/README.md) of a proposed ten-stage strict SDIRK tableau \(A,\boldsymbol b\) of order at least eight over a characteristic-zero field: all weights are nonzero, the only nonzero-residual rows are the endpoints, \(c_1=c_{10}=\gamma=1/2\), \(g_1=g_{10}=1/8\), and \(b_1=-b_{10}\). Write \(U\) for the other eight physical rows, \(N=A-\gamma I\), \(\boldsymbol g=A\boldsymbol c-\boldsymbol c^{\odot2}/2\), and \(\boldsymbol h=N\boldsymbol g\).

**Result.** The necessary relation \(q(c_i)h_i=p(c_i)\) on \(U\), with \(\deg q\le2\) and \(p\in\operatorname{span}(L_3,L_4,L_5)\) for shifted Legendre polynomials, yields a small linear reconstruction of the ordinary nodal polynomial in the coprime chart. Three concrete subcharts are excluded:

* \(q\) constant (a polynomial profile);
* \(q=X-1/2\) with \(p(1/2)\ne0\);
* coprime \(q=(X-1/2)^2+d\) and \(p\) proportional to \(L_4\) (even rational profile).

The general coprime linear-denominator chart has only finitely many possible poles in each front/rear phase. In the quadratic chart, the corners reduce the generic case to two denominator coefficients, or to finitely many denominator choices when the corner matrix loses rank. Common factors and other quadratic profiles remain **unresolved**. The unrestricted strict SDIRK8 interval stays **10–11**.

## 1. Literal endpoint reads and the nodal reduction

Let \(I(X^j)=1/(j+1)\) and let \(\ell(f)=\sum_{i\in U}b_i f(c_i)\) for a scalar function on the zero rows, with \(\ell(hf)=\sum_{i\in U}b_i h_i f(c_i)\) and likewise for \(h^2\). The endpoint weights cancel on ordinary polynomials. Also \(\boldsymbol h\) vanishes at both endpoints: it belongs to \(E_5\), on which the endpoints agree by the weighted pure line \(\boldsymbol b^{\mathsf T}\operatorname{diag}(\boldsymbol g)\). Thus
\[
 \ell(X^j)=I(X^j)\ (0\le j\le7),\qquad
 \ell(h X^j)=0\ (0\le j\le4),\qquad
 \ell(h^2 X^j)=0\ (0\le j\le1).
\]
The last two statements use the genuine pure grades three and six. The normalized reverse cubic defect \(\boldsymbol h^*\) is a nonzero multiple of \(\boldsymbol h\) on \(U\) because both are pure grade three under all-active weighted duality and both vanish on the off-zero endpoints.

The four pegged zero clocks are front \(a,b\), actual rear \(c,d\). With \(t^2=1/2\) and \(u=1+2t\), the two front clocks and their forward \(h\) values are
\[
 a=(1+u)/2,\quad b=(1+w)/2,\quad h_a=u/16,\quad h_b=(w-r)/16,
 \qquad (w,r)=(2-u,0)\ \hbox{or}\ (2u,3u/2-1).
\]
The rear ones reflect an independent such pair; write \(k,l\) for the normalized reverse \(h\) values at \(c,d\). These clocks are distinct, all four \(h\) values are nonzero, and \(h,L_4\) have unequal ratios at each front or rear pair, as shown in the [endpoint replay](../sdirk-eight-half-equal/check_endpoints_and_low_mass.py).

Whenever \(h_i=H(c_i)\) is a single scalar value at each zero clock (for a polynomial or a coprime rational profile), the ordinary quadrature has **seven or eight active distinct sites**. With at most five sites, its first five \(h\) moments would give \(H=0\) on all those sites; the four nonzero corner values would need four canceled clock groups of at least two physical rows each, leaving no ordinary sites. With six sites, at least one complete front or rear pair is present: one missing corner needs at least two active physical rows beyond the six ordinary sites. On six sites the exact degree-three scalar Gram is nonsingular, with nondegenerate two-dimensional weighted orthogonal complement. The nonzero isotropic \(H\) and the column \(L_4\) both lie in this complement, and they are mutually orthogonal by the paid \(h\) moments. They must then be proportional, contrary to the ratios at the complete corner pair. With seven or eight sites no canceled zero-clock group can fit among eight physical zero rows, so all four corners belong to the quadrature.

Let \(P_4(X)=(X-a)(X-b)(X-c)(X-d)\) and factor the monic ordinary nodal polynomial as \(D=P_4Q\), \(\deg Q=n-4=3\) or \(4\). If the weighted moments \(\ell(f/q^2)\) are known through \(\deg f\le11\), then
\[
                         \ell(P_4 Q X^j/q^2)=0,\qquad 0\le j<n-4              \tag{1}
\]
determines \(Q\) uniquely. Its coefficient matrix \([\ell(P_4X^{i+j}/q^2)]_{i,j=0}^{n-5}\) is the Vandermonde congruence of the diagonal weights \(b_{\rm agg}P_4(c_i)/q(c_i)^2\) at the \(n-4\) noncorner sites. These weights are nonzero, so the matrix is invertible even over a nonordered field. The \(j=3\) equation is an additional test when \(n=7\). The same argument works without a denominator.

The literal fourth row is a zero at clock \(s\). Its three strict taps solve
\[
 \begin{pmatrix}1&1&1\\\gamma&a&b\\\gamma^2-(2/3)g_1&a^2&b^2\end{pmatrix}
 \begin{pmatrix}v_1\\v_2\\v_3\end{pmatrix}
 =\begin{pmatrix}s-\gamma\\s^2/2-\gamma s\\s^3/3-\gamma s^2\end{pmatrix},
 \qquad H_{\rm tap}(s)=g_1v_1 .
\]
These are its actual three low graded reads, with the pure relation
\(A\boldsymbol c^{\odot2}-\boldsymbol c^{\odot3}/3=(2/3)(\boldsymbol g+\boldsymbol h)\).
The matrix is invertible in both phases. For \(s=a,b\) it would make a literal twin, so the scalar gate \(q(s)H_{\rm tap}(s)-p(s)=0\) must hold either at one of the two rear sites or at a root of \(Q\).

## 2. Reusable square-denominator moment identity

Suppose \(q\) is monic quadratic and \(\gcd(p,q)=1\). Then \(q(c_i)\ne0\) at every physical zero clock. Define a linear functional \(\Lambda\) on polynomials of degree below four by
\[
 \mathcal T(f)=I\!\left(\operatorname{quo}_{q^2}f\right)
                  +\Lambda\!\left(\operatorname{rem}_{q^2}f\right),
 \qquad \mathcal T(qp)=\mathcal T(Xqp)=\mathcal T(p^2)=\mathcal T(Xp^2)=0 .
\]
The four remainders from these conditions form a basis: if \(q^2\) divides \(r p^2+q s p\) with \(\deg r,\deg s<2\), reduction modulo \(q\) and coprimality force \(r=0\), then canceling \(q\) forces \(s=0\). See the [Lean residue receipt](../../lean/RKCert/ReviewedNative/SDIRK8SquaredDenominatorReceipts.lean) for the guarded polynomial proof. The actual functional \(f\mapsto\ell(f/q^2)\) agrees with \(\mathcal T\) through degree eleven, because the polynomial quotient has degree at most seven and the four pure moment statements hold at actual sites. Thus (1) is an explicit linear nodal reconstruction, without solving for individual weights or splitting \(q\). Repeated roots of \(q\) cause no difficulty.

For a coprime linear \(q=X-\xi\), necessarily \(\deg p=5\). Otherwise the paid \(\ell(pX^3)=0\) and ordinary degree at most seven force \(p\propto L_4\), incompatible with the front/rear pole relation in the [half-diagonal proof](../sdirk-eight-half-equal/README.md). Write \(p=q S_4+r\), \(r=p(\xi)\ne0\), so \(h=S_4(c)+r/q(c)\). Then:
1. \(\ell(h)=0\) fixes \(\ell(1/q)=-I(S_4)/r\).
2. \(\ell(pX^3)=0\) fixes ordinary moment eight using the leading coefficient of \(p\).
3. \(\ell(h^2)=0\) fixes \(\ell(1/q^2)\), after division of \(S_4\) by \(q\) and use of moment eight.
4. \(\ell(Xh^2)=0\) fixes ordinary moment nine from \(X S_4^2\); in the remainder use \(X/q^2=1/q+\xi/q^2\).

These two additional ordinary moments and two residue values give the same reconstruction (1) through degree eleven. For constant \(q\), scale to one. The same pole incompatibility rules out \(\deg p\le4\), and for degree five the four paid moments of \(p X^3,p X^4,p^2,Xp^2\) successively determine ordinary moments eight through eleven. This is the denominator-free version.

## 3. Corner ranks and exact excluded charts

Let \(V(y)=(L_3(y),L_4(y),L_5(y))\) in any fixed degree normalizations. The coefficient vector of \(p\) solves
\[
 p(a)=h_a q(a),\quad p(b)=h_b q(b),\quad l q(d)p(c)-k q(c)p(d)=0 .
\]
The first two equations already have rank two using the \(L_3,L_4\) columns. Let \(p_0\) be the particular solution using those columns, and \(p_\perp\) a nonzero null polynomial. Its values at \(c,d\) are nonzero in all phases. The coefficient of \(p_\perp\) in the last equation is
\(\Delta=l q(d)p_\perp(c)-k q(c)p_\perp(d)\).
For \(q=X-\xi\), \(\Delta\) is affine with nonzero slope, and its singular value is inconsistent with the last equation on \(p_0\). For \(q=X^2+\alpha X+\beta\), \(\Delta\) is affine with nonzero coefficient of \(\beta\); substitution of its singular line into the last equation on \(p_0\) leaves a nonzero quadratic in \(\alpha\). The [exact corner check](check_corner_degeneracies.py) verifies these facts. In particular the generic quadratic profile is rational in two denominator coefficients, and the singular phases have at most two denominator choices (the numerator need not be fixed there).

All the scripts use \(t^2=1/2\). Fix the front sign and check both rear signs, which is exhaustive by conjugation:

* **Polynomial profile.** The [eight exact phase checks](check_polynomial.py) fix \(p\) from the corner system and reconstruct the nodal cubic or quartic using ordinary moments eight through eleven. The literal \(H_{\rm tap}-p\) is nonzero at both rear sites and coprime to both residual factors.
* **Coprime central simple pole.** The [linear replay](check_linear.py) takes \(\xi=1/2\). Three phases have \(p(\xi)=0\), so are not in this coprime chart. In the other phases the two extra ordinary moments and two residue evaluations reconstruct the nodal factor; the same fourth-row coprimeness and rear checks exclude it.
* **Even quadratic profile.** The front \(h,L_4\) determinant fixes \(d\) and the scale of \(p\) for \(q=(X-1/2)^2+d\), \(p\propto L_4\). The [even replay](check_even_quadratic.py) tests this coprimality, filters by the rear ratio, then reconstructs \(Q\) and verifies that the fourth-row gate misses all candidate sites. In particular an even rational \(h\) on a reflected set of **eight distinct** zero clocks is impossible in the coprime quadratic chart: cross-multiplication of the two rational profiles has degree at most seven and eight roots, so is an identity. Coprimality and monicity force \(q\) even about \(1/2\), and the even numerator in the shifted Legendre span is proportional to \(L_4\).

The additional nodal condition with \(j=3\) in (1) is nonzero in every tested seven-site subchart, but the fourth-row checks cover both seven and eight sites independently.

## 4. General coprime simple poles: a finite chart

For \(q=X-\xi\), the corner system fixes \(p\) rationally in \(\xi\); the unique singular corner value is excluded. The moment reconstruction then fixes \(Q\) rationally in \(\xi\) wherever an actual tableau can exist, since its moment matrix necessarily has nonzero determinant. The fourth-row gate must vanish at one of the rear clocks or have a common root with \(Q\). Its two rear evaluations and its resultant with \(Q\) are rational functions of \(\xi\), none identically zero: the same exact linear replay tests all of them at the common rational benchmark \(\xi=1/3\), including every denominator, the gate's degree-five leading coefficient, and coprimeness with each monic \(Q\). The leading-degree tests ensure the resultant identity specializes without degree drop. Thus only finitely many \(\xi\) can occur, although their exact exclusions outside the central subchart are not proved here.

## Verification and scope

Run each Python check file in this directory with Python 3 and SymPy. All calculations use rational quotient arithmetic in \(\mathbb Q[t]/(t^2-1/2)\), exact polynomial gcds, and verified units; no root search or network access is used. The Lean receipt proves the reusable polynomial kernel step, not the entire Runge–Kutta argument. Coprimality is essential when evaluating \(p/q\) at actual clocks. A common factor may vanish at a real physical clock where the original relation does not determine \(h\); that possibility is not removed by symbolic cancellation. Repeated roots of a denominator coprime to \(p\) are allowed in the square-denominator identity.
