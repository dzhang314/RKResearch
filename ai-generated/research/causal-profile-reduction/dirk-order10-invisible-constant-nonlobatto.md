# An invisible cubic row cannot have a non-Lobatto aggregate with constant L

**Scope.** Assume a genuine eleven-stage lower triangular tableau of full rooted order ten over a characteristic-zero field. Use the [one-clock band](dirk-order10-one-physical-dirty-clock.md) at the corrected paid grades and the [invisible constant inventory](dirk-order10-invisible-constant-three-heads.md). Assume the nonzero cubic defects \(g=Ac^2-c^3/3\) occur at one numerical clock, have one common value, and have zero individual weights. In the terminal identity
\[
 e_T=H(c)+\delta g+L(c)h,\qquad h=(A-\xi/2)g,\quad H=X-14X^2+56X^3-84X^4+42X^5,
\]
suppose \(L\) is a nonzero **constant polynomial**. Then the ordinary aggregate is Lobatto. There is no ordered-field, positivity, or real-only assumption. The affine nonshared-pole, shared-pole, and four-head Lobatto branches are outside this result.

Let \(I f(X)=\int_0^X f\), \(I^*f(X)=\int_X^1 f\), \(C=\operatorname{diag}(c)\), \(\beta=b^\top\), and \(R=CA-AC-A^2\). For an actual forward column of grade \(j\) with scalar profile \(P\) and an actual reverse marked row of grade \(i\) with profile \(Q\), the scalar reads for their pairing and their pairing through \(A\) are \(\int QP\) and \(\int QIP\). The grade costs are \(i+j\) and \(i+j+1\). This is the actual one-mark elementary calculus, not weighted transposition.

## 1. Physical stages 5 and 7 are the crossed pivots

Suppose the ordinary aggregate differs from Lobatto. The regular one-dirty inventory leaves exactly one invisible physical cubic row, eight individually active nonzero nonterminal exterior clocks, one actual origin \(o\), and the true terminal \(T\). There are either eight off-Lobatto exterior clocks or seven with one extra exterior physical clock one. The nine nonterminal exterior clocks are distinct and have \(h=-H/L\); all eight nonzero values of \(h\) are live. The cubic row is physical stage 2 (no extra zero-clock row) and has \(h=0\); it may share a clock with an exterior row. The true terminal is physical stage 11. In particular stages 3–10 are the eight nonzero nonterminal exterior clocks. No division by the origin's weight is used.

The actual reverse cubic \(G=\beta(1-C)^2 A-\beta(1-C)^3/3\) is supported on the nine nonterminal exterior coordinates and live at **every** one by the barycentric formula of the regular atlas. \(E_5^\perp=\langle G,GC\rangle\), and the annihilator of \(E_4\) with zero terminal coordinate is \(\langle G,GC,GC^2\rangle\). The latter uses rank seven and \(e_T\notin E_4\): the nine exterior restrictions of polynomials of degree at most four and \(h=-H/L\) are independent; any remaining pure \(g\) coefficient is detected at the invisible row. The G-row shifts are independent at distinct live exterior clocks.

Write \(a=c_3,b=c_4,u=c_5,y=c_6,w=c_7\). The forward kernel is
\[
 P_3=X(X-a)(X-b),\qquad V=P_3(c)-P_3(\xi)g/\gamma,\qquad \gamma=\xi^3/6.
\]
Indeed \(RV\in F_5=\langle g,h,Ch\rangle\) and the strict prefix at the invisible row and at \(a,b\) kills its coefficients. Thus \(RV=0\), and its first live read at stage 5 forces \(d_5=0\). Write \(J=IP_3\). The actual grade-four primitive \(AV\) vanishes through stage 5, so \(J/h\) is constant at \(a,b,u\). The constant is nonzero since \(J(a)=a^3(2b-a)/12\) and \(J(b)=b^3(2a-b)/12\) cannot both vanish. The previously established actual paired cut gives
\[
 u(4ab-a^2-b^2)=ab(a+b).
\]
It uses inputs of degree at most four.

Choose a nonzero reverse row \(W_3=\beta Q_3(C)+\alpha G\) with \(\deg Q_3\le3\) and \(Q_3(1)=0\), cancelling coordinates 8,9,10. The row space has dimension four by profile separation; \(Q_3\ne0\) since the three killed coordinates are G-live. The row \(W_3R\) is paid on \(E_4\) (3+2+4), is terminal-out, and has those same three zeros by triangularity. In \(\langle G,GC,GC^2\rangle\) these three distinct live reads force \(W_3R=0\). The crossed cubic pivots cannot cross or be adjacent. Thus \(W_3\) is live at stage 7 and \(d_7=0\). The [three-stage overlap](dirk-order10-three-stage-overlap.md) gives \(d:=d_6\ne0,\ a_{65}\ne0,\ a_{76}\ne0\). The rank argument allows the extra exterior clock one at 7 or 8; \(w=1\) is treated by a separate finite guard.

## 2. The lifted forward quartic gives a cubic stage equation

Set \(s=a+b,\ p=ab,\ t=s/u\). This parameter \(t\) is not the terminal stage. The paired cubic gives \(p=u^2t^2/(6-t)\), so \(u,t,6-t\ne0\). Also \(3-2t\ne0\): at \(t=3/2\) the roots of \(X^2-sX+p\) would be \(u,u/2\), contrary to distinct \(a,b,u\). Set \(D=(X-u)P_3\). Since \(h=-H/L\) and \(J/h\) is constant through stage 5, \(H=eJ+(r+42X)D\), with \(e\ne0\). The first two coefficients give
\[
 r=-1/(up),\qquad e=2[-14-r(p+us)]/p.
\]
On the exterior \(AV=J-H/e=-(r+42X)D/e\). The next two polynomial coefficients give the early equations in §4.

The literal overlap equation at stage 6 is \(a_{65}(y-u-d)V_5=d^2V_6\), so \((AV)_6=a_{65}(y-u)V_5/d\ne0\). Also \(V_6=P_3(y)\ne0\). Define
\[
 k=1-(y-u)/d,\quad V_4=(C-u)V+kAV,\quad P_4=D+kJ.
\]
This column is zero through stage 6, and \(k\ne0,1\). On the exterior \(V_4=D[1-k(r+42X)/e]\), so \(y=(e/k-r)/42\) and \(V_4\) is live at stage 7. The exterior polynomial for \(AV_4\) has degree at most six, since \(AV_4\in E_5\). It vanishes through stage 7 by \(d_7=0\) and therefore is a scalar \(\sigma\) times \((X-w)V_4\) there. The latter is a polynomial identity on the exterior: the nine distinct exterior clocks separate degrees through six. Its scalar primitive \(I P_4\) differs from the actual exterior polynomial by a multiple of \(H\), since \(F_5\) on the exterior is \(\langle h,Ch\rangle\). Hence
\[
 I P_4-\sigma(X-w)P_4=\lambda H .
\]
Here the expression has degree at most five. If \(\sigma=0\), double vanishing of \(I P_4\) at zero and the simple root of \(H\) imply \(P_4=0\), impossible by its linear coefficient \(-up\).

Exact coefficient expansion gives
\[
 IJ=B XD+N J+E XJ,\qquad
 B=\frac{t}{10(3-2t)},\quad N=\frac{s}{5(3-2t)},\quad E=\frac{3-4t}{5(3-2t)} .
\]
The basis \(D,XD,J,XJ\) is independent: the \(X\) coefficient kills the constant coefficient of \(D\); evaluating at \(a,b\) then kills the two \(J\) terms using their nonzero \(J\) values, leaving \(XD\). Since \(ID=(X-u)J-IJ\), comparison gives
\[
 \lambda r=\sigma w,\quad 42\lambda=(k-1)B-\sigma,\quad
 \lambda e=-u+(k-1)N+\sigma wk,\quad \sigma k=1+(k-1)E .
\]
Set
\[
\begin{gathered}
 S_k=1+(k-1)E,\quad L_k=k(k-1)B-S_k,\quad
 w_N=rL_k,\quad w_D=42S_k,\quad y_N=e-rk,\quad y_D=42k,\\
 d_N=y_N-u y_D,\quad d_D=y_D(1-k).
\end{gathered}
\]
Then \(w=w_N/w_D,\ y=y_N/y_D,\ d=d_N/d_D\), and
\[
 \mathcal F(k)=y_D[-u+(k-1)N]+(rk-e)L_k=0.
\]
Its leading coefficient is the nonzero \(rB\).

## 3. The lifted reverse quartic fails a finite scalar rank test

The front-equation test in §4 first excludes \(w=1\). The reverse overlap gives \(a_{76}(w-y-d)(W_3)_7=d^2(W_3)_6\) and \((W_3A)_6=a_{76}(w-y)(W_3)_7/d\ne0\). Therefore
\[
 k'=(w-y)/d-1,\quad W_4=W_3(C-w)+k'W_3 A
\]
is zero strictly after physical stage 5, using \(d_7=0\) also at coordinate 7. Its scalar profile is \(Q_4=(X-w)Q_3+k'I^*Q_3\), with \(Q_4(1)=0\). This profile is nonzero: if zero, differentiation gives \((X-w)Q'_3+(1-k')Q_3=0\). In the powers of \(X-w\) a nonzero polynomial solution is a single monomial times a scalar in characteristic zero, which cannot vanish at \(1\) since \(w\ne1\). The primitive \(W_3 A\) uses the true grade-four reflected integration-by-parts identity; its difference from \(\beta I^*Q_3(C)\) lies in \(E_5^\perp\).

Take any polynomial \(P\) of degree at most four, \(P(0)=0\), such that \(P(a)/h_a=P(b)/h_b\). Subtract the common multiple of \(h\) and then a multiple of \(g\) correcting the invisible row. This grade-four column is zero through stage 4 and can meet \(W_4\) only at stage 5, where \(d_5=0\). Thus the two paid functionals
\[
 P\longmapsto\int Q_4 IP,\qquad P\longmapsto\int Q_4(X-u)P
\]
are multiples of \(P\mapsto P(a)/h_a-P(b)/h_b\). The first multiple is nonzero: otherwise the four moments at degrees 2–5 would vanish, contrary to \(Q_4\ne0\) and the nonsingular shifted Beta form on \((1-X)\mathbb K[X]_{\le3}\). Nonsingularity over the rationals follows from the positive real integral of the square with weight \(X^2(1-X)\), so this uses no ordering of the tableau field.

Normalize the nonzero scale of \(Q_4\) so \(m_{j+1}:=\int X^{j+1}Q_4=(j+1)f_j\) for \(1\le j\le4\), where
\[
 (f_1,f_2,f_3,f_4)=((s^2-3p)/p^2,\ s/p,\ 3,\ 2s).
\]
To see the normalization, \(a^j/J(a)-b^j/J(b)\) is that \(f_j\) times the same factor \(-12(a-b)/[(a-2b)(2a-b)]\) for all four \(j\), and \(h/J\) is a common nonzero constant here. For the second functional the multiplier is \(R_0=3-2u f_1/f_2\) by \(P=X^2\), with \(f_2\ne0\). Its \(P=X\) read gives \(m_1=(2-R_0)f_1/u\). Thus the coefficients \(q\) of \(Q_4\) in \((1-X)X^j\), \(j=0,\ldots,3\), are the following Beta inverse applied to \(((2-R_0)f_1/u,2f_1,3f_2,12)\):
\[
 \begin{pmatrix}300&-2100&4200&-2520\\-2100&16800&-36120&22680\\
 4200&-36120&81480&-52920\\-2520&22680&-52920&35280\end{pmatrix}.
\]
Membership of \(Q_4\) in the image of \(Q\mapsto(X-w)Q+k'I^*Q\) on anchored cubics requires the determinant of its three columns followed by \(q\) to vanish; this is unchanged by the normalization. Write
\[
 T_{12}=\begin{pmatrix}6&2&1\\-6&2&1\\0&-4&1\\0&0&-3\end{pmatrix},\qquad
 D_0=w_Dy_Dd_N,\quad V_0=w_Ny_Dd_N,\quad K_0=(w_Ny_D-y_Nw_D)d_D-D_0 .
\]
Here \(T_{12}\) is \(12I^*\) on the displayed anchored bases. The first three determinant columns, scaled by \(12D_0\), have entries
\[
 12D_0[i=j+1]-12V_0[i=j]+K_0(T_{12})_{ij}\qquad(0\le i\le3,\ 0\le j\le2).
\]
This is not a duplicate of the paired cubic or of the forward quartic: the cleared determinant is a unit modulo \(\mathcal F\) at both exact residue primes.

## 4. Exact certificate and characteristic-zero transport

The two early equations from coefficients three and four have numerators
\[
\begin{aligned}
F_0={}&756t^3u^4+168t^3u^2+28t^3u+3t^3-1008t^2u^2-336t^2u-45t^2+1008tu+216t-324,\\
F_1={}&42t^4u^4+42t^3u^4-84t^3u^3-7t^2u-t^2+42tu+9t-18,
\end{aligned}
\]
with denominators \(3t^2u^2(t-6)\) and \(t^3u^3\). Their resultant in \(u\) is \(1037232t^{13}(t-6)^4(t-3)\Pi(t)\), with
\[
 \Pi=243t^{10}-2511t^9+20839t^8-201939t^7+1127457t^6-3341909t^5+
 4387533t^4-240993t^3-3165372t^2+698544t+1333584 .
\]
At \(t=3\) their rational gcd in \(u\) is a nonzero multiple of \(u\), inadmissible, so \(\Pi(t)=0\).

In each coefficient algebra \(\mathbf F_\ell[t]/(\Pi)\) for \(\ell=419,719\), independent modular replays verify:
1. The early equations in \(u\) have a polynomial combination \(u-U\), and both vanish at \(U\). The elements \(U,t,6-t,3-2t\) and all scalar denominators used above are units.
2. After substituting \(u=U\), \(\mathcal F\) has degree three with unit leading coefficient. The product \(k(k-1)w_D d_N(w_N-w_D)(w_Ny_D-y_Nw_D)\) is a unit modulo \(\mathcal F\), in particular rejecting \(w=1\) before using the reverse rank test.
3. The cleared determinant is also a unit modulo \(\mathcal F\), contradicting its necessary vanishing.

For transport, \(t,u,k\) are algebraic successively by the resultant, the nonzero \(u\)-leading term \(756t^3\), and the cubic. Work only in their number field. At a prime over either residue characteristic, \(t\) is integral because the leading coefficient of \(\Pi\) is a unit. The checked unit \(t\) makes \(756t^3\) a unit so \(u\) is integral. The first check makes the cubic's denominators and leading coefficient units, so \(k\) is integral. Now the second check makes the defining rational geometry regular, and the third makes the determinant nonzero after reduction. Thus it cannot vanish in characteristic zero. We never reduce tableau entries, mark coefficients, or unknown clocks outside this number field. The modular test is in a quotient algebra, so no enumeration just over base-field roots is assumed.

## Verification boundary

The [independent Python checker](check-dirk10-invisible-constant-nonlobatto.py) recomputes rational coefficient identities, resultant, Beta inverse and modular checks. The large quotient computations are independently replayed in the exact source checker, not assumed to be kernel-checked. The [field module](../../lean/RKCert/ReviewedNative/DIRKOrderTenInvisibleConstantRegularField.lean) proves the two literal middle cancellations and the front cubic clearance by standard kernel-checked field algebra. The actual-tableau graded and characteristic-zero bridges above are mathematical, not a full native HasOrder adapter. The unrestricted DIRK10 stage interval stays 11–12.
