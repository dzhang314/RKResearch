# Opposite halves with different free labels: a finite nine-site ERK11 atlas

**Scope.** Continue the [genuine nine-site six-pair chart](ERK11-SIX-PAIR-DORMANT-CLOCK-SEPARATION.md).
The four calibrations \(a,h=a/2,d=1-b,e=1-b/2\) are distinct and
nonendpoint. The left extras are \(\{e,t\}\) and the right extras
are \(\{h,s\}\), with \(t\ne s\). Thus the two crossing pairs
are \(h,e\), and the inner active clocks are \(t,s\), in either
physical order, together with one genuinely new dormant clock \(z\).
The result is a finite set of algebraic clock tuples for **each**
dormant position \(8,9,10\) and each active order, over
characteristic zero given the inherited actual chart and mixed
payment. It is not an exclusion of those finite fibers. The
ordered step securing genuine nine-site separation in one
alias case is still separate.

## 1. A paid crossover including the dormant site

Write
\[
 P_4(X)=(X-a)(X-h)(X-d)(X-e),\qquad H_6(X)=P_4(X)(X-t)(X-s),
 \qquad g(w)=w(1-w)(a-w)(w-d).
\]
At either crossing \(w=h,e\), the forward and reflected observed
responses are \(w^2(a-w)/a\) and \((1-w)^2(w-d)/b\) respectively
in their natural scales. There is no triple or dormant occurrence at
either crossing. The [cross-pair response calculation](ERK11-MIXED-OVERLAP-TWO-CROSS-EXIT.md),
using \(\mu_w=\kappa/H'_6(w)\), the zero first-response pool and
the constant scale between the two response directions, therefore
makes
\[
 B_w H'_6(w)\,\frac{w^2(1-w)^2(a-w)(w-d)}{ab}
\]
the same at \(w=h,e\). It uses the two literal visits to each
crossing and the live pair pools from the [six-pair law](ERK11-SIX-PAIR-SITE-MASK.md),
not any scalar approximation using only eight sites.

The true nine-site scalar Lagrange numerator for either active
\(w\) is \(X(X-1)(X-z)H_6(X)/(X-w)\), of degree eight.
Set \(q_0=\int_0^1 X(1-X)H_6(X)\,dX\) and use the formal
divided difference
\[
 {\cal J}_6(w)=\int_0^1 X(X-1)
                  \frac{H_6(X)-H_6(w)}{X-w}\,dX .
\]
By the difference identity for \((X-z)H_6(X)\), Lagrange payment gives
\[
 B_w H'_6(w)
   =\frac{(w-z){\cal J}_6(w)-q_0}{w(w-1)(w-z)}.
\]
Indeed the extra term in the divided difference is \(H_6(X)\);
its integral against \(X(X-1)\) is \(-q_0\).
All displayed site denominators are live. Hence the following
quantity is identical at the two true crossing sites:
\[
 g(w)\left({\cal J}_6(w)-\frac{q_0}{w-z}\right).
\]
Only the already-paid degree-eight scalar Lagrange test is
added to the inherited crossover response law. In particular
this does not assume that \(H_6\) alone supports scalar quadrature.

## 2. Shifted moments and the nonvertical crossover

Let \(m_j=\int_0^1 X(1-X)P_4(X)X^j\,dX\) for \(0\le j\le4\).
These tests have degrees at most ten. Their localization onto
\(z,t,s\) has three live modified weights: the dormant one
is its physical nonzero \(b_i\), and \(B_tB_s\ne0\) by the
ordinary-pair law. Thus \(\Omega=\det(m_{i+j})_{0\le i,j\le2}\)
is their product times the squared Vandermonde and is live.
This assertion does not need positive weights.

For \(E_j=m_{j+1}-z m_j\), \(0\le j\le3\), put
\[
 \Delta=E_0E_2-E_1^2,\qquad
 \Sigma=E_0E_3-E_1E_2,\qquad
 \Pi=E_1E_3-E_2^2 .
\]
The two remaining shifted weights at \(t,s\) are live;
\(\Delta=w_tw_s(t-s)^2\ne0\). Actual shifted nodal
equations give \(\Delta(t+s)=\Sigma\) and \(\Delta ts=\Pi\).
In particular the polynomial
\(F_2(X)=\Delta X^2-\Sigma X+\Pi\)
has the actual remaining roots, so its discriminant and
its values at \(0,1,a,h,d,e,z\) are nonzero.
The companion algebra of the [same-free chart](ERK11-NINE-SITE-DISTINCT-SAME-FREE-EXIT.md)
shows \(m_0\Pi-m_1\Sigma+m_2\Delta=\Omega\).

Let \(\widehat H=P_4 F_2\), and define \(\widehat{\cal J}\) using
\(\widehat H\) in the preceding divided difference. At an
actual tuple \(\widehat H=\Delta H_6\); its ordinary modified
mean is exactly \(\Omega\), as a polynomial before specialization.
The cleared crossover equation is \(X_c(a,b,z)=0\), where
\[
 X_c=\frac{
 g(h)[(h-z)\widehat{\cal J}(h)-\Omega](e-z)
 -g(e)[(e-z)\widehat{\cal J}(e)-\Omega](h-z)}
 {h-e}.
\]
The rational polynomial division by \(h-e\) is exact:
on \(h=e\) the two summands agree coefficientwise. The
actual denominator is live by the four-distinct hypothesis.
Each \(\Delta,\Sigma,\Pi\) is at most quadratic in \(z\),
so \(X_c\) is at most quartic. Crucially at any actual widths
it is **not an identically zero polynomial in \(z\)**:
at the algebraic test value \(z=h\), even though a physical
dormant collision is forbidden,
\[
                          X_c(a,b,h)=g(h)\Omega\ne0.
\]
Here \(g(h)\ne0\) from the end and calibration exclusions.
Thus a retained width pair has at most four dormant clocks,
regardless of any later contact rank loss.

## 3. Two actual clock equations, with no choice of slope pivot

The first inverse-Gram contact of physical axes 7 and 11 tests
\[
 \begin{gathered}
 L_0=(a-e)(a-t),\quad L_1=-et,\quad
 R_0=(h-d)(s-d),\quad R_1=-(1-h)(1-s),\\
 F=L_0R_0+T_4(a)L_1R_0+T_4(b)L_0R_1+U_{4,4}(a,b)L_1R_1=0 .
 \end{gathered}
\]
These are the derivative-front rows with their live actual
prefactors removed, as in the [two-half crossing contact](ERK11-FOUR-DISTINCT-TWO-HALF-CROSS-EXIT.md).
The prefactors use the two genuinely new extras and the
literal distinct end/front labels, not the number of scalar
clock sites. The coefficient arrays for \(T_4,U_{4,4}\) are
included in the replay.

For the second equation let the model square-clock vectors be
\(V_a=X^2(X-a)^2,\ V_b=(1-X)^2(X-d)^2\) and their primitives
\(P=JV_a,\ Q=\bar J V_b\). Write the interval integrals
\[
 H=\int PV_b=\int V_aQ,\quad C_1=\int XPV_b,\quad
 C_2=\int XV_aQ,\quad J_0=\int PQ,\qquad I_j=\int X^jV_aV_b.
\]
The actual \(V_L,V_R\) are zero through physical 7 and from
physical 11 respectively, and their actual \(A\) and weighted
transpose primitives are zero through 8 and from 10.
If \(u=c_8,v=c_{10}\), the four products
\[
 (C-u)V_L\cdot (C-v)V_R,\qquad
 (AV_L)\cdot(C-v)V_R,\qquad
 (C-u)V_L\cdot(A^\star V_R),\qquad
 (AV_L)\cdot(A^\star V_R)
\]
all isolate physical 9. Each has total grade ten; the clock
factors in the first product kill the actual rows 8 and 10.
The paired scalar values are respectively
\(I_2-(u+v)I_1+uvI_0,\ C_1-vH,\ C_2-uH,\ J_0\).
Multiplying the two middle values and comparing with the
product of the first and last gives the true bilinear
\[
 B(u,v)=A_0uv+B_0u+C_0v+D_0=0,\qquad
 \begin{cases}
 A_0=H^2-J_0I_0,\\
 B_0=J_0I_1-HC_1,\\
 C_0=J_0I_1-HC_2,\\
 D_0=C_1C_2-J_0I_2.
 \end{cases}
\]
This argument does not divide by an individual grade-five
amplitude or a model square read. For dormant physical 9 use
\((u,v)=(t,s)\) or \((s,t)\). For dormant physical 8 use
\((u,v)=(z,s)\) or \((z,t)\). Reflection of the actual paired
model slots maps dormant physical 10 to 8, exchanges \(a,b\)
and sends the left/right selected free labels to \(1-s,1-t\).
The geometry is unchanged; no ordinary reverse order eleven
or reversed square beyond the mixed ledger is invoked.

Treat each of \(F\) and the appropriate \(B\) as a bilinear
\(\sum_{i,j\le1} f_{ij}t^is^j\), allowing zero coefficients.
Put \(Y=\Delta t\), so \(Y^2-\Sigma Y+\Delta\Pi=0\).
At any true root, the cleared bilinear becomes \(U Y+V=0\), with
\[
 U=f_{10}-f_{01},\qquad
 V=\Delta f_{00}+\Sigma f_{01}+\Pi f_{11}.
\]
Their necessary compatibility and individual norm equations are
\[
 D_c=U_F V_B-U_B V_F=0,\qquad
 N_F=V_F^2+\Sigma U_FV_F+\Delta\Pi U_F^2=0,\qquad
 N_B=V_B^2+\Sigma U_BV_B+\Delta\Pi U_B^2=0 .
\]
For example each norm is the product of the evaluations at
\(Y,\Sigma-Y\), since \(Y(\Sigma-Y)=\Delta\Pi\).
No step divides by \(U_F,U_B\), \(H\), \(J_0\), or a derivative
contact determinant. Simultaneous zero slopes are covered.

## 4. Exact projection and finite clock fibers

The standalone rational replay forms all four combinations
of central/edge and the active order. It takes exact gcds
against guards and removes only their divisors: the nonzero
calibration differences, \(z\)'s distinctness, \(\Omega\),
\(\Delta\), the free discriminant and the seven forbidden
evaluations of \(F_2\) listed above. It then takes the three
resultants in \(z\) of \(X_c\) against \(D_c,N_F,N_B\).
The only subsequent removals divide **width-only** live
guards, including \(\Omega\). The raw and reduced bidegrees
\((\deg_b,\deg_a)\) are:
\[
\begin{array}{c|ccc|ccc}
 &\multicolumn{3}{c|}{\text{raw}}&\multicolumn{3}{c}{\text{reduced}}\\
 &D_c&N_F&N_B&D_c&N_F&N_B\\ \hline
 9,\ \text{both orders}&(62,62)&(92,92)&(92,92)&(50,50)&(68,68)&(68,68)\\
 8,\ \text{both orders}&(69,69)&(92,92)&(76,76)&(57,55)&(68,68)&(64,60)
\end{array}
\]
In each of the four orientation calculations the reduced
\(D_c\) and \(N_F\) projections are relatively prime in
\(\mathbf Q[a,b]\), as are \(D_c\) and \(N_B\).
All rational operations are exact. A genuine finite \(z\)
root makes the univariate Sylvester resultant vanish even
on specialized degree drops. The first gcd already shows
that the possible width pairs are a finite algebraic set:
two plane polynomials with no common component have only
finitely many common points. This reasoning is unchanged by
extension of the characteristic-zero base field.

At such a width pair the crossed polynomial \(X_c\) is
not zero identically by Section 2; then \(F_2\) is a true
quadratic by the proved-live \(\Delta\). It follows that at
most four dormant values and at most two assignments of
\(t,s\) survive over any retained width pair. This does not
say that every such tuple is achievable, nor eliminate the
remaining exact finite fibers. The exact replay is separate
from the Lean companion, which checks the ring-level
compatibility, norm, and nonvertical evaluation arithmetic.
