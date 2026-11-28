# Nine live sites: both edge contact pivots are live in the half-half different-extra chart

**Scope.** Continue the [genuine dormant nine-site six-pair chart](ERK11-SIX-PAIR-DORMANT-CLOCK-SEPARATION.md).
Suppose \(h=e\), i.e. \(b=2-a,\ d=a-1,\ h=a/2\), and the two
fronts choose different free two-subsets. Their common free label
is \(t\), the left-only label is \(u\), and right-only \(v\);
the three inner slots are \(\{\zeta,u,v\}\). The dormant \(\zeta\)
is at physical 8 (or 10 by polynomial reflection). This proves
that the two linear contact solves for \(v,u\) are both live
over characteristic zero. It excludes their **entire singular
fibers**, not the regular half-half edge chart, a central dormant,
or the four-distinct charts.

## 1. Literal contact pivots and the two width projections

Use the integer inverse anchored Gram matrix \(N\), suppressing
its factor 210 in zero pairings. Let \(D_\zeta\) be the known
adjusted grade-five model evaluation at the dormant stage;
through physical 8 the actual left primitive is zero and the
dormant response is zero, so the left row is \(D_\zeta/a^5\).
Write \(D_R^{(0)},D_R^{(b)}\) for the reverse model derivative
rows at local \(0,b\). The pairings of \(D_\zeta\) with
these two rows each have the exact polynomial factor
\(a\zeta(a-\zeta)\); remove it (all three factors are live)
and call the residual cubics \(K_0,K_1\).
The actual right row 11 is a nonzero multiple of
\(r_0D_R^{(0)}+r_1D_R^{(b)}\), with
\(r_0=(t-d)(v-d),\ r_1=-(1-t)(1-v)\).
Its off-diagonal with physical 8 is
\[
 (t-d)(v-d)K_0-(1-t)(1-v)K_1=0.
\]
As a linear equation for \(v\) its coefficient is
\(\beta=(t-d)K_0+(1-t)K_1\). If \(\beta=0\), consistency
also gives \(d(t-d)K_0+(1-t)K_1=0\).
Subtract, use \(b(t-d)\ne0\), and then \(1-t\ne0\):
the singular case is exactly \(K_0=K_1=0\).

The exact resultant of these cubics in \(\zeta\), for \(b=2-a\),
has only the width factors \(a^{12}(a-2)^3\) and one degree-21
factor \(F_{21}(a)\). Their last nonconstant subresultant
is linear in \(\zeta\) with unit leading coefficient in
\(\mathbb Q[a]/(F_{21})\); its root specifies \(\zeta\)
in that coefficient ring. The replay also checks both
cubics vanish at this root and the simple clock guards
there. This is an exact fiber description, not an assumption
that the cubics have no real common root.

For the other pivot, write
\(\Gamma_0=r_0+T_4(b)r_1\) and
\(\Gamma_1=T_4(a)r_0+U_{4,4}(a,b)r_1\).
The row-7/row-11 contact is
\[
 (a-t)(a-u)\Gamma_0-tu\Gamma_1=0.
\]
Its coefficient \(\gamma=(a-t)\Gamma_0+t\Gamma_1\)
is singular only if \(\Gamma_0=\Gamma_1=0\):
use the actual \(a,t,a-t\ne0\). Since \(r_1\ne0\)
the derivative Gram determinant vanishes. In this
half-half chart its exact factorization is
\[
 U_{4,4}(a,2-a)-T_4(a)T_4(2-a)
 =-16a(a-2)F_6(a),
\]
where
\[
 F_6=2475a^6-14850a^5+34140a^4-37560a^3
            +20136a^2-4752a+352 .
\]
The coefficient replay confirms \(F_{21}\) and \(F_6\)
are coprime. More strongly, each singular fiber below
is impossible independently.

## 2. Right-contact singular: a degree-21 coefficient algebra

In \(\mathbb Q[a]/(F_{21})\) use the justified rational
\(\zeta\) above. Write \(P_3=(X-a)(X-a/2)(X-d)\).
Put \(m_j=\int X(1-X)P_3 X^j\),
\(e_j=m_{j+1}-\zeta m_j\), and
\(p_j=e_{j+1}-t e_j\), \(0\le j\le3\).
These are the moments of the actual shifted calibrated
factor with the shared free root removed. The two paid
shifted nodal rows are the two equations for the sum
and product of \(u,v\). Define
\[
 \delta=p_0p_2-p_1^2,\quad
 S_N=p_0p_3-p_1p_2,\quad
 P_N=p_1p_3-p_2^2 .
\]
If \(\delta=0\), consistency forces both other minors
zero. The exact coefficient-mod-101 test gives their
three-way gcd equal to 1; all three degrees are bounded
by two and \(\delta\)'s degree-two leading coefficient
is a unit. The finite-free lift below thus excludes that
rank dropout. Otherwise
\(u+v=S_N/\delta,\ uv=P_N/\delta\).

The full first contact is bilinear in \(u,v\), say
\(M_{00}+M_{10}u+M_{01}v+M_{11}uv\).
Its four coefficients come from the actual derivative
factors and are polynomials of degree at most two in \(t\).
Substitute the sum and product to obtain
\[
 A_0+\delta B_0 u=0,\qquad
 A_0=\delta M_{00}+S_NM_{01}+P_NM_{11},\quad
 B_0=M_{10}-M_{01}.
\]
If \(B_0=0\), \(A_0=0\); their exact coefficient-mod-101
gcd is 1, with degree bound four retained for \(A_0\).
Otherwise \(u=-A_0/(\delta B_0)\). Its quadratic relation
then yields the degree-at-most-eight necessary equation
\[
 R=A_0^2+S_N A_0B_0+P_N\delta B_0^2=0 .
\]

Here is the independent diagonal used in the second
polynomial. Use \(N\)-pairings throughout this paragraph,
including \(V_0=\langle D_\zeta,r_\zeta\rangle_N\),
\(V_1=\langle D_\zeta,r_d\rangle_N\), and
\(A_R=\langle\Phi_L,r_d\rangle_N,\ B_R=\langle\Phi_L,r_\zeta\rangle_N\).
The actual reciprocal-weight diagonal at dormant physical
8 and its opposite off-diagonal give
\[
 210b_\zeta(A_R V_0-B_R V_1)=a^5 A_R .
\]
No division by \(A_R\) or \(V_i\) occurs. With
\(\widehat H=P_3(X)(X-t)(\delta X^2-S_NX+P_N)\)
use the exact scalar Lagrange formula
\(b_\zeta=\int X(X-1)\widehat H/
 [\zeta(\zeta-1)\widehat H(\zeta)]\).
Substitute \(u\) above in \(A_R,B_R\) and clear their
common scalar \(\delta B_0\). The result is a polynomial
in \(t\) of degree at most eight. Its exact gcd with
\(R\) modulo 101 is 1, and \(R\) retains degree eight
with unit leading coefficient. This excludes every
right-contact singular fiber.

## 3. Left-contact singular: a degree-six coefficient algebra

On \(F_6\), left derivative evaluations pair to zero
with the right derivative row. Its coefficient ratio is
\(r_0=-T_4(b)r_1\). The remaining dormant off-diagonal
is \(K_1-T_4(b)K_0=0\). The residual cubic here has
the exact factors \(\zeta(\zeta-a)\) in
\((\mathbb Q[a]/F_6)[\zeta]\). Indeed before the original
\(\zeta(a-\zeta)\) was cleared, both derivatives at
\(0,a\) vanish as well because the left derivative
rows have zero pairing. The exact quotient calculation
checks these two extra factors and the surviving linear
coefficient is a unit. Since the two removed clocks
are forbidden, the actual \(\zeta\) is the single
specified linear root in the degree-six algebra.

The right ratio gives
\[
 v=\frac{d(t-d)+T_4(b)(1-t)}
          {(t-d)+T_4(b)(1-t)}
   =v_N/v_D .
\]
The denominator is live on an actual layout: if it
were zero, so would the numerator, whose difference
from it is \(b(t-d)\ne0\).
Use the scaled degree-five factor
\(P_3(X)(X-t)(v_D X-v_N)\) in the \((X-\zeta)\)
weighted moments \(j=0,1,2\), called \(q_0,q_1,q_2\).
Their degrees in \(t\) are at most two. The two
actual nodal equations require \(q_1=u q_0\),
\(q_2=u q_1\). If \(q_0=0\) all three vanish;
the exact modular gcd is 1 with \(q_0\)'s degree two
retained. Otherwise \(u=q_1/q_0\) and
\(R=q_0q_2-q_1^2=0\), of degree at most four.
The same dormant diagonal as above, now using
\[
 \widehat H=P_3(X)(X-t)(v_DX-v_N)(q_0X-q_1)
\]
and clearing the \(\Phi_L\) read by \(q_0\),
gives a polynomial of degree at most seven.
Its mod-101 gcd with \(R\) is 1, with \(R\) retaining
degree four and unit leading coefficient. Thus the
left-contact singular fiber is impossible too.

## 4. Why the modular computations close actual fibers

In both fiber families the exact base polynomial
\(F_{21}\) or \(F_6\) retains degree mod 101 and is
made monic over \(\mathbb Z_{(101)}\). All coefficients
used for the forced \(\zeta\) have unit denominators
(or are obtained from the exact linear unit pivot).
When a list of required equations in \(t\) has
modular gcd 1, one polynomial retains its actual degree
bound with unit leading coefficient, as recorded above.
Make it monic. Its quotient is finite free over the
scalar base, itself finite free over \(\mathbb Z_{(101)}\).
Modular Euclidean computations divide only by units,
so the remaining required equations generate the
unit ideal modulo 101. In a fixed basis, the linear
map combining their multiplication operators has a
maximal minor that is a unit over \(\mathbb Z_{(101)}\).
Thus it is surjective in characteristic zero as well.
An actual evaluation where every required equation
vanishes is impossible. This is a reduction of the
exact coefficient algebra, not of an unknown tableau.

Accordingly the original two contact pivots are both
live in the half-half different-extra edge-dormant
chart. The proof for physical 10 exchanges the scalar
and mixed anchored systems, using only the known
weighted transpose through grade five. Reflected
ordinary order eleven is not required.

The standalone [`replay_n12_half_edge_contact_pivots.py`](erk11-nine-site-half-different-edge-pivots/replay_n12_half_edge_contact_pivots.py)
rebuilds both exact width fibers and checks each of these
gcds and leading units with SymPy. No separate Lean
replay or regular-fiber closure is claimed here.
