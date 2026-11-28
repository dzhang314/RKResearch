# Nine live sites: central two-clock product and the half–half rank-one exit

**Scope.** In the [genuine nine-site six-pair chart](ERK11-SIX-PAIR-DORMANT-CLOCK-SEPARATION.md),
put the dormant stage at physical 9, with clock \(\zeta\).
The generalized product below holds for either equal or distinct
inner clocks \(x=c_8\), \(y=c_{10}\) with the inherited mixed
payments. For **half–half overlap with different extra sets**,
we then exclude both singular orientations of this product over
any characteristic-zero field, **given genuine nine-site
separation** and the inherited actual anchored mixed Gram.
This is a determinant-zero exit only. It does not exclude the
regular determinant-live layout, other overlap types, or ordinary
17-stage ERK11.

## 1. Paid product: physical orientation matters

Write \(V_a=X^2(X-a)^2\), \(V_b=(1-X)^2(X-d)^2\),
\(P=JV_a=\int_0^X V_a\), \(Q=\bar J V_b=\int_X^1 V_b\),
and \(W=V_aV_b\). Here \(a\) is the left width, \(d=1-b\)
is the right plateau in the physical clock coordinate, and all
integrals without limits are over \([0,1]\). The actual vectors
\(V_L,V_R\) have respective grade-four models \(V_a,V_b\).
They vanish through rows 1–7 and 11–17 respectively. Thus
\(A V_L\) vanishes through row 8 and
\(A^\star V_R\) from row 10 onward. The actual dormant row
reads \(V_L,V_R\) as \(V_a(\zeta),V_b(\zeta)\). Use
\[
 \begin{gathered}
 H=\int P V_b=\int V_aQ,\quad C_1=\int X P V_b,
 \quad C_2=\int XV_aQ,\quad J_0=\int PQ,\quad I_j=\int X^jW,\\
 I_{xy}=I_2-(x+y)I_1+xy I_0.
 \end{gathered}
\]
Both expressions for \(H\) integrate \(V_a(s)V_b(t)\)
over \(0\le s\le t\le 1\); the difference of \(C_1,C_2\)
inserts \(t-s\). Inserting that simplex length is also the
definition of \(J_0\), so \(J_0=C_1-C_2\).

Put \(P_9=(AV_L)_9,\ Q_9=(A^\star V_R)_9\), and write
\(b_9\) for the dormant physical output weight. The four paid
measurements are
\[
\begin{aligned}
 C_1-yH &= b_9(\zeta-y)P_9V_b(\zeta),\\
 C_2-xH &= b_9(\zeta-x)V_a(\zeta)Q_9,\\
 J_0 &= b_9P_9Q_9,\\
 I_{xy} &= b_9(\zeta-x)(\zeta-y)V_a(\zeta)V_b(\zeta).
\end{aligned}
\]
Indeed the two products with one primitive are supported on
\(\{9,10\}\) and \(\{8,9\}\) before inserting the clock
subtractions \(C_{\rm clk}-yI\) and \(C_{\rm clk}-xI\).
The product with both primitives is already supported on
\(\{9\}\); the product without primitives is supported on
\(\{8,9,10\}\) before inserting both clock subtractions.
The respective grades are \(5+4+1,4+5+1,5+5,4+4+2\),
all paid at order eleven by the actual order-ten weighted
transpose. No reverse ordinary order eleven is assumed.
Multiplying the first two equations and comparing the
last two gives, without a clock or weight division,
\[
 (C_1-yH)(C_2-xH)=J_0 I_{xy}.
\]
It includes the repeated-pair equation at \(x=y\).
In particular the \(C_1\) factor uses **physical row 10**,
not the left-only label by definition.

Define \(A_0=H^2-J_0 I_0\),
\(B_0=J_0 I_1-H C_1\),
\(C_0=J_0 I_1-H C_2\),
\(D_0=C_1C_2-J_0I_2\).
The central product says \(A_0xy+B_0x+C_0y+D_0=0\),
equivalently on that zero set
\[
 (A_0x+C_0)(A_0y+B_0)=-\Delta_0,\qquad
 \Delta_0=A_0D_0-B_0C_0 .
\]
This arithmetic is in the companion Lean gate over a
commutative ring. Over a field, a zero denominator
\(A_0x+C_0\) requires also \(B_0x+D_0=0\) and hence
\(\Delta_0=0\); the reverse solve is analogous. This is
the actual simultaneous-vanishing test. Separately,
when \(A_0\ne0=\Delta_0\), the product factors and only
requires \(x=-C_0/A_0\) **or** \(y=-B_0/A_0\); it does
not require both. If \(A_0=0,\Delta_0\ne0\) the equation
is linear with both \(B_0,C_0\) nonzero, not a pole.

## 2. Exact half–half determinant and geometry

Take \(h=e=a/2\), \(b=2-a\), \(d=a-1\). Let \(t\)
be the common free extra, \(u\) the left-only free label,
and \(v\) the right-only one. Thus \(\{x,y\}=\{u,v\}\),
with **both** possible physical orientations allowed.
The active hull is
\[
 H_6=(X-a)(X-h)(X-d)(X-t)(X-u)(X-v).
\]
All these active labels, the endpoints, and \(\zeta\)
are pairwise distinct. The only two shifted nodal rows
used below are
\(\int X(1-X)(X-\zeta)H_6 X^j=0\), \(j=0,1\).
We may multiply the hull by a nonzero common scalar.

With \(T_4\) and \(U_{4,4}\) the derivative-Gram
polynomials of the existing two-front atlas, let
\[
\begin{gathered}
 F_4=33a^4-132a^3+176a^2-88a+16=41580J_0,\\
 F_6=2475a^6-14850a^5+34140a^4-37560a^3
                 +20136a^2-4752a+352 .
\end{gathered}
\]
The rational replay verifies
\[
 1646877554784000000\Delta_0=-a^2(a-2)^2F_4F_6,\qquad
 U_{4,4}(a,b)-T_4(a)T_4(b)=-16a(a-2)F_6 .
\]
It also verifies \(\gcd(A_0,\Delta_0)=1\), so on a
singular fiber \(A_0\ne0\). The corresponding matrix
really has rank one. A global sign for \(\Delta_0\) is
unavailable: \(F_6\) can change sign for real widths.
Over an ordered field \(F_4>0\) directly, since with
\(s=a-1\) one has \(3F_4=11(3s^2-1)^2+4\). The
unordered argument below nevertheless checks **both**
width factors. Widths \(a=0,2\) are already forbidden.

## 3. The characteristic-zero \(F_4=0\) fiber

The exact rational coefficient check gives \(H\ne0\)
on \(F_4=0\). Since \(J_0=0=b_9P_9Q_9\), at least
one of \(P_9,Q_9\) vanishes. Reflect the clocks and
exchange the two mixed systems if needed, so that
\(P_9=0\); this exchanges \(a\) and \(2-a\) and preserves
\(F_4=0\). The first paid measurement now fixes
\(y=g=C_1/H=C_2/H\). The actual anchored left dormant
row becomes \(D_\zeta/a^5\), where
\[
 D_\zeta=a^5\ell_\zeta-30P(\zeta)\ell_a .
\]
Here \(\ell_s\) means evaluation at physical clock \(s\)
on the left anchored model space. This is the same
literal polynomial as the edge-port equation: at central
9 it follows from the just-proven \(P_9=0\), not from
chronological automatic vanishing.

Use the inverse anchored Gram pairing suppressed by its
common scalar factor 210, with the existing derivative
bases \(D_L^{(0)},D_L^{(a)},D_R^{(0)},D_R^{(b)}\).
The two pairings of \(D_\zeta\) with the right derivative
rows have the live common factor \(a\zeta(a-\zeta)\).
Call the residual cubics \(K_0,K_1\).
The actual right derivative coefficients at row 11
are proportional to \(R_0=(t-d)(v-d),\
R_1=-(1-t)(1-v)\), both nonzero. Their off-diagonal
with row 9 says \(R_0K_0+R_1K_1=0\).
In \(\mathbb Q[a]/(F_4)\), the exact gcd of the cubics
is 1, so at an actual \(\zeta\) both \(K_0,K_1\)
must be nonzero. Normalize the right derivative row to
\((K_1,-K_0)\). Thus the first contact at rows 7 and 11
has coefficients
\[
 \Gamma_0=K_1-T_4(b)K_0,\qquad
 \Gamma_1=T_4(a)K_1-U_{4,4}(a,b)K_0 .
\]
Both are nonzero: vanishing of one forces the other by
the actual left factors \(L_0=(a-t)(a-u),L_1=-tu\),
and simultaneous vanishing contradicts the derivative
determinant unit on \(F_4=0\).

For completeness the two actual contact solves are
\[
 u=\frac{a(a-t)\Gamma_0}{(a-t)\Gamma_0+t\Gamma_1},\qquad
 v=\frac{d(t-d)K_0+(1-t)K_1}{(t-d)K_0+(1-t)K_1}.
\]
The left denominator cannot vanish because its numerator
is nonzero. In the right solve, denominator and numerator
cannot vanish simultaneously: their difference is
\(b(t-d)K_0\ne0\). If the fixed physical \(y=g\)
is \(u\), solve first for
\[
 t=\frac{a(a-g)\Gamma_0}{(a-g)\Gamma_0+g\Gamma_1};
\]
if it is \(v\), solve first for
\[
 t=\frac{d(g-d)K_0+(1-g)K_1}{(g-d)K_0+(1-g)K_1}.
\]
Exactly the same numerator or difference argument earns
each live denominator. Then solve for the remaining
exclusive label by the preceding two contact formulas.
The scaled hull \((X-a)(X-h)(X-d)(X-g)\) times the
two remaining numerator-cleared factors gives the **raw**
two shifted equations of degree ten in \(\zeta\) in
both orientations. Their gcd in the exact coefficient
field is 1. This includes all specialized degree drops
and does not require a shifted Hankel pivot.

## 4. The \(F_6=0\) fiber: both null lines and both orientations

Reflection of the mixed order conditions sends
\((a,x,y)\) to \((2-a,1-y,1-x)\).
It carries \(A_0\) to itself and \((B_0,C_0)\) to
\((-A_0-C_0,-A_0-B_0)\). As \(F_6\) is preserved, we
may assume the forced root is the **physical row-8**
clock \(x=x_0=-C_0/A_0\). Denote the possible other
forced root by \(y_0=-B_0/A_0\); do not assume it yet.

On \(F_6=0\) the derivative matrix is
\(\left(\begin{smallmatrix}1&T_4(b)\\ T_4(a)&T_4(a)T_4(b)\end{smallmatrix}\right)\).
Thus the actual first off-diagonal factors as
\((L_0+T_4(a)L_1)(R_0+T_4(b)R_1)=0\).
If the left factor is zero, the left derivative row is
proportional to \(D_L^{(a)}-T_4(a)D_L^{(0)}\) and
\[
 t=\frac{a(a-u)}{a-u+T_4(a)u}.
\]
If the right factor is zero, the right row is
proportional to \(D_R^{(b)}-T_4(b)D_R^{(0)}\) and
\[
 t=\frac{d(v-d)+T_4(b)(1-v)}{(v-d)+T_4(b)(1-v)}.
\]
The first denominator is live by \(a(a-u)\ne0\);
the second by the difference \(b(v-d)\ne0\).
This gives two explicit scaled hulls in each orientation
\((u,v)=(x_0,y)\) or \((y,x_0)\).

To derive the actual central row needed for the next
off-diagonal, \(J_0\ne0\) on \(F_6\), hence \(P_9,Q_9\ne0\).
All factors in the fourth paid measurement are nonzero,
so \(I_{xy}\ne0\). The product and measured amplitudes
give in particular
\[
 Q_9=\frac{J_0(\zeta-y)V_b(\zeta)}{C_1-yH}.
\]
The denominator is nonzero by the first paid measurement.
Write \(r_s\) for evaluation at \(s\) on the right
anchored model space. The actual right dormant row,
multiplied by the live \(b^5(C_1-yH)\), is
\[
 \mathcal R(\zeta,y)=
 b^5(C_1-yH)r_\zeta+
 30\{J_0(\zeta-y)V_b(\zeta)-(C_1-yH)Q(\zeta)\}r_d .
\]
This uses \(Q(d)=b^5/30\) and the inherited fact that on
a dormant row the only possible anchored correction is
a multiple of \(r_d\). The analogous left-row calculation
shows that its pairing with the right null line vanishes
identically on this width branch. That equation is not
independent and is not used for an exclusion.

* **Left null, \(y\ne y_0\).** Pair the left null line
  against \(\mathcal R\) at row 9. The replay verifies
  the exact factor \((1-\zeta)^2(\zeta-d)^2\); the
  remaining affine-in-\(\zeta\) polynomial has both
  coefficients divisible by \(y-y_0\), their exact
  whole gcd in \(y\) being \(y-y_0\). After these live
  factors are removed its leading coefficient is a
  nonzero constant in the width field. Thus \(\zeta\)
  is fixed. With the corresponding left-null scaled
  hull, the two raw shifted polynomials in \(y\) have
  degrees \((1,1)\) or \((2,2)\), and exact gcd 1.
* **Both central roots fixed, \(y=y_0\).** Either null
  relation fixes \(t\) with a live denominator. In all
  four combinations of null line and physical orientation,
  the two raw shifted equations in \(\zeta\) are linear
  and have exact gcd 1.
* **Right null.** With the right-null scaled hull, put
  \(m_j=\int X(1-X)\widehat H_6 X^j\) for \(j=0,1,2\).
  If \(m_0=0\), the true shift equations force
  \(m_1=m_2=0\), and the three raw polynomials have gcd 1
  in either orientation. Otherwise
  \(\zeta=m_1/m_0\) and \(m_0m_2-m_1^2=0\).
  Homogeneously substitute this \(\zeta\) into the actual
  **left row 7 versus right dormant row 9** off-diagonal,
  using the scaled left derivative coefficients
  \(((a t_D-t_N)(a-u),-t_Nu)\) where \(t=t_N/t_D\).
  The exact off-diagonal has the live factor
  \((1-\zeta)(\zeta-d)\), removed before the substitution.
  Its cleared polynomial and the shifted determinant have
  degrees \((8,4)\) or \((5,2)\), and exact gcd 1.

The reflection only exchanges previously paid mixed
equations, not ordinary reversed order eleven. The two
width polynomials are irreducible over \(\mathbb Q\),
and the replay verifies their exact degrees. Therefore
each calculation in the corresponding abstract rational
coefficient field applies under any evaluation at a root
in any characteristic-zero field. No particular real
root is chosen for the proof, and no modular reduction of
an unknown tableau or numeric root scouting is used.

The standalone replay is
replay_n12_half_different_center_rank_one.py, depending
only on SymPy. ERK11CentralTwoClockProductGate.lean
checks the generic paid-product cancellation, expansion,
and singular-factor identity. The physical grade ledger,
width factorizations and exact fibers remain mathematical
proof plus the rational replay, not an end-to-end Lean
tableau proof.

The [standalone fiber replay](erk11-nine-site-central-two-clock-rank-one/replay_n12_half_different_center_rank_one.py)
and [independent coefficient replay](erk11-nine-site-central-two-clock-rank-one/check_width_coefficients.py)
are archived together. The
[product gate](../lean/RKCert/ReviewedNative/ERK11CentralTwoClockProductGate.lean)
and
[centered determinant and positive-quartic scalar identities](../lean/RKCert/ReviewedNative/ERK11CentralWidthDeterminant.lean)
pass Lean 4.34.1, 4.35.0, 4.36.0, and 4.37.0-rc1 with standard axioms.
The full rooted-order ingress and fiber exclusion remain mathematical.
