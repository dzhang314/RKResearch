# Central nine-site regular chart: the matched exclusive orientation is impossible

**Scope.** Continue the [finite regular central atlas](ERK11-NINE-SITE-HALF-DIFFERENT-CENTER-FINITE.md):
half–half overlap and different extra sets, genuine nine
clock sites, \(\Delta_0\ne0\), and dormant physical stage
9. “Matched” means the left-only label \(u\) is physical
row \(8\), clock \(x\), and the right-only label \(v\)
is physical row \(10\), clock \(y\). This excludes
the entire matched orientation over characteristic zero
given those hypotheses. The shifted, reciprocal and
orientation guards are literal. The opposite orientation
is **not** excluded here, but two additional paid
polynomial constraints for it are derived below.

## 1. Repeated-exclusive contact from two actual rows

Let \(\langle\ ,\ \rangle_N\) be the inverse mixed Gram
pairing omitting the common scale factor 210; all
pairings below are zero tests. For a left-only label
\(u\), let \(i\) be its left front occurrence (physical
6 or 7) and \(k\) its inner occurrence (physical 8
or 10). Let \(F_i,F_k\) be the forward pure responses.
They are distinct and \(F_i\ne0\) by the live pair
law and actual calibration. Define \(s_u=1-F_k/F_i\).
The grade-four square-clock vector \(V_L\) is zero at
\(i\), and for any two same-clock noncarrier rows in
this pair its difference after eliminating the response
coefficient is the scalar model \(V_a(u)\).
In particular \(V_L(k)=s_uV_a(u)\).

Use \(L_j\) for the actual anchored grade-five
functional at physical \(j\). The inherited general
noncarrier row form is a model evaluation plus the
response times a polynomial coefficient and a
single correction proportional to evaluation at
\(a\). Since \(c_i=c_k=u\), subtracting
\((F_k/F_i)L_i\) from \(L_k\) removes the response
functional. Evaluate the remainder on \(P=JV_a\)
to measure its sole correction: the actual primitive
\(P_i=(A V_L)_i=0\), and the model has \(P(a)=a^5/30\).
This gives the exact functional identity
\[
 a^5(L_k-(F_k/F_i)L_i)
   =s_u D_u+30 P_k\,\ell_a,\qquad
 D_u=a^5\ell_u-30P(u)\ell_a .
\]
Nothing is assumed about \(P_k\). Both \(L_i,L_k\)
pair to zero with the actual right row 11 \(\Phi_R\):
when \(i=6\) it is the zero anchored row, and when
\(i=7\) it is the paid off-diagonal; \(k=8\) or 10
is another off-diagonal. Thus
\[
 s_u\langle D_u,\Phi_R\rangle_N+
 30P_k\langle\ell_a,\Phi_R\rangle_N=0 .
\]
The reverse identity uses the right-only label \(v\),
\(Q=\bar J V_b\), actual \(R_k\), and
\(D^R_v=b^5 r_v-30 Q(v)r_d\), without requiring reverse
ordinary order eleven.

In matched orientation \(P_8=0\), \(Q_{10}=0\)
by literal strictness (the square-clock vectors
vanish through their seventh row). The \(s_u\) and
reverse factors are nonzero, giving the two **new**
off-diagonal contacts
\[
 \langle D_x,\Phi_R\rangle_N=0,\qquad
 \langle\Phi_L,D^R_y\rangle_N=0 .
\]
This proof works whether the repeated exclusive
label was local sixth or seventh at its own front.
It uses no unknown scalar response scale, nor any
substitution of an active row for a dormant row.

## 2. Raw contact polynomials in the matched orientation

Keep the earlier \(a,b=2-a,d=a-1,h=a/2\) and
\(y=Y/E\) from the regular central product,
\(E=A_0 x+C_0,\ Y=-(B_0 x+D_0)\).
All roots and widths retain the genuine nine-site
guards. Write \(T_a=T_4(a),\,T_b=T_4(b)\) and
\(U=U_{4,4}(a,b)\).
Let \(K_0,K_1\) be the pairings of \(D_x\) with
right derivatives \(D_R^{(0)},D_R^{(b)}\) divided
by the live factor \(a x(a-x)\).
Let \(J_0'(w),J_1'(w)\) be the pairings of left
derivatives \(D_L^{(0)},D_L^{(a)}\) with \(D^R_w\)
divided by the live factor \(b(1-w)(w-d)\). These
are explicit cubics in the respective clock.
The notation \(J_i'\) here denotes these pairings,
not derivatives of the central scalar moment \(J_0\).

The derivative row coefficients in this orientation
are \(L_0=(a-t)(a-x), L_1=-tx,\,
R_0=(t-d)(y-d), R_1=-(1-t)(1-y)\).
All four are nonzero. The first new contact says
\(R_0 K_0+R_1 K_1=0\).
Thus either both \(K_i\) vanish or both are live.

**Full dropout.** The exact \(x\)-resultant of
the pair \(K_0,K_1\) has factors of degrees \(1,1,21\)
with multiplicities \(3,12,1\); the linear factors
are the forbidden widths \(a=0,2\). In the degree-21
irreducible rational coefficient field the exact
cubic gcd is linear, specifying \(x\). The replay
checks the genuine width and denominator conditions
and both \(J_0'(y),J_1'(y)\) are nonzero there.
The second new contact now fixes
\[
 t=\frac{a(a-x)J_0'(y)}{(a-x)J_0'(y)+xJ_1'(y)} .
\]
The numerator is live, hence so is its exact
denominator. With this \(t\), the two true shifted
nodal equations are inconsistent: for the moments
\(m_j=\int X(1-X)\Pi_5 X^j\) of the previous packet,
the exact field element
\[
  (m_1-tm_0)(m_3-tm_2)-(m_2-tm_1)^2
\]
is nonzero. This checks the whole true dropout,
not merely the roots that retain an optional
leading coefficient after a change of field.

**Live front.** Normalize the right derivative
coefficients to \((K_1,-K_0)\). The first Gram contact
then has left coefficients
\(\Gamma_0=K_1-T_bK_0,\ \Gamma_1=T_aK_1-U K_0\).
They are individually live: one zero forces both
because \(L_0,L_1\ne0\), and both zero contradict
\(U\ne T_aT_b\) in the present \(\Delta_0\ne0\) chart.
Let
\[
 t_D=(Y-dE)K_0+(E-Y)K_1,\quad
 t_N=d(Y-dE)K_0+(E-Y)K_1 .
\]
The first new contact forces \(t=t_N/t_D\):
\(t_D\) cannot vanish because \(t_D-t_N=b(Y-dE)K_0\ne0\).
The actual derivative row of the left is now
proportional to \((\Gamma_1,-\Gamma_0)\).
Thus the exact algebraic system is
\[
 \begin{aligned}
 F_1&=(a t_D-t_N)(a-x)\Gamma_0-t_N x\Gamma_1=0,\\
 F_2&=\Gamma_1\,E^3J_0'(Y/E)-\Gamma_0\,E^3J_1'(Y/E)=0,\\
 F_3&=(t_Dm_1-t_Nm_0)(t_Dm_3-t_Nm_2)
       -(t_Dm_2-t_Nm_1)^2=0 .
 \end{aligned}
\]
The second equation is the second new contact.
The last is the actual two shifted rows after
substitution of \(t=t_N/t_D\), eliminating
\(\zeta\) by their determinant; it does not
assume a third shifted row. The previously
proved two-live-site pivot and reciprocal guards
remain applicable.

## 3. Exact width projection and every fiber

Remove exactly \(ab^2 x(x-a)\) from \(F_1\),
\(ab^5\) from \(F_2\), and \(b^2\) from \(F_3\).
The divisions are exact and every removed factor
is live. The reduced bidegrees \((a,x)\) are
\((24,6),(34,6),(52,12)\). The two rational
\(x\)-resultants, first with second and first
with third, have degrees 326 and 556 in \(a\).
Their exact common gcd has seven irreducible
factors. Widths of degrees \(1,1,4,6\) divide
\(\Delta_0\) and hence are impossible here.
The remaining degrees are 17, 21, 27.
For each, compute in the complete exact
irreducible rational coefficient field, not
a single selected real root. The common
\(x\)-gcd of the three reduced equations is
linear and:
* in degree 17 it divides \(Y-E\), forcing \(y=1\);
* in degree 21 it divides \(K_0\), the full
  already-excluded dropout because both \(R_i\)
  are live, and its width polynomial is exactly
  the dropout width above;
* in degree 27 it divides \(Y-dE\), forcing \(y=d\).

The first and third are forbidden clock collisions.
Polynomial resultants apply at every actual common
finite root even if an \(x\)-degree specializes.
The separate triple gcd checks full true fibers,
not just intersections of two projections. The
standalone replay uses exact rational SymPy and
python-flint arithmetic. Nothing is deduced from
unknown tableaux reduced modulo a prime.

## 4. The opposite orientation: independent paid quadratic marks

If \(u=y,v=x\), the same-contact row difference
holds, but \(P_{10},Q_8\) need not vanish. There
is still no unknown response variable in its
weighted form. The vanishing first-response pool
gives \(b_k s_u=B_u\), the actual scalar pool.
Put \(\gamma_u=b_k V_L(k)V_R(k)\) and
\(M_u=b_k P_kV_R(k)\). Since
\(V_L(k)=s_u V_a(u)\), the weighted forward contact is
\[
 \gamma_u\langle D_u,\Phi_R\rangle_N+
 30V_a(u)M_u\langle\ell_a,\Phi_R\rangle_N=0 .
\]
It was obtained by multiplication only; it remains
true if \(\gamma_u\), \(P_k\), or \(V_R(k)\) is zero.
Define \(I(p,q)=I_2-(p+q)I_1+pq I_0\).
The mixed grade-four product with two clock
factors isolates row 10:
\(\gamma_y(y-x)(y-\zeta)=I(x,\zeta)\).
The forward primitive times the reverse square
clock vector with one clock factor gives
\(M_y(y-\zeta)=C_1-\zeta H\).
Thus, exactly at the paid total grade ten,
\[
 I(x,\zeta)\langle D_y,\Phi_R\rangle_N+
 30V_a(y)(y-x)(C_1-\zeta H)
       \langle\ell_a,\Phi_R\rangle_N=0 .
\]
Likewise the reflected equation is
\[
 I(y,\zeta)\langle\Phi_L,D^R_x\rangle_N+
 30V_b(x)(x-y)(C_2-\zeta H)
       \langle\Phi_L,r_d\rangle_N=0 .
\]
These testing polynomials are affine in \(\zeta\)
before substituting \(t\), and at most quadratic
after \(t=q_1/q_0\) is cleared. They are stronger
clock tests than just the old dormant diagonal
and first contact. No closure of the opposite
orientation is asserted in this packet.

ERK11RepeatedExclusiveContactGate.lean verifies
the weighted cancellation over arbitrary
commutative rings. The same-clock functional
transfer, payment, clock guards, and rational
elimination remain mathematical plus the exact
replay, not an end-to-end Lean tableau proof.

The [standalone exact replay](erk11-nine-site-half-different-center-matched-exit/replay_n12_half_different_center_matched_exit.py)
checks the remaining algebraic clock fibers. The
[portable Lean gate](../lean/RKCert/ReviewedNative/ERK11RepeatedExclusiveContactGate.lean)
checks weighted contact, the clock clearing, and the mass factor on all
four tested Lean versions, separately from the tableau-level chronology.
