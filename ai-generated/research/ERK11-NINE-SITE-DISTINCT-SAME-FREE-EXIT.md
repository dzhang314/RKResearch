# Nine live sites: four distinct calibrations cannot share the same free pair

**Scope.** Continue the [genuine nine-site six-pair chart](ERK11-SIX-PAIR-DORMANT-CLOCK-SEPARATION.md).
Here the four calibration labels \(a,h=a/2,d=1-b,e=1-b/2\)
are distinct, and **both** fronts choose the same two
free labels \(t_1,t_2\). Thus these are the two crossing
pairs, and the remaining two inner active clocks are
\(h,e\), once each. This excludes every dormant position
\(8,9,10\) and both physical orders of \(h,e\), over
**characteristic zero** given genuine nine-site separation
and the inherited actual mixed order payments. It does
not exclude the other four-distinct two-cross diagrams,
or ordinary 17-stage ERK11.

## 1. True paired moments and the two anchored marks

Use the usual models \(V_a=X^2(X-a)^2\),
\(V_b=(1-X)^2(X-d)^2\), primitives \(P=JV_a,Q=\bar J V_b\),
and integrals over \([0,1]\)
\[
 H=\int PV_b=\int V_aQ,\quad C_1=\int XPV_b,\quad
 C_2=\int XV_aQ,\quad J_0=\int PQ,\quad
 I(p,q)=\int V_aV_b(X-p)(X-q).
\]
Write \(z\) for the dormant clock, and \(x,y\)
for the two actual active inner clocks in their
physical order. “Matched” means \(x=h,y=e\);
“opposite” means \(x=e,y=h\). The left-only
half \(h\) occurs at actual forward third
and one inner row, and \(e\) occurs at actual
reflected third and one inner row. Those front
occurrences have nonzero calibrated responses,
zero unadvanced and primitive square-clock
values, and zero anchored rows. The proof of
the [literal same-clock row differences](ERK11-NINE-SITE-HALF-DIFFERENT-CENTER-MATCHED-EXIT.md)
therefore applies at these earlier front
occurrences as well. It needs only those zero
reads and the nonzero and distinct pair
responses, not a sixth- or seventh-row premise.

Let \(\langle\,,\,\rangle_N\) denote inverse
anchored Gram with its factor 210 removed.
Define \(D_w=a^5\ell_w-30P(w)\ell_a\) and
\(D^R_w=b^5r_w-30Q(w)r_d\).
Let \(K_j(w)\) be the pairings of \(D_w\) with
the two right derivative basis rows divided by
\(aw(a-w)\), and \(K_j^R(w)\) the pairings of
left derivative basis rows with \(D_w^R\) divided
by \(b(1-w)(w-d)\). These are exact cubic
polynomials, not arbitrary pivots.
All these removed factors are live at \(w=h\)
or \(w=e\) in the associated orientation.

Write \(\sigma=t_1+t_2,\ \pi=t_1t_2\).
The derivative row coefficients are
\[
 L_0=a^2-a\sigma+\pi,\quad L_1=-\pi,\qquad
 R_0=d^2-d\sigma+\pi,\quad R_1=-(1-\sigma+\pi).
\]
Each is live as the actual product of nonzero
clock differences. Their first contact is
\[
 F=L_0R_0+T_4(a)L_1R_0+T_4(b)L_0R_1
      +U_{4,4}(a,b)L_1R_1=0.
\]
The order of \(t_1,t_2\) on either front
does not alter these coefficients, up to the
already-live actual derivative prefactors.

Let \(P_4=(X-a)(X-h)(X-d)(X-e)\), and
\[
 m_j=\int X(1-X)P_4 X^j,\quad 0\le j\le4.
\]
These actual scalar tests have degree at most
ten and their only surviving sites are
\(z,t_1,t_2\); all three modified scalar weights
are live. The free pair scalar pools are live by
\(B_t f_1f_2=-\mu_t\ne0\) from the
[six-pair law](ERK11-SIX-PAIR-SITE-MASK.md).
Thus the unshifted determinant
\[
 \mathcal H_3=\det(m_{i+j})_{0\le i,j\le2}
\]
is the product of the three modified weights
and the squared distinct-clock Vandermonde:
it is nonzero even with signed weights.
Put \(E_j=m_{j+1}-z m_j,\ 0\le j\le3\).
The shifted moments leave only \(t_1,t_2\).
Consequently
\[
 \Delta_{\rm sh}=E_0E_2-E_1^2
 =w_1w_2(t_1-t_2)^2\ne0
\]
for the two live shifted weights. The two actual
shifted nodal equations give the exact homogeneous
Cramer formulas
\[
 \sigma=\sigma_N/\Delta_{\rm sh},\
 \pi=\pi_N/\Delta_{\rm sh},\qquad
 \sigma_N=E_0E_3-E_1E_2,\quad
 \pi_N=E_1E_3-E_2^2 .
\]
Neither an extra shifted row nor a positive
moment signature is assumed. Natural guards
include that \(\Delta_{\rm sh}X^2-\sigma_NX+\pi_N\)
does not vanish at \(0,1,a,h,d,e,z\), and that
its discriminant is nonzero. We never assume
\(\sigma_N\ne0\).
The companion Lean file checks this scalar
Cramer algebra and the three-site determinant.
It also checks the relation
\(\mathcal H_3=m_0\pi_N-m_1\sigma_N+m_2\Delta_{\rm sh}\)
before any homogeneous scaling of \(z\).

## 2. Physical-9 central exits

At physical 9 dormant, the usual four products
supported only on that row give the width-only
equation
\[
 C_{\rm mid}=(C_1-yH)(C_2-xH)-J_0 I(h,e)=0
\]
at either actual assignment \((x,y)\) of \(h,e\).
The orders remain \(5+4+1,4+5+1,5+5,4+4+2\);
in particular there is no reverse ordinary
order eleven. The genuine dormant square
product gives \(I(h,e)\ne0\), with both model
values literal there.

**Matched central.** Now \(P_8=0,Q_{10}=0\).
The literal repeated-exclusive differences
directly give
\(\langle D_h,\Phi_R\rangle_N=0\),
\(\langle\Phi_L,D_e^R\rangle_N=0\).
Let \(k_j=K_j(h), \ell_j=K_j^R(e)\).
As equations in \((\sigma,\pi)\), their rows,
including constants, are
\[
 (r_S,r_P,r_c)=(-d k_0+k_1,k_0-k_1,d^2 k_0-k_1),\qquad
 (l_S,l_P,l_c)=(-a\ell_0,\ell_0-\ell_1,a^2\ell_0).
\]
Define \(\delta=r_Sl_P-r_Pl_S,\ S_N=r_Pl_c-r_cl_P\),
\(P_N=l_Sr_c-r_Sl_c\).
Actual consistency gives
\(\delta\sigma=S_N,\ \delta\pi=P_N\),
without any denominator.

If \(\delta=0\), \(C_{\rm mid}\) and the two
necessary equations \(\delta=S_N=0\)
give exact \(b\)-resultants of \(a\)-degree
36 and 36 with constant common gcd.
Thus no singular contact rank remains.
If \(\delta\ne0\), substitute the two
Cramer ratios into the first derivative
contact \(F\) and form
\[
 \widehat H_6=P_4(\delta X^2-S_N X+P_N),\qquad
 \widetilde m_j=\int X(1-X)\widehat H_6 X^j .
\]
This modified quadrature survives only
at \(z\); consequently \(\widetilde m_0\ne0\)
and \(\widetilde m_0\widetilde m_2-\widetilde m_1^2=0\).
With the same width-only \(C_{\rm mid}\) the
remaining two \(b\)-resultants are degrees
36 and 96, again exact gcd 1.
The reduced \(C_{\rm mid}\) is bidegree \((3,3)\);
any canceled fraction factors are exact divisors
of the listed live guards, including the
regular actual derivative factors when used.
No clock order or modular lift is needed here.

**Opposite central.** Use the actual shifted
\(\Delta_{\rm sh}\) formulas from Section 1 to
clear \(\sigma,\pi\), and use the weighted
same-clock contacts at physical 10 and 8:
\[
\begin{aligned}
 M_L={}&a\, I(e,z)(R_0 k_0+R_1 k_1)
  +30h(a-h)(h-e)(C_1-zH)\langle\ell_a,\Phi_R\rangle_N=0,\\
 M_R={}&b\, I(h,z)(L_0\ell_0+L_1\ell_1)
  +30(1-e)(e-d)(e-h)(C_2-zH)\langle\Phi_L,r_d\rangle_N=0.
\end{aligned}
\]
These formulas already remove the live factors
\(h(a-h)\) and \((1-e)(e-d)\) from the actual
row differences. They use grade \(4+4+2\)
for the isolated square-clock amplitude and at
most \(5+4+1\) for its primitive partner,
without division by these amplitudes.

The same true dormant read gives the actual
center primitive values
\[
 P_9=(C_1-hH)(z-e)V_a(z)/I(h,e),\qquad
 Q_9=(C_2-eH)(z-h)V_b(z)/I(h,e).
\]
The scaled left and right dormant rows are
\[
 \begin{aligned}
 L^\#&=I(h,e)D_z+30(C_1-hH)(z-e)V_a(z)\ell_a,\\
 R^\#&=I(h,e)D^R_z+30(C_2-eH)(z-h)V_b(z)r_d.
 \end{aligned}
\]
Divide the first by \(z(z-a)\) and the second
by \((1-z)(z-d)\) to get cubic rows \(L_3,R_3\).
Their reciprocal diagonal is
\[
 B_{\rm cen}=210\langle L_3,R_3\rangle_N
 -a^5b^5I(h,e)(z-e)(z-h)z(z-a)(1-z)(z-d)=0.
\]
This is \(1/b_9\) for the actual anchored rows,
using the standalone four-product support
to express the same reciprocal weight.
It is not the edge-dormant \(Q_8=0\) assumption.

Take the three \(z\)-resultants of \(M_L\) with
\(M_R,B_{\rm cen},F\). Project each against
\(C_{\rm mid}\) by a \(b\)-resultant. Their exact
\(a\)-degrees are 630, 957, 718, and the common
gcd is \(a^8\) up to a nonzero rational scalar.
This forbidden \(a=0\) closes the opposite
orientation, including all finite degree-drop
fibers of the nested projections.

## 3. Physical-8 edge exits, including affine dropout

At physical 8 dormant use \(z=c_8,x=c_9,y=c_{10}\).
The individually masked versions of the four
products isolate **active** physical 9, giving
\[
 (C_1-yH)(C_2-zH)=J_0 I(z,y).
\]
With the central bilinear coefficients
\(A_0,B_0,C_0,D_0\), this is the affine equation
\[
 \mathcal E z=\mathcal N,\qquad
 \mathcal E=A_0 y+B_0,\quad
 \mathcal N=-(C_0y+D_0).
\]
No division by \(I(z,y)\) is used, and the model
square values need not be the actual values
at active physical 9.

The physical-8 forward primitive vanishes
by chronology, so the literal left anchored
row there is \(D_z/a^5\). Its contact with
physical 11 is
\(G=K_0(z)R_0+K_1(z)R_1=0\)
after removing its live edge factor \(az(a-z)\).
Use the actual \(\Delta_{\rm sh}\) substitution
throughout \(G,F\) and the remaining contact.
If \(y=e\) (matched), the right same-clock
difference at physical 10 uses \(Q_{10}=0\)
and gives \(R_{\rm mark}=\ell_0 L_0+\ell_1 L_1=0\).
If \(x=e\) (opposite), multiply the right
same-clock difference at physical 9 by the
other actual primitive, using \(b_9P_9Q_9=J_0\).
The needed mark, divided by \((1-e)(e-d)\), is
\[
 R_{\rm mark}=b(C_1-hH)(\ell_0 L_0+\ell_1 L_1)
    +30(1-e)(e-d)(e-h)J_0\langle\Phi_L,r_d\rangle_N=0.
\]
This does not divide by an unknown isolated
moment, or assume its sign.

If \(\mathcal E=0\), consistency forces
\(\mathcal N=0\). Remove only actual live
width factors of these polynomials.
Their \(b\)-resultant has degree 18 matched
or 32 opposite. Project the additional
\(\operatorname{Res}_z(G,R_{\rm mark})\)
against \(\mathcal E\) in \(b\).
The width gcd is already constant for
matched; for opposite also project the
first contact via
\(\operatorname{Res}_z(G,F)\), yielding
constant gcd. Thus the full affine dropout
is excluded, not just its generic part.

If \(\mathcal E\ne0\), use \(z=\mathcal N/\mathcal E\)
and clear exactly the live denominators.
The reduced \((a,b)\)-bidegrees for
\((G,F,R_{\rm mark})\) are
\((23,22),(27,23),(15,13)\) matched and
\((28,27),(31,27),(20,19)\) opposite.
Use the two \(b\)-resultants with first gate
\(G\). Their respective degrees are
\(1081,611\) or \(1537,1048\).
The exact coefficient-bound CRT uses
94 or 129 certified integer primes, with
modulus product more than twice every
coefficient determinant bound. It does
not reduce an unknown tableau modulo a prime.

The width gcds have degrees 294 and 520.
Up to constants they factor into:
* matched: \(a^{36}\), one degree-108 factor,
  and degrees 6 and 9 each to power 10;
* opposite: \(a^{108}(a-2)^{40}\), one degree-132
  factor, degree 15 to power 10, and degree 6
  to power 15.

The linear width guards \(a,a-2\) are live.
For each remaining irreducible width factor,
the exact homogeneous guard and candidate
power tests are:
\[
\begin{array}{c|r|c|r}
\text{orientation}&\text{degree}&\text{guard pair}&
 \text{common power in }G,F,R_{\rm mark}\\\hline
\text{matched}&108&\mathcal H_3,\ \Delta_{\rm sh}^{\#}&1\\
&6&\mathcal E,\mathcal N&2\\
&9&\mathcal E,\mathcal N&2\\\hline
\text{opposite}&132&\mathcal H_3,\ \Delta_{\rm sh}^{\#}&1\\
&15&\mathcal E,\mathcal N&2\\
&6&\mathcal E,\mathcal N&3
\end{array}
\]
Here \(\Delta_{\rm sh}^{\#}\) is the homogeneous
cleared shifted determinant at
\(z=\mathcal N/\mathcal E\).
A linear subresultant of the guard pair
provides a candidate in \(b\); any common
global factor removed solely to construct
that candidate is not used to dismiss an
actual root. The replay checks the **raw**
guard pair at that candidate exactly,
together with the corresponding initial
homogeneous Taylor coefficients of all
three required gates. Thus the forbidden
linear candidate divides the equations to
the stated power exactly.

The candidate leading denominators are
units in the complete width coefficient
reductions modulo 101. After exact
monic division by the forbidden power,
all three quotient degrees are retained
and their gcd is constant in every
residue coefficient factor. A maximal
unit minor in the multiplication maps
of the resulting finite-free monic
quotient lifts the unit ideal to
characteristic zero, as in the
[earlier edge proof](ERK11-NINE-SITE-HALF-DIFFERENT-EDGE-EXIT.md).
Thus these are true whole-fiber exits,
not degree-preserving assertions about
an unknown stage tableau.

Reflection exchanges the two fronts and
their paired supports to cover physical 10
dormant. No ordinary reversed order eleven
is used. The standalone exact replay needs
SymPy and python-flint (verified 0.9).
ERK11TwoFreeShiftedHankelGate.lean checks
the actual two-free Cramer identities and
the scalar three-site Hankel algebra over
commutative rings; the actual moment transfer
and full exact coefficient exits remain
mathematical plus replay, not a native Lean
ordinary order-eleven tableau exclusion.

See the [standalone replay](erk11-nine-site-distinct-same-free-exit/replay_n12_distinct_same_free_exit.py), [exact output](erk11-nine-site-distinct-same-free-exit/exact-replay.txt), and [portable scalar gate](../lean/RKCert/ReviewedNative/ERK11TwoFreeShiftedHankelGate.lean).
