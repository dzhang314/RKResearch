# Ten active labels, twelve active rows: exact two-pair reconstruction and inner cuts

**Scope.** Continue the all-live, half-clock, two-carrier, two-new-boundary order-eleven equality problem with \(q=10\) nonzero-first-pool labels and \(n=12\) active noncarrier rows, as in the [ten-label overlap note](ERK11-NONZERO-FIRST-POOL-TEN-LABEL-OVERLAPS.md). There are exactly two unequal active pairs; the sole-triple chart was already excluded. This note gives an exact reconstructible rational profile and scalar-measure reduction over characteristic zero, a topology inventory, and actual mixed clock exclusions. It does **not** exclude either entire census split or change an unrestricted stage interval. The ordered signs and the exclusion of the double-zero center are explicitly marked.

## 1. True two-pool polynomial and pair charges

Keep \(F\) as the physical grade-three pure response, \(C\) the clock multiplier, and \(s\) the two-carrier indicator at clock \(\theta\). Put \(p,r\) for the two repeated active labels, \(D_s\) the monic hull of the eight active singleton labels and \(D=(X-p)(X-r)D_s\). Let \(P,Q,B\) be the paid first, second and third interpolants: for each active label \(x\),
\[
 P(x)=D'(x)\nu_x,\qquad Q(x)=D'(x)\mu_x,\qquad B(x)=D'(x)\tau_x,
\quad \deg P\le1,\quad\deg Q\le4,\quad\deg B\le7 .
\]
Here the three pools are the actual \(b_i\)-weighted moments of \(F_i,F_i^2,F_i^3\). At a singleton \(P(x)B(x)=Q(x)^2\). At a two-active-row pair \((f,g)\) with ordinary weights \(b_1,b_2\), the same difference equals
\[
 D'(x)^2 b_1 b_2 fg(f-g)^2\ne0.
\]
Thus the polynomial
\[
 P B-Q^2=\lambda D_s,\qquad \lambda\ne0
\]
is exact, since it has degree at most eight, vanishes at all eight singleton sites, and is nonzero. In particular:

* If \(P\) is constant it is nonzero, \(Q\) has degree four and \(\lambda=-\operatorname{lc}(Q)^2\).
* If \(P\) is linear, its unique root \(\xi\) cannot be a singleton because the actual singleton \(\nu_x\) is live. Therefore \(D_s(\xi)\ne0\), and \(-Q(\xi)^2=\lambda D_s(\xi)\) proves \(Q(\xi)\ne0\). The affine denominator of \(Q/P\) does not cancel, **even if its root is a pair label**.

Define the true grade-four pair with model \(Q\)
\[
 T=Q(C)\mathbf1-P(C)F-Q(\theta)s.
\]
It vanishes at the carriers and the singletons. There is exactly one dormant noncarrier besides the two physical endpoints; write \(\zeta\) for its clock (aliases allowed). Away from the carriers, \(T\) is thus supported on the endpoints, the two active pairs and this one dormant row. At each pair label separately its response-weighted charge is zero:
\[
 \sum_{c_i=x} b_i F_i T_i=Q(x)\nu_x-P(x)\mu_x=0 .
\]
Neither active \(T_i\) can be zero there: if one were, both would be zero by that charge and the live \(b_iF_i\), then the two distinct \(F_i\)'s would give \(P(x)=Q(x)=0\), contrary to \(\lambda D_s(x)\ne0\). The higher charge is explicit:
\[
 \sum_{c_i=p} b_i F_i^2 T_i=-\lambda/(p-r),\qquad
 \sum_{c_i=r} b_i F_i^2 T_i=-\lambda/(r-p).
\]
Indeed \(Q\mu-P\tau=-\lambda D_s/D'\). Independent of the exact degree of \(Q\), \(T\) does **not** descend to grade three: either its model has degree four, or \(P\) is genuinely affine and \(CF\) is independent of \(s,F\) in the measured pure grade-four flag. This prevents using the earlier grade-five primitive masks at an unearned total grade.

The raw dormant moment
\[
 m_j=\int X^j X(1-X)(X-p)(X-r)Q(X)
      =b_{\rm dorm}\,\zeta^j\zeta(1-\zeta)(\zeta-p)(\zeta-r)Q(\zeta),
 \qquad 0\le j\le2,
\]
is paid by the actual mask of \(T\), of grade \(8+j\). This is rank one or zero. We do **not** cancel \(m_0\), the dormant clock differences, or \(Q(\zeta)\).

## 2. A ghost remainder without a simple-root or live-weight condition

Use the possibly repeated formal hull
\[
 \Omega_1=X(X-1)(X-\zeta),\qquad \Omega=(X-p)(X-r)\Omega_1,\qquad R=\Omega Q.
\]
The actual vector \(\Omega(C)T\) is zero at grade nine. Its zeroth and first payoffs give \(\int R=\int XR=0\). Define the polynomial divided-difference integral
\[
 M_R(Z)=\int_0^1 \frac{R(Y)-R(Z)}{Y-Z}\,dY .
\]
Then the stronger ordinary-measure ingress is the exact congruence
\[
 \boxed{D_s M_R+P^2\Omega_1\equiv0\pmod Q.}
\]
No root of \(Q\) is required simple, and nothing is divided by \(Q\) at a pair or dormant clock.

To see it, integrate the numerator quotient as a polynomial in \(Y\) of degree at most eight, using the ordinary paid scalar rule. This gives, in the rational function field of \(Z\),
\[
 M_R(Z)=\sum_i \frac{b_i R(c_i)}{c_i-Z}-R(Z)\sum_i\frac{b_i}{c_i-Z}.
\]
At a singleton \(x\), both \(P(x)\) and \(Q(x)=P(x)F_x\) are live, and ordinary \(b_x=P(x)^2/[D'(x)Q(x)]\). Therefore
\[
 b_x R(x)=\frac{\Psi(x)}{D_s'(x)},\qquad \Psi=P^2\Omega_1.
\]
Every other term of the first sum is killed by \(\Omega\) or cancels at the common carrier clock. Because \(\deg\Psi\le5<8=\deg D_s\), the elementary partial fractions of \(\Psi/D_s\) identify that first sum with \(-\Psi(Z)/D_s(Z)\). After multiplication by \(D_s\),
\[
 D_s M_R+\Psi
 =Q\left[D_s\Omega\sum_i\frac{b_i}{Z-c_i}\right].
\]
The bracket is a polynomial: after the exact opposite carrier shares cancel, every clock in the ordinary measure is a root of \(D_s\Omega\). A repeated factor only adds divisibility. This proves the congruence over a characteristic-zero coefficient field without a squarefree guard.

### Exact response and ordinary measure reconstruction

Once the profile and the scalar clocks are specified, the eight ordinary singleton weights are fixed by the preceding \(P^2/(D'Q)\) formula. Subtract those point masses from the ordinary rule. The remaining ordinary measure is supported on the **distinct labels** among \(p,r,\zeta,0,1\). Its pool at any such label is
\[
 \int\ell_\xi-\sum_{\text{singleton }x} b_x\ell_\xi(x),
\]
where \(\ell_\xi\) is the degree-at-most-four Lagrange polynomial on those distinct labels. This computes the residual even if \(Q\) vanishes at a pair; it does not treat an aliased dormant and pair share as individually resolved by clock data.

If a pair label has no dormant or endpoint read there, this earns its ordinary pool \(G=b_1+b_2\). Its two actual responses then solve a quadratic with sum \(S\) and product \(U\), with
\[
 \nu S-GU=\mu,\qquad \mu S-\nu U=\tau,\qquad
 G\mu-\nu^2=b_1b_2(f-g)^2\ne0.
\]
It determines the unordered pair of responses and then their two weights via the degree-one interpolation on \(f,g\). The actual physical ordering still has to be imposed. For any pair with a known calibrated state \(f\), even if aliased by the dormant row, the other response is
\[
 g=\frac{\tau-f\mu}{\mu-f\nu},\qquad
 \mu-f\nu=b_2g(g-f)\ne0 .
\]
The two ordinary weights follow from \(\nu,\mu\), since the coefficient determinant is \(fg(g-f)\ne0\). Every occupied full plateau has this calibrated first response. None of these reconstructions assumes \(P\ne0\) or \(Q\ne0\) at the pair.

## 3. Topologies and actual mixed middle restrictions

Write \(k\) for the number of active fifths and \(m\) for the active middle rows. The only counts are \((k,m)=(1,3),(2,2)\). Both-new gives internally distinct calibrated nonplateau triples \(3,6,7\) and \(11,12,15\) in physical indices, and their clocks avoid the corresponding own plateau. Thus:

* In \((1,3)\), orient the full plateau to the left, at \(a\), with the other plateau \(d\) having dormant physical 13. The second pair cannot be a third active hit at \(a\), and hence \(a=e\) is forbidden by the two-pair census. If it is at \(d\), it consists of physical 14 and one of \(3,6,7,8,9,10\). Otherwise it uses at most one of the left calibrated triple and at most one of the right triple, plus the possible middle rows. In particular there is no option of two nonplateau pair copies entirely on the same flank. The surviving half-half overlap \(h=e\) would specifically pair physical 3 and 15. The surviving single mixed \(h=d\) would specifically pair 3 and 14, with the dormant 13 at that same label. If the second pair is at \(d\), \((C-d)T\) has possible support only at physical \(1,4,5,17\). Its nonzero model and injectivity on the reflected first eleven therefore force its physical-17 read live, so \(Q(1)\ne0\).
* In \((2,2)\), both plateau pairs are already used at \(a,d\). All the other active labels are singleton, so \(h=e,a=e,h=d\) are impossible. There is one dormant middle \(\zeta\). Neither its clock being distinct from all active labels nor \(Q(\zeta)\ne0\) is assumed.

Use the true grade-four square-clock vectors \(V_L,V_R\) with models \(V_a=X^2(X-a)^2,\ V_b=(1-X)^2(X-d)^2\), and the strict grade-five primitives \(u=AV_L,\ v=A^\star V_R\) with models \(P_a=JV_a,\ P_b^\star=\bar J V_b\). Their respective products \(V_LV_R,uV_R,V_Lv,uv\) are supported in physical \(\{8,9,10\},\{9,10\},\{8,9\},\{9\}\). Their grades with the used clock insertions are at most ten. Mixed payment uses the actual reverse grade-five pure annihilator rather than ordinary reverse order eleven. Put
\[
 \begin{gathered}
 H=\int P_a V_b=\int V_aP_b^\star,\quad
 C_1=\int X P_a V_b,\quad C_2=\int X V_a P_b^\star,\quad J_0=\int P_a P_b^\star,\\
 I_j=\int X^j V_a V_b,\qquad 0\le j\le2 .
 \end{gathered}
\]

If the second pair in \((1,3)\) has both active copies in the middle, let its clock be \(p_0\), and let \(q_0\) be the remaining active singleton middle clock. The three \(V_LV_R\) moments give
\[
 I_2-(p_0+q_0)I_1+p_0q_0 I_0=0 .
\]
If the pair is at \(8,9\) then \(C_2=p_0H\) (the \(V_Lv\) payment is all at its clock); if at \(9,10\) then \(C_1=p_0H\). If the pair is at \(8,10\), the same shared-row calculation as in the [central repeated-pair identity](ERK11-NINE-SITE-CENTRAL-REPEATED-PAIR-IDENTITY.md) yields
\[
 (C_1-p_0H)(C_2-p_0H)=J_0\int (X-p_0)^2 V_a V_b .
\]
Here physical 9 is active; its true \(V_L,V_R\) values are used in both sides and cancel as products. One must not substitute dormant point models at physical 9. All these displayed identities are characteristic zero, without division.

Over an ordered field \(H,J_0,I_0\) are positive, \(0<C_i<H\), and \(I_0I_2-I_1^2>0\). These inequalities follow from rational positive-definite Gram matrices of the relevant polynomial squares on the interval or on the primitive simplexes (adding \(X,1-X\) proves the strict centroid bounds). Positive rational Gram pivots extend to all ordered fields. Thus in the adjacent case the repeated clock is strictly between 0 and 1. In every middle-pair case \(I_1-p_0 I_0\ne0\): otherwise the two-node relation contradicts the strict variance. In particular the singleton middle clock is uniquely
\[
 q_0=(I_2-p_0 I_1)/(I_1-p_0 I_0)
\]
and lies opposite the repeated clock relative to \(I_1/I_0\). The two pooled numerical \(b_i V_L(i)V_R(i)\) masses are both positive by integration of the squared Lagrange polynomials at these two nodes. In the outer-pair case \(p_0\) lies outside the closed interval with endpoints \(C_1/H,C_2/H\). Its quadratic is not identically zero: if all coefficients vanished, \(H^2=J_0I_0\) and \((C_1+C_2)/(2H)=I_1/I_0,\ C_1C_2/H^2=I_2/I_0\), contrary to strict variance and the nonnegative square of \(C_1-C_2\).

## 4. Dormant aliases: a genuine ordered exit

In \((2,2)\), the paid single-row product \(J_0=b_9u_9v_9>0\) over ordered fields implies \(u_9,v_9\ne0\). Since \(u_9=A_{98}V_L(8)\) and \(v_9=A^\star_{9,10}V_R(10)\), the dormant physical 8 cannot have clock \(0\) or \(a\), and dormant physical 10 cannot have clock \(1\) or \(d\). These assertions require no statement about the opposite-side read. At a dormant central row, if either actual square-clock read vanishes, the ordinary three quadratic moments reduce to the two distinct active outer clocks. The matching shifted primitive read puts \(c_8=C_2/H\) when \(V_L(9)=0\), or \(c_{10}=C_1/H\) when \(V_R(9)=0\); the other clock is again determined by the exact two-node relation and strict variance.

If **both** square-clock reads vanish at a dormant center then \(\zeta\in\{0,a\}\cap\{1,d\}\). Since \(a\ne d\), this is either \(d=0,\zeta=0\), or the reflected \(a=1,\zeta=1\). Write \(x=c_8,z=c_{10}\). Both shifts give \(Hx=C_2,\ Hz=C_1\). The degree-two \(V_LV_R\) mask vanishing at \(x,z\) gives
\[
 H^2 I_2-H I_1(C_1+C_2)+I_0 C_1C_2=0
\]
without division or ordering. For \(d=0\), the exact rational numerator after multiplying by \(871363785600000\) is
\[
 S(a)=680625a^6-2214300a^5+2982540a^4-2140908a^3+
        869470a^2-190365a+17640.
\]
The reflected chart gives the same polynomial in the reflected width. Over an ordered field it is strictly positive: the homogeneous cleared substitutions \(a=-t,\ a=t/[2(1+t)],\ a=(5+8t)/[10(1+t)],\ a=(4+t)/5\) have **all** coefficients positive for \(t\ge0\). They cover, respectively, the negative exterior, \([0,1/2)\), \([1/2,4/5)\) and the positive exterior. The standalone standard-library exact replay derives all six degree-two integrals, the sextic and the positive coefficients from rational integration. The adjacent core Lean checks the local pool, variance, cleared centering and integer substitution identities. The double-zero dormant center is therefore excluded over ordered fields, while over unordered characteristic zero it has the exact sextic constraint. The double-zero exit actually needs only distinct plateaus, the both-new mixed payments and a response-zero central stage; the other two inner clocks do not have to be singleton for that particular sextic argument. The overall twelve-active case remains open.

The [portable Lean scalars](../lean/RKCert/ReviewedNative/ERK11TwelveActivePairGate.lean)
check on all four requested core versions. See the [exact replay and receipts](erk11-ten-twelve-active-audit/).
