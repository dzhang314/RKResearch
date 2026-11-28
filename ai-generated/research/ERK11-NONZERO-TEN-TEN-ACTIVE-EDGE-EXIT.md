# Ten active labels: the ten-active dormant edge is impossible

**Scope.** Continue the maximal all-live, half-clock, two-carrier, two-new-boundary order-eleven equality problem, with ten active clock labels and nonzero first pooling, as in the [ten-label overlap note](ERK11-NONZERO-FIRST-POOL-TEN-LABEL-OVERLAPS.md). Here exactly ten noncarrier rows have nonzero response. This excludes the remaining dormant middle row at physical **8 or 10** over characteristic zero. The physical-9 placement is separate. We assume neither ordering nor reverse ordinary order eleven. No unrestricted stage interval changes.

## 1. The support and rank-one moments are literal

Continue with \(F\) the forward grade-three pure response, \(a,d\) the two plateaus, \(h=a/2,\ e=(1+d)/2\) their half-clocks and \(b=1-d\) the reflected width. Write \(C=\operatorname{diag}(c_i)\) and \(s\) for the two-carrier indicator at clock \(\theta\). All ten active rows are singletons. Removing the two possible fifth active rows does not change the distinct active clock count, so the census forces both fifths dormant and exactly two of the three middle rows 8–10 active. Call the remaining middle physical row \(i\), at clock \(\zeta\).

The pooled interpolation polynomials \(P,Q_*,B\) have degrees at most \(1,4,7\), respectively. On every active singleton \(PB=Q_*^2\), and this is an identity since there are ten distinct roots and degree at most eight. Therefore \(K=Q_*/P\) is a nonzero cubic (degree at most three) and gives the true response on each actual active row. The literal grade-three vector
\[
 T'=K(C)\mathbf1-F-K(\theta)s
\]
has scalar model \(K\), and is supported only at physical \(1,5,i,13,17\). At each of these rows its read is \(K\) of its clock.

**All support guards needed below hold without real-root arguments.** Both orientations read their grade-five spaces injectively on the first eleven rows. In the forward direction the possible reads of \(T'\) there are only physical \(1,5,i\). If fewer than three distinct clock labels had nonzero reads there, a nonzero polynomial of degree at most two would mask all of them and produce an actual grade-five vector zero on the first eleven. It cannot be the zero vector, because its model is that polynomial times nonzero \(K\), and grade-five model separation holds. The reverse direction applies the same argument at \(17,13,i\), because \(T'\) and its clock multiplies are actual there from the common low-grade pure spaces. Thus all five named readings are live, \(\zeta\notin\{0,1,a,d\}\), and \(a\ne0,d\ne1\). Also \(a,h,d,e\) are pairwise distinct because those four calibrated active rows are singleton. No extra restriction \(a\ne1\), \(d\ne0\), or exclusion of an alias of \(\zeta\) with an unrelated active clock is needed.

Put \(w=X(1-X)\) and
\[
 m_j=\int_0^1 X^j w(X)(X-a)(X-d)K(X)\,dX\qquad(0\le j\le3).
\]
The actual vector \(C^j C(1-C)(C-a)(C-d)T'\) has grade \(7+j\le10\) and is supported only on \(i\). Therefore
\[
 m_j=b_i \zeta^j w(\zeta)(\zeta-a)(\zeta-d)K(\zeta)
     =\zeta^j m_0,\qquad m_0\ne0 .
\]
In particular \(m_0m_2-m_1^2=0\) and \(m_0m_3-m_1m_2=0\). The arithmetic exit below uses these denominator-free conditions; it does not require dividing the candidate equations by \(m_0\).

## 2. Paid inverse-Gram and primitive contacts

Let \(V_L,V_R\) be the actual grade-four square-clock vectors with models \(V=X^2(X-a)^2,\ W=(1-X)^2(X-d)^2\); write \(p=AV_L,\ r=A^\star V_R\) with primitive models \(P_a=JV,\ P_b^\star=\bar J W\). By strictness \(p=0\) through physical 8 and \(r=0\) from physical 10. The actual grade-five vectors
\[
 L_\zeta=C(C-a)T',\qquad R_\zeta=(1-C)(C-d)T'
\]
are anchored through the first six and last six physical rows respectively. Their scalar models are \(X(X-a)K\) and \((1-X)(X-d)K\). The mixed grade-five payment pairs them with the other orientation's actual grade-five space by ordinary order eleven and the known reverse grade-five pure annihilator; it does not assume ordinary reverse order eleven. If \(i=8\), the product \(p R_\zeta\) is literally zero: \(R_\zeta\) can only read physical \(1,5,8\), and \(p\) vanishes there. Hence the true scalar condition is
\[
 I_L=\int_0^1 (1-X)(X-d)P_a(X)K(X)\,dX=0.
\]
For \(i=10\), use \(L_\zeta r\) instead and reflect. The reflection uses only the mixed payment and reverses the exact calibrated data, so is valid at order ten of the transposed tableau.

Every one of the three calibrated nonplateau hits at either end is a singleton. With \(\kappa\ne0\) the reflected response scale, this gives
\[
 K(a)=-a^2/2,\quad K(h)=-K(a)/4,\quad
 \kappa K(d)=-b^2/2,\quad K(e)=-K(d)/4.
\]
The left extra clocks in physical 6–7 have hull proportional to
\((K-X^2(a-X)/a)/(X-h)\). Indeed the two extras and \(h\) are three distinct roots of the cubic numerator, and its nonzero value \(K(a)\) ensures it is not zero identically. Likewise the two right extras' hull is proportional to \(((1-X)^2(X-d)/b-\kappa K)/(X-e)\), of genuine degree two because the numerator has three distinct roots and value \(-\kappa K(d)\ne0\) at \(d\). In the [paid off-diagonal first inverse-Gram contact](ERK11-LIVE-TRIPLE-EIGHT-CLOCK-HANKEL.md#3-literal-derivative-contact-of-rows-7-and-11), evaluating these hulls at \(a,0\) and \(d,1\), respectively, yields the exact width/profile condition
\[
 \mathcal C(K)=K(a)K(d)+T_4(a)K(0)K(d)+T_4(b)K(a)K(1)
                 +U_{4,4}(a,b)K(0)K(1)=0.
\]
The only row scaling factors canceled are nonzero: the factors \(2/a\) and \(2\kappa/b\), and the leading coefficients of the actual hulls.

## 3. A two-coefficient profile and the exact projections

Use the two degree-at-most-three polynomials
\[
\begin{aligned}
 A(X)&=(X-d)(X-e)\,[4(h-d)(h-e)(X-h)+(a-d)(a-e)(X-a)],\\
 B(X)&=(X-a)(X-h)\,[4(e-a)(e-h)(X-e)+(d-a)(d-h)(X-d)].
\end{aligned}
\]
By the four distinct calibrations they span all cubics with the two half relations, with \(A(a)\ne0,\ B(d)\ne0\), and \(K\) is proportional to \(A+tB\) for some \(t\ne0\). Both coefficients are live by \(K(a),K(d)\ne0\). The \(m\)-minors, \(\mathcal C\), and (as applicable) \(I_L=0\) are invariant under this nonzero scaling. Let \(\ell_0,\ell_1\) be the two primitive reads \(I_L\) of \(A,B\).

If exactly one \(\ell_j\) vanishes, the edge primitive equation contradicts the two live coefficients. If both are live, replace \(K\) projectively by \(\ell_1 A-\ell_0B\), and divide each moment polynomial by its exact common factor, up to rational scale,
\[
 G=(a-d)(2a-d-1)(a-2d)(a-d-1).
\]
All four factors are live by the distinct calibrations. Let \(N_j\) be these normalized moments. Use the two marks \(N_0N_2-N_1^2,\ N_0N_3-N_1N_2\) and the normalized contact obtained by dividing \(\mathcal C(\ell_1 A-\ell_0B)\) by \(a(d-1)G^2\). The divisions are polynomial identities and are checked exactly. The resultants in \(d\) of the first mark with each of the other two have degrees **228, 250** in \(a\) with gcd proportional to \(H_{19}(a)^4\), where \(H_{19}\) is irreducible of degree 19. Over the exact field \(\mathbb Q[a]/H_{19}\), the three univariate \(d\) marks have gcd the **square** of the monic linear gcd of \(\ell_0,\ell_1\). Thus any root of the three marks already has both primitive coefficients zero, contrary to this case. The exact rational quotient-field replay checks the repeated factor, not merely its radical modulo a prime.

If both \(\ell_j=0\), their exact \(d\)-resultant has degree 44 with distinct irreducible factors of degrees \(1,6,6,6,6,19\). On each of the five smaller factors the exact \(d\)-gcd is linear and forces a forbidden calibration collision. On the remaining \(H_{19}\) it is also linear, with no such assumed collision. The degree-19 polynomial retains full degree and is irreducible modulo 31, and at least one of the two primitive coefficient polynomials retains its degree in \(d\) at that place. Thus an algebraic \(a,d\) candidate is integral sequentially and the reduction of \(d\) is the single common linear root. With this substitution, the two rank-one moment marks and \(\mathcal C(A+tB)\) are genuine quadratic polynomials in \(t\), all with degree preserved at 31. This earns integrality of any root \(t\). Their three reduced quadratics have unit gcd in \(\mathbb F_{31^{19}}\). No solution remains.

This is a coefficient lift in the finite extension determined by the exact projections, not a reduction of an unverified tableau. The standalone replay computes the rational and finite-field certificates, including literal zero comparisons for field scalars. The adjacent Lean file checks the denominator-free scalar rank-one, edge-kernel, and shared-row factorizations over any commutative ring. The tableau support and field projection arguments are mathematical.

The [exact replay outputs and Lean receipts](erk11-ten-ten-active-audit/)
document the checks. The [portable scalar identities](../lean/RKCert/ReviewedNative/ERK11TenActiveMomentGate.lean)
pass on all four requested core Lean versions; the tableau exclusion is mathematical.
