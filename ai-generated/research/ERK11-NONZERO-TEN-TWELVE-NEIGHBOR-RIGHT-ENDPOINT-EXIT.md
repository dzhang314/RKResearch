# The sole right profile endpoint zero is impossible at the neighboring singleton

**Scope.** In the fixed ordered, all-live, half-clock two-carrier \(17\)-stage ERK11 chart with both seventh boundaries new, \(q=10,n=12\), both full plateau pairs, and sole dormant row 9 sharing the active physical row 8 singleton \(s=c_8\notin\{0,1,a,d\}\), this excludes the actual branch \(Q(1)=0\). The \(K_0=0\) curve is separately [closed](ERK11-NONZERO-TEN-TWELVE-NEIGHBOR-K-ZERO-COMPLETE.md), so use \(K_0\ne0\). This is the **right** endpoint in the **same** \(s=c_8\) orientation; it is not the reflection of the earlier \(Q(0)=0\) result. Reflection transfers it to \(Q(0)=0\) for \(s=c_{10}\). Combined with the [left endpoint exclusion](ERK11-NONZERO-TEN-TWELVE-NEIGHBOR-LEFT-ENDPOINT-EXIT.md), both endpoints must be live in any remaining neighboring layout. No unrestricted stage count changes.

## True width equations and all leading losses

The [anchored endpoint read](ERK11-NONZERO-TEN-TWELVE-NEIGHBOR-ENDPOINTS-AND-FIXED-RANK.md) gives the width-measured right primal profile \(Q_*=k_R/(X-d)\), \(k_R(X)=[L_9,r_X^{\rm ev}]\), and \(Q'(1)\ne0\). Since \(Q(0)\ne0\), the actual left product and \(P_*\) are measured by the full coordinate inverse; its relative scale at the right half determines the right product via the simple right root. None of this uses a fixed moment or raw affine pivot.

Let \(A=E_R\) be the cleared exact condition \([L_9,r_d^{\rm ev}]=0\), and \(B\) the true opposite **left** temporal equation on this measured profile. They have bidegrees \((21,21),(58,55)\) as in the [finite mask proof](ERK11-NONZERO-TEN-TWELVE-NEIGHBOR-INDIVIDUAL-MASK-FINITENESS.md). The coordinate restrictions \(a=1\), \(d=0\) each give exact univariate joint gcd one. The leading coefficient \([b^{21}]A\) has exact irreducible factors of degrees 2,4,15. Its quadratic has discriminant \(-15\). For the quartic and degree-fifteen fields, the exact \(b\)-degrees are \((20,54)\) for \(A,B\). The simple \(a\)-places \((p,a)=(29,8),(41,24)\) retain degree 20 of \(A\) and give entire residue \(b\)-gcd one, excluding each whole finite leading-loss fiber. No degree-21 assumption is made at those exact widths.

The normalization \(Q_*\) cannot have degree one. Otherwise \(k_R\) is proportional to \((1-X)(X-d)\). Pair against all left anchored models \(X(X-s)(X-a)f(X)\), \(\deg f\le2\); the actual row \(L_9=\ell_s+\epsilon\ell_a\) kills them. Thus the monic cubic \((X-a)(X-d)(X-s)\) is orthogonal to degrees at most two for \(X(1-X)\), giving the normalized \(14X^3-21X^2+9X-1\). The same six exact root allocations as in the left proof contradict \(C_2-sH=0\). This use of the measured \(s=C_2/H\) is in the original orientation. The reduced ghost modulus below is therefore not constant.

## Actual left plateau and reduced ghost

Use the true row-scale in \(k_R\). Since \(R_9=r_s^{\rm ev}+\eta r_d^{\rm ev}\) and \(k_R(d)=0\), the reciprocal diagonal yields \(k_R(s)=1/b_9\). Put \(\omega=X(1-X)(X-a)(X-d)\) and \(\rho=b_9\omega(s)\). Then
\[
 \rho Q_*(s)=s(1-s)(s-a).
\]
Put \(\Omega=-\omega\), \(R=\Omega Q_*=X(X-1)(X-a)k_R(X)\), and \(M_R(Z)=\int(R(X)-R(Z))/(X-Z)\). The actual anchored read \(L_9=\ell_s+\epsilon\ell_a\) gives
\[
 M_R(1)=s(s-a),\qquad M_R(a)=-s(1-s)-\epsilon a(1-a).
\]
For instance \(R(X)/(X-1)=X(X-a)k_R(X)\), paired against \(L_9\); at \(a\) use \(-X(1-X)k_R\). Thus \(M_R(a)-\rho Q_*(s)/(a-s)=\epsilon a(a-1)\), and the [compact ordinary plateau law](ERK11-NONZERO-TEN-TWELVE-NEIGHBOR-AFFINE-PLATEAU-LAW.md) simplifies using \(a,1-a\ne0\):
\[
 \gamma\lambda_*(q-fp)=\epsilon f(t-fq).
\]
Here \(p=P_*(a)\), \(q=Q_*(a)\), \(t=B_{\tau,*}(a)\), \(f=-a^2/2\), and \(\gamma\) is the live common actual \(P,Q\) scale. The two genuine left responses \(f,g\) are nonzero and distinct, so \(\delta=q-fp\ne0\), \(t-fq=g\delta\). Hence \(\gamma\lambda_*=\epsilon f g\), in particular **\(\epsilon\ne0\)**. The unmultiplied law covers \(P_*(a)=0\); that value is not declared a universal live guard.

Let \(r=Q_* /(X-1)\). In the ordinary ghost congruence, both numerator terms
\[
 A_{\rm gh}=D_sM_R-\rho Q_*(s)D_s/(X-s),\qquad
 B_{\rm gh}=P_*^2 X(X-1)
\]
vanish at \(X=1\), using the exact \(M_R(1)\) read. The whole identity reduces exactly to
\[
 \widetilde A+\gamma\widetilde B=0\bmod r,\quad
 \widetilde A=A_{\rm gh}/(X-1),\quad
 \widetilde B=P_*^2 X .
\]
The modulus is nonconstant; \(r(0)\ne0\) by the opposite actual endpoint. The identity \(P_*B_{\tau,*}-Q_*^2=\lambda_* D_s\), \(\lambda_*\ne0\), and nonzero first pool at all active singletons imply \(P_*,Q_*\) are coprime. Thus \(\widetilde B\) is invertible modulo the true-degree \(r\). No chosen coefficient of the original vanishing normalization row is assumed nonzero, and a dropped quartic leading coefficient is not interpreted as a contradiction.

With the homogeneous \(D_\lambda,L_\lambda\) of the compact plateau proof, use the true multiply-only form
\[
 U+\gamma V=0,\quad
 U=-\epsilon f(D_\lambda q\delta+L_\lambda D_s(a)),\quad V=L_\lambda p\delta .
\]
The all-width necessary condition is \(V\widetilde A-U\widetilde B=0\bmod r\). Neither a pivot at \(p\) nor a quartic \(Q_*\) is required for this implication; the specific active residue exit below earns its cubic residue modulus.

## Exact width factorization and complete finite fibers

For primitive integer representatives of \(A,B\), the absolute Sylvester coefficient bound is \(\|A\|_1^{55}\|B\|_1^{21}\), and the degree bound is \(21\cdot55+58\cdot21=2373\). The bound has 12423 bits. By 208 distinct degree-retaining prime resultants and a 12481-bit combined modulus strictly exceeding twice the bound, bounded CRT recovers the exact integer resultant of degree 2359. Exact factorization yields
\[
 1^{28},\ 2^{10},\ 2^{12},\ 4^4,\ 8^3,\ 8^{119},\
 12^3,\ 12^3,\ 12^3,\ 15^4,\ 20^3,\ 60^3,\
 111,\ 150,\ 258,\ 368 .
\]
The linear factor is \(a=0\); the two quadratics have negative discriminants. The quartic and degree-15 factors belong to the independently checked \(A\)-leading loss.

Each small factor in this table divides the indicated **exact** guard norm \(\operatorname{Res}_b(A,G)\). At the indicated simple \(a\)-place the entire residue gcd of \(A,B\) is the same linear polynomial as the entire residue gcd of \(A,G\); \(A\) retains degree 21 and has unit derivative at the root. The exact guard norm supplies an integral guard-zero root, and Hensel uniqueness in \(A\) identifies that root with every exact candidate at this embedding.

| Degree, multiplicity | Lost guard \(G\) | \((p,a,b)\) | Guard norm degree |
|---|---|---|---:|
| 8,3 | \(H\) | \((19,12,9)\) | 84 |
| 12,3 | \(z_D\) | \((37,3,18)\) | 167 |
| 12,3 | measured \(U\) width guard | \((29,28,23)\) | 246 |
| 12,3 | \(J_0\) | \((17,3,2)\) | 82 |
| 20,3 | \(s-d\) | \((29,5,12)\) | 104 |

The octic of multiplicity 119 is a genuine higher residue fiber, not a selectable simple \(b\). In its exact \(a\)-field the linear subresultant with \(H\) measures an \(H\)-zero root of \(A\). The companion verifies the root exactly and removes **all seven exact copies** of that linear factor in \(A\). The residual \(b\)-degree 14 is retained at \((p,a)=(19,13)\), and its complete gcd with \(B\) is one. Thus every exact root is either killed by the live \(H\) guard or excluded from the residual fiber.

The degree-60, 111, and 150 factors all divide the exact **diagonal numerator \(\alpha'\)** guard norm of degree 979. Bounded CRT for that norm uses 85 primes (5094-bit bound, 5101-bit modulus). The common simple places are \((23,16,16),(61,3,34),(19,2,14)\) with \(A\)-derivative residues \(15,48,12\); both whole gcds are the same linear polynomial at each place. Thus the live \(\alpha'\) vanishes in each exact field. The degree-60 factor is identified by exact divisibility, not by the degree of a different moment or \(J_0\) norm.

## Shared degree-258 field: why the calibrated transfer is valid

The degree-258 factor is the **same exact** irreducible polynomial as the degree-258 factor in the left endpoint projection. Also it divides the degree-626 exact resultant of the two endpoint width equations \(E_L,E_R\). At \((41,10,28)\) the exact \(a\)-factor is simple and both \(E_L,E_R\) retain full \(b\)-degrees \(14,21\). The three complete residue gcds \(E_L/E_R,\ E_L/T_L,\ E_R/T_R\) are all \(b-28\) (here \(T_L,T_R\) mean the respective opposite temporal width equations), and the two endpoint width derivatives are \(35,11\). Existence from the cross resultant and successive Hensel uniqueness in the two endpoint width polynomials show that any actual right \(b\) is also the exact \(b\) from the **formal left endpoint width system**. The cross resultant alone is only an existence test, not root identity.

Use the earlier independently verified degree-258 exact \([P_L(0)=0]\) guard in that formal left width system. All its formal shape denominators are units at the shared place. Its left hull \(B_L^{\rm form}\) has value \(21\bmod41\) at 0, hence no root there. Its \(Q_L^{\rm form}=Xr_L\) and nonzero \(P_L^{\rm form}=cX\), \(c\ne0\), satisfy the left calibrated divisibility by \(B_L^{\rm form}\) from their **algebraic** basis reconstruction; no actual \(Q(0)=0\) is inferred in the present chart.

To transfer that guard, let \(K_4\) denote the common corrected kernel on polynomials of degree at most three for the four rows \(j=0,1,2,3\). The formal \(r_L\) belongs to \(K_4\): its true-width primal \(k_L=(X-a)Xr_L\) pairs with \((1-X)(X-d)X^j\) by \(R_9\)'s simple eval, giving \(\int\omega X^j r_L=\rho s^j r_L(s)\). The actual right profile \(Q_R=(1-X)r_R\) gives the same identity for \(r_R\) by its primal \(k_R=(X-d)(1-X)r_R\) and the opposite anchors \(X(X-a)X^j\). These formulas use only degrees at most five and the measured reciprocal diagonal. The kernel \(K_3\) of the first three rows on degree at most four has dimension two by full moment rank. Each \(r\in K_4\) has both \(r,Xr\in K_3\). If \(\dim K_4\ge2\), it would equal \(K_3\) and make it nonzero and \(X\)-invariant, contrary to maximal polynomial degree. Thus \(r_L,r_R\) are proportional.

Since \(X\) is coprime to the formal left hull, \(B_L^{\rm form}\mid Q_L^{\rm form}-P_L^{\rm form}f_L\) implies \(B_L^{\rm form}\mid r_L-c f_L\). Therefore \(Q'=(1-X)r_L,\ P'=(1-X)c\) still satisfy the left calibrated divisibility with the same formal hull. Here \(Q'\) is proportional to the actual right \(Q_R\), which is live at 0. The left full coordinate inverse on that live endpoint uniquely measures \(t_L\) and its \(P\) for any such calibrated representation. Consequently the actual \(P\) is proportional to \(P'\), so \(P(1)=Q(1)=0\). This is forbidden by the live \(\lambda_* D_s(1)\) in the third-pool relation (1 cannot be an active singleton when its \(Q\) read is zero). No equality of the two distinct endpoint profiles was assumed.

## Genuine compact plateau contradiction in degree 368

At the simple \(a\)-place \((53,15,42)\), \(A\) retains \(b\)-degree 21 and the entire residue \(b\)-gcd is linear with root 42. This accounts for all exact \(b\) via its unit leading coefficient. Every measured width and profile denominator needed here is a unit. Both products have residues \(t_L=33,t_R=47\). In increasing order the actual normalized profiles and the two oriented hulls are
\[
 P_*=(49,27),\quad Q_*=(35,43,2,27,52),\quad
 B_L=(48,16,4,1),\quad B_R^{\rm oriented}=(31,12,6,1).
\]
The reduced modulus \(r=Q_* /(X-1)\) retains a cubic leading unit. The left plateau has \(\epsilon=32\), \((D_\lambda,L_\lambda)=(45,4)\), giving the compact \((U,V)=(45,6)\bmod53\). The exact compatibility remainder is instead \(44+7X+48X^2\bmod53\). Thus every candidate of this final large factor fails.

All 16 factor fields, both coordinate and all leading fibers, and the normalization-only cases are accounted for. No bivariate gcd by itself is used as a root exclusion: each exact projected factor has a whole univariate \(b\)-fiber check or independently forbidden \(a\)-field. The ordered-field hypotheses earn the inherited width signs and live guards; the subsequent field and arithmetic steps are characteristic zero with those guards.

The checkpoint-free source uses python-flint 0.9.0 and SymPy 1.14.0. Its default replay rebuilds the two primary width resultants and the shared \(\alpha'\) norm. It depends on the earlier exact left degree-258 \(P(0)\) guard; the flag \(\texttt{--reprove-left-guard}\) also rebuilds that earlier guard norm. The primary CRT (208 primes; 193.796s reference) and the composed exact audit (31.701s after reusing the two hash-checked previously exact width norms) were run separately. This is an exact arithmetic and paper tableau proof, not a compiled full Lean theorem.
