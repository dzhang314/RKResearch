# Ten active labels: the complete eleven-active flat-pair exit

**Scope.** In the [ten-label nonzero-first-pool chart](ERK11-NONZERO-FIRST-POOL-TEN-LABEL-OVERLAPS.md) of the all-live, half-clock, two-carrier, two-new-boundary order-eleven equality case, suppose exactly eleven noncarrier rows have nonzero response. This excludes the **entire eleven-active chart** over characteristic zero, including all surviving placements of its flat opposite-weight pair. It is not an exclusion of ten, twelve or thirteen active rows, and no unrestricted stage interval changes. This proof does not use ordering or reverse ordinary order eleven.

## 1. The two half-calibration conditions

Continue with the earlier common grade-three response \(F\), cubic pooled profile \(K\), left width \(a\), right width \(b=1-d\), half-clocks \(h=a/2,\ e=(1+d)/2\), and scale \(\kappa\ne0\) such that the reflected response is \(\kappa F\). The two fifths are dormant. There is exactly one repeated active pair with common response, opposite ordinary weights, and clock distinct from \(0,1,a,d\). Both plateau fourths are singleton, so
\[
 K(a)=-a^2/2,\qquad \kappa K(d)=-b^2/2.
\]
The inherited overlap exits in particular give \(a\ne d,\ a\ne e,\ h\ne d,\ h\ne e\). The cubic is nonzero and the scalar-clock cancellation of the flat pair gives
\[
 (X-a)(X-d)K(X)\in\operatorname{span}\{R_4,R_5\},
\quad
 R_4=42X^4-84X^3+56X^2-14X+1,\quad
 R_5=132X^5-330X^4+300X^3-120X^2+20X-1 .
\]
Since \(R_4,R_5\) have no common root (checked by exact polynomial gcd), the polynomial
\[
 R_a(X)=R_5(a)R_4(X)-R_4(a)R_5(X)
\]
is nonzero and spans the pencil members vanishing at \(a\). Hence the actual pencil vector is a live multiple of \(R_a\). In particular
\[
 \Phi(a,d)=R_a(d)/[-2(d-a)]=0;
\]
the quotient expression is an exact polynomial of bidegree \((4,4)\).

If \(h\) is a singleton, its forward measurement gives \(K(h)=a^2/8=-K(a)/4\). Write
\[
 L(a,d)=
 \frac{2}{a}\left[4(a-d)R_a(a/2)+(a/2-a)(a/2-d)R_a'(a)\right].
\]
The two identities \(R(h)=(h-a)(h-d)K(h)\) and \(R'(a)=(a-d)K(a)\) for \(R=(X-a)(X-d)K\) prove \(L(a,d)=0\), using the live scalar between \(R\) and \(R_a\). The quotient by \(a\) is an exact symbolic division, with \(L\) integral of bidegree \((9,1)\). If \(e\) is a singleton, the reflected measurement gives \(K(e)=-K(d)/4\), and the reflected necessary equation is \(Q(a,d)=L(1-d,1-a)=0\), bidegree \((1,9)\). Reflection preserves the Jacobi pencil since \(R_4(1-X)=R_4(X), R_5(1-X)=-R_5(X)\).

## 2. When both halves are singleton

The two exact primitive resultants in \(a\), of \((\Phi,L)\) and \((\Phi,Q)\), both have degree 40 in \(d\). Their gcd is the diagonal octic
\[
 W(d)=\Phi(d,d)=2772d^8-11088d^7+18648d^6-17136d^5+9360d^4
                    -3096d^3+604d^2-64d+3.
\]
Therefore an actual candidate has \(W(d)=0\). The three polynomials \(\Phi,L,Q\) all divide exactly by \(a-d\) over \(\mathbb Q[d]/W(d)\), as checked by substituting \(a=d\) and taking exact remainders. The true \(a\ne d\) means the three resulting quotients must vanish simultaneously. In particular no apparent diagonal annihilation in the width projection is treated as a real candidate.

The octic retains full degree and is irreducible at 23. Thus the actual algebraic \(d\) is integral there and the coefficient residues belong to \(\mathbb F_{23^8}\), up to Frobenius. The reductions retain their full degrees in \(a\), before and after division by the monic \(a-d\). In particular \(a\) is algebraic and integral at the place, by the retained leading coefficient of the degree-three quotient of \(\Phi\). The three reduced quotients have unit gcd, impossible. No ordering of widths has been used. This closes every pair placement when both halves are singleton, including one or both copies in the physical middle.

## 3. When a half is in the pair

By reflection it is enough to take \(h\), at physical 3. The half \(e\) is a singleton because the common-half overlap is already excluded. The inherited characteristic-zero pair straddle then puts the second copy at physical \(j=9,10,11,\) or \(12\): rows 14 and 15 have the distinct singleton clocks \(d,e\), and the other late rows are not active. Its literal forward response is the same \(a^2/8\) as physical 3.

Now \(Q=q_1(d)a+q_0(d)\) vanishes, along with \(\Phi\). Its exact primitive resultant against \(\Phi\) in \(a\) has distinct irreducible factors of degrees \(8,8,24\). The replay checks \(q_1\) is coprime to the entire resultant, so \(a=-q_0(d)/q_1(d)\). The diagonal octic \(W\) forces \(a=d\) by the exact remainder of \(q_0+d q_1\); the other octic forces \(a=e\) by the exact remainder of \(2q_0+(1+d)q_1\). Both are forbidden literally. Denote the surviving degree-24 factor by \(H_{24}\).

Over every residue component of \(H_{24}\) at 23 (degrees 1, 4, 7, 12), the replay checks \(q_1\) is a unit, that \(R_a\) retains degree five and \(K_0=R_a/[(X-a)(X-d)]\) has live evaluations at \(a,d\). Hence the true expressions
\[
 K=\frac{-a^2}{2K_0(a)}K_0,\qquad \kappa=\frac{-b^2}{2K(d)}
\]
are integral with every stated divisor a unit. The known forward and reverse nonplateau response profiles are
\[
 L_f(X)=X^2(a-X)/a,\qquad L_r(X)=(1-X)^2(X-d)/b .
\]

* If \(j=11\) or \(12\), its own reversed calibration at the extra clock \(h\) would give \(L_r(h)=\kappa a^2/8\). The exact residue difference is nonzero in all four factors of \(H_{24}\).
* If \(j=9\) or \(10\), both right extras are singleton. Together with the right half \(e\), they are the three distinct roots of \(L_r-\kappa K\), whose degree is exactly three by the residue check. Thus the two right extra clocks have hull proportional to \(A_R=(L_r-\kappa K)/(X-e)\). The two left extras remain singleton and are distinct roots of the genuine cubic \(g=K-L_f\) (do not assume \(g(h)=0\)). Write \(g=(X-u)A_L\), with \(A_L\) proportional to the actual two left extras' hull; this defines the omitted root \(u\) in the coefficient field. It is integral at the same place because the replay checks full degree three for \(g\).

For the two middle placements, use the genuine off-diagonal [first inverse-Gram contact](ERK11-LIVE-TRIPLE-EIGHT-CLOCK-HANKEL.md#3-literal-derivative-contact-of-rows-7-and-11) in physical rows 7 and 11, with \(R_0=A_R(d),\ R_1=-A_R(1)\), \(L_0=A_L(a),\ L_1=-A_L(0)\). The two row scalings from possibly nonmonic hulls are live and do not affect its zero. Put
\[
 J_0=R_0+T_4(b)R_1,\quad J_1=T_4(a)R_0+U_{4,4}(a,b)R_1.
\]
The contact becomes \(J_0A_L(a)-J_1A_L(0)=0\). The exact equalities \((a-u)A_L(a)=g(a)=K(a)\) and \((-u)A_L(0)=g(0)=K(0)\) now give the necessary affine mark
\[
 J_0K(a)u+J_1K(0)(a-u)=0 .
\]
There is no division by \(u\), \(a-u\) or the affine leading coefficient. At each of the four \(d\) residue components, the affine mark and the full cubic \(g(u)\) have unit gcd. Thus no \(u\) is possible. The same proof applies with the two ends reflected. A lone derivative row at 11 would give only an identity here after factoring off \(e\); the proof genuinely uses the off-diagonal two-front contact.

The arithmetic replay computes the exact integer resultants and forbidden component congruences, then checks irreducibility or factor degrees, all necessary leading terms and divisors, and the finite extension field gcds. It uses explicit scalar zero comparisons. These are coefficient-ring lifts from algebraic normal forms; nothing assumes an unknown tableau can be reduced without first proving integrality. The adjacent Lean file verifies the half-calibration and omitted-root identities over a commutative ring. The paid RK and finite-place ingress remain mathematical.

The [kernel logs and exact replay](erk11-ten-eleven-active-audit/) record
the arithmetic receipts. The [portable contact identities](../lean/RKCert/ReviewedNative/ERK11TenLabelFlatPairContactGate.lean)
pass on all four requested core Lean versions; the tableau proof is mathematical.
