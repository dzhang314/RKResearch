# Disjoint two-later-singleton prefixes: all low/low off-diagonal phases are impossible

Assume the [disjoint (1,1) seven-clock setting](../sdirk-eight-all-dirty-seven-quadratic-both-s-both-two-s-disjoint-scale/README.md): strict ten-stage SDIRK, ordinary order at least eight over a characteristic-zero field, all ten physical quadratic defects nonzero, both physical endpoints singleton, exactly seven distinct clocks. Each actual first-three prefix has one later S and one later D; their observed D labels differ. Take low-law phases (A3 or star) on both ends and **unequal normalized later S offsets** \(a\ne b\). This packet excludes A3A3, A3S (or SA3 by the actual weighted mirror), and SS on that off-diagonal branch. It does not assert anything about the same-phase diagonal or a high-law arm.

## Exact rational two-clock frame and actual paid residuals

Use \(y=x-1\), endpoints \(0,H\), \(m=(H+2)/2\), later S sites \(s=a\) and \(t=H-b\) in original coordinates. The observed D labels are
\(p=\delta_f(a)\), \(q=H-\delta_r(b)\), where \(\delta(z)=2z\) for A3 and \(2-z\) for star. Write \(f_p,\rho_q\) for their paid original and normalized reverse defects; at actual later S the defects in their own normalization are \(f_s=k(a)/2,\rho_t=k(b)/2\), \(k(z)=1+2z-z^2\). A3 pays its actual third D defect \(N(z)/(2D(z))\) using the [true tap formulas](../sdirk-eight-all-dirty-seven-quadratic-both-s-both-two-s-disjoint-rank/README.md), and either genuine star order has equal D and S defects. Thus pair evaluation does not permute the original tableau.

For the live off-diagonal chart the [rank-safe rational determinant reduction](../sdirk-eight-all-dirty-seven-quadratic-both-s-both-two-s-disjoint-scale/README.md) gives
\[
 b=\frac{(2-a)Q(H)-P(H)}{P(H)a+Q(H)},
 \qquad P(H)a+Q(H)\ne0.
\]
The defined \(P,Q\) are the quartics in that packet and \(Q^2-P(P-2Q)\ne0\) is a genuine nonzero guard. The [low/low boundary proofs](../sdirk-eight-all-dirty-seven-quadratic-both-s-both-two-s-disjoint-low-boundaries/README.md) exclude \(H=2\) and loss of the \(R\)-scale line. Hence use
\[
 \lambda=N_0/M_0,\qquad N_0-M_0=(a-b)H(H-2),\quad
 R_2=\frac{(a-2)(b-2)H-a-b+4}{2M_0},\quad
 R_1=\frac{\lambda-1}{2H}-H R_2 .
\]
The \(R_2\) expression is the paid read at \(s=a\) with the two known endpoints, after cancellation of \(a(H-a)\ne0\). In particular \(M_0,\lambda,H-2,\lambda-1\ne0\) at any genuine candidate. Here \(R(y)=1/2+R_1 y+R_2 y^2\) is the actual graph. The two paid scale equations ensure that \(R(t)=\lambda\rho_t\) and that the true \(K=\lambda(A_2+B R)\) is the quadratic through its paid values at \(0,s,H\), also paying \(K(t)=L_4(t)/\rho_t\).

## Two graph rows and true unshared common-\(\beta\) row

Let \(L_j\) mean the centered monic Legendre polynomials evaluated at \(y-H/2\). Set
\[
\begin{gathered}
 D_{\rm ax}=(q-p)L_4(p)L_4(q),\\
 S_{\rm ax}=L_4(p)L_3(q)-L_4(q)L_3(p),\qquad
 A_{\rm ax}=(q-p)L_4(q)L_3(p)-pS_{\rm ax}.
\end{gathered}
\]
The true affine \(F_*\) is \((A_{\rm ax}+S_{\rm ax}y)/D_{\rm ax}\): the observed D labels are distinct and \(L_4\ne0\) at them by consecutive Legendre coprimality. Thus
\[
 M_3=[D_{\rm ax}L_3-(A_{\rm ax}+S_{\rm ax}y)L_4]/[(y-p)(y-q)]
       =\sum m_i y^i
\]
is the exact scaled cubic for the unobserved D times the known graph; neither the hidden D nor the roots of \(R\) need be solved. By the true [seven-clock factorization](../sdirk-eight-all-dirty-seven-clock/README.md), it equals \((\ell_0+\ell_1 y)R\) with \(\ell_0=2m_0,\ \ell_1=2m_1-4m_0 R_1\), nonzero actual graph pivots. The two coefficient rows are
\[
 E=m_2-2m_0R_2-\ell_1R_1=0,\quad G=m_3-\ell_1R_2=0 .
\]
They are necessary regardless of a possible common root between \(R\) and a D label.

In addition the genuinely paid single copy at each of \(p,q\) forces one shared **coefficient** \(\beta=B\lambda\), not a shared clock. Specifically
\[
\begin{array}{ll}
 X_p=\lambda L_4(p)-f_pK(p),&U_p=f_p(f_p-R(p)),\\
 X_q=L_4(q)-\rho_qK(q),&U_q=\rho_q(\lambda\rho_q-R(q)).
\end{array}
\]
The true Legendre read gives \(X_p=\beta U_p,\ X_q=\beta U_q\), so \(Y=X_pU_q-X_qU_p=0\). The two \(U\)'s are nonzero by the actual graph-off property at D. The computation does not determine any mate or invert an interpolant coefficient.

## Exact outer quartic and its true diagonal guard

Clear the integer numerators of \(E,G,Y\) with denominator support verified successively from true clock, Möbius, tap, nonzero scale, lower graph, Legendre and graph-off guards. Take the ordinary affine \(a\)-resultants of \(E,G\) and \(E,Y\), removing only true \(H\)-only guards. No leading coefficient at a specialized \(H\) is assumed nonzero; an actual common \(a\) still makes its nominal Sylvester determinant vanish. The candidate \(H\) is in the exact gcd of these two projections:

| Actual phase pair | Projected degrees | Irreducible common \(H\) factor |
| --- | --- | --- |
| SS | 327,142 | quartic, multiplicity 2 |
| A3S | 327,388 | quartic, multiplicity 4 |
| A3A3 | 327,508 | quartic, multiplicity 2 |

The quartic is the same in each:
\[
 2H^4-19H^3+13H^2+64H+32 .
\]
In its exact abstract rational field the three specialized rows in \(a\) have joint gcd of degree two, supported **entirely** on the numerator of the true nonzero \(a-b\). The replay checks repeated-factor trim exactly in the abstract field. Therefore there is no off-diagonal root in any characteristic-zero extension. Neither a real sign, positive-characteristic test, generic-leading assumption, nor a physical fourth row is used in this packet.

Run `SYMPY_GROUND_TYPES=flint python check_ll_offdiag.py` with SymPy 1.14 and python-flint 0.8; the replay is self-contained. The [candidate Lean scalar companion](../../lean/RKCert/Research/SDIRKEightDirtySevenBothSingletonBothTwoSDisjointLLOffdiag.lean) verifies the unshared two-read \(\beta\)-clearing and low-law graph curvature identities only. The whole order reduction and elimination are not all native Lean. The general numeric stage interval does not change.

The exact arithmetic was independently replayed. The accompanying Lean scalar statement is a draft, not asserted kernel-checked in this release.
