# Disjoint two-later-singleton prefixes: exact two-clock base in all six phases

Keep the [disjoint (1,1) seven-clock hypotheses and paid quadratics](../sdirk-eight-all-dirty-seven-quadratic-both-s-both-two-s-disjoint-rank/README.md): strict ten-stage SDIRK, ordinary order at least eight over a characteristic-zero field, all ten quadratic defects nonzero, both endpoints singleton, precisely seven clock labels, and each actual first-three prefix with one later D and one later S, at different D labels. This packet is a **dimension reduction**, not a general disjoint chart exclusion. It leaves a two-clock base, a finite partner root condition and explicit physical graph/D conditions.

## Singleton offsets and two paid scale rows

Use common diagonal one with \(y=x-1\), endpoints \(0,H\), and reflect by \(H-y\). Write \(a=s\) for the forward later S offset and \(b=H-t\) for the reverse later S offset. The two D labels are \(p=\delta_f(a)\), \(q=H-\delta_r(b)\), where the inverse maps from later S to D are \(a/2,2a,2-a\) in A2, A3 and star. These are their actual physical phases (the two star orders have the same consumed pair data). Keep all genuine tap guards and the six distinct labels \(0,H,p,q,a,H-b\). In particular \(H,a,b,H-a,H-b,H-a-b\ne0\).

Use \(\phi(a)=2 f_s(a)\), \(\psi(b)=2\rho_t(b)\). The law is **low** \(k(a)=1+2a-a^2\) in A3 or star, and **high** \(N(a/2)/D(a/2)\) in A2, with their true nonzero denominators and numerators. The genuine weighted mirror pairs the high/low choices with their reversals; the six charts consist of three low/low, two high/low, and one high/high. This grouping changes only the subsequent scale algebra; all D offsets and defects still depend on the actual phase.

Evaluate centered \(L_4\) at the original label \(y\) and write \(L_z=L_4(z)\), using \(L_{H-b}=L_b\) by parity. Put
\[
 d=H-a-b,\quad
 N_0=a+b-2H-H\frac{\phi-1}{a}(H-b),\quad
 M_0=a+b-2H-H\frac{\psi-1}{b}(H-a).
\]
These are the two terms of the true \(R\)-scale line \(M_0\lambda=N_0\), after canceling only nonzero clock factors. With
\[
 U=H(H-b)L_a-(H-a)d L_0\phi,\quad
 V=H(H-a)L_b-(H-b)d L_0\psi ,
\]
the line for \(K=\lambda(A_2+B R)\) is \(b\psi U\,\lambda=a\phi V\). Both follow from the four actual singleton reads, by multiplying their cleared quadratic secants. These rows do not invert a coefficient of \(\lambda\).

At a genuine candidate their determinant vanishes:
\[
 \mathcal E=b N_0\psi U-a M_0\phi V=0.
\]
The [separate rank-zero exclusion](../sdirk-eight-all-dirty-seven-quadratic-both-s-both-two-s-disjoint-rank/README.md) means an actual scale is now uniquely recovered by one of these two formulas. If \(M_0\ne0\), use \(N_0/M_0\); if \(M_0=0\), actual consistency gives \(N_0=0\), and the second line must have a nonzero coefficient, so use \(a\phi V/(b\psi U)\). In either case actual \(\lambda\ne0\). This retains an individually missing rank.

## Exact determinant quotient and every all-coefficient drop

In every law pair, divide \(\mathcal E\) by \(H a b(H-a)(H-b)(H-a-b)\), a true nonzero factor. For the same law (low/low or high/high), it is also antisymmetric in \(a,b\), so handle \(a=b\) separately and divide by \(a-b\) off diagonal. After clearing only the true high-law denominators, the resulting primitive polynomials have exact partial degrees:

| S laws | degrees in \((H,a,b)\) | Actual parameter conclusion |
| --- | --- | --- |
| low/low, off diagonal | (4,1,1) | rational \(b\) in \((H,a)\), no missing slope |
| high/low | (4,8,2) | nonzero polynomial of degree at most 2 in \(b\) over the base |
| high/high, off diagonal | (4,7,7) | nonzero polynomial of degree at most 7 in \(b\) over the base |

When \(a=b\) in a same-law chart, the two actual affine rows are equal at \(\lambda=1\) by reflection of the known S reads. Since they cannot both lose rank, \(\lambda=1\) is forced. This is a separate symmetric *paid profile*, not an assertion that the method is invariant under reflection. The mixed-law chart does not divide by \(a-b\).

For low/low off diagonal the residual polynomial, up to a nonzero rational scalar, is exactly
\[
 P(H)ab+Q(H)(a+b)+P(H)-2Q(H),
\]
where
\[
\begin{split}
 P(H)&=2H^4-4H^3-72H^2+104H-128,\\
 Q(H)&=-5H^4+20H^3+60H^2+120H-40.
\end{split}
\]
Since \(P,Q\) are coprime, a possible vanishing slope \(Pa+Q=0\) would require \(P\ne0\). The remaining term \(Qa+P-2Q\) would then be \(P(1+2a-a^2)\ne0\), a contradiction. Thus
\[
 b=\frac{(2-a)Q-P}{Pa+Q}
\]
at every genuine off-diagonal point. Moreover the exact clearing identity
\[
 k(b)(Pa+Q)^2=\bigl[Q^2-P(P-2Q)\bigr]k(a)
\]
makes the square bracket a further true nonzero guard. No ordering or degree-eight sign test is required.

For the two cases with a high law forward, let \(c_i(H,a)\) be **all** coefficients of the residual polynomial in \(b\). To lose every such coefficient, the smallest nonzero \(a\)-degree coefficient and each other one must vanish together. Project these pairs in \(a\) and take their exact gcd in \(H\). In high/low the two resultant degrees are 60,60; in high/high all seven are degree 56. In both cases the common factors have degrees 4,8,12 with multiplicities 3,1,1. In the abstract degree-four \(H\)-field the exact joint \(a\)-gcd has degree three and is supported on the true forbidden \(D(a/2)=0\). In the degree-eight and degree-twelve fields the exact joint gcd has degree one and is supported on the true forbidden \(N(a/2)=0\). The checker verifies these removals using exact field gcds. Resultant vanishing is necessary even with a lost highest coefficient. Hence the partner polynomial is **not identically zero** at any genuine base, but all smaller degrees are allowed. These arguments are not finite-prime filters.

## Remaining paid graph and D gates, without a hidden clock variable

Once \(H,a,b,\lambda\) are fixed as above, reconstruct \(R,K\) by their true values at \(0,a,H\). Fit \(F_*\) through \(L_3/L_4\) at the **unshared** observed D labels \(p,q\); these are distinct and their \(L_4\) values nonzero. Set \(M_3=(L_3-F_*L_4)/[(y-p)(y-q)]=\sum m_i y^i\). The true [seven-clock decomposition](../sdirk-eight-all-dirty-seven-clock/README.md) gives \(M_3=(\ell_0+\ell_1y)R\), with \(\ell_0=2m_0\), \(\ell_1=2m_1-4m_0 r_1\) for \(R=1/2+r_1 y+r_2 y^2\). Hence the two necessary remaining coefficient rows are
\[
 m_2-2m_0r_2-\ell_1r_1=0,\qquad m_3-\ell_1r_2=0 .
\]
They do not assume the two roots of \(R\) split or that \(R\) and the D cubic are coprime. The actual third D can be read afterward as \(-2m_0/\ell_1\), with the genuine nonzero slope and distinct label guards.

For the paid forward D defect \(f_p\) and normalized reverse D defect \(\rho_q\), define
\[
\begin{array}{ll}
 X_p=\lambda L_4(p)-f_p K(p),& U_p=f_p(f_p-R(p)),\\
 X_q=L_4(q)-\rho_q K(q),& U_q=\rho_q(\lambda\rho_q-R(q)).
\end{array}
\]
The true different D pairs give the **same** \(\beta=B\lambda\): \(X_p=\beta U_p,\ X_q=\beta U_q\). Thus \(X_p U_q-X_q U_p=0\) is an independent paid row, not a guessed mate or shared-D Vieta product. Both \(U\)'s are nonzero by true graph-off. These give low-dimensional exact constraints for the continuation; they are not asserted infeasible in the whole remaining base here.

Run `SYMPY_GROUND_TYPES=flint python check_scale_reduction.py` with SymPy 1.14 and python-flint 0.8; there are no cached rows. The [scalar Lean companion](../../lean/RKCert/Research/SDIRKEightDirtySevenBothSingletonBothTwoSDisjointScale.lean) verifies the low-law difference and cleared rational-pivot identities only. The whole disjoint chart is not excluded, and the numeric stage interval is unchanged.

The exact arithmetic was independently replayed. Any accompanying Lean scalar statement is a draft, not asserted kernel-checked in this release.
