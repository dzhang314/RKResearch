# Both singleton endpoints, disjoint later singleton taps: partial high/low exclusions

Assume strict ten-stage SDIRK of ordinary order at least eight over a characteristic-zero field. All ten literal quadratic defects are nonzero, there are exactly seven clock labels, and both literal endpoint labels are singleton. Use the genuinely quadratic seven-clock graph with three doubled and four singleton labels. At each end the literal first three rows use one other singleton and one doubled label; the two observed doubled labels are different. This packet excludes the lost first scale-row case and the regular \(Q=0\) case defined below for both unequal-law charts **A2/A3 and A2/star**. The complementary regular \(Q
e0\) case is not covered by this packet. It is closed by the [separate univariate off-curve proof](../sdirk-eight-all-dirty-seven-quadratic-both-s-both-two-s-disjoint-hl-residual/README.md), which does not use a bivariate gcd to infer membership. Reverse their roles by the actual weighted mirror, not by permuting stages. Both genuine star orders have the same paid scalar reads. It does not address the disjoint A2/A2 off-diagonal or unequal-count charts.

## True taps and two scale lines

Use the [disjoint scale setup](../sdirk-eight-all-dirty-seven-quadratic-both-s-both-two-s-disjoint-scale/README.md) with diagonal one, \(y=x-1\), endpoints \(0,H\), reflected axis \(H-y\), and \(m=(H+2)/2\ne0\). Write \(a,b\) for later singleton offsets from their own endpoint: the actual singleton labels are \(0,a,H,t=H-b\). The A2 front has doubled \(p=a/2\) physically second, with paid \(f_p=k(a/2)/2\), \(f_s=N(a/2)/(2D(a/2))\). A3 rear has \(q=H-2b\), \(\rho_q=N(b)/(2D(b))\); star rear has \(q=H+b-2\), \(\rho_q=k(b)/2\). Both pay \(\rho_t=k(b)/2\), where
\[
 k(u)=1+2u-u^2,\quad D(u)=-2+u+4u^2-u^3,\quad
 N(u)=(1+4u-4u^2)D(u)+4u^2(3u-2).
\]
All six known labels \(0,a,H,t,p,q\) differ. For each arithmetic law the literal second gap \(u\) excludes \(0,2,2/3\), and \(k(u),N(u),D(u)\ne0\); star excludes \(0,1,2\) and \(k(b)=0\). These are the [actual first-three guards](../sdirk-eight-all-dirty-seven-quadratic-both-s-mixed-share-rank/README.md#physical-coordinates-and-all-nine-types), not positivity. In particular the gap-two departure would revisit the first singleton. No assumption on \(L_4(0)\) is used.

Let \(\phi=2f_s,\psi=2\rho_t\), \(d=H-a-b\), and use centered \(L_j=L_j(y)\) as in the [seven-clock decomposition](../sdirk-eight-all-dirty-seven-clock/README.md). With reverse-to-original scale \(\lambda\ne0\) the actual singleton lines are
\[
\begin{aligned}
 M\lambda &= n, &
 n &= a+b-2H-H(\phi-1)(H-b)/a, \\
 && M &= a+b-2H-H(\psi-1)(H-a)/b,\\
 b\psi U\lambda&=a\phi V, &
 U&=H(H-b)L_4(a)-(H-a)dL_4(0)\phi,\\
 &&V&=H(H-a)L_4(b)-(H-b)dL_4(0)\psi.
\end{aligned}
\]
Their simultaneous rank zero is already excluded by the [graph-pivot proof](../sdirk-eight-all-dirty-seven-quadratic-both-s-both-two-s-disjoint-rank/README.md). The residual partner polynomial \(\Gamma\) from the second-by-first determinant has nominal degrees \((4,8,2)\) in \((H,a,b)\). Only \(H a b(H-a)(H-b)d\) and the paid tap denominators are cleared to construct it. In particular there is **no \(a-b\) division**.

## Two cubic graph rows and unshared doubled reads

Once \(\lambda\) is supplied, interpolate \(R=1/2+r_1y+r_2y^2\) from the actual reads \(R(a)=f_s,R(H)=\lambda/2\), and \(K=\lambda(A_2+BR)\) from \(K(0)=2\lambda L_4(0),K(a)=\lambda L_4(a)/f_s,K(H)=2L_4(H)\). Both come directly from the actual singleton defect and Legendre graph. Fit the actual affine \(F_*\) by the two values \(L_3/L_4\) at \(p,q\); \(L_4(p),L_4(q)\ne0\) by consecutive Legendre coprimality. Define
\[
 M_3=\frac{D_{\rm ax}(L_3-F_*L_4)}{(y-p)(y-q)}
       =m_0+m_1y+m_2y^2+m_3y^3,\qquad D_{\rm ax}=(q-p)L_4(p)L_4(q).
\]
The division is exact by the paid two anchors. The true seven-clock factorization gives \(M_3=(2m_0+\ell_1y)R\), \(\ell_1=2m_1-4m_0r_1\). The hidden doubled label differs from the singleton zero, so the true slope and constant of that linear factor are nonzero. The genuine quadratic graph makes \(r_2\ne0\) and then \(m_3\ne0\). The two equations used are
\[
 E=m_2-2m_0r_2-\ell_1r_1=0,\qquad G=m_3-\ell_1r_2=0.
\]
No root splitting or distinctness between a graph root and a doubled label is used. The additional equation comes from the **same** \(B\lambda\) in the two *unshared* actual doubled reads:
\[
 \begin{split}
 X_p&=\lambda L_4(p)-f_p K(p),& U_p&=f_p(f_p-R(p)),\\
 X_q&=L_4(q)-\rho_q K(q),& U_q&=\rho_q(\lambda\rho_q-R(q)),\\
 Y&=X_p U_q-X_q U_p=0.
 \end{split}
\]
The two \(U\)'s are nonzero: a doubled residual lies off \(R\), since the four singletons already exhaust the degree-four polynomial \(L_4-R(A_2+BR)\). No mate or literal fourth is needed.

## Separate lost rank and exact quadratic elimination

*If \(M=0\)*, then \(n=0\), and \(w=1+H(\phi-1)/a\ne0\): the first constant term can be written \(n=w(b-H)+(a-H)\). Thus \(b=(2H-a+H^2(\phi-1)/a)/w\) is rational in \(H,a\). The remaining scale line has \(U\ne0\) by joint rank and \(V\ne0\) because \(\lambda\ne0\). Substitute its exact \(\lambda=a\phi V/(b\psi U)\). Project \(M\) against \(E,G,Y\) in \(a\); their joint \(H\)-factors have degree/multiplicity \((2,1),(2,1),(6,1),(6,1),(2,3)\) in both phases. In the corresponding exact \(H\)-fields the joint \(a\)-gcd degrees are \(1,1,1,1,3\). Respectively both first factors are removed by \(k(a/2)\ne0\); the other three by \(N(a/2)\ne0\), \(a\ne H\), and \(D(a/2)\ne0\).

*If \(M\ne0\)*, then \(n\ne0\) and use the \(R\)-interpolant with \(\lambda=n/M\). Project \(\Gamma\) against each of \(E,G,Y\) in \(b\). After true b-independent guard removals their exact gcd has the sole irreducible factor \(Q(H,a)\) of bi-degree \((2,4)\), squared, in both phases. A common zero of these bivariate resultants need not lie on their polynomial gcd: isolated intersections off \(Q=0\) are not ruled out by this calculation. Thus the remaining proof assumes \(Q=0\). This is the same nontrivial factor of the exact line-resultant of the \(b\)-linear numerators of \(M,n\), after \(H(H-a)\). Write the numerator of \(M\) as \(j+kb\) and the partner as \(c_0+c_1b+c_2b^2\). On \(Q=0\), the checker proves the exact reduction
\[
 k^2\Gamma=(kb+j)\big(kc_2b+kc_1-jc_2\big),\qquad
 k^2c_0-kjc_1+j^2c_2\equiv0\pmod Q .
\]

*On \(k\ne0\)*, \(j+kb\ne0\), so project the residual linear polynomial \(L=kc_2b+kc_1-jc_2\) against the same three rows in \(b\), reduce each modulo \(Q\), and project each remainder against \(Q\) in \(a\). The joint \(H\)-factor degrees and multiplicities are \((28,2),(2,5),(7,10)\). The latter two fields already force \(k=0\) at their only common \(a\), inadmissible here. In degree 28 the exact joint \(a\)-gcd is linear. At that \(a\), the joint \(b\)-gcd of \(\Gamma,E,G,Y,L\) is linear and **forces \(n=0\)**, so it cannot give a true \(M\ne0\), \(\lambda\ne0\) point.

*On \(k=0\)*, use the independent \(Q,k\) resultant in \(a\), not the reduced linear \(L\). Its two non-guard factors have degrees two and seven. In the degree-two field the joint \(a\)-gcd forces \(j=0\) too, contrary to \(M\ne0\). In the degree-seven field the only exact common \(a\) gives unit joint \(b\)-gcd from the original \(\Gamma,E,G,Y\). This also allows the case in which a true coefficient of the initial quadratic \(\Gamma\) drops. On \(k\ne0\) no division by \(c_2\) was made either; all projections are nominal polynomial resultants, which still vanish at genuine common finite roots with a lost top coefficient. Every univariate factor is taken over \(\mathbb Q\); exact gcds in the corresponding abstract irreducible fields exclude roots in **all** extensions of these fields. No real ordering, good-place inference, or finite sampling is used.

## Replay and native scope

Run `SYMPY_GROUND_TYPES=flint python check_hl.py` in this folder (SymPy 1.14, python-flint 0.8; no caches or compiled kernel). The script clears only audited true denominators or factors known nonzero from the paid physical frame, and constructs/factors each projection in exact integer polynomial arithmetic. The [candidate Lean scalar gates](../../lean/RKCert/Research/SDIRKEightDirtySevenBothSingletonBothTwoSDisjointHL.lean) cover the two-scale determinant, the lost front-slope guard, and the residual quadratic factor identity. Tableau ingress and the number-field census are not verified by this Lean module. The general numeric stage interval does not change.

The exact arithmetic replay was independently reproduced. The scalar Lean source is a draft, not kernel-checked for this release.
