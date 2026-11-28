# Mixed both-singleton prefixes, one shared D: the two paid scale lines cannot both be rank zero

Work over a characteristic-zero field with a strict ten-stage SDIRK tableau of ordinary order at least eight, ten nonzero literal quadratic defects, and exactly seven distinct clocks. Both physical endpoints are singleton. One literal orientation starts S,D,D; its opposite has precisely one later D and one later S (S,D,S or S,S,D), and its observed D is one of the two observed forward D labels. There are nine genuine phase meshes in this scope. This packet proves that the coefficients of the actual mirror scale in the two independently paid quadratic reads **cannot both vanish**. It does not on its own exclude their nonzero-rank cases.

## Physical coordinates and all nine types

Orient with S,D,D first; use normalized coordinate \(y=x-1\), endpoints \(0,H\), half-width \(m=(H+2)/2\), and reflected coordinate \(H-y\). Denote the shared D by \(p\), the other observed forward D by \(q\), and the later observed reverse S in original coordinates by \(t\). The labels \(0,H,p,q,t\) are distinct. A true arithmetic prefix with actual second offset \(a\) has the paid pair \(a,2a\) and defects \(\kappa(a)/2,N(a)/(2D(a))\), with
\[
 \kappa(a)=1+2a-a^2,\quad D(a)=-2+a+4a^2-a^3,\quad
 N(a)=(1+4a-4a^2)D(a)+4a^2(3a-2).
\]
The input guards are \(a\ne0,2,\ 3a-2\ne0,\ \kappa D N\ne0\); gap two contradicts the actual singleton-first departure law. A true star with offsets \(a,2-a\) pays equal defects \(\kappa(a)/2\) and has \(a\ne0,1,2,\ \kappa\ne0\). Its two possible physical orders give the same consumed pair list by their own literal equations, without permuting a proposed tableau.

The forward types are A1 (arithmetic with shared D first of the two later D's), A2 (arithmetic with shared D second), and S (star, using its shared offset \(u\)). In both arithmetic forward types \(u\) is the actual second offset. Let \(v\) denote the reverse **D offset**, in its own reflected and normalized axis. Its possible later S offsets for reverse A2 (D second), A3 (D third) and S (star) are \(2v,v/2,2-v\); in A3 the actual arithmetic second gap is \(v/2\). Thus \(H=p+v\), and \(t=H-\text{reverse S offset}\). This lists three forward times three reverse types, not a restriction of either chronology.

## Two paid affine scale rows, with no guessed missing D copy

Let \(f_p,f_q\) be the forward normalized defects, \(\rho_p,\rho_t\) the measured reverse defects, and \(\lambda\ne0\) the actual reverse-to-original scale. At \(p\), the two exact original defects are \(f_p,\lambda\rho_p\), and Vieta gives \(\beta=B\lambda=-L_4(p)/(f_p\rho_p)\). The paid quadratic \(T=\lambda A_2\) has five point values:
\[
\begin{array}{c|l}
 0&2\lambda L_4(0)-\beta/2\\
 H&2L_4(H)-\beta\lambda/2\\
 p&-\beta(f_p+\lambda\rho_p)\\
 q&\lambda L_4(q)/f_q-\beta f_q\\
 t&L_4(t)/\rho_t-\beta\lambda\rho_t .
\end{array}
\]
These come from the two endpoint S equations, true shared Vieta, and the known original D and reflected S copy. No unidentified mate is used. As in the [previous paid quadratic gate](../sdirk-eight-all-dirty-seven-quadratic-both-s-one-shared-double/README.md#exact-graph-recovery-and-five-paid-values-of-one-quadratic), put \(J(s)=(H-s)T(0)+sT(H)\). For \(s=q,t\) require
\[
 p(p-H)[HT(s)-J(s)]-s(s-H)[HT(p)-J(p)]=0 .
\]
They are affine in \(\lambda\); write them \(A+\lambda B_1=0,C+\lambda D_1=0\), keeping \(B_1\) distinct from the true paired-fibre \(B\). Thus rank zero would require **all four** \(A,B_1,C,D_1=0\).

The [common frame](mixed_share_common.py) also fits the true affine \(F_*\) through \(L_3/L_4\) at \(p,q\), and computes \(M_3=(L_3-F_*L_4)/[(y-p)(y-q)]=\sum m_i y^i\). Its \(m_3\ne0\) follows from the genuinely quadratic graph/cubic D factor, and \(m_0\ne0\) because \(0\) is a paid singleton distinct from D. These guards follow from actual order, not a generic rank assumption. If the unobserved third D is \(z\) then \(M_3(z)=0\) and
\[
 R(y)=\tfrac12-\frac{z y}{2m_0}\bigl(m_2+m_3(z+y)\bigr),\qquad
 \lambda=2R(H).
\]
The true rear S equation \(R(t)=\lambda\rho_t\) additionally gives
\[
 z=\frac{m_0}{m_3 H t(t-H)}
      \bigl[H-t+(t-2H\rho_t)\lambda\bigr].
\]
This affine recovery, with only genuine nonzero denominators, is provided for the nonzero-rank continuation. The rank-zero contradiction below does not invoke the unobserved D or its graph read.

## Exact rank-zero projection

Clear the four row numerators using only the actual tap, distinct-label, Legendre and graph guard support. Project \(A\) against each of \(B_1,C,D_1\) separately in \(v\), retain nonzero projections, strip only genuine \(u\)-only factors, then take their gcd. A rank-zero point must lie on its root set even if nominal leading coefficients drop at a special \(u\). The exact table is:

| Mode | Nonzero projected degrees | Irreducible \(u\) factor degrees |
| --- | --- | --- |
| A1A2 | 61,57,59 | 2,7 |
| A1A3 | 112,72,76 | 5,9,12 |
| A1S | 61,31,18 | 2 |
| A2A2 | 49,60,64 | 5,9 |
| A2A3 | 100,75,88 | 12,8 |
| A2S | 49,34,28 | 5 |
| SA2 | 16,26,23 | 2 |
| SA3 | 55,48,47 | 5,12 |
| SS | 16,8 | 2,2 |

All factors have multiplicity one. In each of the 16 abstract exact \(u\)-fields the joint \(v\)-gcd has degree one. It is entirely supported on a specified true guard: \(H=0\), \(t=0\), \(q=t\), or the actual A3 later D's numerator \(N(v/2)=0\). The checker verifies that exact guard, including the two distinct quadratics in the SS row. Hence rank zero is impossible in any characteristic-zero extension. Neither finite reduction nor a positivity assumption is used.

Run `SYMPY_GROUND_TYPES=flint python check_rank_zero.py` with SymPy 1.14 and python-flint 0.8. The linked [Lean scalar companion](../../lean/RKCert/Research/SDIRKEightDirtySevenBothSingletonMixedShareRank.lean) states the denominator-free scale determinant and graph secant identities only. The entire tableau reduction is not native Lean, and no numeric stage bound changes.

The publication audit independently re-ran the complete exact elimination. The scalar Lean companion is a draft and was not kernel-checked for this release.
