# Disjoint high/high off-diagonal: zero graph-scale rank is impossible

Use the [disjoint two-later-singleton setup](../sdirk-eight-all-dirty-seven-quadratic-both-s-both-two-s-disjoint-scale/README.md). This packet excludes **A2/A2 with distinct later offsets and \(M=0\)**. As in the underlying setup, the field has characteristic zero, all ten literal quadratic defects are nonzero, the genuinely quadratic seven-clock graph has four singleton clocks and three doubled clocks, the literal endpoints are singleton, and the two actual end prefixes observe different doubled labels. No ordering is used. A high/high regular-scale candidate remains separate.

## True boundary pivots

Keep the original coordinate \(y=x-1\) with endpoints \(0,H\), and use \(a,b\) for the later singleton offsets from their respective ends. The two physical second rows have doubled labels \(p=a/2,\ q=H-b/2\); the later singleton labels are \(s=a,\ t=H-b\). With \(u=a/2\) and \(v=b/2\), the actual A2 taps are
\[
 f_p=k(u)/2,\quad f_s=N(u)/(2D(u)),\qquad
 \rho_q=k(v)/2,\quad \rho_t=N(v)/(2D(v)),
\]
with \(k,D,N\) as in the [unequal-law scale calculation](../sdirk-eight-all-dirty-seven-quadratic-both-s-both-two-s-disjoint-hl/README.md). The genuine pair requires \(u,v\ne0,2,2/3\), all their \(k,D,N\) nonzero, all six labels pairwise distinct, and \(a\ne b\) here.

Writing \(\phi=2f_s,\ \psi=2\rho_t,\ d=H-a-b\), the two actual scale lines are \(M\lambda=n\) and \(b\psi U\lambda=a\phi V\), using the \(n,M,U,V\) in the linked packet with the current A2/A2 taps. If \(M=0\) then \(n=0\). Because \(n=w(b-H)+(a-H)\) with \(w=1+H(\phi-1)/a\) and \(a\ne H\), necessarily \(w\ne0\). Thus
\[
 b=(2H-a+H^2(\phi-1)/a)/w.
\]
The [joint-rank exclusion](../sdirk-eight-all-dirty-seven-quadratic-both-s-both-two-s-disjoint-rank/README.md) gives \(U\ne0\), and the true nonzero reverse scale gives \(V\ne0\). Recover \(\lambda=a\phi V/(b\psi U)\). There is no assumption that the \(R\)-scale coefficient is invertible. In particular \(L_4(0)\) is not divided out.

The two true cubic graph equations \(E,G\) and the unshared two-D common-\(B\lambda\) row \(Y\) are reconstructed as in the [unequal-law packet](../sdirk-eight-all-dirty-seven-quadratic-both-s-both-two-s-disjoint-hl/README.md) with the actual high rear tap. Numerator and denominator guards are checked in order. The equation \(M=0\) remains an independent row after recovering \(b\).

## Complete exact characteristic-zero projection

Project \(M\) against \(E,G,Y\) in \(a\). The exact guarded univariate \(H\)-degrees are \(663,639,505\), and their common factors have the following degrees and multiplicities. The subsequent column concerns exact polynomial gcd in the abstract irreducible \(H\)-field, not gcd in a bivariate ring.

| \(H\) degree | Multiplicity | Joint \(a\)-gcd degree | Guards removing all roots |
|---:|---:|---:|---|
| 3 | 2 | 2 | \(N(a/2)\ne0\) |
| 6 | 2 | 2 | \(k(a/2),N(a/2)\ne0\) |
| 3 | 4 | 2 | \(a\ne H\) |
| 1 | 6 | 4 | \(a\ne H,\ k(a/2)\ne0\) |
| 2 | 39 | 6 | \(a\ne H,\ D(a/2)\ne0\) |
| 3 | 39 | 6 | \(a\ne H,\ D(a/2)\ne0\) |

All gcds and guard divisions are exact over these characteristic-zero fields and exclude their roots in every extension. No residue or field splitting argument is used.

## Useful off-diagonal scale guard

Separately, every branch of this disjoint clock pattern with \(a\ne b\) has \(\lambda\ne1\). If \(\lambda=1\), in the centered coordinate \(x=y-H/2\), the true quadratics \(R\) and \(C=A_2+BR\) have equal values at opposite endpoints: \(R(\pm H/2)=1/2\), \(C(\pm H/2)=2L_4(H/2)\). Each is even. Hence \(J_S=L_4-RC\) is even. The genuine four distinct singleton roots give
\[
 J_S=\theta(x^2-H^2/4)(x-a+H/2)(x-H/2+b),\qquad \theta\ne0.
\]
Its cubic coefficient is \(\theta(b-a)\). Evenness forces \(a=b\), a contradiction. Neither \(L_4(H/2)\ne0\) nor any ordering is required. This guard does not imply exclusion of every regular-scale candidate.

## Replaying

Run `SYMPY_GROUND_TYPES=flint python check_rankzero.py` (SymPy 1.14, python-flint 0.8, no cache). This uses the exact fraction core and exact fibre arithmetic in the two preceding packets; the proved scope does not depend on their conjectures. The scalar native companion verifies the evenness and cubic-coefficient gates, not the complete tableau proof. The global 10–11 stage interval is unchanged.
