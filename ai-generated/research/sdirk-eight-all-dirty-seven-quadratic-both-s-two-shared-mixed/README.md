# Both singleton endpoints, two shared D labels, one arithmetic and one star

Work over a characteristic-zero field. Suppose a strict ten-stage SDIRK tableau of ordinary order at least eight is all-dirty with exactly seven distinct clocks and both physical endpoints singleton. Assume both physical prefixes are S,D,D and use the same two D labels, with one true arithmetic prefix and one true star. This packet excludes that mixed phase in either actual orientation. It does not assume both opposite rows have the same physical order, nor cover two arithmetic phases or a single shared D label.

## Literal clocks and a single paid quintic

Orient by the actual weighted mirror so arithmetic is forward. In diagonal-one coordinate \(y=x-1\), the two D labels are \(u,2u\), and the endpoints \(0,H\). The true rear star on those same labels gives \(u+2u=2H-2\), so \(H=1+3u/2\). In centered Legendre coordinate \(y-H/2\) take \(m=(H+2)/2\). The actual front D residuals are
\[
 f_1=\kappa(u)/2,\qquad f_2=N(u)/(2D(u)),
\]
where \(\kappa=1+2u-u^2\), \(D=-2+u+4u^2-u^3\), and \(N=(1+4u-4u^2)D+4u^2(3u-2)\). In the actual star the two normalized reverse residuals are equal to \(r=1-u^2/8\), for either actual order: their normalized offsets are \(1+u/2,1-u/2\). The original defects in those later physical occurrences are \(\lambda r\) for the true nonzero mirror scale \(\lambda\); all the paid residuals here are nonzero.

The two actual doubled-fibre product equations
\[
 L_4(u)=-B f_1\lambda r,\qquad L_4(2u)=-B f_2\lambda r
\]
imply \(L_4(u)N(u)-L_4(2u)\kappa(u)D(u)=0\). The exact factorization is
\[
 -\frac{u(3u-2)(u^2-2u-1)}{1120}
 (639u^5-4686u^4+5552u^3+7776u^2-1392u-1568).
\]
Only the last factor is possible: \(u=0\) would repeat the first label; \(3u=2\) would null the true arithmetic third tap; \(\kappa(u)=0\) contradicts the all-dirty assumption. The surviving quintic is irreducible over \(\mathbb Q\).

## The actual last singleton read contradicts the recovered graph

Over that exact \(u\)-field, fit the true affine \(F_*\) from \(L_3/L_4\) at \(u,2u\). These Legendre values are nonzero by consecutive coprimality, and the distinct D anchors pay a unique affine. Define
\[
 M(y)=\frac{L_3(y)-F_*(y)L_4(y)}{(y-u)(y-2u)}
      =m_3y^3+m_2y^2+m_1y+m_0,
\]
where \(L_j(y)\) denotes the centered mode evaluated at \(y-H/2\). By the [seven-clock decomposition](../sdirk-eight-all-dirty-seven-clock/README.md), the actual third D is a root \(z\) of \(M\), and \(M/(y-z)\) is proportional to the true graph \(R\). The graph and D cubic are both nonzero at the first singleton, so \(m_0\ne0\); also \(z\ne0\). The paid \(R(0)=1/2\) fixes the true scale
\[
 R(y)=\tfrac12-\frac{z\,y}{2m_0}\bigl(m_2+m_3(z+y)\bigr),\qquad
 \lambda=2R(H)=1-\frac{H z}{m_0}\bigl(m_2+m_3(z+H)\bigr).
\]
No choice of whether \(M\) splits and no residual-root separation at unrelated labels is used.

The product at \(u\) fixes \(\beta=B\lambda=-L_4(u)/(f_1r)\). The degree-two polynomial \(T=\lambda A_2\) has four actual paid evaluations:
\[
\begin{array}{c|l}
 0&2\lambda L_4(0)-\beta/2\\
 u&-\beta(f_1+\lambda r)\\
 2u&-\beta(f_2+\lambda r)\\
 H&2L_4(H)-\beta\lambda/2.
\end{array}
\]
The first/last values are true singleton equations, and the two inner values are the actual doubled-root Vieta sums. The first three distinct labels interpolate \(T\). Evaluating at \(H\) and subtracting the last paid value is a polynomial in \(z\) of degree at most two, with no division by an interpolated coefficient. The replay finds the exact unit gcd with \(M(z)\) in the abstract quintic field. This eliminates every possible actual third D, even in extensions.

Run `python check_two_shared_mixed.py` with SymPy 1.14. The candidate Lean scalar companion verifies the denominator-free product and scaled Vieta gates; not all rooted-order ingress and elimination are formalized. Ordered fields, positivity, and the unsolved both-singleton chronologies are not invoked. The general stage interval is unchanged.

The publication audit independently replayed the corresponding exact arithmetic; the new Lean companions here are draft scalar lemmas, not claimed kernel-checked in this release.
