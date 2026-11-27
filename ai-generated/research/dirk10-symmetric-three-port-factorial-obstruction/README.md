# A factorial-localization obstruction for the symmetric rank-one DIRK10 chart

Let \(S=\mathbb Z[1/10!]=\mathbb Z[1/210]\). The existing symmetric three-port rank-one family cannot give a tableau over \(S\). This is a **complete exclusion of the stated chart**, allowing all rational heights, signed weights, exterior clocks and retaps consistent with its actual rank-one cross row. It is **not** a lower bound for unconstrained DIRK12 over \(S\).

## Scope and scalar collapse

Use nine distinct rational scalar sites with centered coordinates
\[
             0,\ \pm1,\ \pm\alpha,\ \pm\beta,\ \pm\gamma,
        \qquad \beta=\frac{3\gamma^2-2}{6\gamma^2-3}.
\]
The relation is the branch used by the [known rational twelve-stage tableaux](../dirk10-twelve-field-portfolio/README.md). The old \(u\) row is Simpson, its physical midpoint \(u/2\) is omitted by the decoder \(\Pi\), and the cross block is
\[
        (EJ-TE)\Pi+\boldsymbol\eta\,\sigma,
        \qquad
        \sigma=(A_{u,\bullet}-J_u\Pi)/H(u),\qquad
        H(X)=X(1-14X+56X^2-84X^3+42X^4).
\]
The physical right endpoint has weight \(w_1\) and
\(\eta_1=H(1)-J_1H/w_1=1-1/(30w_1)\). The stated literal merges do not identify the midpoint with any other stage. No other reverse-row equations are assumed in this exclusion.

If a tableau is over \(S\), its row sums and quadrature weights belong to \(S\); every prime \(\ell\ge11\) can therefore be reduced, whether or not the scalar sites remain distinct or the weights remain nonzero. Order ten pays exact integration of centered polynomials through degree nine. If the reduced sites are contained in \(0,\pm1,\pm s,\pm t\), testing \(Z^2(Z^2-1)(Z^2-s^2)(Z^2-t^2)\) gives
\[
           21s^2t^2-9(s^2+t^2)+5=0.
\]
No five-site subset \(0,\pm1,\pm s\) is possible: the analogous even hull of degree six, and its multiple by \(Z^2\), would force \(s^2=3/7=5/9\), impossible at every such prime.

Put \(\gamma=m/n\) in lowest terms, \(m,n>0\) (changing its sign changes no sites). The four integers
\[
 n,\qquad U=3m^2-n^2,\qquad V=2m^2-n^2,\qquad W=9m^2-5n^2
\]
must all be smooth on \(\{2,3,5,7\}\). This is immediate for \(n\). A prime outside this set dividing \(V\) cannot divide \(3m^2-2n^2\), so the clock \(\beta\) forces \(V\) smooth. If such a prime divides \(U\), then \(\gamma^2=1/3\) and \(\beta=1\). The seven-site test forces \(\alpha^2=1\), leaving at most five sites. If it divides \(W\), then \(\gamma^2=5/9\) and \(\beta=-1\); the test forces \(\alpha=0\), again at most five sites. Both are contradictions. None of \(U,V,W\) can vanish for a nonzero rational \(\gamma\).

## Finite reduction for \(\gamma\)

Primitivity of \(m,n\) gives the following bounds for the valuations of \(U,W\):
\[
\begin{array}{c|cccc}
  &2&3&5&7\\ \hline
 U&0\text{ or }1&0\text{ or }1&0&0\\
 W&0\text{ or }2&0\text{ or }2&0\text{ or }1&0
\end{array}
\]
For the prime 2 use odd squares modulo 8 (or unlike parity). At 3, if \(3\nmid n\) both are units; otherwise \(U\) has valuation one and \(W=9(m^2-5(n/3)^2)\) has valuation two by nonsquareness of 2 modulo 3. At 5, 3 is nonsquare and \(W\) is either a unit or has valuation one according as \(5\nmid m\) or \(5\mid m\). At 7, neither 3 nor \(9/5=6\) is a square. Consequently \(|U|\le6\), \(|W|\le180\), and \(U+W=6V\) gives \(|V|\le31\). The identities \(m^2=U-V\), \(n^2=2U-3V\) give \(m\le6,n\le10\).

The finite check leaves \(\gamma=1,1/3,2/3\). The first has coincident original sites. At \(\gamma=1/3,\beta=5/7\), reduce modulo 11, where \(\beta=-\gamma\) and \(\gamma^2=5\). The seven-site identity then forces \(\alpha^2=5\), collapsing to five sites again. Only \(\gamma=2/3,\beta=2\) remains.

## The last rational candidate family still has an unpaid terminal

For the remaining mesh set \(Y=\alpha^2\). The unique degree-nine weights at either of the two \(\alpha\)-sites and at physical 1 are
\[
 w_\alpha=\frac{-1}{15Y(Y-4)(Y-1)(9Y-4)},\qquad
 w_1=\frac{145Y-159}{3150(Y-1)} .
\]
They follow by integrating the scalar cardinal polynomials on the squared centered knots \(0,1,Y,4,4/9\), then halving the appropriate pair masses. The independent rational replay directly integrates the numerators. Because the first weight has a constant smooth numerator, every factor in its displayed denominator must be a unit in \(S\). Writing \(\alpha=m/n>0\) in lowest terms, this forces both \(n\) and all seven forms
\[
         m,\quad m\pm n,\quad m\pm2n,\quad 3m\pm2n
\]
to be smooth.

Every determinant of two distinct coefficient pairs of the seven forms is a nonzero divisor of 120 in absolute value. If a power of a prime divides two forms, it divides the corresponding determinant: the two linear combinations eliminate \(m\) and \(n\) separately, and \(\gcd(m,n)=1\). Thus each of the four permitted primes can exceed its valuation in 120 on **at most one** of the seven forms. At least three forms therefore have absolute value at most 120. Taking two and using the \(2\)-by-\(2\) inverse with coefficients bounded by \(3,2\) gives \(m\le480,n\le720\).

The complete finite check leaves seven possible \((m,n)\). The accompanying terminal numerators \(145m^2-159n^2\) are
\[
\begin{array}{c|rrrrrrr}
 (m,n)&(4,1)&(6,1)&(1,2)&(1,3)&(4,3)&(2,5)&(2,7)\\ \hline
 &2161&5061&-491&-1286&889&-3395&-7211 .
\end{array}
\]
None is smooth. Since the denominator of \(w_1\) already pays, at least one forbidden prime divides \(w_1\) for every remaining mesh.

Finally this *weight numerator* is a real denominator obstruction, not merely a failed unit test in an algorithm. In the actual terminal row the tap into the omitted physical Simpson midpoint is exactly
\[
 A_{\mathrm{terminal},\,u/2}
       =\left(1-\frac{1}{30w_1}\right)\frac{2u}{3H(u)} .
\]
The other cross term has zero column there, and the merges do not alter this column. At a forbidden prime dividing \(w_1\), the first factor has negative valuation, the second has nonpositive valuation because it is \(2/[3(H(u)/u)]\), and \(H(u)/u\in S\). So the literal tap cannot belong to \(S\).

## Evidence

    python3 -B check.py

The standard-library audit verifies the two finite enumerations, the mod-11 collapse, all determinant sizes, and the scalar moment formula. The core Lean module **DIRK10SymmetricThreePortArithmetic** checks the closed arithmetic without extra axioms on the four named Lean versions. The mathematical tableau reduction and the valuation/count argument are given above; the finite Lean arithmetic is not a native theorem about all tableaux.
