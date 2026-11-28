# A genuinely non-arithmetic seven-node DIRK12 remainder

This is an exact forward-bank and signed remainder ingredient for the
proposed width-19 factorial-only splice. It is **not** a full
19-stage tableau. Let \(S=\mathbb Z[1/12!]\).

Start with the five fixed proper sites
\[
 R=\{1/4,1/3,1/2,2/3,5/6\}
\]
of the first arithmetic-grid remainder, and put
\(P=\prod_{r\in R}(X-r)\),
\(m_j=\int_0^1 X^{j+1}(1-X)^3P(X)\,dX\).
Here \((m_0,m_1,m_2)=(-1/15120,-23/3991680,-1/1496880)\).
The two-site nodal condition is
\[
 m_2-(q+t)m_1+qt m_0=0.
\]
At \(q=1/18\) the denominator in
\(t=(m_2-qm_1)/(m_1-qm_0)\) is nonzero and \(t=1/6\).
Thus the seven proper sites are
\[
 C=\{1/18,1/6,1/4,1/3,1/2,2/3,5/6\}.
\]
A 13-site consecutive arithmetic grid containing both 0 and 1 has
spacing \(1/m\) with \(m\le12\); it cannot contain \(1/18\).
The exact signed cubic offsets in this same order are
\[
 \boldsymbol\Delta=
 (-59049/4743200,-15/1232,-256/121275,-117/15400,
  -391/110880,-87/84700,-27/215600).
\]
All eight paid moments
\(\sum_{x\in C}\Delta_x x^j=-j!/(j+4)!\)
for \(1\le j\le8\) hold. The unit offsets occur at
\(1/18,1/6,1/4,5/6\). None of the gaps within \(C\), or to the
origin, require an unpaid prime. The one nonunit base gap
is the terminal gap \(1-1/18=17/18\).

## Controlling which gap can be released

For any five-site pencil with this weight, put
\(D=m_1^2-m_0m_2\). When \(D\ne0\), the moving-node offset is
\[
 \Delta_q=-\frac{D}{6qP(q)(q-t)(m_1-qm_0)}
\]
and symmetrically for \(t\). These identities follow by integrating the
two moving cardinal polynomials and using
\((m_1-qm_0)(m_1-tm_0)=D\). A paid moving difference or origin gap
can have an unpaid prime only if the prime divides \(D\); the
gap to 1 is not in this formula. In the present pencil
\(D=-1/91048624128\) is a unit. Thus the nonunit terminal gap
is a deliberate cross-gap release, not an unverified cancellation
of a moving cardinal denominator.

More generally, at a prime \(p>12\) with \(v_p(D)=1\), exactly one
of \(m_1-qm_0,m_1-tm_0\) has valuation one. The two nodes cannot
coincide modulo \(p\), and the exceptional one cannot coincide
with any fixed node or the origin if its \(\Delta\) is to be paid.
The other can have at most one simple collision. If it meets a
fixed node modulo \(p\), the fixed cardinal numerator then reduces
to the exceptional \(m_1-tm_0\) (or the exchanged form), so also
vanishes there. This supplies an actual exact cancellation for a
first-order fixed-node collision, rather than treating all gaps
as automatically harmless.

## An actual old forward interface

For a four-trapezoid reverse split choose the first two nontrap
slots at \(1/18,1/6\), and the three copy clocks
\((r,z,u)=(1/4,1/2,1/3)\). The literal ten-row old bank uses the
clocks
\[
0,1/40,1/20,1/10,1/24,1/8,1/4,3/8,1/2,1/3.
\]
The standalone replay rebuilds its Lagrange-integral tap rows,
checking the six true size-six ports and the original two pure
size-seven ports, all through the complete old tree list. The
old row at \(r\) minus its exact integrated six-port decoder
row is a genuine nonzero \(\boldsymbol\sigma\), silent on all
child tree sizes through five. The update of the last old row
is \(\eta(u)\boldsymbol\sigma\), with
\(\eta(u)=H_{\rm Jacobi}(u)/H_{\rm Jacobi}(r)=-1024/243\).
The replay verifies all corrected low flags and the true
rank-four size-seven projected residual band
\(f(0)=f(z)=0,\ f(u)=\eta(u)f(r)\), not just scalar interpolation.

The split reverse proof does not need the unpaid terminal gap:
the initial Vandermonde involves only the terminal and four
trap donors, the \(2\times2\) extra pivot uses the first two
nontrap clocks, and the top interpolation uses only the
remainder and origin. To solve the scalar quadrature cheaply
without inverting this gap, use the eight-node base
\(B=\{0\}\cup C\), with \(M=\prod_{b\in B}(X-b)\).
For chosen terminal score \(\theta\) and four mutually unit-gap
trap heads \(h\), solve
\[
 \sum_h w_h M(h) h^j
  =\int_0^1 M(X)X^j\,dX-\theta M(1),\qquad 0\le j\le3.
\]
This uses an ordinary four-node Vandermonde just on the head
clocks, followed by the separate divisibility tests by \(M(h)\).
The eight remaining scores are then the integrals of the
eight base cardinal polynomials minus the actual terminal and
head taps. Polynomial division by monic \(M\) proves exactness
through degree eleven. Importantly there is no division by
\(M(1)\), even though its unpaid part is 17. This factor only
sets congruences on the free score \(\theta\) when the paid
head conditions are tested. A full winning paid score and
top reverse fit is still required.

The Python replay is independent of prior files. The core Lean
certificate rechecks the eight scaled remainder moments on all
four listed versions. The old bank and general divisibility
proofs are not claimed to be native Lean.
