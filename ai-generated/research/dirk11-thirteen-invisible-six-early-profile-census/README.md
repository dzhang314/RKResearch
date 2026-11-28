# Early-ghost unordered profile census and neighboring clean marks

**Scope.** Work in the normalized no-late invisible-six
DIRK11/13 chart over characteristic zero, with an actual nonempty
first reverse gap, \(\alpha\ge1\). Use the rooted hypotheses,
notation and exact initial ghost gates of the
[early-ghost proof](../dirk11-thirteen-invisible-six-alpha1-five-zero/README.md).
In particular \(l(z)=w_0(z)=0\), the affine slope \(l_1\ne0\),
and the first literal ghost's diagonal is zero.
This is a finite profile statement **at fixed ordinary clocks**,
not a finite list of ordinary clock schedules or a numerical
order-stage improvement.

## 1. Exact unordered old profiles

Let \(R=Y^3+c_2Y^2+c_1Y+c_0\), \(c_0\ne0\), and
\(P=Ym,\ P_0=YR\) as in the early-ghost proof. The identity
\(IP=lP+\delta P_0\) holds exactly, with \(l\) affine.
If \(\deg m\le1\), comparison of degrees gives \(\delta=0\),
hence \(P\) divides its own primitive. A nonzero polynomial
with zero constant coefficient can do this only if it is a monomial:
the quotient must have both degree and valuation one, and
comparison of nonzero coefficients would otherwise give
different primitive denominators. In degree two, \(\delta=0\)
likewise forces a monomial. Thus a nonmonomial \(m\) may be
normalized \(m=Y^2+rY+s\), with \(\delta=1/4-l_1\ne0\).
The coefficient of \(Y\) forces \(l_0 s=-\delta c_0\), so \(s\ne0\).

The other two coefficients of \(IP=lP+\delta P_0\) give
\[
 \delta(c_1-s-c_0r/s)=s/4,\qquad
 \delta(c_2-r-c_0/s)=r/12.
\]
In particular the exact necessary affinity relation is
\[
 D=c_0r^2-(2s^2+c_1s)r+3c_2s^2-3c_0s=0.
\]
For \(rs\ne0\) the second of those identities permits the
live denominator \(s(c_2-r)-c_0\), and \(l_1\ne0\) gives
\[
 p=r c_0,\qquad q=3s c_2-4rs-3c_0\ne0,\qquad z=p/q.
\]
Let \(n\) be the old \(m\)-multiplication determinant and
\((w_0^\#)_i\) the coefficients of its adjugate applied to
\(IP_0/Y\bmod R\). Thus \(w_0^\#=n w_0\) and \(n\ne0\).
A cleared literal ghost gate is
\[
 \mathcal H=\sum_{i=0}^2 (w_0^\#)_i p^i q^{2-i}=0.
\]
In the ring of rational polynomials in the old coefficients,
reduce this in \(r\) by \(D\) (whose leader \(c_0\) is live),
obtaining the exact affine \(\mathcal A=A_1(s)r+A_0(s)\).
The coefficient identity is
\[
 \operatorname{Res}_r(D,\mathcal A)
 =\tfrac3{100}(c_2s-c_0)^2 F_1(s) F_2(s)^2 F_n(s)
\]
with
\[
 \begin{aligned}
 F_1&=96s^3-80c_1s^2+75c_0c_2s-75c_0^2,\\
 F_2&=s^3-c_1s^2+c_0c_2s-c_0^2,\\
 F_n&=-c_0c_1^2+(-12c_0c_1+12c_0c_2^2-c_1^2c_2)s
      +(-36c_0-4c_1c_2)s^2+12c_2s^3 .
 \end{aligned}
\]
No \(A_1\) is divided by in this necessity. All factors
are nonzero as polynomials in \(s\) at every fixed old hull:
\(c_0\ne0\), and if \(c_2=0\), the quadratic coefficient
of \(F_n\) is \(-36c_0\). Thus for \(rs\ne0\) there are
at most ten \(s\) and at most two \(r\) per \(s\), even at
a vanishing \(A_1\) or a repeated root. The result is
independent of the forward-carrier degree and \(\tau\).

Separate exact contacts:

* If \(r=0\) and \(m\) is not monomial, the coefficient equations
  first force \(c_2\ne0,\ s=c_0/c_2\). They also force
  \(s-c_1\ne0\), and then \(l_1=(2s-c_1)/(4(s-c_1))\).
  The literal \(w_0(z)\) equation, homogeneously evaluated
  at \(z=-c_0/(2s-c_1)\), has numerator
  \(c_0^2(c_0-c_1c_2)^2(6c_0-5c_1c_2)/(15c_2^3)\).
  The live factors leave \(6c_0=5c_1c_2\), so \(l_1=-1\).
  This is impossible when \(\alpha=2\).
* If \(r\ne0,\ c_2s=c_0\), then \(c_2\ne0\), and \(D=0\)
  fixes \(r=(2c_0+c_1c_2)/c_2^2\). The exact specialized
  \(\mathcal H\) is
  \(-8c_0^4(2c_0+c_1c_2)^2F_c/(5c_2^{10})\), with
  \(F_c=12c_0^2+8c_0c_1c_2-6c_0c_2^3+c_1^2c_2^2\).
  All the factored divisors outside \(F_c\) are live.
* **Only when \(A_1\ne0\)**, an \(F_1\) root necessarily gives
  \(r=15(c_2s-c_0)/(16s)\), hence \(l_1=-1\). An \(F_2\)
  root then gives \(r=(c_2s-c_0)/s\), and \(R=(Y+c_0/s)m\),
  impossible because the actual split old \(m\) values are live.
  Both assertions use exact evaluation of the affine
  \(\mathcal A\) on the corresponding candidate \(r\);
  uniqueness is not assumed at \(A_0=A_1=0\).

On the remaining \(F_n\) branch with live \(A_1\),
a further exact homogeneous identity implements a smaller profile:
\[
 A_1\,6c_2s+A_0(c_1+6s)=Q_n F_n .
\]
The source gives the indicated explicit rational \(Q_n\).
If \(c_1+6s=0\), then \(F_n=12c_0c_2^2s=0\), forcing
\(c_2=0\); both \(A_0,A_1\) vanish at that contact. Thus the
regular \(F_n\) profile uses
\[
 r=\frac{6c_2s}{c_1+6s},\qquad
 z=-\frac{2c_0c_2s}{c_0c_1+6c_0s-c_1c_2s+2c_2s^2}.
\]
Both denominators are live in that branch by the argument
above and the literal affine-root formula. Also \(c_2\ne0\)
there since \(r\ne0\). This does not claim a formula for
the singular \(A_0=A_1=0\) fiber.

## 2. A true adjacent clean read without ghost-weight reconstruction

When \(\alpha=1\), write \(V=1-a\) for the next regular clean
reverse site, \(d=A_{aa}\), \(k=G_a/b_a\) in the same normalized
G scale, and \(T=N_{V,z}G_z/b_a\). No division by \(k\) is
needed below, so this identity also applies to \(\tau=0\).
Inclusive weighted matching as in the early-ghost proof gives
the three literal reads (all polynomials evaluated at \(V\)):
\[
 \begin{aligned}
 IP-d(P-k)+T &= l k,\\
 IP_1-d(P_1-Vk)+zT &= r_1 k,\\
 IP_0-dP_0 &= w_0 k .
 \end{aligned}
\]
Use \(P_1=YP-\kappa P_0\), \(r_1=Yl-t-\kappa w_0\) and
\(IP_1=Y IP-I^2P-\kappa IP_0\) to get
\(I^2P(V)=t(V)k+(z-V)T\). Substitute this in both exact
integration-by-parts equations, and use \(l(V)=l_1(V-z)\).
The resulting **adjacent clean debit** is
\[
 (d+z-V)T=d^2(P(V)-k).
\]
It has a Lean proof from the displayed scalar hypotheses.
In particular it does not invert \(d,z-V,1+l_1\), or \(k\).

For **any \(\alpha\ge1\) and \(\tau\ne0\)**, the two total
tail marks into \(a\) can be computed without a ghost weight.
Work in forward coordinates, choose the common G scale so
\(G\phi=H_{\rm bary}\), and let \(K_b=F_b-rH\) as in the early
quadratic notebook (also defined for cubic \(U\)).
The actual \(F_6\) formula supplies
\(\Omega=K_b+UQ_3\), of degree at most six,
with \(\Omega(c_i)=A(C(C-b)\phi)_i\) on every ghost.
This is zero at all ghosts before \(a\), and on each late ghost
it equals \(A_{ia}a(a-b)U(a)\); no other clean donor of that
signal can occur. Write \(T_j=\sum_{\text{late }i} N_{V,i}G_i
(1-c_i)^j/b_a\). Pair the actual \(G\in E_7^\perp\) with
\((1-X)^j\Omega(X)\) for \(j=0,1\). At terminal \(G_T=0\).
At the other clean rows \(G_i=H_i/U(c_i)\).
The \(Q_3\) term vanishes in the sum by the clean barycentric
annihilator, since each \(X^j Q_3\) has degree at most four.
Therefore
\[
 T_j=-\frac{\sum_{\text{six clean}}H_i(1-c_i)^jK_b(c_i)/U(c_i)}
 {b_a\,a(a-b)U(a)} .
\]
There is no division by the origin's possibly zero weight.
Equivalently, if \(S_6\) is the nonterminal clean hull in
forward coordinates and \(R_f=T_5/[(X-a)(X-b)]\), write
\[
 M_j=[X^5]\left((1-X)^j K_b(X)/U(X)\bmod S_6\right).
\]
By barycentric interpolation and \(S_6'(a)=a(a-b)R_f(a)\),
this gives \(T_j=-k R_f(a) M_j\).
It enables exact computation of the two paid degrees at \(a\)
from the carrier/ordinary profile alone. No contradiction is
claimed merely from these formulae.

## 3. Remaining count ledger

The reciprocal identity always gives \(U(0)\ne0\):
for \(\tau\ne0\) the barycentric row is live at the origin;
for \(\tau=0\) the cubic \(U\) has exactly the three old
distinct forward roots, none at the origin. Constant and linear
carriers were already excluded, and all \(\alpha=0\) cases
are closed by the earlier packets. The remaining cubic counts
are \((1,0,5),(1,1,4),(1,2,3),(2,0,4),(2,1,3)\), with
\(\tau=0\) excluded in the first by the early-ghost proof.
The remaining quadratic counts are the same list without
\((1,0,5)\), and always have \(\tau\ne0\).
For \(\alpha=1\) quadratic the five-prefix multiplier
\(\nu\) must be nonzero; the monomial and mixed contacts
are further restricted by the associated packets.
A remaining count does not designate a realized tableau.

Run **python3 project.py** for the exact identities in §1.
No modular inference enters those coefficient identities.
The native scalar module **DIRKOrderElevenInvisibleSixEarlyGhost**
checks the two principal adjacent rows and distinct-ghost crossings.
The polynomial/rank ingress is still an exact written proof.
