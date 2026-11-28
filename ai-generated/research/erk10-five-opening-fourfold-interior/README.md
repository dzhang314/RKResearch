# ERK10: a fourfold interior label cannot support the seven-label chart

**Theorem.** Use the actual order-ten word budget in the
[five-opening decoder](../erk10-five-opening-nonsplit-kernel/README.md).
The ten physical high rows have seven distinct nonzero forward
clock labels, and the unique clock 1 is the first reverse row.
Suppose one of the six interior reverse ordinates occurs four
times, and the other five labels are all singletons. Then this
chart is impossible over **every field with \(10!\ne0\)**,
with arbitrary chronologies, arbitrary physical weights, and
arbitrary total weight at the fourfold label. There is no ordering
or positivity assumption. This is not an unrestricted stage
lower bound.

The endpoint assumptions are substantial: uniqueness and first
reverse position force every positive-grade actual reverse
defect to be zero at \(y=0\). The proof does not transfer to a
duplicated endpoint or an endpoint after other reverse rows.
The exclusion pertains to an actual short-word continuation
of the stated five-opening chart, not to arbitrary tableaus.

## Actual low profiles and the first two live singletons

Write \(\boldsymbol y=\boldsymbol1-\boldsymbol x\),
\(\boldsymbol w\) for the high scores, and \(K=B^T\) in
reverse causal order. This unweighted transpose acts on
score-weighted vectors even when some physical weights vanish.
For the unique repeated interior ordinate \(a\ne0\) define
\(\boldsymbol w_a\) to agree with \(\boldsymbol w\) only on
the four \(a\)-copies, and to be zero elsewhere.

The actual first primitive, second primitive, composed, and
third primitive defects are
\[
\begin{aligned}
 \boldsymbol u&=K(\boldsymbol w\odot\boldsymbol y)
                     -\boldsymbol w\odot\boldsymbol y^{\odot2}/2,\\
 \boldsymbol g&=K(\boldsymbol w\odot\boldsymbol y^{\odot2})
                     -\boldsymbol w\odot\boldsymbol y^{\odot3}/3,\\
 \boldsymbol h&=K\boldsymbol u,\\
 \boldsymbol k&=K(\boldsymbol w\odot\boldsymbol y^{\odot3})
                     -\boldsymbol w\odot\boldsymbol y^{\odot4}/4 .
\end{aligned}
\]
Their grades are \(2,3,3,4\), respectively. As in the
[full three-pair argument](../erk10-five-opening-three-pair-complete/README.md),
all grade-at-most-three defects lie in the label-sum kernel
\(S\): they vanish at every singleton (of either zero or nonzero
score), and their entries sum to zero on the fourfold label.
The proof is the same six-interior Vandermonde after
duality with the actual short tests. Moreover the
grade-at-most-four defect space \(D_4\) has dimension at most
three, from the shifted Hilbert \(5\) nominal powers and the
two independent forward residuals. Neither argument uses
the multiplicity type of the six interior labels.

By the [scalar support factorization](../erk10-five-opening-three-pair-complete/ALL-PAID-FIELDS.md),
there are at least five distinct high labels with nonzero
grouped score. At most two of these can be the endpoint and
the repeated interior label. Hence there are at least **three**
live singletons, and in particular first and second live
singletons \(t,s\). Earlier zero-score singleton donors have
no scalar or grade-at-most-three defect inputs. Their physical
stages need not be inert at higher grades.

## The first live singleton forces a two-dimensional nilpotent block

Before the singleton \(t\), the nonzero-ordinate scalar inputs
can come only from earlier copies of \(a\). Write
\(S_t=(K\boldsymbol w_a)_t\). Its exact local first and second
primitive conditions give
\[
 aS_t=w_t t^2/2,\qquad a^2S_t=w_t t^3/3,
 \qquad\text{hence }t=3a/2,\ S_t\ne0 .
\]
At any earlier \(a\)-copy, all prior scalar inputs of positive
degree also come only from \(a\); hence there
\(\boldsymbol g=a\boldsymbol u+(a^3/6)\boldsymbol w\).
Consequently at \(t\),
\[
 (K\boldsymbol g)_t
   =a h_t+(a^3/6)S_t = (3a^4/16)w_t\ne0
\]
because \(h_t=0\). Thus \(D_4\not\subseteq S\) and the
grade-at-most-three defect space \(D_3\subseteq D_4\cap S\)
has dimension at most two.

Let \(M\) be the literal strict submatrix of \(K\) between
the \(a\)-copies strictly preceding \(t\). Write
\(\boldsymbol w_*\) for their score vector. The restrictions
of \(\boldsymbol u,\boldsymbol g\) there are
\[
 aM\boldsymbol w_*-a^2\boldsymbol w_*/2,\qquad
 a^2M\boldsymbol w_*-a^3\boldsymbol w_*/3 .
\]
The two vectors \(\boldsymbol w_*,M\boldsymbol w_*\) are
independent. Indeed \(\boldsymbol w_*\ne0\) by \(S_t\ne0\).
If \(M\boldsymbol w_*\) were proportional to
\(\boldsymbol w_*\), the coefficient would be zero since
\(M\) is nilpotent. Then the \(K\boldsymbol u\) value at \(t\)
would be \(-a^2 S_t/2\ne0\), contradiction. The coefficient
determinant transforming these two vectors to
\(\boldsymbol u,\boldsymbol g\) is \(-a^4/6\ne0\).
In particular those restrictions are independent, so \(D_3\)
is exactly their two-dimensional full span.

Since \(\boldsymbol h\in D_3\), restricting to this old block
gives
\(M^2\boldsymbol w_*\in\operatorname{span}(\boldsymbol w_*,
M\boldsymbol w_*)\).
The restriction of \(M\) to that invariant span is nilpotent.
In the cyclic basis \(\boldsymbol w_*,M\boldsymbol w_*\),
a nonzero first component in \(M^2\boldsymbol w_*\) would make
it invertible; with that component zero a nonzero second one
would be a nonzero eigenvalue. Both are impossible. Thus
\(M^2\boldsymbol w_*=0\) and on the pre-\(t\) rows
\(\boldsymbol h=a\boldsymbol u-\tfrac32\boldsymbol g\).
The identity holds globally because \(\boldsymbol h\in D_3\)
and restriction to those \(a\)-rows is injective on \(D_3\).

## The grade-four identity removes any feedback through the first singleton

Define
\[
 \boldsymbol F=\boldsymbol k+\tfrac34 K\boldsymbol g
                              -\tfrac{3a}4\boldsymbol g .
\]
On pre-\(t\) copies, \(M^2\boldsymbol w_*=0\) gives
\(\boldsymbol k=a^3 M\boldsymbol w_*-a^4\boldsymbol w_*/4\)
and \(K\boldsymbol g=-a^3 M\boldsymbol w_*/3\), so
\(\boldsymbol F=0\) there. At \(t\), the first two moments
give \(k_t=-9a^4 w_t/64\), exactly \(-3/4\) times the preceding
nonzero \((K\boldsymbol g)_t\), while \(g_t=0\). Thus \(F_t=0\).
The kernel of evaluation at \(t\) on \(D_4\) is exactly
\(D_3=\operatorname{span}(\boldsymbol u,\boldsymbol g)\):
it contains \(D_3\), has dimension at most two, and
\((K\boldsymbol g)_t\ne0\). The pre-\(t\) restriction now
proves \(\boldsymbol F=0\) globally.

Consider an \(a\)-row \(r\) after \(t\) but before the second
live singleton \(s\). Inductively at all earlier \(a\)-rows
\(g_i=a u_i+(a^3/6)w_i\). Set
\(S=(K\boldsymbol w_a)_r\) and \(T=K_{r,t}w_t\).
These account for every nonzero-ordinate scalar input, since
any other earlier singleton is scored zero. Their first three
moment errors are
\[
 u_r=aS+tT-w_r a^2/2,\quad
 g_r=a^2S+t^2T-w_r a^3/3,\quad
 k_r=a^3S+t^3T-w_r a^4/4.
\]
Also \((K\boldsymbol g)_r=a h_r+a^3 S/6\), because
\(\boldsymbol g,\boldsymbol u\) vanish at the first singleton
and at all the ghost singletons. Use the global \(\boldsymbol h\)
identity in \(F_r=0\). All \(S\) and \(w_r\) terms cancel,
leaving exactly
\[
                         (9a^3/32)T=0
\]
after \(t=3a/2\). Hence \(T=0\), restoring the induction
hypothesis for the new \(a\)-row. This argument also permits
zero scores on some or all of these later copies.

## The next live singleton is impossible

At the second live singleton \(s\), all earlier \(a\)-rows
therefore satisfy the same \(\boldsymbol g\) relation, and
\(u_s=g_s=h_s=0\). Divide the weighted taps by the nonzero
score \(w_s\) and call the results \(S,T\), for \(a\) and \(t\).
The first two scalar payments and \(F_s=0\) give
\[
 2(aS+tT)=s^2,\qquad
 3(a^2S+t^2T)=s^3,\qquad
 9a^3S+8t^3T=2s^4 .
\]
Here the correction to the effective cubic moment is exactly
\(a^3 S/8\), from \(\tfrac34 (K\boldsymbol g)_s\).
Multiply the first equation by \(2t^2\), the second by
\(-4t\), and add the third. The left-hand side is
\(a(2t-3a)^2 S=0\). The right-hand side is
\(2s^2(s-t)^2\); since both clocks are nonzero and the two
singletons are distinct, this is impossible. The proof is
uniform in the aggregate score of the repeated label.

## Reproduce

    python3 -B audit.py
    # From the overlay or repository root:
    sha256sum -c ai-generated/research/erk10-five-opening-fourfold-interior/sources.sha256

The weighted rank and nilpotent cyclic-span arguments are
mathematical. The exact replay checks every scalar change of
basis and the final two polynomial cancellations. Portable
Lean scalar evidence is tracked separately from the full
tableau implication.

The [portable scalar checks](LEAN.md) passed on all four target Lean releases. The cyclic-span and full tableau reductions remain mathematical.
