# A paid clock-invariant defect line need not force a paired hull fit

For every integer $p\ge4$ there is a rational strictly explicit tableau
of exact rooted-tree order $p$ whose **entire grade-two defect space**
is a clock-invariant line. Its outgoing primitive defect has a nonzero
coalesced profile on exactly $p$ clocks, but this profile admits no
literal weighted paired-hull fit on the physical clocks. The failure
includes overlapping hulls and repeated factors. It concerns the fit
itself, without added nuisance masses as in the
[masking theorem](RK-NUISANCE-MASKING.md). There is no weight-sign,
stage-minimality, or narrow-width assertion.

In general, if a clock-invariant space $U$ lies in the actual paid
defect space, its direct output vanishes at every clock: the individual
clock projectors are polynomials in clock multiplication and preserve
$U$, so the paid scalar output kills each projected vector. This is the
[clock-local mechanism](../../lean/RKCert/ReviewedNative/ClockLocalAnnihilator.lean).
The profile tested below is not a direct output of $U$: it comes from
the actual outgoing action of $A$.

## 1. Realizing an arbitrary paid outgoing mass

Fix $p\ge4$ and a set $S$ of $n\ge p$ distinct rational clocks. Choose
any rational masses $\omega_x$ on $S$ satisfying
$$
\sum_{x\in S}\omega_x x^j=0\qquad(0\le j\le p-4).
$$
We construct a strictly lower triangular $A$ and rational $\mathbf{b}$ satisfying
the reviewed [rooted-tree order predicate](../../../RKResearch/OrderConditions.lean).
Define the clock vector and the normalized Butcher weight vector by
$$
\mathbf{c}\coloneqq A\mathbf{1},\qquad
\boldsymbol{\nu}_t\coloneqq \frac{t!}{|t|}\boldsymbol{\Phi}_t(A).
$$
For a tree with children $\tau$, the stage recursion is
$$
\boldsymbol{\nu}_t=\prod_{\tau\text{ child of }t}\bigl(|\tau|\,A\boldsymbol{\nu}_\tau\bigr)
$$
with pointwise product and leaf column $\mathbf{1}$. The order condition
for $t$ is exactly $\mathbf{b}\cdot\boldsymbol{\nu}_t=1/|t|$.

Number the first three rows $0,1,2$. Row $0$ is zero, row $1$ has only
$A_{10}=3$, and row $2$ has $A_{20}=A_{21}=3/2$. Their clocks are
$0,3,3$. Set
$$
\mathbf{q}\coloneqq 2A\mathbf{c}-\mathbf{c}^{\odot 2},\qquad \boldsymbol{\eta}\coloneqq\mathbf{e}_1-\mathbf{e}_2.
$$
On the seed rows, $\mathbf{q}$ has coordinates $(0,-9,0)$, and $\boldsymbol{\eta}\cdot\mathbf{1}=\boldsymbol{\eta}\cdot\mathbf{c}=0$,
$\boldsymbol{\eta}\cdot\mathbf{q}=-9$.

Append a donor block with one row at each $x\in S$. Its only entries
are $x-x^2/6$ to row $0$ and $x^2/6$ to row $1$; thus the new row $i$ has $c_i=x$ and $2(A\mathbf{c})_i=x^2$.
Consequently $(\boldsymbol{\nu}_t)_i=x^{|t|-1}$ through tree order three.
If the current donor block gives these powers for tree orders at most $r+1$, append a block on the same clocks and choose each
row's coefficients $a_z(x)$ on the preceding block to satisfy
$$
\sum_{z\in S}a_z(x)z^j=\frac{x^{j+1}}{j+1}\qquad(0\le j\le r).
$$
Use any $r+1$ distinct donors and set the other coefficients to zero.
The Vandermonde system is invertible, and the tree recursion makes the
new block exact through tree order $r+2$. Repeat until the last donor block
is exact through tree order $p-1$. No donor row uses itself or a later row.

For each $x\in S$ append $p$ output rows, indexed by
$\lambda=0,1,\ldots,p-1$. Use a baseline row supported on the last donor block, given by the
same system with $r=p-2$, then add the row covector
$\lambda\boldsymbol{\eta}$ to the first three columns. These output rows never use
one another. Their clocks remain $x$ and the coordinates of $\mathbf{q}$ vanish there,
since the perturbation kills both $\mathbf{1}$ and $\mathbf{c}$ under the dot product.
The coordinates of $\mathbf{q}$ also vanish on donor rows, so
$$
\mathbf{q}=-9\mathbf{e}_1,\qquad F_2=\operatorname{span}\{\mathbf{q}\}.
$$
The second equality is exact: at orders one and two there is a single
tree at each order, and at order three the two normalized columns are
$\mathbf{c}^{\odot2}$ and $2A\mathbf{c}$. Thus the reviewed
[grade-two space](../../lean/RKCert/ReviewedNative/GradedDefects.lean)
is the indicated one-dimensional line, invariant under clock
multiplication. Define the outgoing vector by
$$
\mathbf{v}\coloneqq A\mathbf{q}.
$$
It belongs to $F_3$ because $3\mathbf{v}$ is the difference of the normalized
weight vectors of the extensions of the two order-three trees. At output row
$(x,\lambda)$, the coordinate of $\mathbf{v}$ is
$\lambda(\boldsymbol{\eta}\cdot\mathbf{q})$, since every baseline donor
has a zero coordinate in $\mathbf{q}$.

Give all earlier rows weight zero. Let $B_x$ be quadrature weights on
$S$ for the formal integral from $0$ to $1$, exact through degree
$p-1$; weights on any $p$ distinct nodes, with zeros on the remainder,
suffice by interpolation. At each $x$ choose rational weights by the
square Vandermonde system
$$
\sum_{\lambda=0}^{p-1} b_{x,\lambda}\lambda^j=
\begin{cases}
 B_x,&j=0,\\
 \omega_x/(\boldsymbol{\eta}\cdot\mathbf{q}),&j=1,\\
 0,&2\le j\le p-1.
\end{cases}
$$
Consequently the actual coalesced $b_i v_i$ mass at $x$ is $\omega_x$.

To verify **all** order conditions, take $d=|t|\le p$. The child
factor at row $(x,\lambda)$ is
$x^{|\tau|}+\lambda|\tau|(\boldsymbol{\eta}\cdot\boldsymbol{\nu}_\tau)$, since every baseline donor
is stage-exact at the needed child order. The product has degree at
most $d-1$ in $\lambda$. Its constant coefficient is $x^{d-1}$.
The coefficient of $\lambda$ is
$$
\sum_{\substack{\tau\text{ child of }t\\|\tau|\ge3}}
|\tau|(\boldsymbol{\eta}\cdot\boldsymbol{\nu}_\tau)x^{d-1-|\tau|},
$$
a polynomial of degree at most $p-4$ in $x$, or zero if the sum is
empty. Here the order-one and order-two child columns are precisely
$\mathbf{1},c$, both killed by $\eta$. The output weights annihilate
the higher powers of $\lambda$; the assumed $\omega_x$ moments kill
the linear term. Thus $\mathbf{b}\cdot\boldsymbol{\nu}_t=1/d$ for every actual tree
of order at most $p$. The construction uses $3+n(2p-3)$ rows, with
no assertion that this number is optimal.

## 2. A quadratic numerator forbids every physical paired fit

Take $n=p$. Choose $p$ distinct odd primes $\pi_i$, and for each let
$e_i$ be the integer with $2^{e_i}<\pi_i<2^{e_i+1}$. Define
$$
r_i\coloneqq \frac{\pi_i}{2^{e_i}},\qquad
x_i\coloneqq\frac{r_i-2}{r_i-1},\qquad S\coloneqq\{x_i\},\qquad
T\coloneqq\prod_{x\in S}(X-x),\qquad N\coloneqq(X-1)(X-2).
$$
The $x_i$ are distinct and negative, and $(2-x_i)/(1-x_i)=r_i$.
Set
$$
\omega_x\coloneqq\frac{N(x)}{T'(x)},\qquad
\mu(F)\coloneqq\sum_{x\in S}\omega_x F(x)=[X^{-1}]\,FN/T .
$$
The last identity is the simple-pole expansion because $N/T$ is
proper. Each mass is nonzero. For $n$ such active nodes the first
nonzero monomial has degree $n-3$: use the leading term of the
quadratic numerator at infinity. Thus precisely $n\ge p$ is needed
to pay the outgoing degree range $0,\ldots,p-4$, and $n=p$ suffices.
The tableau has exact order $p$, since the pure clock test of degree
$p$ fails: its quadrature annihilates $T$, but the formal integral
of $T$ is positive (each factor has positive constant term). Since
$T$ is monic and lower degrees are exact, the degree-$p$ monomial fails.

Suppose there were a nonzero gain $\theta$ and monic positive-degree
hulls $Q,D$, split with roots among the physical clocks
$S\cup\{0,3\}$, with arbitrary possible overlap and multiplicities,
such that $P$ is invertible modulo $QD$, $Q+PR=\sigma D$, and
$\mu=\theta(\Lambda_D-\sigma\Lambda_Q)$ as actual functionals.
By the [all-degree identity](COMMUTATIVE-RINGS.md), this would give
$$
\frac{N}{T}=-\frac{\theta R}{QD}.
$$
Indeed both fractions are proper: the hull identity gives
$\deg R\le\max(\deg Q,\deg D)<\deg(QD)$ if $R\ne0$. Testing every
monomial gives equality of all their negative Laurent coefficients,
which identifies proper fractions.

There are no physical clocks at $1,2$, so the fraction equality
forces $R(1)=R(2)=0$. The hull relation then gives
$Q(1)=\sigma D(1)$ and $Q(2)=\sigma D(2)$, in particular $\sigma\ne0$,
and
$$
\frac{Q(2)}{Q(1)}=\frac{D(2)}{D(1)} .
$$
These quotients multiply the factors $(2-x)/(1-x)$ with their
respective multiplicities. At $0,3$ those factors are $2,1/2$.
At $x_i$ the factor $r_i$ contains a unique odd prime $\pi_i$.
Comparing each odd-prime valuation forces the multiplicities of
$Q,D$ at every $x_i$ to agree.

At $w=0,3$ the left fraction $N/T$ is regular. If $Q,D$ had unequal
multiplicities at $w$, $\sigma D-Q$ would vanish only to the smaller
multiplicity. Since $P(w)\ne0$ when $w$ occurs in either hull, $R/(QD)$
would have a pole of the larger multiplicity, contradicting the
actual point profile. Thus the inactive multiplicities agree as well.
Monicity gives $Q=D$, and then evaluation at $1$ gives $\sigma=1$.
The hull relation forces $R=0$, contrary to the nonzero profile.

Even with the whole first nonzero defect flag a paid invariant line,
the cross-clock fit of its genuine outgoing column requires hypotheses
beyond invariance and rooted-tree payment. The no-fit argument does not
use output weight signs; the construction does not claim positive weights.
