# Two independent selectors at a stopped Runge–Kutta clock

A zero local primitive does not erase a signed atom, even when the
signed law is the exact tilted output quadrature of the same tableau.
We give a selector test for each of the two identities, then exhibit
exact order-six ERK and positive-diagonal SDIRK examples that separate
them. This is a mathematical result and an exact arithmetic check,
not a Lean formalization or a new stage bound.

## 1. The actual grouped sources

Work over an ordered field. Use the
[reviewed rooted-tree order](../../../RKResearch/OrderConditions.lean)
`HasOrder p A b` for the actual tableau, and set $c=A\mathbf1$.
Write $I_{u,v}$ for the difference of normalized formal primitives of
a polynomial at $v$ and $u$. Choose one direction. Use oriented clocks
$x_i=c_i$ for the prefix, $x_i=1-c_i$ for the reflected suffix. Let
$B(x)=\sum_{x_i=x}b_i$ be the grouped output weight. Define the full
sources, including the diagonal, by
$$
\begin{aligned}
N_F(x)_{\rm pre}
 &=\sum_{x_i=x}\sum_j b_i A_{ij}F(x_j),\\
N_F(x)_{\rm suf}
 &=\sum_{x_i=x}\sum_j b_j A_{ji}F(x_j).
\end{aligned}
$$
In the suffix formula the evaluation is at the oriented clock of the
*later weighted stage* in the strict sum. In particular a target stage
with zero individual output is not automatically removed. Write
$N_F(x)$ for the chosen source.

For polynomials $Q,F$ with $\deg Q+\deg F+2\le p$, the identity is
$$
 \sum_x Q(x)\big(N_F(x)-B(x)I_{0,x}F\big)=0. \tag{1}
$$
For the prefix, the degree-$d$ monomial stage defect
$(d+1)(Ac^d)_i-c_i^{d+1}$ has zero $b_i c_i^k$ pairing when
$d+k+2\le p$. This is the actual
[reviewed bushy root cut](../../lean/RKCert/ReviewedNative/BushyMoments.lean);
powers here are componentwise. Divide by $d+1$ and expand the two
polynomials. For the suffix, in the physical coordinate transpose the
finite double sum and apply the same mixed identity with $F,Q$
exchanged. It becomes $\sum_i b_i F(c_i)I_{0,c_i}Q$.
The ordinary bushy quadrature is exact on the two polynomials
$F(X) I_{0,X}Q$ and $Q(X) I_{X,1}F$, of degree at most
$\deg F+\deg Q+1$. Their integrals agree by the primitive product rule.
Hence the suffix identity uses $I_{c_i,1}F$ in the physical coordinate.
Replace both polynomial arguments by their compositions with $1-X$.
The latter integral becomes $I_{0,1-c_i}F$ in the oriented coordinate,
giving (1) there as well. No full-tree order assumption on a transposed
tableau is made.

If $A$ is lower triangular and $a$ is the chosen stop, the full source
at $a$ splits as
$$
 N_F(a)=N_F^{\rm strict}(a)+D(a)F(a),\qquad
 D(a)=\sum_{x_i=a}b_i A_{ii}. \tag{2}
$$
The strict terms have $j<i$ for the row and $j>i$ for the weighted
column. Reflection does not negate $D(a)$; same-clock off-diagonal
terms remain in the strict sums. A root $F(a)=0$ removes the actual
diagonal term for both ERK and DIRK, but does not establish that the
strict sum is zero.

## 2. Independent degree budgets for source and atom

A selector at $a$ for a finite difference of weights $\Delta_x$ is a
polynomial $Q$ with $Q(a)\ne0$ and $Q(x)\Delta_x=0$ for all $x\ne a$.
Then $\sum_x Q(x)\Delta_x=0$ implies $\Delta_a=0$. In particular, if
all nonzero off-stop differences are in a finite set $E$ avoiding
$a$, take $Q=\prod_{x\in E}(X-x)$, of degree $|E|$.
Weights on the two sides of a comparison must be coalesced at each
clock before selecting. Matched weights need no root.

Apply this first to the residual in (1). A cover $E$ of its possible
nonzero off-stop sites pays when
$$
 |E|+\deg F+2\le p. \tag{3}
$$
This proves $N_F(a)=B(a)I_{0,a}F$. For the prefix it suffices to
include clocks of output-live rows other than $a$. For the suffix
one must also include clocks $x_i$ with possible weighted inflow
$b_j A_{ji}\ne0$, unless its net coefficient is already known
zero. Neither side needs to charge every physical clock if the
omitted residuals are known zero. In particular, if
$N_F(a)=0$ and $B(a)\ne0$, the true local primitive is zero.

For the atom comparison, suppose the analytic signed law
$$
 I_{0,1}(F H Q)=\sum_x\mu_x Q(x) \qquad (\deg Q\le q) \tag{4}
$$
includes the stop $a$, with other locations and signed weights specified.
Here $H$ is the polynomial multiplying the local profile $F$.
Write $\widehat\mu_x=B(x)F(x)H(x)$ for the actual pure tableau tilt.
The pure bushy word of `HasOrder p A b`, extended by polynomial
linearity, gives the same integral for this tilt whenever
$\deg(FHQ)+1\le p$. In the suffix this is the same pure word applied
to the whole reflected polynomial. If an off-stop label occurs more than once, its coefficient in (4)
is the total weight of all its occurrences.

Thus if $U$ covers the possible nonzero off-stop differences
$\mu_x-\widehat\mu_x$, a second nodal selector, of degree $|U|$, proves
$$
 \mu_a=B(a)F(a)H(a) \tag{5}
$$
under the separate guards $|U|\le q$ and $\deg(FH)+|U|+1\le p$.
One may use any selector $Q_m$ for this difference, needing only its
one literal law test and the exact degree $\deg(FH Q_m)+1\le p$.
The test for (3) is mixed; the test for (5) is pure. They are not
interchangeable. At a live stop with $H(a)\ne0$, once (5) is paid,
erasure is equivalent to $F(a)=0$, not to a primitive being zero.

The support-only charge is sharp: on $m\ge2$ distinct permitted sites,
including $a$, the nonzero weights $1/\prod_{y\ne x}(x-y)$ annihilate
all tests of degree at most $m-2$ by the Lagrange leading coefficient
identity, without vanishing at $a$. Conversely, sign information can
save degree. If a difference measure has at most $k$ sign changes on
its ordered nonzero support, annihilating all moments through degree
$k$ forces it to vanish: put one root between each sign change and
choose the leading sign so each nonzero paired term is positive.

A second literal source of a small discrepancy is a reviewed branch
defect. For the [reviewed root residual](../../lean/RKCert/ReviewedNative/RootMomentCuts.lean)
$r_i$ of a tree $u$, the masses $\sum_{x_i=x}b_i r_i G(x_i)$
annihilate a test $Q$ under $|u|+\deg G+\deg Q+1\le p$ by the root
cut paired with bushy partners. If the stop difference in (5) is
known to be a sum of such components, each can be selected at its own
paid support. This is not an order identity for an arbitrary signed
law.

## 3. Application to a stopped sign bracket

In the [finite stopped bracket](../../lean/RKCert/ReviewedNative/FiniteStoppedBracket.lean),
$F=WP$ and $H$ is a nonempty product of factors $d-X$ with $d\ge1$.
For an interior stop $a$, $H(a)>0$. With the stated mesh, separator
and degree conditions there, true local zero gives
$\tau S<0<\tau(S+J)$, where $S$ is the left signed sum divided at each
site by $H$, and $J=\mu_a/H(a)$. If the independent comparison (5)
is paid and $F(a)=0$, these inequalities are incompatible. This is a
conditional transport to the bracket, not a claim that a tableau
necessarily supplies its sparse signed law, cancellation, or budgets.

The source and atom requirements are already independent on affine
profiles: $X-a/2$ has zero primitive on $[0,a]$ but nonzero value at
$a$, whereas $X-a$ has zero value and nonzero primitive. If a profile
is selectable there is a useful way to enforce both. Suppose $W$ is
positive on the left nodes of a positive exact interval rule and the
needed degrees are paid (for the [published 19-node rule](../../lean/RKCert/ReviewedNative/PositiveIntervalGrid19.lean)
it suffices that $\deg W+3\le19$). Put
$$
 \omega=W(X-a)^2,\qquad
 \xi=I_{0,a}(X\omega)/I_{0,a}(\omega),\qquad
 P=(X-a)^2(X-\xi).
$$
The finite positive quadrature gives $I_{0,a}(\omega)>0$ and
$0<\xi<a$. Then $I_{0,a}(WP)=0$ and $(WP)(a)=0$. The double stop
root preserves the one-cut sign fit: the left separator is $\xi$
with sign $+1$, since $P(x)(x-\xi)=(x-a)^2(x-\xi)^2$, and no right
cut is needed. If the two selectors and the same signed law meet
their other guards, this profile pays both zeros. No other degree
or sparsity condition of the bracket is implied by the construction.

## 4. Exact order-six counterexamples with the literal tilted law

Choose a real root $t$ of
$$
 g(T)=50T^4-120T^3+95T^2-30T+4
$$
between $773087032049/10^{12}$ and $773087032050/10^{12}$. The exact
endpoint signs are $+$ and $-$. Set
$$
 \alpha=t/2,\qquad
 s=(10t^2-15t+6)/(30t^2-30t+10),\qquad C=(s,\alpha,t,1).
$$
The denominator is positive and $0<s<\alpha<t<1$. Over
$\mathbb Q(t)\subset\mathbb R$, let $\ell_j$ be the Lagrange basis for $C$,
$b_j=I_{0,1}\ell_j$, and $G_{ij}=I_{0,C_i}\ell_j$. In node order the
four weights lie respectively in
$(202,203),(383,385),(346,347),(67,69)$ in units of $10^{-3}$,
as certified by rational interval evaluation.

For $V=(X-s)(X-\alpha)(X-t)(X-1)$, the two expressions
$120 I_{0,1}V$ and $120 I_{0,1}(XV)$ are respectively
$$
\begin{aligned}
 &s(30t^2-30t+10)-(10t^2-15t+6),\\
 &s(10t^2-15t+6)-(5t^2-9t+4).
\end{aligned}
$$
They vanish by the definition of $s$ and $g(t)=0$: the numerator
of the second expression after clearing the denominator is $-g(t)$.
Division by $V$ proves quadrature through degree five.
The degree-six nodal test is
$$
 \rho=I_{0,1}(X^2V)=-1/532+(3/380)t-(7/570)t^2+t^3/152,
 \qquad -77/10^6<\rho<-76/10^6.
$$
It vanishes under the nodal quadrature but not under the integral,
so the bush of size seven fails. These quadrature conclusions also
hold for the reflected nodes and their reflected weights: reflection
preserves degrees, and $(1-X)^6$ has the same degree-six leading term.

**Actual tableau order.** Each row of $G$ integrates all polynomials
through degree three, so $G\mathbf1=C$. With $d_U$ the product of the factorials of
the children of a tree $U$, its stage vector through size five is
$C^{|U|-1}/d_U$. This follows by applying the row integration to each
child of size at most four. It also covers all size-six trees except
the root configuration with a single child $U$ of size five. Here
$b^T G=(b_j(1-C_j))_j$ because $I_{0,X}\ell_j$ and
$(1-X)\ell_j$ have equal unit integrals by the primitive product
rule, and both polynomials are paid by quadrature. Hence $b^T G C^4=1/5-1/6=1/30$ and gives
$1/(6\cdot5\cdot d_U)$ for that tree. The seed tableau therefore has
actual reviewed order six, not just the pure moments.

To make a lower-triangular tableau, put one initial stage of diagonal
$\gamma$ and zero output, followed by five consecutive four-row blocks.
Every row has diagonal $\gamma$. The first block takes its strict input
only from the initial row, with coefficients $C_i-\gamma$. Each
later block takes strict input only from its predecessor via
$G-\gamma I$. Only the final block has the output $b$.
All blocks have clocks $C$. The first block agrees with the seed
on trees through size two. Induct on the next block's tree size:
the current diagonal term uses child values already proved in that
block; the strict term uses the previous block's child values. Together
the action is $\gamma I+(G-\gamma I)=G$. Thus each new block earns
one more size, and the final output has order six. The failed bush
of size seven is preserved because the visible weights and clocks
are unchanged.

Use the following three cases, reflecting the seed nodes and weights
in the last two:

| Tableau | Physical seed clocks | Common diagonal | Chosen side |
| --- | --- | --- | --- |
| positive SDIRK | $C$ | $t$ | prefix at physical $t$ |
| strict ERK | sorted $1-C$ | $0$ | reflected suffix at physical $1-t$ |
| positive SDIRK | sorted $1-C$ | $1-t$ | reflected suffix at physical $1-t$ |

Each tableau has 21 stages and **four actual physical clocks**:
the initial row does not add a clock. All clocks lie in $[0,1]$ and
the output weights are nonnegative with four positive weights.
Clocks repeat across the blocks, so they are not monotone in stage
index. The positive SDIRK designation here concerns the diagonal,
not all strict coefficients.

**The same genuine stopped law in each case.** In the analytic
coordinate set $F=P=X-\alpha$, $W=1$, and $H=1-X$ (pole at $1$).
The analytic stop is $t$ and the tilted actual output law is
$\mu(x)=B(x)(1-x)(x-\alpha)$. Only $s,t$ survive: the node
$\alpha$ is killed by $P$ and $1$ by $H$. In particular
$\mu(s)<0<\mu(t)$. Every law test of degree at most three is paid
by actual degree-five quadrature. The left separator is $\alpha$,
the sole off-stop atom is $s$ on the left, and there are no right
cuts or right atoms. On the left the sign fit is the square
$(x-\alpha)^2>0$ wherever $P(x)\ne0$; on the right $P>0$. The bracket cost is $1+2=3$,
grid cost is $5\le19$, local degree is $1$, and survival cost is
$1+1<19$. The finite mesh and pole guards hold.

The actual mixed selector is paid at $3+1+2=6$ on all four clocks
and $B(t)>0$ in the analytic coordinate.
The true local integral is $t^2/2-\alpha t=0$, and the actual full
source is zero. For the implicit cases the separate diagonal part
is positive and the strict part is negative; both vanish for ERK.
The pure comparison is already exact, yet the stop value
$\mu(t)=B(t)(1-t)t/2$ is strictly positive. The bracket correctly
gives $S<0<S+J$, with $S=\mu(s)/(1-s)$ and $J=\mu(t)/(1-t)$.
This refutes erasure from source cancellation even with both
selector budgets, the actual signed law, and the original scalar
sign conditions.

## Exact replay and scope

Run `python3 check-selector-paid-stopped-atoms.py` in this directory.
The [checker](check-selector-paid-stopped-atoms.py) uses only standard
library fractions and modular polynomial arithmetic. It verifies the
quartic endpoint signs, all 37 rooted-tree shapes through size six in
each literal lower-triangular tableau, the failed order-seven bush,
the grouped sums and all four signed-law monomials. The
[exact output receipt](selector-paid-stopped-atoms.receipt) records this
check. No floating point or Lean is used. The result supplements the
[nodal clock cut](nodal-cut-recurrence.md) and [multi-clock mask](multiclock-mask-cut.md)
with a distinct signed-law comparison; it does not replace their
chronological conclusions or alter any stage-count table.
