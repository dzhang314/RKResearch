# What survives if every diagonal entry must be the same

The smaller all-unit-diagonal DIRK parity construction uses
different diagonals in different branches. Constant diagonal
is not obtained by calling its blocks singly diagonal. This
note separates the restrictions of symmetric extrapolation
from a refinement of the already published donor construction.

## Limits of fixed-diagonal midpoint powers and symmetric blocks

Let $\gamma\ne0$ over $\mathbb Q$. First allow different
total branch times. Take any number of midpoint substeps of
normalized width $2\gamma$, optionally followed by one
implicit Euler halfstep of normalized width $\gamma$.
All these are legitimate common-$\gamma$ branches.
On a branch of total normalized time $T$, the raw reads
of the order-three bush $B$ and tall tree $L$ are
$$
\begin{array}{c|cc}
 & L & B\\ \hline
\text{midpoints only}
  &T^3/6+\gamma^2T/3 &T^3/3-\gamma^2T/3\\
\text{with terminal implicit Euler}
  &T^3/6+5\gamma^2T/6&T^3/3+2\gamma^2T/3 .
\end{array}
$$
These are direct sums at the stage clocks
$\gamma(2j-1)$. For example the midpoint row
applied to the clock vector gives
$\gamma^2(2j^2-2j+1)$; the terminal halfstep
changes only its last weight from $2\gamma$
to $\gamma$. Thus in both cases
$2L-B=\gamma^2T$. Every output-weighted
combination consistent through order one has
weighted time $1$, so this contrast is
$\gamma^2\ne0$. No choice of branch lengths
or extrapolation weights in this architecture
gives order three. This proof also applies to
paid rings when $\gamma$ is a unit.

A broader limit applies to normalized consistent
selfadjoint blocks. A genuine common-$\gamma$
RK block has scalar stability
$R(z)=P(z)/(1-\gamma z)^m$ after cancellation.
If $R(z)R(-z)=1$, the numerator must be
$(1+\gamma z)^m$ by factorization and $P(0)=1$.
Consistency gives $2m\gamma=1$. All normalized
consistent selfadjoint blocks with that one
diagonal therefore have the same scalar stability,
and its formal logarithm starts as
$$
                           z+(\gamma^2/3)z^3+\cdots .
$$
In particular an affine combination of such
blocks cannot remove the third-order tall
defect. This uses only scalar reciprocity, which
is necessary for nonlinear selfadjointness.
The same obstruction to a third-order identity
follows after specialization to any residue
field with $3!$ and $\gamma$ units.

Neither limit applies to all nonsymmetric
common-diagonal methods. For example, a
composition of one-stage updates with effective
weights $w_i$ and fixed stage diagonal
$\gamma$ has the extra contrast term
$\sum_{i>j} w_iw_j(2\gamma-w_j)$ in
$2L-B-\gamma^2\sum_i w_i$, so arbitrary strict
weights are not covered by the midpoint
identity. As a concrete different construction,
the tableau with rows $(1)$, $(-1,1)$,
$(-1,2,1)$, and weights $(2/3,5/12,-1/12)$,
has clocks $(1,0,2)$, the three bush moments,
and $\mathbf b\cdot A\mathbf c=1/6$.
Its next bush read is zero, so it has exact
order three over $U_3$ with common unit
diagonal $1$.

## Stage reuse and a unit defect in the published donor method

The order-raising row formula here is not a new
existence theorem. The existing
[prescribed common diagonal construction](../exact-order-over-rings/PRESCRIBED-COMMON-DIAGONAL.md)
gives all orders with an added tall correction,
and the [quadrature donor realization](../quadrature-donor-realization/realization.md)
gives the row solve with prescribed output support
and weights. We use exactly that donor step.

A row of clock $x$ is pure through tree order $g$
when its stage values through that order are
$x^{|t|-1}/F(t)$, with $F(t)=\prod t_{\rm child}!$.
With $g-1$ existing pure-order-$(g-1)$ donors
at clocks $z_j$ having unit differences, a new
row of clock $x$ and diagonal $d$ can be
made pure through order $g$ by solving
$$
 \sum_j a_j z_j^k=\frac{x^{k+1}}{k+1}-d x^k
                   \qquad(0\le k\le g-2).
$$
The unit Vandermonde makes this a solve over
the ring. Induct on the child tree, not on
implicit stage evaluations: the diagonal term
uses a smaller tree at the new stage and
cancels the $d x^k$ term. This is the
published pure-tree donor proof.

For $p\ge3$, the initial diagonal-only row
at clock $\gamma$ is already pure through
order two. Reuse it in that bank, adding only
one row of clock $\gamma+1$ with entry $1$
from the first row and diagonal $\gamma$.
Then build banks of sizes $3,\ldots,p-1$
as before, and build the final pure-order-$p$
rows. Consecutive integer labels, or their
translations, give all needed unit gaps.
This saves one helper compared with rebuilding
a two-row bank from the initial stage.

One exact construction uses $p+1$ final rows.
At consecutive clocks $0,\ldots,p$ solve
$$
             \sum_i b_i c_i^k=\frac1{k+1}\ (0\le k<p),
             \qquad \sum_i b_i c_i^p=0 ,
$$
by a unit Vandermonde. The second equation
specifies zero, not the unpaid value $1/(p+1)$.
The pure-order-$p$ rows turn the first
equations into every paid rooted condition,
and the next bush has cleared defect $-1$.
Counting the reused bank gives
$\binom p2-1+(p+1)=p(p+1)/2$ stages.
For $p=2$, use the initial row at $\gamma$
as one of three active pure-order-two rows,
adding clocks $\gamma+1,\gamma+2$ and solving
the three displayed moments. This has the
same bound. At $p=1$ arbitrary prescribed
$\gamma$ need not permit one stage (take
$\gamma=1/2$); use a second row of clock
zero with weight one if necessary. When
$\gamma=1$ is chosen, implicit Euler alone
already has exact order one.

There is also a support-preserving unit refinement
of the published one-extra-donor step. For $p\ge2$ and any
given paid scalar quadrature with masses $\mu_x$
at its $m$ contributing clocks, enlarge the
last helper bank to $p$ pure-order-$(p-1)$
donors. Keep the paid donor equations and set
their extra moment so that
$$
  (A\mathbf c^{p-1})_i=x^p/p+\eta
       \quad\text{at every active row of clock }x,\qquad
  \eta=-\frac{\sum_x\mu_x x^p}{p}.
$$
All rows use the **same** $\eta$. The added
equation is solvable by the enlarged unit
Vandermonde and does not affect any paid tree.
The unary graft of the $p$-vertex bush has
raw read
$$
             \sum_x\mu_x(x^p/p+\eta)=0
$$
since the masses sum to one. Its cleared defect
is therefore $-1$, stronger than just
choosing a nonzero defect separately in each
coefficient ring. This does not divide by
$p+1$ or any individual mass. With the
pure-two reuse, for $p\ge3$ the count is
at most $\binom p2+m$. In particular, an
ordinary $p$-node unit-Vandermonde quadrature
gives the same $p(p+1)/2$ bound with at most
$p$ active sites and a unit non-bush defect.
The $p=2$ support-preserving perturbation
itself uses two helper leaf rows, as in the
published construction.

These are refinements of existing donor-stage
realization and a precise limit on symmetric
extrapolation, not an SDIRK stage minimum.
Choosing $\gamma=1$ gives a genuine common
unit diagonal over $U_p$ and under every
allowed nonzero base change.
