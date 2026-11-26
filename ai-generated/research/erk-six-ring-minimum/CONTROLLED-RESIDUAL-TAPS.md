# Moving repeated clocks: an exact controlled-tail criterion

A repeated physical stage lets one reallocate an output weight without
changing pooled quadrature. That operation alone does not preserve the
non-bush rooted equations. The criterion below describes exactly when
a fixed prefix can be extended by terminal copies at selected clocks
so as to repair those equations by linear row corrections. An independent
clock-polynomial test helps choose the clocks before building the tails.

Work over a nonzero commutative unital ring $R$ in which $p!$ is a
unit. All divisions by rooted tree factorials of orders at most $p$
and by positive integers at most $p$ are therefore allowed. Let
$A$ be a strict prefix tableau with $n$ stages, $\mathbf b$ its
prefix readout, $\mathbf c\coloneqq A\mathbf1$ and
$C\coloneqq\operatorname{diag}(\mathbf c)$. Write
$\mathbf h_t\coloneqq\boldsymbol{\Phi}_t(A)$. The prefix is
not assumed to have order $p$.

## 1. The fixed-prefix correction problem

Choose an integer $2\le d\le p+1$ with $2d>p-1$. A small child has
order less than $d$. Select prototype stages $i_1,\ldots,i_m$ at
clocks $\xi_k\coloneqq c_{i_k}$, with each $\xi_j-\xi_i$ for
$i\ne j$ a unit. Assume the prototype rows $\mathbf a_{i_k}$
have the following exact small-child values:
$$
 \mathbf a_{i_k}\cdot\mathbf h_v=\xi_k^{|v|}/v!
                  \qquad (|v|<d).
$$
Append $m$ mutually independent final rows. For each $k$ put
any unit $w_k$ of output weight there and subtract $w_k$ from
the original prototype weight. Initially let that final row
copy the prototype, padded to the first $n$ donor stages; this
leaves the entire scalar rooted output unchanged. Permit only
row changes of the form
$$
 \mathbf a_{i_k}+\mathbf L_k/w_k,\qquad
 \mathbf L_k\in\operatorname{Hom}_R(Q,R),\quad
 Q\coloneqq R^n/\operatorname{span}_R\{\mathbf h_v:|v|<d\},
$$
where a functional on $Q$ is pulled back to a row on $R^n$.
The rows stay strict since they still use only prefix donors.
Since the leaf column is $\mathbf1$, the added rows keep their
clocks and **all pooled quadrature weights remain unchanged**.

For a baseline tree $t$ of order at most $p$ define its desired
output correction by
$$
 \Delta_t\coloneqq \frac1{t!}-\mathbf b\cdot\mathbf h_t.
$$
At most one root child can have order at least $d$. If it is
$u$, write $r$ for the sum of the orders of the other children.
Any such $r$ can also be used as a number of leaf siblings.
The correction required with that canonical all-leaf remainder is
$$
 F_r(u)\coloneqq
 \frac{1}{u!(|u|+r+1)}-\mathbf b\cdot C^rA\mathbf h_u,
 \qquad d\le |u|,\quad |u|+r+1\le p .
$$
Let $\overline{\mathbf h}_u$ be the image of $\mathbf h_u$ in $Q$.
Write $P(T)\coloneqq\prod_{k=1}^m(T-\xi_k)
=T^m+\sum_{j=0}^{m-1}p_jT^j$.

**Criterion.** There is an order-$p$ corrected tableau of this
form if and only if all four tests below hold.

1. If all root children of a paid tree $t$ are small, then
   $\Delta_t=0$ already.
2. If $t$ has the big child $u$ and small-child list $S$ of
   total order $r$, then
   $\Delta_t\prod_{v\in S}v!=F_r(u)$. In particular different
   small-sibling shapes with the same $r$ must agree after
   the displayed normalization.
3. For each $j=0,\ldots,m-1$ there is an $R$-linear map
   $G_j:Q\to R$ equal to $F_j(u)$ at every
   $\overline{\mathbf h}_u$ for which $j$ is paid.
4. The remaining values obey the clock recurrence on every
   paid window:
   $F_{r+m}(u)+\sum_{j=0}^{m-1}p_jF_{r+j}(u)=0$.

**Proof.** The child columns at each added row are unchanged on
its donors, and each tap vanishes on the small ones. The only
varying factor in the root product is therefore the one for
the big child, when present. Taking the difference between
the final and baseline outputs gives
$$
 \frac{1}{\prod_{v\in S}v!}
       \sum_{k=1}^m \xi_k^r\,\mathbf L_k(\overline{\mathbf h}_u).
$$
The corresponding difference is zero when there is no big
child. This proves necessity of the first two tests, and the
last two follow by taking $G_j=\sum_k\xi_k^j\mathbf L_k$
and using $P(\xi_k)=0$.

Conversely, solve the Vandermonde system
$G_j=\sum_k\xi_k^j\mathbf L_k$ for $0\le j<m$ in
$\operatorname{Hom}_R(Q,R)$. The determinant is a product of
the unit clock differences. For a fixed big child all the
paid values of $r$ form an initial interval starting at
zero. Hence its required values and the new tap expression
agree throughout the interval by the monic recurrence;
there is no condition at an unearned order. The first two
tests then cover every root shape. Multiplying back by
$t!$ proves the literal cleared conditions.

### Paying the first two tests and extending the taps

The first two tests follow, for instance, from exact pooled
quadrature through degree $p-1$ and the small-child values
being exact at every prefix stage of nonzero weight. Over a
ring it suffices more generally that $b_i$ annihilate each
individual small-child discrepancy at stage $i$. A telescoping
product expansion then replaces the small factors by their
reference values in the weighted readout. The prototypes
themselves still need exact unweighted small-child values.
The stated tests can also be checked directly without such
pointwise stage hypotheses.

Over a field, test 3 only asks that the prescribed values
kill all linear relations among the indicated class columns.
The resulting functional extends from their span to $Q$.
Over a ring, such an extension is automatic if the indicated
span is a direct summand of $Q$, but not from a rank count
alone. The criterion uses actual extensions. Equivalently,
the fixed-prefix equations can be viewed as one finite
linear system in the row coefficients of the $\mathbf L_k$.
This system can be checked at all maximal localizations:
its target is in the image exactly when its class in the
cokernel is zero, which is detected by those localizations.
This does not justify gluing different nonlinear tableau
prefixes or testing only their residue-field images.

### Two taps at orders seven and eight

With $m=2$ the new condition reads
$$
 F_{r+2}(u)=(\xi_1+\xi_2)F_{r+1}(u)-\xi_1\xi_2F_r(u).
$$
For $p=7$ or $8$, choose $d=4$. At $p=7$ the only recurrence
test is $r=0$ for children of order four. At $p=8$ there are
$r=0,1$ tests for order-four children and $r=0$ for
order-five children, in addition to the other three
conditions. If over a field the first two functionals are
independent on the common child span where $F_2$ is paid,
the recurrence at $r=0$ determines the sum and product of
any two successful clock labels there. It does not ensure
that these roots are available prototype labels. Two physical
tails at the same clock give just one tap in the displayed
output formula and do not provide this extra mode.

The cutoff is real: once the tree $[u,u]$ of order $1+2d$
is paid, a tap on an order-$d$ child generally contributes
the quadratic term $\mathbf L_k(\overline{\mathbf h}_u)^2/w_k$.
The affine criterion does not include such conditions. At
order six, the endpoint family in
[the optional endpoint family](OPTIONAL-ENDPOINT-FAMILY.md)
is the $d=3$ mechanism with one label and one terminal copy.

## 2. A donor-local clock filter before construction

This separate necessary test does not require exact small-child
values. Suppose a triangular tableau has order $p$ through its
rooted equations. For a chosen monic clock polynomial $P$
of degree $m$, let $D$ be any donor set such that
$P(c_i)=0$ for every contributing receiver $i$ of each
$j\in D$; contributing means $b_i A_{ij}\ne0$.
For $j\notin D$, require either $f(c_j)=0$ or
$(\mathbf b\cdot C^\ell A)_j=0$ for all $0\le\ell\le m$,
where $f$ is a polynomial. Then by pooling the receiver
terms column by column,
$$
          \mathbf b\cdot P(C)A f(\mathbf c)=0.
$$
If $\deg f+m+2\le p$, the rooted equations pay each monomial
of this expression: the structural operation is a bush,
a unary graft, and some additional leaves. The reference
value of $C^\ell A\mathbf c^j$ is the iterated moment
$1/((j+1)(\ell+j+2))$. Thus the clock ansatz must satisfy the
exact algebraic condition
$$
     \int_0^1 P(X)\left(\int_0^X f(Y)\,dY\right)dX=0 .
$$
Here the integrals just mean the indicated paid polynomial
coefficient divisions over $R$; no positivity is used.

For the seven-stage derivation choose $D=\{4,5,6,7\}$,
$P(X)=(X-1)(X-1/2)$ and $f(X)=X(X-c_3)$. Donors 1 and 3
are masked, while the stage-2 integration defect kills its
three paid taps. The iterated moment is $(3c_3-2)/720$.
This forces the clock used in the certificate. The same
filter can constrain other two-label suffixes using paid
polynomials, before solving for any tail coefficients.

These are construction and rejection criteria for fixed
prefixes and clock placements, not order-seven or
order-eight existence, optimal width, or a claim about
the first unpaid defect of a repaired tableau.
