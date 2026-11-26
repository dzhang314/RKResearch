# An eight-stage explicit method of exact order six over every admissible ring

Let $R$ be a nonzero commutative unital ring. The factorial-cleared
six-vertex tall-tree equation implies that $720$ is a unit. Thus a
necessary condition for order six is that $2,3,5$ are units. The
eight-stage tableau below shows that this condition is also sufficient
for exact order six. Here $U$ denotes $\mathbb Z[1/30]$. The argument
does not settle whether seven stages suffice over $U$.

The tableau is strictly lower triangular. The entries of each displayed
row of $A$ start at its first column, and the remaining entries are zero.

| Stage | Row of $A$ through column $i-1$ at stage $i$ | Weight |
|:---|:---|:---|
| 1 | none | $11/120$ |
| 2 | $1/3$ | $0$ |
| 3 | $0,\ 2/3$ | $27/40$ |
| 4 | $1/12,\ 1/3,\ -1/12$ | $27/40$ |
| 5 | $-1/16,\ 9/8,\ -3/16,\ -3/8$ | $-4/15$ |
| 6 | $0,\ 9/8,\ -3/8,\ -3/4,\ 1/2$ | $-4/15$ |
| 7 | $-1/2,\ 3/2,\ 0,\ 0,\ 0,\ 0$ | $1/12$ |
| 8 | $29/4,\ -24,\ 63/4,\ 18,\ 0,\ -16,\ 0$ | $1/120$ |

## Why splitting one row removes the denominator

The first six rows and weights are from the first rational seven-stage
tableau in [Butcher, *On Runge–Kutta processes of high order*](https://doi.org/10.1017/S1446788700023387).
Its last row and weight are
$$
 \mathbf a \coloneqq (9/44,-9/11,63/44,18/11,0,-16/11),
 \qquad b_7 \coloneqq 11/120.
$$
The entries of $\mathbf a$ need $11$ inverted. Write the new rows using
$$
 \mathbf a_0 \coloneqq (-1/2,3/2,0,0,0,0),
 \qquad \mathbf r \coloneqq 11(\mathbf a-\mathbf a_0).
$$
Both $\mathbf a_0$ and $\mathbf r$ belong to $U^6$.
The rows $\mathbf a$ and $\mathbf a_0$ each sum to $1$.
Their dot products with the first six clocks
$(0,1/3,2/3,1/3,1/2,1/2)$ are both $1/2$.
Hence $\mathbf r$ annihilates the first-six-stage Butcher weight
vectors for the only two trees of order less than three, namely
$\bullet$ and $[\bullet]$.

For a tree $t$, let $P_t(z)$ denote the entry of the Butcher weight
vector at a stage with row $\mathbf a_0+z\mathbf r$ acting on the
first six stages. The rooted-tree recurrence expresses $P_t(z)$ as
the product, over the children of the root, of their weight vectors'
dot products with this row. Only a child of order at least three
can give a factor that depends on $z$. If $|t|\le 6$, the
children cannot include two such trees, since the root itself
contributes one vertex. Thus $P_t(z)$ is affine, and
$$
 \frac{11}{120}P_t(1/11)
   =\frac{1}{12}P_t(0)+\frac{1}{120}P_t(1).
$$
The two new stages use only the first six stages, so their joint
contribution agrees with the old last stage for every tree of order
at most six. The first six stages are unchanged.

The same identity holds for the seven-vertex tall tree, since its
root has only one child. Its read is $-1/2160$, giving cleared
defect $7!(-1/2160)-1=-10/3$, a unit of $U$. The identities
proved over $\mathbb Q$ hold in its subring $U$, and are preserved
by every unital map $U\to R$. The unit defect remains nonzero in
every such nonzero $R$.

[The independent exact checker](check.py) enumerates all 37 rooted
trees through order six, verifies the equations for the eight-stage
tableau directly, checks the prime support of every denominator, and
checks the tall-tree defect. It requires only Python's standard
library. The construction and replay are not a Lean certificate.

## The row argument in general

The same split works at order $p$ if a terminal row is
$\mathbf a_0+\mathbf r/\ell$, its output weight is $\ell u$,
and $\mathbf r$ annihilates the preceding-stage weight vectors for
every tree of order less than $d$, where $2d>p-1$. The two rows are
$\mathbf a_0,\mathbf a_0+\mathbf r$ with weights
$(\ell-1)u,u$. Here the original coefficients are understood over a
localization in which $\ell$ is a unit, and the coefficient ring is
assumed to embed in that localization. All other rows and weights
must already belong to the coefficient ring. No later stage may
use the old row. The argument does not glue local solutions.
