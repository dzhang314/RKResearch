# The exact seven-stage minimum for explicit order six over rings

Let $R$ be a nonzero commutative unital ring, and use the
factorial-cleared Runge–Kutta order conditions. An explicit method of
exact order six exists over $R$ if and only if $720$ is a unit.
When it exists, the minimum is **seven stages**.

The six-vertex tall tree has tree factorial $720$. Its cleared
equation forces $720$ to be a unit, independently of the stage count.
The existing [uniform explicit lower bound](../../lean/RKCert/ReviewedNative/ERKUniform.lean)
applies over every nonzero commutative unital ring and gives
$\max(6,\lfloor(3\cdot 6+1)/2\rfloor-2)=7$. That lower bound is
already formalized in Lean. The construction below has a separate
exact arithmetic certificate.

## Seven-stage tableau

The matrix is strictly lower triangular. The row at stage $i$ lists
columns $1$ through $i-1$.

| Stage | Row of $A$ | Weight |
|:---|:---|:---|
| 1 | none | $11/120$ |
| 2 | $1/3$ | $0$ |
| 3 | $0,\ 2/3$ | $27/40$ |
| 4 | $1/12,\ 1/3,\ -1/12$ | $27/40$ |
| 5 | $7/4,\ -9,\ 9/4,\ 6$ | $1/12$ |
| 6 | $-3/64,\ 9/8,\ -9/64,\ -27/64,\ -1/64$ | $-8/15$ |
| 7 | $-65/4,\ 81,\ 9/4,\ -33,\ -1,\ -32$ | $1/120$ |

The stage clocks are $0,1/3,2/3,1/3,1,1/2,1$. Compared with the
first rational tableau in
[Butcher's 1964 paper](https://doi.org/10.1017/S1446788700023387),
one midpoint stage is moved to the terminal endpoint: stages 5 and 7
have clock $1$ and split its pooled weight $11/120$. The midpoint has
a single weight $-8/15$. This keeps the pooled quadrature unchanged,
but it does not by itself imply order six. The change in the strict
rows is essential.

Set
$$
 U \coloneqq \mathbb Z[1/30].
$$
All entries of the tableau belong to $U$. The [exact checker](check.py)
verifies the factorial-cleared equations over $\mathbb Q$, hence over
its subring $U$. It represents each rooted tree by the sorted tuple of
the trees at its root. The empty tuple is $\bullet$. For a given size
it enumerates every multiset of children whose total size is one less.
The recursion computes $\boldsymbol{\Phi}_t(A)$ by taking the
coordinatewise product of $A\boldsymbol{\Phi}_u(A)$ over those
children, starting with the all-ones vector for $\bullet$. It checks
$$
 t!\,\mathbf b\cdot\boldsymbol{\Phi}_t(A)=1
$$
for all 37 rooted trees through order six. The counts by order are
$1,1,2,4,9,20$, and the checker verifies uniqueness as well as the
equations. The replay uses exact fractions, not approximations, and
requires only the Python standard library.

For the seven-vertex tall tree, the only contributing path uses all
seven stages. Its weighted product is
$$
 \left(-\frac4{15}\right)
 \left(-\frac1{64}\right)6
 \left(-\frac1{12}\right)\frac23\frac13
 =-\frac1{2160},
$$
where the first factor is the product of the final weight and the
coefficient from stage 6 to stage 7. Its cleared defect is
$7!(-1/2160)-1=-10/3$, a unit of $U$. If $720$ is a unit in $R$,
then $2,3,5$ are units and there is a unital map $U\to R$. The
polynomial order identities and the unit defect survive this map.
Consequently the method has exact order six in every such $R$,
including residue characteristic seven. There is no need to invert
$7$ or to choose a square root.

The previous [eight-stage pole split](../erk-six-ring-witness/README.md)
provides a reusable denominator-removal argument but is no longer
the best stage count for this problem. No literature priority claim is
made for the literal seven-stage tableau.
