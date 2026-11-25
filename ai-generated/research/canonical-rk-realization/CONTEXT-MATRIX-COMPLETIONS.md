# Completing order-paid context matrices, with and without strict support

Work over a field $K$ in which $1,\ldots,p$ are units, with $p\ge 1$.
These units are also forced by the reviewed order conditions:
quadrature follows from the bushes, and the quadrature identity of
order $j$ makes $j$ a unit.

Use the [literal tree notation](../../../RKResearch/FiniteRootedTree.lean)
$\bullet$, $[t]$, and $t\mathbin{\#}u$ for a leaf, unary extension,
and rooted sum. For an actual tableau,
the [Butcher weight vector](../../../RKResearch/OrderConditions.lean)
$\boldsymbol{\Phi}_t(A)$ starts at $\mathbf{1}$, with operations
$A$ and $\odot$. Its scalar output is
$f(t)\coloneqq\mathbf{b}\cdot\boldsymbol{\Phi}_t(A)$.
The context matrix has entries $H_{C,t}\coloneqq f(C[t])$.
A context is a sequence of unary extensions and rooted sums with
fixed trees. It adds a fixed number of vertices, denoted $c(C)$.
The whole paid board consists of **all** pairs $(C,t)$ with
$c(C)+|t|\le p$, with prescribed value $1/(C[t])!$.
Rank of the whole matrix means the supremum of finite submatrix
ranks.

A completion can mean just filling entries. A stronger requirement
is that there be a single function $f$ on literal trees, so that
two insertions producing the same tree have the same value even
when unpaid. Stronger still is the following construction of $f$:
use a finite-dimensional commutative associative unital $K$-algebra
$V$ for the columns, one linear unary operator $L$, and one linear
readout $\lambda$. Start at the unit for $\bullet$, use $L$ for
$[t]$, and algebra multiplication for $t\mathbin{\#}u$. Each
context then acts linearly in its hole, so the resulting matrix
has rank at most $\dim_K V$. This allows an abstract algebra, not
necessarily the coordinatewise algebra of a Runge–Kutta tableau.

## The whole paid board has minimum rank $\lceil p/2\rceil$

Put $r\coloneqq\lceil p/2\rceil$. The lower bound even for
entrywise completions is the already fully paid bush rectangle:
for $0\le i,j<r$, let $B_j$ be the root with $j$ leaves and let
$C_i[t]\coloneqq B_i\mathbin{\#}t$. Its entry is $1/(i+j+1)$,
since its forest factorial is $1$ and its order is $i+j+1\le p$.
This Cauchy matrix is invertible. A column combination,
viewed as a rational function of the row index, gives after
clearing denominators a polynomial of degree at most $r-1$ with
zeros at $0,\ldots,r-1$. It is zero, and evaluation at the distinct
poles $-j-1$ forces all coefficients to vanish. All differences
and denominators used here are units.

For the upper bound we build a *single* completion from an algebra
of dimension $r$ over $K$. Thus repeated insertions and all
abstract algebra identities are retained, not merely the entries
of one rectangle. On polynomials of degree at most $p-1$, put
$\ell(x^j)\coloneqq 1/(j+1)$. Formal integration from zero is
$I(x^j)\coloneqq x^{j+1}/(j+1)$ in that range. The reference
polynomial for a paid tree is
$P_t\coloneqq (|t|/t!)x^{|t|-1}$, whose coefficient is the
reciprocal of the forest factorial. It starts at $1$, obeys $P_{[t]}=I P_t$ and
$P_{t\mathbin{\#}u}=P_t P_u$, and satisfies
$\ell(P_t)=1/t!$. These are the same forest-factorial rules as in
the [rectangular rank calculation](CONTEXT-MATRIX-RANK.md).

Choose a monic polynomial $q$ of degree $r$ with
$\ell(q a)=0$ for $\deg a\le p-1-r$. To do so, use the Cauchy
matrix above to solve for the $r$ lower coefficients of $q$ from
$\ell(qx^j)=0$ for $0\le j<r$. If $p=2r-1$, the last equation
uses an extra moment at degree $2r-1$; give this extra moment any
value for the purpose of the solve. It is not a required
orthogonality equation and does not change the paid $\ell$.
Write $\rho$ for polynomial remainder modulo $q$. In particular,
whenever $\deg F\le p-1$,

$$
\ell(F)=\ell(\rho F).
$$

Use $V\coloneqq K[x]/(q)$, with unary operator
$L(\overline F)\coloneqq\overline{I(\rho F)}$ and readout
$\lambda(\overline F)\coloneqq\ell(\rho F)$. Both are defined on
all of $V$ because $\deg(\rho F)<r$. Let $R_t$ be the remainder
representative of the column of $t$ in this algebra. It has
degree at most $|t|-1$: a unary extension integrates and then
takes a remainder, while a rooted sum multiplies and then takes
a remainder.

The invariant that pays for all shapes is

$$
\ell(wR_t)=\ell(wP_t)
\qquad
\text{whenever }\deg w+|t|-1\le p-1.
$$

For the leaf this is immediate. In a rooted sum, the remainder
can be removed inside $\ell(wR_{t\mathbin{\#}u})$: the
difference is a multiple of $q$ of degree at most $p-1$.
Then use the two induction hypotheses with tests $wR_u$
and $wP_t$, respectively:

$$
\ell(wR_{t\mathbin{\#}u})
=\ell(wR_tR_u)=\ell(wP_tR_u)=\ell(wP_tP_u).
$$

For a unary extension, the same weighted remainder argument
first reduces the left side to $\ell(wI(R_t))$.
Integration by parts in the paid degree range gives

$$
\ell(wI(a))=\ell\bigl((\ell(w)-I(w))a\bigr).
$$

Indeed, integrate the derivative of $I(w)I(a)$ from zero to one
and use $\ell(F)=(I(F))(1)$. The product of the antiderivatives
has degree at most $p$, so all denominators needed in this
identity are paid. The new test $\ell(w)-I(w)$ has degree at most
$\deg w+1$, within the induction budget for $t$. Apply the
induction hypothesis with this test and then reverse integration
by parts to obtain $\ell(w I(P_t))$. This proves the invariant
for all trees, since a graft is a unary extension followed by a
rooted sum. Taking $w=1$ yields the prescribed value for every
tree of order at most $p$.

Consequently the one context-consistent completion just
constructed has rank exactly $r$. It gives the ceiling for
**any selection of nonrectangular paid entries**, with no need
to make independently chosen rows agree later. No splitting
of $q$, positivity, or change of coefficient field is needed.
The argument is not an existence claim for an $r$-stage tableau
over the original field.

## Strict support raises the obstruction to $p$

Let $\operatorname{ht}(t)$ count edges in a longest root-to-leaf
path. In a strictly lower triangular tableau, every stage with
a nonzero tree column must have a path of this length ending
there in the graph of nonzero entries, with an edge from $j$
to $i$ when $A_{ij}\ne0$. The leaf, unary and product rules
prove this by induction: a unary step moves one edge, and a
nonzero product is nonzero in both factors. Thus a finite
output-relevant path bound $D$ forces $f(t)=0$ when
$\operatorname{ht}(t)>D$.

For the rank lower bound, only this eventual vanishing on
tall trees and their repeated insertion values are needed.
Write $T_0\coloneqq\bullet$, $T_{k+1}\coloneqq[T_k]$
and $m_k\coloneqq f(T_k)$. Let $U_i$ add $i$ unary roots.
The submatrix at $(U_i,T_j)$ is $m_{i+j}$ since
$U_i[T_j]=T_{i+j}$. In particular $m_{p-1}=1/p!\ne0$:
the tall tree at index $p-1$ has order $p$. A cutoff
$D<p-1$ is therefore inconsistent. If $D=p-1$, use the exact
$p$ by $p$ block with $0\le i,j<p$. Its anti-diagonal
$i+j=p-1$ equals $1/p!$, and all $i+j\ge p$ are zero.
After reversing the columns it is upper triangular with
nonzero diagonal, so has rank $p$.

More generally, for **any** finite $D$ take $d$ to be the last
index with $m_d\ne0$. The same argument on $0\le i,j\le d$
uses the anti-diagonal $i+j=d$ and the zeros $i+j>d$.
Thus the context matrix has rank at least $d+1\ge p$,
even if the actual finite cutoff is larger than $p-1$. This
works for any context-consistent completion with such a
cutoff and, in particular, for actual strict ERK. Equivalently,
any strict ERK tableau has a path of at least $p-1$ edges to an
output stage, by the nonzero paid tall moment.

These hypotheses are different from merely pinning zero
entries of a partial matrix. For example, if $D\ge 2p-2$,
start with the rank-$r$ completion above and zero every row
with $c(C)\ge p$ and every column with $|t|>p$. This keeps all
paid entries and does not increase rank. A surviving cell
has $\operatorname{ht}(C[t])\le |C[t]|-1\le 2p-2$, so this
entrywise completion meets all height-forced zeros at that
cutoff. For $p\ge2$ it cannot also meet the repeated tall
insertion values, since that would force rank at least $p$.

## Sharpness in the strict support relaxation

Use $V\coloneqq K[x]/(x^p)$, with multiplication modulo
$x^p$, projected integration $L(\overline F)\coloneqq
\overline{I(\rho F)}$ and the same readout
$\lambda(\overline F)\coloneqq\ell(\rho F)$. The tree column of
order at most $p$ is the class of $P_t$; every higher-order
column is zero because the product adds exponents and a
unary extension raises the exponent by one until it reaches
$p$. Therefore all paid outputs are correct, all outputs of
order greater than $p$ are zero, and literal insertion values
agree. This is a context matrix of rank exactly $p$: it
factors through $V$, and the tall $p$ by $p$ minor gives the
lower bound.

This construction can meet any prescribed **allowed-edge**
graph on chronological stages, as long as it contains a path
of $p-1$ edges ending at an allowed output vertex. On the
selected path, index its vertices by $0,\ldots,p-1$ and take
the strict unary matrix $N$ with only
$N_{i,i-1}\coloneqq 1/(p-i+1)$ for $1\le i<p$. Use the terminal
vertex as the only output, with weight one. Transport the
polynomial algebra to these vector coordinates by

$$
\mathcal T(x^j)\coloneqq j!N^j\mathbf{1}
\qquad (0\le j<p).
$$

The map is invertible: the column for $x^j$ vanishes at all
indices $i<j$, and its entry at $j$ is nonzero. It takes the unit to $\mathbf{1}$ and
intertwines $L$ with $N$, by the identity
$j!N^{j+1}\mathbf{1}=\mathcal T(x^{j+1}/(j+1))$ before
truncation. The terminal entry of $N^j\mathbf{1}$ is the
product of the last $j$ subdiagonal entries,
$1/(j+1)!$. Thus the terminal entry of $\mathcal T(x^j)$
is $1/(j+1)$, the required readout.

The ideals $(x^k)$ become exactly the coordinate spaces
supported on path suffixes. Multiplication preserves every
such suffix and $N$ increases its starting index. Unused
vertices can be added as independent scalar factors with
zero unary action and zero output, preserving the unit,
chronological suffix support and the allowed edges. There
is no requirement that every allowed edge be used or that
the output weights be prescribed. Conversely, in any such
relaxation a nonzero paid tall output requires the path,
since that output uses only $N^{p-1}$, the unit, and the
readout. Thus the existence of the path exactly characterizes
feasibility in this relaxation, and $p$ is the sharp rank
when it is feasible.

For $p\ge2$ the transported multiplication is **not** the
coordinatewise multiplication $\odot$: the nonzero class of
$x$ is nilpotent, which cannot happen in $K^p$ with $\odot$.
Keeping all chronological suffix ideals does not enforce
individual coordinate multiplication. In fact, a unital
bilinear multiplication with unit $\mathbf{1}$ that
preserves *every* coordinate line as an ideal must be
coordinatewise: distinct coordinate indicators multiply to
zero, and each indicator is idempotent by multiplying it by
the unit. Any bound above $p$ for genuine explicit tableaux
must use some condition not retained by the strict support
relaxation. The construction gives no actual ERK upper bound for $p\ge2$,
and it says nothing about additional diagonal, sign, or
fixed-weight conditions. A nonzero common diagonal instead
has the separate [height-equivalence result](COMMON-DIAGONAL-HEIGHT.md),
not the vanishing rule used here.
