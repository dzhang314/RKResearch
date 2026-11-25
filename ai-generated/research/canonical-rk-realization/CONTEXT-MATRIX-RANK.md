# Context-matrix rank of the complete and order-limited rooted series

Let $\boldsymbol{\Phi}_t(A)$ be the
[Butcher weight vector](../../../RKResearch/OrderConditions.lean)
of the rooted tree $t$. Define the scalar weight by

$$
f(t)\coloneqq\mathbf b\cdot\boldsymbol{\Phi}_t(A).
$$

The order $|t|$ counts vertices. Write $\bullet$ for the leaf,
$[t]$ for adding a unary root, and $t\mathbin{\#}u$ for joining
roots. In particular,

$$
\boldsymbol{\Phi}_\bullet(A)=\mathbf{1},\qquad
\boldsymbol{\Phi}_{[t]}(A)=A\boldsymbol{\Phi}_t(A),\qquad
\boldsymbol{\Phi}_{t\mathbin{\#}u}(A)
=\boldsymbol{\Phi}_t(A)\odot\boldsymbol{\Phi}_u(A).
$$

A context $C$ starts with one hole and applies a finite sequence of
two operations to the current tree: add a unary root, or join its root
with the root of a fixed tree. Write $C[t]$ for insertion. This is the
literal context syntax in
[the reviewed split comparison](../../lean/RKCert/ReviewedNative/CanonicalSplitUniqueness.lean).
The context matrix is

$$
H_{C,t}\coloneqq f(C[t]).
$$

The two results below distinguish the complete matrix from a
rectangle whose every entry is fixed by the order conditions.

## The complete matrix recovers the canonical width

Over a field, define $\operatorname{rank}H$ as the supremum of
the ranks of the finite submatrices. Each finite-stage realization
gives a factorization: the column at $t$ is
$\boldsymbol{\Phi}_t(A)$, and the row at $C$ applies the unary
matrix actions and the fixed coordinatewise multipliers of $C$
to an arbitrary stage column, then applies the output row.
The latter is linear in the stage column. A realization with $s$
stages therefore bounds every finite submatrix rank by $s$.

Now use the [canonical reduction](PROOF.md): coalesce identical
full profiles, then restrict the aggregate tableau to its visible
stages. Let the resulting width be $r$. Its raw outputs are unchanged.
The [native reduction and uniqueness proof](../../lean/evidence/canonical-root-integration/README.md)
establishes the two properties used here: the literal columns span
the full coordinate space of the reduced tableau, and each remaining
coordinate can be observed. More specifically, the
[visibility proof](../../lean/RKCert/ReviewedNative/CanonicalVisiblePrune.lean)
uses a path of nonzero entries to a stage with nonzero output weight.
Gating by the coordinate indicator after each action makes the
readout a nonzero multiple of the initial coordinate. A visible
stage need not itself have nonzero output weight.

Those gates do not require extra rows in $H$. Each coordinate
indicator on the reduced tableau is a finite linear combination
of literal tree columns, since those columns span the full space.
Hence multiplication by an indicator is the same combination of
multiplications by literal columns. Expanding a finite composition
one multiplier at a time expresses each path readout as a finite
linear combination of the literal context rows. The nonzero path
coefficients are invertible in the field, so the literal rows span
the entire dual of the reduced stage space.

Choose $r$ independent **literal** rows, and independently $r$
independent **literal** columns. The resulting square submatrix
factors as the corresponding basis-of-rows matrix times the
basis-of-columns matrix. Both are invertible, so this submatrix
has rank $r$. For $r=0$ every entry vanishes. Consequently

$$
\boxed{\operatorname{rank}H=r.}
$$

In particular this width is minimal among finite tableaux with the
same complete raw series. This is a mathematical consequence of the
canonical properties, not a separate stage-minimum theorem claimed
by the cited Lean audit and not a minimum at a fixed classical order.

For explicit midpoint over $\mathbb Q$, with row $(0,1)$ and the
sole nonzero matrix entry $A_{21}=1/2$, use columns $\bullet$ and
$[\bullet]$. The rows that join a root with those same two trees give
the first matrix below. The empty and unary contexts instead give
the second:

$$
\begin{pmatrix}1&1/2\\1/2&1/4\end{pmatrix}
\qquad\text{and}\qquad
\begin{pmatrix}1&1/2\\1/2&0\end{pmatrix}.
$$

The ranks are one and two, respectively. The unary context sees the
effect of the first stage despite its zero output weight.

## The exact ceiling for a fully paid rectangular block

Let $p\ge 1$, and select finite nonempty sets of contexts and input
trees such that every selected entry has $|C[t]|\le p$. Let $c(C)$
be the number of vertices the context adds, independent of its input.
It is one per unary root, plus $|u|-1$ per root join with $u$.
Put $g\coloneqq\max_C c(C)$. Every input then satisfies $|t|\le p-g$.

Assume the reviewed order conditions through $p$, written
$\operatorname{RKOC}(p)$. For a paid tree $t$, they prescribe
$f(t)=1/t!$, where $t!$ is the reviewed tree factorial. All integers
from $1$ to $p$ must be units: this also follows directly from
the [reviewed quadrature consequence](../../../RKResearch/OrderConditions.lean).
If considering only the formal order data, assume these integers
are nonzero in the field. That suffices even in positive
characteristic.

For the reference calculation, let $I$ be formal integration from
zero, with $I(x^h)\coloneqq x^{h+1}/(h+1)$ wherever paid. The reference
polynomial of a tree is

$$
P_t(x)\coloneqq\frac{|t|}{t!}x^{|t|-1}.
$$

The leaf has polynomial $1$, unary extension applies $I$, and root
join multiplies the two polynomials. This follows directly from the
reviewed forest factorial: it multiplies under root join, and the
forest factorial after a unary extension is $t!$. Applying $I$ once
more and evaluating at $1$ gives $1/t!$. This is a calculation of
the prescribed output, not an assumption that the actual stage
column is a monomial.

Scale each selected column by its input tree's forest factorial,
which is a unit. Its input polynomial is now $x^h$ with
$h=|t|-1$. Different shapes with the same input order then give
identical scaled columns. There are at most $p-g$ different orders.

A context now acts on $x^h$ by unary integrations and multiplication
by fixed monomials. An integration contributes a denominator
$h+\ell$, where $\ell$ is the cumulative increase in the exponent
immediately after that integration. These $\ell$ are strictly
increasing, even if some root joins add zero vertices. The last
integration, for the scalar output, has $\ell=c(C)+1$. Thus the
row has the form

$$
a_C\prod_{\ell\in L_C}\frac{1}{h+\ell},
\qquad L_C\subseteq\{1,\ldots,g+1\},
$$

with a scalar $a_C$ independent of $h$. Partial fractions give

$$
\prod_{\ell\in L_C}\frac{1}{z+\ell}
=\sum_{\ell\in L_C}\frac{1}{z+\ell}
  \prod_{\substack{m\in L_C\\m\ne\ell}}\frac{1}{m-\ell}.
$$

Indeed, after clearing denominators the two sides are polynomials
of degree at most $|L_C|-1$. They agree at the $|L_C|$ distinct
points $z=-\ell$. Every nonzero difference $m-\ell$ is a unit,
since its absolute value is at most $g$. Each evaluation at an allowed $h$ is defined because
$1\le h+\ell\le p$. The scaled rows therefore lie in the span of
the at most $g+1$ single-pole rows. More precisely, only the poles
in $\bigcup_C L_C$ and the distinct input orders matter. In
particular the original block has rank at most

$$
\boxed{\min(g+1,p-g)\le\left\lceil\frac p2\right\rceil.}
$$

To attain the ceiling, set $r\coloneqq\lceil p/2\rceil$.
For $0\le i,j<r$, use the bush $[\bullet]^{\# j}$, the rooted
sum of $j$ copies of $[\bullet]$, with $[\bullet]^{\#0}$ the
one-vertex tree. Define the contexts by

$$
C_i[t]\coloneqq [\bullet]^{\# i}\mathbin{\#}t.
$$
The entries are exactly $1/(i+j+1)$, without rescaling, because
each bush has forest factorial $1$. The largest order is
$2r-1\le p$. To see that the square block is nonsingular, suppose
a column combination vanishes. Clearing the distinct factors
$x+j+1$ yields a polynomial of degree at most $r-1$ that vanishes
at $x=0,\ldots,r-1$, so it is zero. Evaluating at $x=-j-1$
then forces the $j$-th coefficient to vanish. All factors used
are units under the stated hypothesis. This attains the rank
ceiling; it does not construct an $r$-stage tableau of order $p$.

Thus a rank test using a fully paid rectangle of this form cannot
certify more than $\lceil p/2\rceil$ stages from the order-prescribed
entries. This does not limit arguments using nonrectangular
conditions, unpaid entries constrained by the tableau, or additional
chronology or sign information.
