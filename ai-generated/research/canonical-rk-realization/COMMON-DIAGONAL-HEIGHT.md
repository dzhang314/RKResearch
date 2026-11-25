# A sharp height cutoff that preserves the first distinguishing order

Let $A$ be a finite tableau over a commutative ring $R$, with readout
row $\mathbf{w}$. Write $\boldsymbol{\Phi}_t(A)$ for the
[Butcher weight vector](../../../RKResearch/OrderConditions.lean)
of a [rooted tree](../../../RKResearch/FiniteRootedTree.lean). Its
order $|t|$ counts vertices, and its height $H(t)$ counts edges. Let
$\bullet$ be the one-vertex tree, $[t]$ the extension of $t$, and
$t\mathbin{\#}u$ the rooted sum. Define the scalar weight of $t$ by

$$
f(t)\coloneqq\mathbf{w}\cdot\boldsymbol{\Phi}_t(A).
$$

For two tableaux, use their block diagonal matrix and the first
output row followed by the negative of the second. Then $f(t)$
is the difference between their scalar weights for $t$.

## The cutoff

Give each stage $i$ a nonnegative integer depth $d_i$. Fix a
nonnegative integer $D$ and a scalar $\gamma$. Assume:

- A row with $d_i\le D$ has $A_{ii}=\gamma$.
- In such a row, every nonzero off-diagonal entry $A_{ij}$ has
  $d_j<d_i$.
- Every stage with $w_i\ne 0$ has $d_i\le D$.

Rows of greater depth are unrestricted. In a lower triangular
tableau with common diagonal $\gamma$, take $d_i$ to be the longest
path ending at $i$ along nonzero strictly off-diagonal entries,
with $A_{ij}$ an edge from $j$ to $i$. The path length counts
edges. Only the depths of stages with nonzero output weight
need to be bounded by $D$. In a comparison the diagonal $\gamma$
must be shared by both output-relevant parts.

**Theorem.** For every order bound $p$, the following tests are
equivalent:

$$
\begin{aligned}
&f(t)=0 \quad\text{for every }t\text{ with }|t|\le p \\
&\quad\Longleftrightarrow\quad
f(t)=0 \quad\text{for every }t\text{ with }|t|\le p\text{ and }H(t)\le D .
\end{aligned}
$$

Thus agreement through height $D$ implies agreement on the whole
raw rooted series. If the series differ, a tree of height at most
$D$ attains the smallest distinguishing order.

## Proof

The tree orders and Butcher weight vectors satisfy

$$
\begin{aligned}
|[t]|&=|t|+1,
&
\boldsymbol{\Phi}_{[t]}(A)&=A\boldsymbol{\Phi}_t(A),\\
|t\mathbin{\#}u|&=|t|+|u|-1,
&
\boldsymbol{\Phi}_{t\mathbin{\#}u}(A)
 &=\boldsymbol{\Phi}_t(A)\odot\boldsymbol{\Phi}_u(A).
\end{aligned}
$$

A unary root adds one to height. Joining roots takes the maximum
height. Define

$$
U(h,p)\coloneqq
\operatorname{span}_R
\left\{\boldsymbol{\Phi}_t(A)\;\middle|\; H(t)\le h,\ |t|\le p\right\}.
$$

These spans are monotone in both bounds. By linearity,
$A U(h,p)\subseteq U(h+1,p+1)$. By bilinearity, the coordinatewise
product of an element of $U(h,p)$ with an element of $U(h,q)$
lies in $U(h,p+q-1)$ for positive $p,q$.

For every $h\le D$ we prove that each $\boldsymbol{\Phi}_t(A)$
can be matched on all rows of depth at most $h$ by a column
in $U(h,|t|)$. A depth-zero row has no nonzero off-diagonal entries.
On that row structural induction gives the value $\gamma^{|t|-1}$,
so a scalar multiple of the leaf column suffices.

Pass from $h$ to $h+1$ by structural induction on the tree. The
leaf is immediate. Write a graft as $t=v\mathbin{\#}[u]$. By
structural induction choose $\mathbf{V}\in U(h+1,|v|)$ and
$\mathbf{W}\in U(h+1,|u|)$ matching their respective columns
on depths at most $h+1$. By the height induction choose
$\mathbf{Q}\in U(h,|u|)$ matching $\boldsymbol{\Phi}_u(A)$
on depths at most $h$.

For a row $i$ of depth at most $h+1$, every off-diagonal term in
the $i$-th entry of $A(\boldsymbol{\Phi}_u(A)-\mathbf{Q})$
vanishes. Its diagonal term is $\gamma(W_i-Q_i)$. Therefore
$A\mathbf{Q}+\gamma(\mathbf{W}-\mathbf{Q})$ matches
$A\boldsymbol{\Phi}_u(A)$ on those rows and is in $U(h+1,|u|+1)$.
The required approximation is

$$
\mathbf{V}\odot
\bigl(A\mathbf{Q}+\gamma(\mathbf{W}-\mathbf{Q})\bigr)
\in U(h+1,|v|+|u|)=U(h+1,|t|).
$$

At $h=D$, the nonzero entries of $\mathbf{w}$ lie only on
matched rows. If the readout vanishes on all spanning columns of
height at most $D$ and order at most $p$, it vanishes on their
span and thus on every tree of order at most $p$. The converse is
immediate. The proof uses subtraction but no division,
characteristic assumption, or sign condition.

## Sharpness for each prescribed diagonal

Fix $D\ge1$ and use stages $0,\ldots,D$, with
$A\coloneqq\gamma I+N$, where $N$ has ones on the first subdiagonal
and zeros elsewhere. Over any nontrivial commutative ring, compare
the output at stage $D$ with the output at stage $D-1$.

For trees of height at most $h$, all stages with indices at least
$h$ agree. At $h=0$ this holds on $\bullet$. At $h+1$ use
structural induction at this same height bound. In a graft, both
the base factor and the diagonal contribution from its branch
agree by the same-height structural induction, since they use
proper subtrees at the original stages. The predecessor
contribution instead uses the previous height bound $h$:
the branch has height at most $h$ and both predecessor indices
are at least $h$. In particular the two outputs agree through
height $D-1$.

At the tall tree of height $D$, the stage column is
$A^D\mathbf{1}$. In the expansion of
$(\gamma I+N)^D\mathbf{1}$, the terms $N^k\mathbf{1}$
for $k<D$ agree at the two stages. The term
$N^D\mathbf{1}$ has difference $1$ and coefficient $1$.
This tree has order $D+1$, and every smaller tree has height
at most $D-1$. The first difference therefore has order $D+1$
for **each** $\gamma$, including zero and nonzero diagonals.
For $D=0$ there is no smaller nonnegative cutoff.

## Why the hypotheses matter

- Two one-stage tableaux with different diagonals and the same
  weight can agree at $\bullet$ and differ at $[\bullet]$. A
  common diagonal cannot be dropped from a depth-zero cutoff.
- Matrix nilpotence does not replace a bound on path length.
  For distinct nonzero $a,b$ in a field, let $N$ have four stages,
  with $N_{10}=a$, $N_{20}=b$, row $3$ equal to
  $(b-a,-b,a,0)$, and all other entries zero. Then $N^2=0$.
  In $A\coloneqq\gamma I+N$ stages $3$ and $0$ have the same
  row sum $\gamma$, so they agree on every tree of height at
  most one. On the unary extension of the two-leaf bush their
  difference is $ab(b-a)$. The constant and linear terms of the
  squared row sums cancel in row $3$, but the quadratic term
  does not. The actual path depth is two.
- Without a diagonal or path assumption there is a coarser
  height test over a field. If the full stage-column span has
  dimension $r>0$, height $r-1$ suffices for all-order equality.
  The height spans start with the leaf line and are closed
  under coordinatewise products. Equal successive spans are
  already invariant under $A$ and hence contain every tree
  column. Otherwise each step increases dimension. The empty
  stage set is trivial. One can therefore use the sum of the
  two stage counts minus one for a nonempty direct sum.

This is a mathematical cutoff for the raw series, separate from
[canonical realization](PROOF.md) and the checked finite comparison
certificate. It is not a stage minimum over tableaux of a fixed
classical order.
