# Exact dependency depth for a fixed SDIRK diagonal

Let $K$ be a field of characteristic zero, fix $\gamma\in K$ with
$\gamma\ne0$, and let $p\ge2$. Here a strict SDIRK tableau has a lower
triangular matrix $A$ whose diagonal is everywhere $\gamma$. Its
dependency graph has an edge $j\to i$ for each nonzero **off-diagonal**
entry $A_{ij}$. The depth is the maximum length, in edges, of a path
ending at a stage with nonzero output weight. A path of length zero
is allowed. The order-one condition ensures that some output weight
is nonzero.

**Theorem.** Among finite strict SDIRK tableaux over $K$ with this
diagonal and exact algebraic order $p$, the least dependency depth is

$$
\boxed{
D_{\min}(p,\gamma)=
\begin{cases}
p-2,& L_{p-1}^{(1)}(1/\gamma)=0,\\
p-1,& L_{p-1}^{(1)}(1/\gamma)\ne0.
\end{cases}}
$$

Here $L_m^{(1)}$ is the generalized Laguerre polynomial in the
normalization specified below. The widths are unrestricted and the
output weights need not be positive. Exact order means the full
[reviewed rooted-tree conditions](../../../RKResearch/OrderConditions.lean)
hold through order $p$ and fail at order $p+1$. The theorem is not a
minimum-stage or stability assertion.

## 1. Rooted outputs and diagonal shift

Use the [reviewed tree notation](../../../RKResearch/FiniteRootedTree.lean):
$\bullet$ is the leaf, $[t]$ adds a unary root, and $t\mathbin{\#}u$
joins roots. The order $|t|$ counts vertices and the height
$\operatorname{ht}(t)$ counts edges. Write $\boldsymbol{\Phi}_t(A)$ for
the Butcher weight vector. Define the scalar weight by
$$
f_{A,\mathbf{b}}(t)\coloneqq\mathbf{b}\cdot\boldsymbol{\Phi}_t(A).
$$
The Butcher weight vectors satisfy

$$
\boldsymbol{\Phi}_\bullet(A)=\mathbf{1},\qquad
\boldsymbol{\Phi}_{[t]}(A)=A\boldsymbol{\Phi}_t(A),\qquad
\boldsymbol{\Phi}_{t\mathbin{\#}u}(A)
=\boldsymbol{\Phi}_t(A)\odot\boldsymbol{\Phi}_u(A).
$$

Sibling permutation leaves the stage column unchanged because its
root factors are multiplied coordinatewise. The tree factorial $t!$
is the product of the orders of the rooted subtrees at all vertices,
and it too is unchanged. We therefore work on **rooted-tree isomorphism
classes with unordered children**. An assignment on literal ordered
tree expressions is covered only if it is constant on these classes.
The exact-flow target is $F(t)\coloneqq1/t!$.

For an edge set $S\subseteq E(t)$, contract its edges to obtain $t/S$,
preserving the root. For a scalar $\eta$ define

$$
(\mathcal S_\eta f)(t)\coloneqq
\sum_{S\subseteq E(t)}\eta^{|S|}f(t/S).
$$

Then $f_{B+\eta I,\mathbf{b}}=\mathcal S_\eta f_{B,\mathbf{b}}$.
To see this, expand the stage column at a fixed root stage as a sum
over labels of the other vertices by stage indices. Each edge from
a child $v$ to its parent $u$ contributes $A_{\sigma(u),\sigma(v)}$.
Taking the diagonal term $\eta I$ on precisely the selected edges
forces their endpoint labels equal. The remaining labels and edge
factors are exactly those of the contracted tree for $B$. The
expansion counts each subset once, even if different subsets give
isomorphic contractions.

Two consecutive contractions amount to choosing disjoint subsets
of the original edges. Grouping by their union and applying the
binomial formula shows
$\mathcal S_\alpha\mathcal S_\beta=\mathcal S_{\alpha+\beta}$;
in particular $\mathcal S_{-\gamma}$ inverts $\mathcal S_\gamma$.
Every nonempty contraction lowers order. Consequently the transform
preserves agreement through any order cutoff, and it leaves a first
disagreement unchanged on each tree at its first failing order.
All these statements apply to finite assignments through a cutoff
because no larger tree is used.

The explicit/diagonally implicit shift is the Runge–Kutta–Möbius
equivalence of
[Molnár, Fekete and Söderlind, Theorem 3.1](https://link.springer.com/article/10.1007/s10998-022-00510-5).
Their Theorem 4.1 gives the same Laguerre coefficient in the linear
transformed exponential. The finite all-tree realization below
uses the edge expansion here, not just the linear order conditions.

## 2. Exact finite realization by split layers

Let $N\ge1$ and $0\le D\le N-1$. Assume $K$ is infinite, or finite
with $|K|>N-1$. An arbitrary scalar assignment $g$ to the unordered
rooted-tree classes of order at most $N$ is realized by a finite
strictly lower triangular tableau $B$ of depth at most $D$ if and
only if $g(t)=0$ whenever $\operatorname{ht}(t)>D$.

Necessity follows from the stage-label expansion above: any nonzero
summand for a tree at an output stage supplies a directed dependency
path as long as a longest root-to-leaf path of the tree. Because $B$
is strictly triangular, the stage labels on this path are strictly
ordered. If the height exceeds $D$, no such summand is possible.

For sufficiency, for each $0\le h\le D$ take the tree set

$$
\mathcal T_h\coloneqq
\{t:\ |t|\le N-D+h,\quad \operatorname{ht}(t)\le h\}.
$$

We construct layer $h$ so that its stage-by-tree matrix on
$\mathcal T_h$ is square and invertible. At layer zero the tree set
contains only $\bullet$; one row with no inputs gives the matrix
$(1)$. Suppose layer $h-1$ has been constructed. Every root child
of a tree in $\mathcal T_h$ is in $\mathcal T_{h-1}$, by both the
order and height bounds. At any new stage, the row using only stages
in layer $h-1$ can prescribe arbitrarily all the entries
$x_u\coloneqq (B\boldsymbol{\Phi}_u(B))_i$ for
$u\in\mathcal T_{h-1}$: the row is obtained by solving with the
invertible previous matrix.

The value at this new stage for a tree $t\in\mathcal T_h$ is the
monomial $\prod_{u\in\mathcal T_{h-1}}x_u^{m_u(t)}$, where $m_u(t)$
is the multiplicity of the child class $u$ at its root. Distinct
classes at this layer give distinct monomials, including the
constant for $\bullet$. They are linearly independent as functions
over an infinite field. Over a finite field, the degree in each
variable is at most $N-1<|K|$, so they are still independent: a
polynomial with those separate degree bounds that vanishes on the
whole field grid is zero, by the univariate root bound applied
successively in each variable.

The evaluation rows therefore span the full space of these
monomial coordinates: otherwise a nonzero linear functional
annihilating their span would give a nontrivial combination
vanishing at every point. Choose a basis from the evaluation rows
and use the corresponding points as the new stages. This completes
the layer induction. Order the stages by increasing layer and
allow taps only from the immediately preceding layer, so every
dependency path has length at most $D$. Use output weights only
on layer $D$; its invertible matrix realizes $g$ on $\mathcal T_D$.
All remaining targets are zero and are realized by the height
necessity argument. This uses ordinary coordinatewise stage
multiplication at every layer.

The layer matrix $B$ can be chosen once for $(N,D)$, independently
of $g$. In characteristic zero, choose it over the embedded copy
of $\mathbb Q$ by carrying out the same layer induction there.
If the targets lie in a subfield $K_0\subseteq K$ containing
$\mathbb Q$, the final linear solve then gives $\mathbf{b}$
in $K_0$.

Together with the invertible shift this gives a finite criterion
for any fixed diagonal: a target $f$ through order $N$ has a
triangular realization with diagonal $\gamma$ and depth at most
$D$ exactly when $(\mathcal S_{-\gamma}f)(t)=0$ for every tree of
order at most $N$ and height greater than $D$. For the converse,
realize the shifted assignment with $B$ and set $A=B+\gamma I$;
its off-diagonal graph is unchanged.

## 3. Tall obstruction and exact-order attainment

Write $T_m$ for the tall tree with $m$ edges, so that
$|T_m|=m+1$ and $T_m!=(m+1)!$. A choice leaving $j$ of its edges
uncontracted gives $T_j$. The shifted target $G\coloneqq
\mathcal S_{-\gamma}F$ therefore satisfies

$$
\begin{aligned}
G(T_m)
&=\sum_{j=0}^{m}\binom{m}{j}
       \frac{(-\gamma)^{m-j}}{(j+1)!}
 =\frac{(-\gamma)^m}{m+1}L_m^{(1)}(1/\gamma),\\
L_m^{(1)}(x)
&\coloneqq\sum_{j=0}^{m}\binom{m+1}{j+1}\frac{(-x)^j}{j!}.
\end{aligned}
$$

The equality uses
$\binom{m+1}{j+1}/j!=(m+1)\binom{m}{j}/(j+1)!$.
For $m\ge1$ the recurrence is

$$
(m+1)L_{m+1}^{(1)}(x)
=(2m+2-x)L_m^{(1)}(x)-(m+1)L_{m-1}^{(1)}(x).
$$

For the coefficient of $x^j$, divide out $(-1)^j/j!$; Pascal's
identity reduces the difference of the two sides to
$(m+1)\binom mj-(m+1-j)\binom{m+1}j=0$.
The initial polynomials are $L_0^{(1)}=1$ and $L_1^{(1)}=2-x$.
Consecutive polynomials cannot have a common root over $K$: at a
common root the recurrence would force successive earlier
polynomials to vanish, down to $L_0^{(1)}$.

If a tableau has order at least $p$, its shifted output agrees
with $G$ through order $p$. For $p\ge3$, depth at most $p-3$
would force both $G(T_{p-2})$ and $G(T_{p-1})$ to vanish, which
is impossible. At $p=2$ the lower bound $p-2=0$ is automatic.
If $L_{p-1}^{(1)}(1/\gamma)\ne0$, the paid tree $T_{p-1}$
itself forces depth at least $p-1$.

For the upper bounds there are two cases.

- **The Laguerre value is zero.** At order at most $p$, the only
  class of height greater than $p-2$ is $T_{p-1}$, and its shifted
  target is zero. Use the split layers with $N=p$ and $D=p-2$.
  After adding the diagonal, the full order-$p$ conditions hold.
  The shifted output on $T_p$ is zero by depth, but $G(T_p)\ne0$
  by the consecutive-root test. This discrepancy is at order
  $p+1$ and survives the diagonal shift.
- **The Laguerre value is nonzero.** Use $N=p+1$ and $D=p-1$.
  Prescribe $G$ through order $p$ and deliberately replace its
  value on the $(p+1)$-vertex bush by that value plus $1$.
  This bush has height one, within the depth bound. Set the
  other order-$(p+1)$ targets to zero. The split layers meet these
  prescriptions, and shifting back preserves the discrepancy
  on the bush while retaining every order-$p$ condition.

The lower bounds force the constructed depths to be exactly the
ones stated. The proof is algebraic; the finite-depth result in the
[common-diagonal height comparison](../canonical-rk-realization/COMMON-DIAGONAL-HEIGHT.md)
concerns a different cutoff, for equality of already given series.
The finite-field interpolation in Section 2 is independent of
characteristic zero. The same depth formula also follows over a
field in which $1,\ldots,p+1$ are units, since all factorials,
recurrence divisions and interpolation grid sizes used above
are then available. Only Laguerre polynomials of degree at most
$p$ are involved.

## 4. Real and rational diagonals

Over $\mathbb R$, $L_m^{(1)}$ has $m$ distinct positive roots.
Indeed, its coefficients give the Rodrigues formula

$$
L_m^{(1)}(x)=\frac{e^x}{m!\,x}
 \frac{d^m}{dx^m}\bigl(e^{-x}x^{m+1}\bigr).
$$

Integrating by parts $m$ times shows its orthogonality to all
polynomials of degree less than $m$ for the positive weight
$x e^{-x}$ on $(0,\infty)$. The boundary terms vanish because
the exponential dominates at infinity and the derivatives of
$e^{-x}x^{m+1}$ of orders $0,\ldots,m-1$ vanish at zero.
If there were fewer than $m$ sign-changing roots in $(0,\infty)$,
multiplying by the product of their linear factors would give a
nonzero polynomial of constant sign on this interval, contrary
to that orthogonality. Since $L_m^{(1)}$ has degree $m$, the roots
are all simple and positive.

Thus the least depth among real diagonals is $p-2$, attained
for exactly $p-1$ positive diagonals, the reciprocals of these
roots at $m=p-1$. All are real algebraic. For each fixed
$\gamma$ over any characteristic-zero field, the construction
can use rational off-diagonal entries and output weights in
$\mathbb Q(\gamma)$: the shifted targets are in this field and
the layer matrix and its evaluation matrices can be chosen
over $\mathbb Q$. In particular every real-algebraic branch
is realized without any extension beyond $\mathbb Q(\gamma)$.

For $p\ge3$ a rational $\gamma$ cannot satisfy the shallow
equation. The
[existing rational common-diagonal proof](../strict-sdirk-rational-common-diagonal/PROOF.md),
Section 2, gives an elementary no-rational-root argument for
$(-1)^m m!L_m^{(1)}$ when $m\ge2$. Therefore every nonzero
rational diagonal has least depth $p-1$, even if the remaining
coefficients are allowed in a larger characteristic-zero
field. This depth is attainable over $\mathbb Q$ itself.
At $p=2$ the exceptional diagonal is $\gamma=1/2$, with depth
zero, realized by implicit midpoint $A=(1/2)$, $\mathbf{b}=(1)$;
all other nonzero rational diagonals have least depth one.

An additional arithmetic conclusion uses Schur's irreducibility
of $L_m^{(1)}$ over $\mathbb Q$:
[I. Schur, *Affektlose Gleichungen in der Theorie der
Laguerreschen und Hermiteschen Polynome*, J. Reine Angew. Math.
165 (1931), 52–58](https://doi.org/10.1515/crll.1931.165.52);
see the explicit parameter-$1$ attribution in
[F. Hajir, *On the Galois group of generalized Laguerre polynomials*,
J. Théor. Nombres Bordeaux 17 (2005), p. 518](https://ftp5.gwdg.de/pub/EMIS/journals/JTNB/2005-2/article6.pdf#page=2).
Every shallow diagonal then has degree exactly $p-1$ over
$\mathbb Q$, because adjoining a nonzero element is equivalent
to adjoining its reciprocal. This degree conclusion is separate
from the elementary rational obstruction and gives no claim
about stage width.
