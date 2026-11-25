# Quadratic stage bounds at the sharp fixed SDIRK depth

Let $K$ have characteristic zero, let $p\ge2$, and fix a nonzero
$\gamma\in K$. A strict SDIRK tableau here has $A=B+\gamma I$ with
$B$ strictly lower triangular. Depth counts off-diagonal edges on
the longest path feeding a nonzero readout weight. There is no
stability, increasing-abscissa, or stage-minimum claim.

## Result

The [sharp depth theorem](PROOF.md) gives the minimum dependency depth.
Here we bound the number of stages needed to attain it.

Suppose $x_1,\ldots,x_q\in K$ are distinct, $1\le q\le p\le2q$,
and $\sum_i w_i F(x_i)=\int_0^1 F(x)\,dx$ through degree $p-1$.
Integrals here are formal polynomial integrals. Put
$$
  U(p,q)\coloneqq qp-\binom q2.
$$

* If $L_{p-1}^{(1)}(1/\gamma)\ne0$, there is such a tableau of order
  at least $p$, sharp depth $p-1$, and at most $U(p,q)$ stages.
  Its order is exactly $p$ if the quadrature misses the degree-$p$
  moment, or if $L_p^{(1)}(1/\gamma)\ne0$.
* If $p\ge3$ and $L_{p-1}^{(1)}(1/\gamma)=0$, there is such a tableau
  of exact order $p$, sharp depth $p-2$, and at most $U(p,q)-2$
  stages. For $p=2,\gamma=1/2$, implicit midpoint gives the
  exceptional bound of one stage at depth zero.

The last layer has the given mesh and output weights; all previous
layers have zero output weights. Positivity below refers only to
the weights on the final mesh. Every noninitial layer's physical
abscissae $A\mathbf{1}$ are a subset of this mesh, and the initial
stage has abscissa $\gamma$. Off-diagonal entries are affine
in $\gamma$, with coefficients over the node field, and the
nodes and weights can be chosen independently of $\gamma$.
No field extension of $K$ is used when the input quadrature
already lies in $K$.

For every $p\ge2$, real positive quadrature with
$q=\lceil p/2\rceil$, algebraic interior nodes and exact degree
$p-1$ exists. This yields stage bounds with leading term $3p^2/8$
over $\mathbb R$. Positive rational quadrature with $q=p-1$
and exact degree $p-1$ exists for every $p\ge2$, so over any
characteristic-zero field the corresponding exact-order bounds are
$$
 \frac{p(p+1)}2-1,\qquad
 \frac{p(p+1)}2-3\quad(p\ge3),
$$
respectively. The latter choice works over $\mathbb Q(\gamma)$
even on the exceptional algebraic branch, with rational output
weights. Smaller quadratures, when available in the coefficient
field, improve both bounds by the same formula. No such small
rational support is assumed universally.

## 1. Dense collocation gives every paid tree condition

Write $\boldsymbol{\Phi}_t(M)$ for the stage weight column of a rooted tree $t$:
the leaf gives $\mathbf{1}$, unary extension applies $M$, and joining
roots multiplies columns coordinatewise. Equivalently a root
with children $u$ has stage column $\prod_u M\Phi_u(M)$.
Put $P_t(x)=|t|x^{|t|-1}/t!$, where $t!$ is the tree factorial.
Write $I F(x)=\int_0^xF(s)\,ds$ and $\ell(F)=(I F)(1)$.
The tree factorial recursion gives $P_\bullet=1$,
$P_{[t]}=I P_t$, $P_{t\mathbin{\#}u}=P_t P_u$ and
$\ell(P_t)=1/t!$.

Let $H(x)=\prod_i(x-x_i)$ and let $\rho$ take the remainder
modulo $H$. In the paid range $\deg F\le p-1$, exact quadrature
implies $\ell(F)=\ell(\rho F)$, because $F-\rho F$ vanishes at
the given nodes and the quadrature integrates both terms.
Evaluation gives the algebra isomorphism $K[x]/(H)\simeq K^q$,
with coordinate multiplication. If $\ell_j$ is the cardinal
polynomial of mesh point $x_j$, under this isomorphism the
operator $\overline F\mapsto\overline{I(\rho F)}$ is exactly
the dense collocation matrix
$$
 \widehat A_{ij}=(I\ell_j)(x_i).
$$
Thus this is an actual tableau reference, not merely a
nonsplit abstract-algebra completion.

For clarity, use the following projected-integration invariant
from [*Completing order-paid context matrices*](../canonical-rk-realization/CONTEXT-MATRIX-COMPLETIONS.md). Let $R_t$ be the
remainder representative of its stage tree column. It has degree
$\le |t|-1$ by tree recursion: projected integration raises
degree by at most one and projected products add the caps.
For every polynomial $W$ with $\deg W+|t|-1\le p-1$,
$$
 \ell(W R_t)=\ell(W P_t).
$$
It holds for the leaf. For a rooted sum, first remove the
remainder inside $\ell$: the difference times $W$ is a multiple
of $H$ of degree at most $p-1$. Then replace the two factors one
at a time by induction, with tests $W R_u$ and $W P_t$; their
degrees are paid under the same bound. At a unary step, similarly
remove the remainder and use the formal identity
$$
 \ell(W I a)=\ell((\ell(W)-I W)a),
$$
which follows by integrating the derivative of $(I W)(I a)$.
The new test has degree at most $\deg W+1$, paid on the child.
Apply induction and reverse the identity to get the exact
profile payment. Thus all shapes are covered. Taking $W=1$
and using the given quadrature on the remainders proves exact
readouts $\mathbf{w}\cdot\boldsymbol{\Phi}_t(\widehat A)=1/t!$ through order $p$.
No named simplifying-assumption theorem or linear-only test is
being used.

## 2. Rank unrolling preserves the right finite tree domain

For any dense reference $M$ and output row $w$, choose
$0\le D\le p-1$ and put $s_h=p-D+h$ for $0\le h\le D$.
At layer $h$ consider the tree classes
$$
 \mathcal T_h=\{\,t:\operatorname{ht}(t)\le h,\ |t|\le s_h\,\},
 \qquad V_h=\operatorname{span}\{\boldsymbol{\Phi}_t(M):t\in\mathcal T_h\}.
$$
Choose $r_h=\dim V_h$ independent coordinate rows on $V_h$,
so restriction to those coordinates is an isomorphism onto
$K^{r_h}$. One stage at layer $h\ge1$ is indexed by each of
that layer's chosen coordinates. Implement the functional
$v\mapsto(Mv)_i$ on $V_{h-1}$ as a linear row over the preceding
chosen coordinates. This is possible by the restriction
isomorphism and uses only that preceding physical layer.
At layer zero, one leaf stage has no strict inputs.

For $t\in\mathcal T_h$, each root child belongs to $\mathcal T_{h-1}$:
its height drops by at least one, and its order is at most
$s_h-1=s_{h-1}$. The ordinary coordinatewise tree recursion
therefore shows the new stage values equal the chosen coordinates
of $\boldsymbol{\Phi}_t(M)$ on this domain. Use output weights implementing
$v\mapsto wv$ on $V_D$ only in the last layer. The resulting
strictly lower triangular $B$ has that reference readout on
all order-$\le p$, height-$\le D$ trees. Its readout is zero
on taller trees because every strict edge goes between successive
layers. No agreement with an arbitrary dense reference is claimed
on the discarded taller trees.

## 3. Exact layer widths and explicit coefficients

Use $M=\widehat A-\gamma I$, and write $J=I-\gamma\,\mathrm{Id}$
on polynomials (the first $I$ here is integration).
The shifted polynomial profiles $Q_\bullet=1$ and
$Q_t=\prod_{u\text{ child}}J Q_u$ have degree $\le|t|-1$.
For $|t|\le q+1$ their mesh evaluations equal $\boldsymbol{\Phi}_t(M)$:
each child has degree at most $q-1$, so the reference matrix
$M$ applies $J$ to its evaluated polynomial by exact
interpolation. At $h\ge1$ with $s_h\le q$, this puts $V_h$
inside the evaluated polynomials of degree $<s_h$. Also
at any $h\ge1$ the bush columns include
$$
 (x_i-\gamma)^j,\qquad j=0,\ldots,\min(q,s_h)-1.
$$
These span the evaluations of degree $<\min(q,s_h)$, and
when $s_h\ge q$ they already span all $K^q$. Consequently
$$
 V_0=K\mathbf{1},\qquad
 V_h=\operatorname{ev}_{x_1,\ldots,x_q}K[x]_{<r_h},
 \quad r_0=1,\quad r_h=\min(q,s_h)\ (h\ge1).
$$
This is also a rank limitation **within full-reference matching**:
the independent bush columns are physically present, so a change
of interpolating basis alone cannot lower these ranks. It is not
a lower bound on the number of stages of an arbitrary tableau.

Any $r_h$ mesh points may serve as the selected set $S_h$, fixed
independently of $\gamma$. If $L_j^{(h-1)}$ is the cardinal
polynomial at $j\in S_{h-1}$ on that set, the only possible
nonzero strict entries of $B$ have the explicit formula
$$
 B_{(h,i),(h-1,j)}
     =(I L_j^{(h-1)})(x_i)-\gamma L_j^{(h-1)}(x_i),
 \qquad i\in S_h,\ j\in S_{h-1}.
$$
This implements $M$ on $V_{h-1}$: its polynomial representative
has degree $<r_{h-1}\le q$ and both the submesh interpolation
and dense collocation act on it by exact integration.
In particular $(B\mathbf{1})_{(h,i)}=x_i-\gamma$ for $h\ge1$,
so after adding the fixed diagonal the physical clock is $x_i$.
The depth-zero clock is $\gamma$. For $D\ge1$, $r_D=q$ since
$s_D=p$, so the last layer uses the original weights unchanged.
At $D=p-1$ the sum of widths is $\sum_{k=1}^p\min(q,k)=U(p,q)$.
At $D=p-2$, $p\ge3$ implies $q\ge2$; replace the widths at
cutoffs $1,2$ by the single depth-zero leaf width $1$,
giving $U(p,q)-2$.

## 4. Diagonal shift, sharp depth, and first failure

For any scalar tree assignment $f$, the diagonal shift on
its readout is
$$
 (\mathcal S_\eta f)(t)=
   \sum_{E'\subseteq E(t)}\eta^{|E'|} f(t/E').
$$
To see this, expand stage labels and take $\eta I$ on the
edges in $E'$; this identifies their endpoints, leaving the
contracted tree. The transforms compose by addition of shifts,
and every nonempty contraction lowers order. By Section 1,
$M=\widehat A-\gamma I$ therefore realizes
$\mathcal S_{-\gamma}(1/t!)$ through order $p$.

For the $(m+1)$-vertex tall tree $T_m$, the shifted target is
$$
 (\mathcal S_{-\gamma}(1/t!))(T_m)
      =\frac{(-\gamma)^m}{m+1} L_m^{(1)}(1/\gamma).
$$
Group path contractions by the number of remaining edges to
obtain this formula. The Laguerre recurrence from the [sharp-depth proof](PROOF.md) excludes consecutive common roots:
$(m+1)L_{m+1}^{(1)}=(2m+2-x)L_m^{(1)}-(m+1)L_{m-1}^{(1)}$,
and $L_0^{(1)}=1$.

At $D=p-1$ every order-$\le p$ tree lies in the final unrolling
domain. At $D=p-2$ the only excluded class of order $\le p$
is $T_{p-1}$; it has zero shifted **paid** target on precisely
the exceptional branch. Thus $B$ realizes every shifted order
condition through $p$, including the discarded paid tall tree
when present, and $A=B+\gamma I$ realizes every original one.
In either branch its shifted $T_D$ target is nonzero (or
$D=0$ is already minimal), proving depth $D$ is sharp.

At depth $p-2$, the shifted target on $T_p$ is nonzero by
consecutive-root exclusion, whereas its strict readout is zero.
This is a first failure and hence survives shifting back,
since all nonempty contractions have already paid order.
The same next-tall reasoning works at depth $p-1$ when
$L_p^{(1)}(1/\gamma)\ne0$. Otherwise choose the quadrature
with exact degree $p-1$ but not $p$. The order-$(p+1)$ bush
then fails **in the final SDIRK itself**, whose last-layer clocks
and weights are unchanged: its value is
$\sum_i w_i x_i^p\ne1/(p+1)$. No order-$(p+1)$ reference layer
is needed. The exceptional $p=2$ case has $\gamma=1/2$ and
the single-stage midpoint tableau, which satisfies order two,
fails the order-three bush, and has depth zero.

## 5. Positive real and rational meshes of exact degree p-1

For distinct nodes, give them the weights $w_i=\ell(\ell_i)$,
where $\ell_i$ are their cardinal polynomials. Let their monic
node polynomial be $F(x)=\prod_i(x-x_i)$. By polynomial
division, exactness through $q-1+k$ is equivalent to
$\ell(FU)=0$ for every polynomial $U$ of degree $<k$.

Let $G_j$ be the monic orthogonal polynomial of degree $j$
for integration on $[0,1]$. It exists by positive definiteness
of the Gram matrix, whose entries are rational. It has $j$
simple interior roots: if there were fewer than $j$
sign-changing roots there, the product of their linear factors
would be a test of degree $<j$ whose product with $G_j$ has
one sign and nonzero integral, contradicting orthogonality.
For even $p=2q$, take $F=G_q$. This is exact through $2q-1$
but fails on $G_q^2$ of degree $2q$. For odd $p=2q-1$ with
$q\ge2$, take $F=G_q+\varepsilon G_{q-1}$ for a sufficiently
small nonzero rational $\varepsilon$. Disjoint brackets on
the simple roots keep all $q$ roots simple and interior.
The polynomial is orthogonal to all degrees $<q-1$ but
not to $G_{q-1}$; thus exactness stops at $2q-2$.
In both cases each weight is the integral of the square of
the corresponding cardinal polynomial, of degree $2q-2$.
Hence all final-layer weights are positive and their nodes
are algebraic.

For the universal rational choice $q=p-1$, start near a real
$q$-point Gauss mesh (the roots of $G_q$). Choose the first
$q-1$ nodes freely, write $H(x)=\prod_{i<q}(x-x_i)$, and
force the last node
$$
 x_q=\frac{\ell(xH)}{\ell(H)}.
$$
At the original Gauss mesh $\ell(H)=w_q H(x_q)\ne0$ by
exactness and positive $w_q$, and the formula recovers that
last node. Nearby perturbations keep all nodes distinct and
interior; their cardinal weights stay positive by continuity.
Now $F=(x-x_q)H$ has zero integral, giving exactness through
degree $q=p-1$. Degree $q+1$ is also exact only if the
polynomial in free nodes
$$
 \ell(x^2 H)\ell(H)-\ell(xH)^2
$$
vanishes. It is not identically zero: letting all free
nodes be zero gives $1/[q(q+2)(q+1)^2]$.
Thus choose rational free nodes in the positive open
neighborhood avoiding this zero set. The last node and all
weights are rational and degree $q+1$ fails. For $q=1$,
there are no free nodes; the formula gives the midpoint
rule, with its degree-two failure.

## Scope

This is an all-order upper construction at the posted sharp
fixed depth. It replaces arbitrary-assignment tree interpolation
by a small dense reference special to the exact-flow target.
It does not realize every allowed scalar assignment with
quadratic width, prove quadratic width necessary, find
arithmetic-optimal quadratures, enforce increasing or globally
distinct stage clocks, or establish stability. Mesh clocks
can repeat between layers. No numerical search, stored Gauss
input, compiler, or tree enumeration is used.
