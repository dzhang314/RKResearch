# Paid net clock-gap moments and support

Let $R$ be a nonzero commutative ring with identity. Suppose $(A,\mathbf b)$
satisfies the literal, denominator-cleared rooted-tree conditions through
order $p$: for every rooted tree $t$ of size at most $p$,
$$
  t!\,\bigl(\mathbf b\cdot\boldsymbol{\Phi}_t(A)\bigr)=1 .
$$
Here $t!$ is the full rooted factorial, given by the size of $t$ times the
product of the full factorials of its children. Put
$$
  \mathbf c=A\mathbf1,\qquad C=\operatorname{diag}(\mathbf c),
  \qquad H=CA-AC .
$$
For $h\ge1$, aggregate signed contributions at each actual endpoint gap:
$$
  \mu_h(\delta)
    =\sum_{i,j:\,c_i-c_j=\delta} b_i(H^h)_{ij},
  \qquad
  G_h=\{\delta:\mu_h(\delta)\ne0\}.
$$
The gap set is finite. It is the net support after aggregation, not the
set of all differences between stage clocks.

**Net-gap theorem.** Put $d=2h$ and let $q\ge0$ be an integer. For $d+q+1\le p$ one has
$$
  \sum_{\delta\in G_h}\mu_h(\delta)\delta^q
     =\frac{1}{(d-1)!\,(d+q)(d+q+1)}.                         \tag{1}
$$
In particular, for every integer $r\ge0$,
$$
  d+2r+1\le p\quad\Longrightarrow\quad |G_h|\ge r+1.            \tag{2}
$$
More generally, for an integer $t_0\ge0$, there are at least $r+1$
distinct gaps with $\delta^{t_0}\mu_h(\delta)\ne0$ whenever
$d+t_0+2r+1\le p$. The case $t_0=1$ counts only nonzero endpoint gaps.

## Proof of the moments

The $n$-vertex bush has rooted factorial $n$, so every integer
$1,\ldots,p$ is a unit in $R$ under the paid conditions. The following
formal polynomial primitives use only those inverses. Let $J$ denote
zero-origin polynomial integration and $M$ multiplication by $x$, and
write $\mathcal L(f)=(Jf)(1)$.

For a rooted tree, its model polynomial is the product of the primitives
of its children's model polynomials, with model $1$ for the leaf. By
induction its primitive is $x^{|t|}/t!$, and its model scalar output is
$1/t!$. In the actual tableau, a unary root is the action of $A$;
multiplication by $C$ adds one leaf at the root. Thus any word in
$A,C$, on $\mathbf1$, reads an actual tree. Its **scalar** output
$\mathbf b\cdot(\text{word}\,\mathbf1)$ agrees with the corresponding
model output when the word's size, including the initial leaf, is paid.
We use no assertion that the actual stage column equals the model column.

The sign of the commutator matters: $C A-A C$ is modeled by
$M J-J M=J^2$. The last identity follows on each monomial by subtracting
the two primitives. Expanding the commutators gives only signed words of
the same tree size. Consequently
$$
  \mathbf b\cdot(C^j H^h C^a\mathbf1)
   =\mathcal L\bigl(x^j J^d(x^a)\bigr)
   =\frac{a!}{(d+a)!\,(d+a+j+1)}
  \qquad(d+a+j+1\le p).                                      \tag{3}
$$
The same argument applies to a fixed word of unary $A$ letters and
commutator $H$ letters, of total cost $d\ge1$ when their costs are
$1$ and $2$, respectively. Replace $H^h$ by that word throughout the
moment and support argument.

Expand $(c_i-c_j)^q$ and use (3) with $j=q-a$:
$$
 \begin{aligned}
  \sum_\delta\mu_h(\delta)\delta^q
   &=\sum_{a=0}^q(-1)^a\binom qa\,
        \mathbf b\cdot(C^{q-a}H^h C^a\mathbf1)\\
   &=\frac{S(d,q)}{d+q+1},
  & S(d,q)&=\sum_{a=0}^q(-1)^a\binom qa\frac{a!}{(d+a)!}.
 \end{aligned}
$$
Pascal's identity and subtraction of consecutive summands give
$S(d,q+1)=d\,S(d+1,q)$. The starting value is $S(d,0)=1/d!$.
It follows that $S(d,q)=1/((d-1)!(d+q))$, as required. The recursion
keeps $d+q$ within the original denominator budget.

## Proof of the support bound over a ring

Take the $(r+1)$-square Hankel moment matrix with indices $i+j$,
$0\le i,j\le r$. After removing the scalar unit $1/(d-1)!$ from its
entries, the matrix is
$$
    \left[\frac{1}{d+i+j}-\frac{1}{d+i+j+1}\right]_{0\le i,j\le r}.
$$
Augment the Cauchy arrays to a square matrix with Cauchy rows
$\bigl(1/(d+i+j)\bigr)_{j=0}^{r+1}$, $0\le i\le r$, and a final
all-ones row. Replacing the first $r+1$ columns by consecutive
original-column differences is a determinant-one operation. The final row
then has only its last entry nonzero (equal to one), leaving the displayed
matrix as the complementary minor. The determinant is
$$
 \frac{
   \displaystyle\prod_{0\le i<i'\le r}(i'-i)
   \displaystyle\prod_{0\le j<j'\le r+1}(j'-j)}
  {\displaystyle\prod_{i=0}^{r}\prod_{j=0}^{r+1}(d+i+j)} .     \tag{4}
$$
For instance, apply the Cauchy determinant formula with a final row
$1/(z+j)$, multiply that row by $z$, and compare the leading
coefficients at formal infinity. After specialization it uses only the
integer denominators displayed. The largest is $d+2r+1$;
the numerator differences are at most $r+1$. Under the paid hypothesis
all factors are units, so (4) and hence the actual moment determinant are
units in $R$, even in the presence of zero divisors.

On the actual gap set the same Hankel matrix is a sum of the rank-one
arrays
$$
 \sum_{\delta\in G_h}\mu_h(\delta)
       (1,\delta,\ldots,\delta^r)^{\mathsf T}
       (1,\delta,\ldots,\delta^r).
$$
If there were at most $r$ gap labels, every term in the multilinear
determinant on its $r+1$ columns would repeat a column direction.
The determinant would be zero. This proves (2) without any field-rank
assumption. To prove the shifted version, use $i+j+t_0$ as moment
indices, replacing $d$ by $d+t_0$ in (4) and retaining the scalar
$1/(d-1)!$; the actual weights are then $\delta^{t_0}\mu_h(\delta)$.

## What the support counts

- Every nonzero gap mass has a nonzero summand, and expansion of
  $b_i(H^h)_{ij}$ then gives a nonzero full path term. This implication
  does not assume that products of nonzero factors are nonzero.
- For $h=1$, $H_{ij}=(c_i-c_j)A_{ij}$. The gap zero never survives.
  Each counted gap therefore comes from an actual clock-changing edge
  into a receiver with $b_i\ne0$. The sender need not have nonzero
  output weight. With $g=|G_1|$, (2) gives $p\le2g+2$.
- For $h>1$ an endpoint gap may be zero even though the individual
  commutator edges change the clock. If all edges relevant to the
  nonzero path terms have gaps in a set $\Delta$, then
  $G_h\subseteq h\Delta$ (the $h$-fold sumset), so
  $p\le2h+2|h\Delta|$.
- Real full-moment saturation has a separate implication. If
  $g=|G_h|>0$ and $p\ge d+2g$, the degree-$g$ monic gap hull is
  the orthogonal polynomial for the weight
  $x^{d-1}(1-x)/(d-1)!$ on $(0,1)$. Indeed its product with any
  polynomial of degree $<g$ has zero gap sum and is paid by (1).
  If it had fewer than $g$ sign-change roots in $(0,1)$, multiply it
  by the product of the corresponding linear factors. That lower-degree
  test would make the integrand of constant nonzero sign, a contradiction.
  Thus all $g$ roots are simple and interior. Squared cardinal polynomials
  show that the corresponding net masses are positive.
  Neither sign assertion applies to general
  unsaturated gap support, and neither is a sign assertion on $A$
  or $\mathbf b$.

For an additive tableau, fix the choice of unary action $A^\alpha$,
clock $\mathbf c^\beta=A^\beta\mathbf1$, and output
$\mathbf b^\gamma$. Form $C$ from that clock and set
$H_{\alpha\beta}=CA^\alpha-A^\alpha C$. Use this $C$ at **both**
endpoints of the gap probe, with output
$\mathbf b^\gamma\cdot(\text{word}\,\mathbf1)$.
The same argument applies if the selected expanded words are paid by
the corresponding **mixed colored literal** conditions, with the
indicated scalar units in the ring case. Separate monochromatic order
or order of a sum is not a substitute for this premise. None of these
arguments constructs a tableau attaining the bound.
