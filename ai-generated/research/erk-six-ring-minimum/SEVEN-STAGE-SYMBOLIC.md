# A symbolic certificate for the seven-stage ring ERK6 tableau

Write $U\coloneqq\mathbb Z[1/30]$. The following is the exact
tableau in [The exact seven-stage minimum for explicit order six
over rings](README.md), with a tree-recursive proof that does not
depend on enumeration. Each row lists the strict predecessor
coefficients.

| Stage | Row of $A$ | Weight |
|:---|:---|:---|
| 1 | empty | $11/120$ |
| 2 | $1/3$ | $0$ |
| 3 | $0,\,2/3$ | $27/40$ |
| 4 | $1/12,\,1/3,\,-1/12$ | $27/40$ |
| 5 | $7/4,\,-9,\,9/4,\,6$ | $1/12$ |
| 6 | $-3/64,\,9/8,\,-9/64,\,-27/64,\,-1/64$ | $-8/15$ |
| 7 | $-65/4,\,81,\,9/4,\,-33,\,-1,\,-32$ | $1/120$ |

## Verification of every rooted tree through order six

Let $\mathbf c\coloneqq A\mathbf 1=(0,1/3,2/3,1/3,1,1/2,1)$,
$C\coloneqq\operatorname{diag}(\mathbf c)$, and $\mathbf e_2$
be the second coordinate vector. Powers of $\mathbf c$ below
are coordinatewise. Write
$$
 \mathbf x\coloneqq A\mathbf e_2,\qquad
 \mathbf d_j\coloneqq A\mathbf c^{j-1}-\mathbf c^j/j .
$$
The pooled weights are $11/120$ at each endpoint, $27/40$ at
each of $1/3,2/3$, and $-8/15$ at $1/2$. Both the quadrature
and the formal integral on $[0,1]$ are invariant under
$X\mapsto1-X$. A symmetric polynomial of degree at most five
is a linear combination of $1,g,g^2$, where
$g(X)\coloneqq X(1-X)$: use the even powers of $X-1/2$.
The three readouts are $1,1/6,1/30$, the corresponding
integrals. Therefore
$$
 \mathbf b\cdot\mathbf c^k=\frac{1}{k+1}\qquad(0\le k\le5).
$$
Direct substitution of the rows gives the following short list:
$$
\begin{gathered}
 \mathbf x=(0,0,2/3,1/3,-9,9/8,81),\qquad
 \mathbf b\cdot A\mathbf v=\mathbf b\cdot(I-C)\mathbf v
       \quad(\mathbf v\in U^7),\\
 \mathbf d_2=-\mathbf e_2/18,\qquad
 \mathbf d_3=-\mathbf x/27-\mathbf e_2/81,\qquad
 \mathbf b\cdot C^j\mathbf x=0\quad(0\le j\le2),\\
 \lambda(\mathbf v)\coloneqq\mathbf b\cdot C A\mathbf v,\qquad
 \lambda=(1/24,0,9/40,27/80,-1/240,-4/15,0),\\
 \lambda(\mathbf x)=0,\qquad \lambda(\mathbf c^3)=1/24 .
\end{gathered}
$$
In particular $\mathbf b\cdot\mathbf d_4=\mathbf b\cdot\mathbf d_5=0$
by the row-functional identity and the moments, and
$\mathbf b\cdot C\mathbf d_4=\lambda(\mathbf c^3)-
(\mathbf b\cdot\mathbf c^5)/4=0$.

For a rooted tree $t$ of order at most six, set
$$
 \alpha_t\coloneqq |t|/t!,\qquad
 \mathbf D_t\coloneqq
 \boldsymbol{\Phi}_t(A)-\alpha_t\mathbf c^{|t|-1}.
$$
These divisions are paid in $U$. The leaf and the one-edge
tree have zero defect. Unary graft gives
$\mathbf D_{[t]}=A\mathbf D_t+\alpha_t\mathbf d_{|t|}$.
For root merge, the factorial identity gives
$$
 \mathbf D_{t\mathbin{\#}u}
 =\alpha_t C^{|t|-1}\mathbf D_u
  +\alpha_u C^{|u|-1}\mathbf D_t
  +\mathbf D_t\odot\mathbf D_u .
$$
Every nonleaf rooted tree is either a unary graft or can split its
root forest into two nonempty lists for the root merge. These two
formulas show that the spans of all defects through orders three,
four, and five lie in
$$
\begin{split}
 V_3&\coloneqq\operatorname{span}(\mathbf e_2),\\
 V_4&\coloneqq\operatorname{span}(\mathbf e_2,\mathbf x),\\
 V_5&\coloneqq
 \operatorname{span}(\mathbf e_2,\mathbf x,C\mathbf x,A\mathbf x,\mathbf d_4),
\end{split}
$$
respectively. In particular $CV_3\subseteq V_3$ and
$CV_4\subseteq V_5$. For order six, unary graft lands in
$AV_5+\operatorname{span}(\mathbf d_5)$. In the root merge the
only new product of potentially nonzero defects uses orders
three and four, and $V_3\odot V_4\subseteq V_3$. The two
clock-multiplied terms are in $CV_5$: higher powers in those
terms reduce using the two inclusions just stated. Thus all
defects through order six belong to
$$
             V_5+CV_5+AV_5+\operatorname{span}(\mathbf d_5).
$$
The displayed row identities annihilate $V_5$ and $CV_5$
under $\mathbf b\cdot$; they then annihilate $AV_5$ by
$\mathbf b\cdot A\mathbf v=\mathbf b\cdot(I-C)\mathbf v$.
They annihilate $\mathbf d_5$ as well. It follows for every
rooted tree through order six that
$$
 \mathbf b\cdot\boldsymbol{\Phi}_t(A)
 =\alpha_t\,(\mathbf b\cdot\mathbf c^{|t|-1})
 =\alpha_t/|t|=1/t!.
$$

For the seven-vertex tall tree, the strict path is unique. Its
weighted coefficient is
$$
 \left(-\frac4{15}\right)\left(-\frac1{64}\right)6
               \left(-\frac1{12}\right)\frac23\frac13
 =-\frac1{2160}.
$$
The cleared defect is $7!(-1/2160)-1=-10/3$, a unit of $U$.
Thus every nonzero commutative unital ring with $720$ a unit
inherits the cleared paid identities and this first unpaid
defect under the unital map $U\to R$. This does not require
$7$ to be a unit. Necessity of the $720$ unit condition and
the seven-stage lower bound are as stated in [the principal
note](README.md).

## How the endpoint-duplicate chart was chosen

The familiar symmetric pooled quadrature at labels
$0,1/3,1/2,2/3,1$ can keep its total weight at $1$ while
splitting that weight between two rows. This permits a unit
last weight even though $11/120$ is not a unit in $U$.
Place the last three clocks at $1,1/2,1$, rather than
duplicating the midpoint. This changes the internal equations;
it is not a stage relabelling or an order-preserving operation
without further conditions.

In the simplifying ansatz, take $b_2=0$ and $c_2=1/3$, use the row-functional
identity above, and allow the second integration defect only
at stage $2$, with the third in
$\operatorname{span}(\mathbf e_2,A\mathbf e_2)$.
Write $\nu(\mathbf v)\coloneqq\mathbf b\cdot C^2 A\mathbf v$.
The second integration defect at stage 2 is then the unit $-1/18$, so the paid tests for these two taps include $\lambda_2=\nu_2=0$.
For a donor $j\ge4$ all later receiver clocks are $1$ or
$1/2$, so
$$
 \nu_j=(3/2)\lambda_j-(1/2)b_j(1-c_j).
$$
This is the identity $X^2=(3/2)X-1/2$ on those receiver
clocks, followed by the row-functional identity. Test with
$f(X)=X(X-a)$, $a=c_3$, to remove donors $1$ and $3$.
Donor $2$ already has zero taps and zero output weight.
The required moments of $\lambda$, $\mathbf b\cdot(I-C)$,
and $\nu$ on this polynomial are $1/15-a/8$,
$1/12-a/6$, and $1/18-a/10$, respectively. Their
substitution leaves $(2-3a)/720$, so $a=2/3$.
Integration of the vanished nodal polynomial
$X(1-X)(X-a)(X-1/2)(X-c_4)$ then gives
$0=1/360-c_4/120$, hence $c_4=1/3$.

Choose $b_5=1/12$, $b_7=1/120$.
The donor matrix for $1,\mathbf c,\mathbf c^2+\mathbf e_2/27$
on the first three stages has determinant $4/81$, a unit.
Thus row sums and the two integration conditions solve those
columns once the later edges are chosen. The row-functional
identity fixes $b_7a_{76}=-4/15$,
$b_6a_{65}+b_7a_{75}=0$, and
$b_5a_{54}+b_6a_{64}+b_7a_{74}=9/20$.
Use the two polynomial tests $X(X-2/3)(X-1/3)$ and
$X(X-2/3)(X-1)$, which isolate the endpoint and stage 4
once the midpoint contribution is subtracted.
The exact moments of $\lambda$ through degree three and
$\lambda_6=-4/15$ give $\lambda_5=-1/240$,
$\lambda_4=27/80$, yielding $a_{65}=-1/64$ and
$a_{64}=-27/64$. Finally $a_{54}=z$ gives $x_5=-3z/2$;
the condition $\lambda(\mathbf x)=0$ is
$-3/80+z/160=0$, so $z=6$. Solving the remaining row
coefficients gives the literal table above. This is a
construction ansatz, not a classification or a priority claim.
