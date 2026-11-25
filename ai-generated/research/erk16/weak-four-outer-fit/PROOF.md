# A second, shorter weak-four proof: allow the outer root in the fitting polynomial

This supplement **removes the strict-unit-root cut** from the
[complete physical proof](../weak-four-complete/PROOF.md). It does not change
the separate, direct cubic proof. Together the two short first-stop
certificates work directly from the seven global orthogonalities and the two
tests at each first stop. Neither secondary stop test, the prior multi-case
crossing and parity argument, nor an additional diagonal moment is needed.
No numerical value of the physical tableau is fixed. The new
[standard-Python checker](check_outer_fit.py) uses only the first proof's
[rational reference and sign routine](../weak-four-complete/check_uniform.py).

## Exhaustive split without the prior cut

Use the notation of the complete proof. The repeated facts are these. Scale
the degree-eight polynomial $F=QZ$ to leading coefficient $11440$.
The paid global law gives $F=P_0+uJ$ by positive-square detection of the
degree-at-most-six remainder. When $-1<u<0$, the eight disjoint sign
strips give eight simple strict unit roots; all four $Q$ roots are among
them, and the eight-index first-stop proof already excludes this case.
When $u\ge0$, the global weight stays $X$ and the seven interior strips
leave precisely one further root $e\le0$. When $u\le-1$, reflect $X$
to $1-X$ and use the first right stop as the new left stop. The global
weight becomes $1-X$; again seven strictly positive interior roots leave
one $e\le0$. These conclusions use only the global pencil, the exact
rational sign brackets, the degree, and the sign at zero, **not** a prior
count or a chronology inequality. In the two exterior orientations the
positive roots are all simple because the nonpositive eighth root is distinct.

If $e$ is a root of $Z$, all four fitting roots are interior, so the
earlier seven-index checks apply unchanged. In particular, an exterior
negative $e$ cannot be the selected left first stop: the integrand $XQ$
has a fixed nonzero sign between that stop and zero. The chosen first stop
is not zero by the physical source (after reflection this uses $d\ne1$).
If $e$ is a root of $Q$, all four marks are interior, so the selected
left stop is again interior. Only this last possibility requires a new check.
The formal case $e=0$ is covered without division by $e$.

Thus in the new case $0<a<1$ is the selected stop, the actual fitting
polynomial $Q$ has three interior roots and $e\le0$, and the two
equations available at $a$ are exactly
$$
           \int_0^a XQ=\int_0^a X^2Q=0.
$$
There are at least two interior fitting roots before $a$: otherwise a
signed affine separator gives a strictly positive integral against the first
two tests. This is the same two-test argument as in the main proof.

## A bounded coefficient for the unbounded outer root

In either seven-index family let $P$ be the degree-seven reference,
let $T$ be the degree-eight reference with a root at zero, and write the
positive multiple of the actual pencil as
$$
 G_s\coloneqq(1-s)P+sT,\qquad 0<s\le1.
$$
The pairs are $P=J,\ T=XK$ or $P=J^{\mathrm r},\ T=XL$. Use $P_i,T_i$
for the coefficients of $X^i$. Thus $P_8=0,\ P_7>0,\ T_8=11440>0$.
Let $t_1,\ldots,t_7$ be the indexed interior roots, and put
$$
 S\coloneqq\sum_{k=1}^7t_k,\quad
 B\coloneqq-se=\frac{(1-s)P_7+sT_7}{T_8}+sS,\quad
 A\coloneqq sa,\qquad \omega\coloneqq\frac{A}{A+B}.
$$
The formula for $B$ is precisely the coefficient-of-$X^7$ Vieta
identity for $G_s$ with its known leading coefficient $sT_8$; it is
valid even when the exterior root is zero. We have $A>0,\ B\ge0$.
The formula extends algebraically to the reference limit $s=0$ with
$A=0,\ B=P_7/T_8>0,\ \omega=0$. No finite exterior root is asserted
at that reference limit.

Let $I$ be the three interior fitting-root indices, put $z_i=t_i/a$,
and change $X=aY$ in the two stopped laws. Multiplying the exterior
factor $aY-e$ by $s/(A+B)>0$ makes it
$$
                 \omega Y+(1-\omega).
$$
After removal of the other nonzero constant factors the equations are
$$
 \int_0^1 Y^k\bigl(\omega Y+1-\omega\bigr)
         \prod_{i\in I}(Y-z_i)\,dY=0,\qquad k=1,2.
$$
The two-moment vector is affine in each of the four bounded arguments
$(\omega,(z_i)_{i\in I})$.

On each closed rational parameter interval the main checker encloses
each indexed positive root in a rational strip, by affineness in $s$
of both polynomials' boundary signs. Sum the seven lower and upper
endpoints to enclose $S$. The preceding Vieta expression is bilinear in
$(s,S)$; its lower and upper bounds on that rectangle therefore come
from the four corners. Intersect the lower bound for $B$ with $B\ge0$.
Also $A=sa$ is bounded by multiplying the respective nonnegative
lower and upper endpoints. With these absolute bounds a safe closed
interval for the exterior coefficient is
$$
 \frac{A_{\min}}{A_{\min}+B_{\max}}\le\omega\le
 \frac{A_{\max}}{A_{\max}+B_{\min}}.
$$
The checker proves both denominators positive in every visited cell.
The other three coordinates have the same rational ratio enclosures as
in the main proof. Evaluate the two-moment vector at its 16 corners;
strict separation of zero from the convex hull is tested by the same
homogeneous rational plane test. The coefficients and the integrals,
including the affine exterior factor with positive denominator, are
checked by integer arithmetic. There is no evaluation at a physical fibre.

There are exactly 70 admissible rank choices per orientation: choose one
of seven roots as $a$ and three others as the interior $Q$ roots, with
at least two of those strictly before $a$. For both global weights, all
choices are excluded on the entire closed parameter interval using seven
terminal intervals and maximum bisection depth three. Run the new checker
and the main checker; the pair makes no use of the earlier crossing/parity
checks. Degrees below four are treated exactly as in the main proof: degree
at most two by the positive square, and degree three by the direct seven-node
case. This proves the same physical weak-four impossibility and permits the
same ordered-field stage-padding assembly; it is a mathematical proof,
not a new kernel verification.
