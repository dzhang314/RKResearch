# High-support cubic saturation excludes the endpoint-near pivot pairs

This is a separate mathematical deduction, not a new Lean endpoint.
It refines only the high cubic-support branch of an eleven-stage,
order-ten DIRK. Counting $r$ distinct numerical clocks of individually
active dirty stages (rows with $b_i g_i\ne0$), where
$g=Ac^2-c^3/3$, $r=9$ is impossible, and $r=8$ forces a specific
clean interior clock. In the latter branch the earned forward pivot
has 1-based index **$i\le6$**. The reverse conclusion **$j\ge6$**
additionally uses the ordinary grade-six surplus, or just the
resulting rank $\dim E_6=10$.
The proof does not exclude low-support cases or the entire
eleven-stage face.

## Endpoint and moment inputs

Work over a field admitting the paid order-ten identities.
Use the native saturation $\dim E_5=9$, $C(2)$, $D(1)$, $D(2)$,
the true zero row at 0 and the actual active last clock at 1.
The initial cubic defect vanishes. To see the terminal vanishing,
the ordinary reverse space at index 3 has rank two: the first
reverse rank is zero, two strict steps are paid, and it annihilates
the rank-nine $E_5$. Thus its annihilator column space is exactly
$E_5$. Every such reverse row vanishes at the actual terminal,
so its unit column is in $E_5$. Pairing with the grade-three
defect $g$ is paid, and the last weight is nonzero; therefore the
last $g$ entry is zero. In particular $r\le9$.

The exact product moments used below are
$$
 \beta C^k g=0\ (0\le k\le6),\qquad
 \beta C^k g^2=0\ (0\le k\le3),\qquad
 \beta g^3=0 .
$$
These are genuine forward products in grades at most nine, not
products of two marked rows. For distinct labels $x_1,\ldots,x_r$,
write $V(x)=\prod_i(x-x_i)$. The identities
$\sum_i H(x_i)/V'(x_i)=0$ for $\deg H\le r-2$ and the analogous
leading-coefficient identity at degree $r-1$ follow by Lagrange
interpolation. In particular, annihilating clock powers $0,\ldots,k$
on these labels means an interpolated barycentric density of degree
at most $r-k-2$.

## Nine labels

All nine interior stages are dirty, active and pairwise distinct.
The first moments give $b_i g_i=L(c_i)/V'(c_i)$ with degree
$\deg L\le1$ and $L(c_i)\ne0$ on every dirty clock. The second
moments give a polynomial $P$ of degree at most four with
$P(c_i)=L(c_i)g_i$. If $L$ is constant, the third moment forces
the degree-eight top coefficient of $P^2$ to vanish, so $P/L$
has degree at most three. If $L$ is linear with root $u$, divide
$P^2$ by $L$; the quotient has degree at most seven and contributes
zero to the barycentric sum. The residual contribution to the
third moment is
$$
 - P(u)^2/(L'(u)V(u)),
$$
by the standard partial-fraction identity for $1/V$ evaluated at
$u$. Its denominator is nonzero. Hence $L\mid P$, again yielding
a cubic $U=P/L$ agreeing with $g$ on every dirty row.
Now $C(1-C)(U(c)-g)$ is identically zero with scalar profile
$x(1-x)U(x)$ and grade at most five. Its first four paid clock
probes and the shifted Beta matrix force $U=0$. Contradiction.

## Eight labels

For each dirty label $x$, group
$w_i=b_i g_i$ and write $a_x=\sum_{i:c_i=x}w_i$.
The first moments give $a_x=\kappa/V'(x)$.
There is a singleton active dirty row at some label, so $\kappa\ne0$
and every $a_x$ is nonzero. The second moments give a polynomial
$U$ of degree at most three satisfying
$U(x)=(\sum_{i:c_i=x}w_i g_i)/a_x$.
Every singleton dirty row then has $g_i=U(c_i)$.

There is room for at most one duplicate active dirty row.
For such a pair, its third-moment excess over $a_x U(x)^2$ is
$w_1w_2(g_1-g_2)^2/(w_1+w_2)$. The sum of $a_xU(x)^2$ is
zero since $\deg(U^2)\le6$; the literal third moment is zero too.
Thus a repeated pair must have equal $g$, making $g=U(c)$
at both rows. If there were no active interior clean row, the
paid weighted clock reads of $C(1-C)(U(c)-g)$ would all vanish
even at any leftover ghost row, and the same Beta test would
contradict $U\ne0$. There must therefore be exactly eight distinct
active dirty interior rows and one active clean interior row of
clock $\eta$, plus the two endpoints.

The true contrast $v_0=U(c)-g$ is supported on those three clean
rows. Mask it by $C(1-C)(C-\eta)$ and take the four paid clock
tests. It follows that $(x-\eta)U$ is a nonzero multiple of
$$
 J_4(x)=x^4-2x^3+\tfrac43x^2-\tfrac13x+\tfrac1{42},
$$
the monic degree-four polynomial orthogonal against all degrees
below four for weight $x(1-x)$. The formula follows by direct
integration and the shifted Beta matrix. Thus $\eta\ne0,1$
and $U(0),U(1)\ne0$. In fact the origin is active as well:
$(1-C)(C-\eta)v_0$ is supported only at the origin and its
formal integral is a nonzero multiple of $I((1-x)J_4)$.
If the latter were zero, the four previously paid $x(1-x)$
moments would give all five $(1-x)$ moments on this quartic,
contradicting the paid size-five Beta rank. Thus every individual
output weight is nonzero in this high-support branch.

## Endpoint chronology

A normalized forward cubic kernel profile is
$v=P_f(c)+\delta g$, where $\deg P_f\le3$, $P_f(0)=0$,
and $P_f\ne0$. On the eight dirty rows it evaluates the sole
cubic $P_f+\delta U$. If four dirty clocks precede its pivot,
this cubic must be identically zero. Its value at zero would
then force $\delta=0$ since $U(0)\ne0$, and hence $P_f=0$,
contradiction. Therefore at most three dirty rows precede the
pivot. With just one clean interior row this forces $i\le6$;
if $i=6$, that clean row must precede it.

For the backward conclusion, assume $\dim E_6=10$ (for example,
from the established grade-six surplus and the paid anchored
fourth-degree coefficient separation). The true backward cubic
defect $G$ and the weighted ordinary cubic $B g$, for
$B=\operatorname{diag}(b)$, both annihilate $E_6$, both are
nonzero, and so are proportional. A reverse kernel with genuine
endpoint profile $Q(1)=0$ then evaluates $Q+\delta U$ on the
dirty labels after stripping only individual nonzero weights.
The same root count, now at clock 1, shows that no four dirty
rows can follow the reverse pivot. Thus $j\ge6$; if $j=6$,
the clean row must follow it. No backward stage count is claimed
without this rank input.
