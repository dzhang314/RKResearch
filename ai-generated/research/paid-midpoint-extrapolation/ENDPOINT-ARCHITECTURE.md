# Stage sharing and optimality within the unsmoothed endpoint architecture

This is a companion to [the paid-ring construction](PAID-MIDPOINT-EXTRAPOLATION.md).
It concerns arbitrary rational affine combinations of unsmoothed
explicit midpoint endpoints, all run across the same macrostep
$H$. It does not bound explicit methods that use other stage
equations and does not compare numerical efficiency.

## What can actually share a derivative

For $y'=\lambda y$ and $y=1$, write $x=H\lambda$ and let
$Y_{n,j}(x)$ denote the stage polynomial of branch $n$. Its
degree is exactly $j$ and the leading coefficient, for
$j\ge1$, is $2^{j-1}/n^j$ by the two-step recurrence.
The linear coefficient is $j/n$. Consequently stages of
different positive indices differ by degree, while at a fixed
positive index $j$ stages of distinct $n$ differ already in
the linear coefficient. Only $j=0$ is shared. Endpoints at
different $n$ differ in degree, and none is used as a new
derivative evaluation. For the levels in the paid-ring
construction, the same argument survives every allowed
nonzero specialization: the leading coefficients are units,
and the linear difference at equal $j>0$ is
$j(1/n-1/m)$, again a unit when $j,n,m\le p$ and $n\ne m$.
Thus a coincidence modulo a permitted residue characteristic
does not allow more literal reuse either.

## Even and odd levels cannot trade their missing mesh moments

Combine any finite collection of distinct positive integers
$n$ with weights $w_n$; merge equal levels and drop zero
weights. Define the two sets of scalar moments for $k\ge0$:
$$
 E_k\coloneqq\sum_{n\ {\rm even}}w_n n^{-2k},\qquad
 O_k\coloneqq\sum_{n\ {\rm odd}}w_n n^{-2k}.
$$
The exact necessary and sufficient conditions for cleared
rooted order through $p$ over $\mathbb Q$ are
$$
 E_0+O_0=1,\qquad
 E_k=0\quad(1\le k\le\lfloor(p-1)/2\rfloor),\qquad
 O_k=0\quad(1\le k\le\lfloor p/2\rfloor).
$$
Sufficiency is the separate parity degree bound in the main
proof, followed by the vertex-variable test for every tree.
Necessity already holds on the scalar linear test, as follows.

Put $s=x/n$, $a=\operatorname{arsinh}(s)$ and
$b=(1+s^2)^{-1/2}$. The roots of the scalar recurrence
$Y_{j+1}=2sY_j+Y_{j-1}$ are $e^a,-e^{-a}$. The initial
values $1,1+s$ give the endpoint formulas
$$
 \begin{split}
 Y_{n,n}&=\cosh(na)+b\sinh(na) &&(n\text{ even}),\\
 Y_{n,n}&=\sinh(na)+b\cosh(na) &&(n\text{ odd}).
 \end{split}
$$
For $k\ge1$, the coefficient of $x^{2k}$ has
$n^{-2}$-degree at most $k-1$ in the even class. In the
odd class its coefficient at degree $k$ is the coefficient
of $s^{2k}$ in $b$, which is nonzero. Indeed the other
terms from $\cosh(na)$ use at least two factors of $na$
and thus lose at least one mesh power. So degree $2k$
forces $O_k=0$ once the smaller moments vanish.
At degree $2k+1$ the even leading coefficient is the
coefficient of $s^{2k+1}$ in $ba$, from the linear term of
$\sinh(na)$. It is nonzero: each summand in the product of
the two alternating series has sign $(-1)^k$ and positive
magnitude. The odd moment $O_k$ is already zero, so
degree $2k+1$ next forces $E_k=0$. The zeroth condition
is consistency, and induction proves all the displayed
necessary moments. Each parity has the same exact-flow
constant term in the mesh variable, so no extra bias term
occurs in the induction.

If a parity class has $K$ vanishing positive moments and
uses at most $K$ distinct nodes, the first as-many moment
equations as nodes form a homogeneous invertible
Vandermonde system after factoring one nonzero node out
of each column. Hence that parity class has no nonzero
weight. An active class needs at least $K+1$ levels.
With degree $p=2r$ this means at least $r$ even levels
or $r+1$ odd levels. With $p=2r-1$ it means at least
$r$ levels in either class. Each choice minimizes its
derivative count by the smallest positive integers of that
parity. The cheaper parity is the one matching $p$:
its shared-initial count is $r^2+1$ or $r(r-1)+1$,
respectively. Using both classes cannot reduce the count,
as their branches only share the initial derivative.
This proves optimality in the stated architecture, not a
general RK minimum or a literature-priority claim.

For the selected paid-ring tableau there is no inactive branch
to remove, either: each noninitial derivative stage lies on
the consecutive branch chain to that branch's final derivative,
whose output weight is a unit. This does not rule out another
tableau with fewer stages and different full rooted series.
