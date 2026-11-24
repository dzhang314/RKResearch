# A sign-window exclusion for the strong-three order-16 chart

Two forward and two reverse windows on the same original rows suffice
to exclude the centered strong-three chart. The argument uses
polynomial moments over an arbitrary ordered field. Its only
quadrature input is a positive finite rule of bounded degree.

Write $I(l,r;P)$ for the value at $r$ minus the value at $l$
of the formal primitive of $P$. The primitive has zero constant
coefficient. In a moment expression, $x$ denotes the polynomial
variable.

## Positive sampling and sign variation

**Positive-grid proposition.** For every degree $d$ there is a rational
rule with more than $d$ distinct nodes $t_i$ in $(0,1)$, positive
rational weights $w_i$, and
$$
\sum_i w_i t_i^k=\frac{1}{k+1}\qquad (0\le k\le d).
$$
The [rational midpoint-correction proof](erk_order19_zero_first_seed_opposed_windows_20261124.md#formal-moments-and-alternating-signs)
works in every degree. For the fixed degree needed below, the repository
also gives [exact nodes and weights](positive_rational_rule_degree19_20261124.json) through degree 19.
For ordered-field endpoints $l<r$ and $\deg P\le d$, the affine form is
$$
I(l,r;P)=(r-l)\sum_i w_i P\bigl(l+(r-l)t_i\bigr).
$$
If $P\ne0$ and its samples have one weak sign, the moment has that
strict sign: a nonzero polynomial of degree below the grid size cannot
vanish at every distinct node.

For a nonzero polynomial $P$, count sign changes along increasing
finite samples with nonzero evaluations. The maximum on an interval
is its *variation* there. It is at most $\deg P$: if $P$ alternates
on $m+1$ points and $\deg P<m$, the degree-$m$ coefficient of
its Lagrange interpolant vanishes, although all its contributions
have one nonzero sign. Variation counts in successive intervals add
as lower bounds to the total. Witness sequences can be concatenated,
identifying a common endpoint if necessary.

We use two immediate consequences of the positive-grid proposition.

1. A zero moment against a positive weight forces a sign change on
   the interior grid. Two zero moments against positive weights
   $U,V$ whose ratio $U/V$ is strictly monotone on the interval
   force two. If there were only one change, take a separator $s$
   between the two nonzero sample runs. The tested product
   $(U-(U(s)/V(s))V)P$ has a fixed sign on the grid, and the sign is
   strict at a nonzero sample. This contradicts the two zero moments.
2. If an interior grid attains the variation of the corresponding
   closed interval and $P$ is nonzero at an endpoint, that
   endpoint has the sign of the nearest run. Otherwise appending
   the endpoint gives another change.

All integrands below have degree at most 15. A rule exact through
degree 18 with at least nineteen distinct interior nodes therefore
suffices.

## Scalar theorem

Let $q\in K[X]$ be nonzero with $\deg q\le5$, and let $a\ne b$.
The following six equations cannot hold together with the weighted
orthogonality below:
$$
\begin{aligned}
I(0,a;xq)&=I(0,a;x^2q)=0,&
I(0,b;x(x-a)q)&=0,\\
I(b,1;(1-x)q)&=I(b,1;(1-x)^2q)=0,&
I(a,1;(1-x)(x-b)q)&=0.
\end{aligned}
\tag{1}
$$
The orthogonality is
$$
I(0,1;x(1-x)JH)=0\quad(\deg H\le6),
\qquad J=(x-a)(x-b)q .
\tag{2}
$$

### Root location and reflection

Put $W=x(1-x)$. If $\deg J\le6$, testing (2) with $H=J$
contradicts the positive moment of $WJ^2$. Thus $\deg J=7$
and $\deg q=5$.

For an actual root $r=a$ or $b$, write $J=(x-r)U$ and test
with $H=U$. If $r\le0$ or $r\ge1$, the polynomial
$W(x-r)U^2$ has a strict fixed-sign moment on the positive interior
grid. Its degree is at most 15. This proves $0<a,b<1$.
If $(x-r)^2$ divided $J$, write $J=(x-r)^2V$ and test
with $H=V$. The positive moment of $W((x-r)V)^2$ is again a
contradiction. Both roots are therefore simple and $q(a)q(b)\ne0$.

The polynomial $J^*(x)=-J(1-x)$ has the same leading coefficient
and satisfies (2), by reflection. Hence $D=J-J^*$ has degree at
most six and $I(0,1;WD^2)=0$, so
$$
J(1-x)=-J(x).
\tag{3}
$$

### Increasing numerical order

Suppose $a<b$. On $(0,a)$ and $(b,1)$, the pairs of
moments in (1) force at least two changes each. Subtract the masked
forward moment at $a$, which follows from the two tests there,
from the masked moment at $b$. Do the same for the masked reverse
moments at $a,b$. On $(a,b)$ this gives zero moments against
the positive weights $x(x-a)$ and $(1-x)(b-x)$. Their ratio is
the product of the positive strictly increasing functions
$x/(1-x)$ and $(x-a)/(b-x)$. This gives two more changes.
Six changes contradict the degree-five bound.

### Decreasing numerical order

Suppose $b<a$. Let $L=(0,b)$, $M=(b,a)$, and $R=(a,1)$,
and use
$$
U=x(a-x),\qquad V=(1-x)(x-b).
$$
Equation (1) gives zero $Uq$-moments on $L$ and $M$, and zero
$Vq$-moments on $M$ and $R$. On $M$ the weights are positive.
Their ratio
$$
\frac U V=\left(1+\frac b{x-b}\right)
            \left(1-\frac{1-a}{1-x}\right)
$$
is strictly decreasing: both factors are positive and strictly
decreasing there. Thus the variations on the three closed intervals
are at least $1,2,1$. The two remaining equations we will use are
$$
I(L;xq)+I(M;xq)=0,\qquad
I(M;(1-x)q)+I(R;(1-x)q)=0,
\tag{4}
$$
where interval arguments abbreviate the corresponding pair of endpoints.

If $L$ has one change, choose a separator $s$ between its two
nonzero grid runs. Subtracting $U/(a-s)$ from $x$ shows that
$I(L;xq)$ has the strict sign of $q(b)$: the residual weight is
$x(x-s)/(a-s)$, and the endpoint sign agrees with the nearest run.
Likewise, if $R$ has one change, subtract $V/(s-b)$ from $1-x$
at its separator. The residual weight is $(1-x)(s-x)/(s-b)$,
so $I(R;(1-x)q)$ has the strict sign of $q(a)$.

Suppose $M$ has exactly two changes. Choose separators $b<r<s<a$
between its three nonzero grid runs. The endpoint signs agree.
Set $g(x)=V(x)/x=1+b-x-b/x$, and let
$$
h=-1+\frac b{rs},\qquad D=g(r)+(a-r)h .
$$
Here $h$ is the secant slope of $g$ at $r,s$, and
$$
D-g(a)=\frac{b(a-r)(a-s)}{ars}>0,\qquad g(a)>0 .
$$
With $\alpha=h/D,\ \beta=1/D$, the polynomial
$x-\alpha U-\beta V$ vanishes at $r,s$ and has constant term
$\beta b$. It is therefore
$\kappa(x-r)(x-s)$, where $\kappa=\beta b/(rs)>0$. Since the
$Uq,Vq$-moments vanish, $I(M;xq)$ has the strict sign of $q(b)$.
Reflection swaps the weights and shows that $I(M;(1-x)q)$ has the
strict sign of $q(a)$. Strictness in each case is supplied by the
nonzero residual polynomial times $q$ on the positive grid.

At least one outer interval has one change when $M$ has two, since
the total is at most five. Its cross test in (4) then adds two moments
of the same strict sign. It follows that the only remaining variation
counts are $(1,3,1)$.

### The remaining reflected pair

Over any ordered field, two distinct simple roots of a polynomial
have different preceding variation counts. In fact, let $r<s$,
suppose $P=(x-r)U$ with $U(r)\ne0$, and take a variation witness
strictly before $r$. Close enough to $r$, $U$ has the sign of
$U(r)$ on both sides. This requires no completeness: write
$U(r+z)=U(r)+zV(z)$, bound $|V(z)|$ by the sum of the absolute
coefficients for $|z|\le1$, and choose a sufficiently small positive
field element $\epsilon$. One can require $r-\epsilon$ to follow
the witness and $r+\epsilon<s$. The samples at $r-\epsilon$ and
$r+\epsilon$ have opposite signs, increasing the preceding
variation at $s$.

In the $(1,3,1)$ case, $J$ has exactly one change on $(0,b)$
and one on $(a,1)$, because $(x-a)(x-b)$ is positive there.
By (3), $J$ has exactly one change on $(0,1-a)$ as well.
The two roots $b$ and $1-a$ are simple, the latter by reflection
of the simple root $a$. The preceding variation criterion yields
$b=1-a$. Cancelling the now symmetric factor $(x-a)(x-b)$ from
(3) gives $q(1-x)=-q(x)$.

Thus $I(0,1;Wq)=0$. The two forward tests at $a$ give
$I(0,a;Wq)=0$, hence $I(a,1;Wq)=0$. Reflecting at $a=1-b$
gives $I(0,b;Wq)=0$. Together with the forward test at $b$ in
(1), this gives
$$
(1-a)I(0,b;xq)=0,\qquad I(0,b;x^2q)=0 .
$$
Since $1-a>0$, the two resulting zero moments force two changes
on $L$, contradicting $(1,3,1)$. This proves the scalar theorem.

## Physical implication

Consider an actual strong-three mask on the original width-24 explicit
order-16 tableau. The forced origin and simple contrast clocks label
the three contrast rows by $0,a,b$ in physical order, without
asserting a numerical order for $a,b$. Write $q(x)=Q(1-x)$ for
the forward profile. The forward $3+2+1$ and reverse $2+1$ payments
give (1): the first forward row has zero clock, and the reverse
moments are reflected by $x=1-y$.

The global moment comes from the original contrast support at
reflected clock values $1,1-a,1-b$. For a spectator $H$ of degree
at most six, multiply their cubic hull by $H(1-y)$. The result
has degree at most nine and vanishes on the contrast support.
The reflected contrast moment is therefore zero, with exact charges
$5+9+2=16$ and $4+9+3=16$ for the two fitted profiles. Reflecting
this formal moment gives (2). The nonzero profile and its degree
bound are those of the actual mask. The scalar theorem excludes that
origin-present chart.

The local argument also gives a reusable two-pivot statement: interior
pivots, a simple odd-reflection product $(x-a)(x-b)q$, and the six
windows in (1) suffice. The global moment here supplies interiority,
simplicity, and reflection. In increasing numerical order, the local
windows alone suffice once the pivots are interior. These conclusions
concern the strong-three chart; they do not settle the other
width-24 cases.

The scalar proof is given in prose here. No complete Lean certificate for this exclusion is asserted.
