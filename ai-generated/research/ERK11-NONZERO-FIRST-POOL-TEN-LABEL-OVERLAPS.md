# Ten active labels with nonzero first pool: small support and overlap exits

**Scope.** Continue the maximal half-clock, all-live, exactly-two-carrier
ERK11 chart with both front boundaries genuinely new, as in the
[nine-label packet](ERK11-NONZERO-FIRST-POOL-NINE-LABEL-OVERLAPS.md).
Here $q=10$ and the first response pool is not identically zero.
Over characteristic zero this excludes **coincident plateaus** at
every activity count, **all calibration overlaps at $n=11$**, and
the **sole repeated label at $n=12$**. It also gives an exact
support/chronology reduction for the remaining $n=11$ pair; the
assertion that both copies cannot be in physical 8–10 uses ordering.
This is not a stage lower-bound change or the entirety of $q=10$.

## 1. A cubic profile from nine singleton labels

Keep the common grade-three pure response $F$, carrier indicator
$s$, carrier clock $\theta$, and weighted first, second, third
response pools $\nu_x,\mu_x,\tau_x$. Write $D$ for the hull of
the ten active clock labels. The eight, five and two paid moments
give scalar polynomials
$$
 P(x)=D'(x)\nu_x,\quad Q_*(x)=D'(x)\mu_x,\quad B(x)=D'(x)\tau_x,\qquad
 \deg P\le1,\quad \deg Q_*\le4,\quad \deg B\le7 .
$$
Nonzero first pool means $P\ne0$. At a singleton active clock
all three pools are moments of one actual live weight and one
nonzero response. Hence $P(x)B(x)=Q_*(x)^2$ there.
If there is at most one repeated active clock, there are at
least nine singleton clocks. The difference polynomial has
degree at most eight, so it vanishes identically.

If $P$ is linear, evaluation at its root forces $P\mid Q_*$.
If $P$ is constant then $\deg Q_*^2\le7$, so $\deg Q_*\le3$.
In either case the exact quotient $K=Q_*/P$ is a nonzero
polynomial of degree at most three. At a singleton $P(x)$ is
nonzero, and $K(x)$ is the literal response. Define the
actual grade-three vector with model $K$,
$$
 T'=K(C)\mathbf1-F-K(\theta)s.
$$
It is supported only on the two physical endpoints, dormant
noncarriers, and the one possible repeated active group.
This argument has not canceled $P$ at that repeated clock.

Suppose the plateau clocks agree, $a=d$. Removing the optional
active fifth rows 5 and 13 leaves the eight guaranteed flank
hits and $m\le3$ active inner hits. Their label count remains ten.
One collision among the flank hits forces $m=3$ and uses the
entire remaining collision budget. Thus the sole repeated active
clock is the plateau $a$, and even the inactive fifths have
that clock. Consequently $T'$ is supported only at clock labels
$0,1,a$. The literal zero grade-six vector
$C(1-C)(C-a)T'$ has model $X(1-X)(X-a)K(X)$. Its paid
tests through clock degree four force $(X-a)K=0$ by the
nonsingular weight-$X(1-X)$ Gram, a contradiction over any
characteristic-zero field. No reverse ordinary order eleven or
nonzero $P(a)$ was needed.

## 2. The calibrated dormant fifth does not require ordering

We use a small specialization of the earlier primitive support
argument. If the degree-at-most-five polynomial
$R=(X-p)(X-u)K$ kills all moments through degree three for
$w=X(1-X)$, put
$$
 M_u=\int w(X)R(X)/(X-u)\,dX .
$$
For the actual degree-four $U=(C-p)T'$ the model integrals
of $(1-C)U\odot AV_L$ and $CU\odot A^\star V_R$ are
$$
 [P_a(u)/u]M_u,\qquad
 [P_b^\star(u)/(1-u)]M_u,
$$
where the displayed quotients denote their **polynomial**
extensions. Indeed they are quartics: dividing each by
$X-u$ leaves a constant value at $u$ plus a degree-three
quotient killed by the $R$ moments. The total grades are
ten. As before, the second mixed payment follows from
the actual reverse grade-five pure space annihilating
forward $E_5$, not reverse ordinary order eleven.

If $u=a$ is a forward dormant fifth at physical 5, the
normalized own primitive value is $P_a(a)/a=a^4/30$.
If $u=d$ is a reverse dormant fifth at physical 13 it is
$P_b^\star(d)/(1-d)=b^4/30$. These are nonzero over
characteristic zero; no positivity of arbitrary model
primitive values is needed. When the true weighted read of
$C(1-C)U$ gives
$M_u=b_i u(1-u)(u-p)K(u)\ne0$ at that fifth row,
the matching primitive test cannot be numerically zero.
But the own literal primitive is zero at that physical
row. This is an algebraic contradiction.

In particular this applies if masking $p$ leaves just
physical endpoints and the one dormant fifth (clock
$u\ne0,1,p$ and $K(u)\ne0$). It also applies if the
remaining extra physical reads are at clock 0 for the
right $C$ test, or clock 1 for the left $(1-C)$ test:
those reads are killed by the same factor. No generic
nonzero Jacobi weight assumption is needed when the
required $M_u$ is earned from that literal live row.

## 3. The eleven-active-row chart

There is exactly one repeated active pair. Its determinant
$\eta=D'(x)(\nu_x\tau_x-\mu_x^2)$ vanishes since its one
paid total moment is zero. The two active responses are
equal by the pair identity and the live weights. No full
plateau pair can be this equal pair, so both fifths are
dormant and all three middle rows are active. If the sole
pair is at $p$ and $P(p)\ne0$, its common response equals
$K(p)$. If $P(p)=0$, the first pooled response vanishes
and their two ordinary weights are opposite. In that
case the two $T'$ reads at $p$ are equal and cancel in
**every scalar clock moment**, even if nonzero.

As a result $R=(X-a)(X-d)K$ is the same $R_4,R_5$ Jacobi
pencil as in the preceding note. Indeed
$C(1-C)(C-a)(C-d)T'$ has grade at most seven, and
its weighted reads for clock degrees through three vanish:
it kills all possible dormant contributions and the active
pair contributes zero. The numerically nonzero pair
need not be deleted. If at most one of $a,d$ is a distinct
nonendpoint, the same scalar cancellation with at most
one additional clock factor already gives a zero
weight-$w$ Gram through degree four, impossible.
Thus $a,d$ here are distinct nonendpoints.

If the sole repeated label is $a$ or $d$, mask it
out and isolate the other dormant fifth. That other
plateau's active fourth is a singleton, so its cubic
$K$ value is nonzero. The algebraic calibrated-fifth
test excludes this. This proves in particular both
single mixed overlaps $a=e$ and $h=d$ (the double
mix is already impossible by the ten-label count).
It also excludes a pole at an active plateau that
happens to repeat an unrelated physical row.

If $h=e$ is the sole repeat, then $d=a-1$ and the
equal half responses give the ratio $\kappa=b^2/a^2$
of the reflected physical response to $F$. The two
plateau fourths are singleton, so
$$
 K(a)=-a^2/2=K(d).
$$
Consequently $R(a)=R(d)=0$ and
$R'(a)+R'(d)=(a-d)(K(a)-K(d))=0$. For the
nonzero $R_4,R_5$ combination the two necessary minors
can be taken as the value minor and the derivative
minor using its value at $a$. After substituting
$d=a-1$, the respective factors are $-2J(a),8L(a)$, with
$$
\begin{aligned}
 J(a)&=2772a^8-22176a^7+74088a^6-134064a^5+142332a^4
       -89520a^3+31864a^2-5648a+353,\\
 L(a)&=1386a^8-11088a^7+41202a^6-85050a^5+102015a^4
       -70968a^3+27269a^2-5086a+325 .
\end{aligned}
$$
The exact integer Bézout combination is $79986726$, nonzero
in characteristic zero. This closes the shared half without
ordering, independently of whether $P(p)$ vanishes.

In every remaining chart the pair must have
$P(p)=0$ and its common response must differ from $K(p)$.
Otherwise $T'$ has only the fifths and endpoints as possible
support; masking one plateau isolates the other fifth, again
impossible. The repeat clock $p$ is nonendpoint: if $p=0$
use $(C-a)T'$ and the right $C$ test, which removes the
pair and leaves the strict-zero right fifth. If $p=1$, use
$(C-d)T'$ and the left $(1-C)$ test instead. The same
calibrated-fifth contradiction applies. Thus the surviving
pair has a unique root of linear $P$, equal responses,
opposite ordinary shares, and nonzero $T'$ deviation.

That pair must have one occurrence at physical $\le9$ and
one at $\ge9$. If both were at $\le8$, then the left
$(1-C)(C-d)T'$ primitive product is numerically zero through
strictness (including at the forward fifth) and the endpoint
mask. Yet its model read is $(a^4/30)M_a\ne0$. Indeed the
pair cancels in the scalar read of $M_a$; it comes only
from the dormant fifth at $a$ with live $K(a)$, weight and
clock factors. The reflected argument excludes both
occurrences at $\ge10$.

Over an ordered field the two occurrences cannot **both**
be in physical 8–10. The left and right actual grade-four
square-clock profiles are identical across such an equal-state
pair, so its opposite ordinary shares cancel all three
paid moments of $V_L\odot V_R$. That product is already
supported only on physical 8–10. Mask its remaining one
clock $x$ by applying $C-x$ once to each factor: the paid
model integral of the nonzero square
$[(X-x)X(1-X)(X-a)(X-d)]^2$ would be zero. The rational
weighted-square Gram rules this out. This last deduction
is ordered; the preceding straddle and overlap tests are
characteristic zero.

## 4. The twelve-active-row sole repeated label

Here a sole repeated active group is a triple. There must
be exactly one full plateau: two full distinct plateaus
would give two repeated groups, and coincident plateaus are
already excluded. Thus $m=3$, the triple is the full
plateau, and the only dormant nonendpoint physical row
is the fifth at the other plateau. The cubic $T'$ support
is confined to the triple clock, endpoints and this fifth.
Masking the triple isolates the fifth, whose active fourth
is singleton and has live $K$. If one of the plateau clocks
were an endpoint, the one-clock Gram contradiction is
even shorter. Otherwise the calibrated-fifth proof completes
the characteristic-zero exit. Hence surviving $n=12$ must
have two active pairs, both unequal by the paid total
$\eta$ and at least one actual full plateau.

## Native scalar certificates

ERK11SharedClockPrimitiveGate.lean checks both rank-one
moment identities, the literal clock mask, and the
primitive comparison before cancellation over arbitrary
commutative rings, followed by field cancellation under the
explicit live mask. ERK11TenLabelHalfOverlapGate.lean checks
the value and derivative minors and their integer Bézout
combination over arbitrary commutative rings. These are
the scalar certificates, not a native claim about the
tableau census or the ordinary lower bound.

The [kernel receipts and exact output](erk11-ten-label-overlap-audit/) record
replays on every requested core Lean release, 4.34.1 through 4.37.0-rc1.
The independent scalar arithmetic can be reproduced with
`python3 -B replay_erk11_ten_label_half_overlap.py`.
