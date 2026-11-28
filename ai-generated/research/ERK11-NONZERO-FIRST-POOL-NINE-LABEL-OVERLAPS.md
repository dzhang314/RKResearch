# Nine active labels with nonzero first pool: two overlap exclusions and a sharp repeat census

**Scope.** Continue the maximal all-live, half-clock, seventeen-stage
ERK11 chart with exactly two quadratic carriers at physical 2 and 16
and [both front boundaries genuinely new](ERK11-SOLE-LATE-CARRIER-TWO-FRONT.md).
The zero-first-pool branch is separate. In the nonzero-first-pool case
the number $q$ of active noncarrier clock labels is 9, 10 or 11.
For $q=9$, this note excludes coincident plateaus over an ordered
field and simultaneous mixed overlaps over a characteristic-zero
field. It further gives a small repeat census and a finite width
projection in one single-mixed-overlap subchart. It does not
exclude $q=9$ generally or move the ordinary stage bounds.

Throughout, grade is rooted size minus one, so total grade at most
ten is paid. Write $s$ for the carrier indicator, $\theta$ for its
common clock, $F=\theta As$ for the physical grade-three pure
response, and $C=\operatorname{diag}(c_i)$. Active means $F_i\ne0$.
The left plateau and half are $a,h=a/2$; the right ones are
$d=1-b,e=1-b/2$. Here $b$ alone in clock formulas is the reflected
width, not the output row, whose entries are $b_i$.

## 1. Three pooled moments and an actual repeat mask

For distinct active sites $x$ put
$$
 \nu_x=\sum_{c_i=x} b_iF_i,\qquad
 \mu_x=\sum_{c_i=x} b_iF_i^2,\qquad
 \tau_x=\sum_{c_i=x} b_iF_i^3 .
$$
Dormant rows contribute zero to these pools even at an active
clock. The paid clock moments of these three rows vanish through
degrees 7, 4 and 1 respectively. If $D(X)$ is the monic hull
of the $q$ active labels, barycentric interpolation gives
$$
 P(x)=D'(x)\nu_x,\quad Q_*(x)=D'(x)\mu_x,\quad
 \deg P\le q-9,\quad\deg Q_*\le q-6 .
$$
Indeed $\sum f(x)/D'(x)$ reads the leading coefficient of
the remainder modulo $D$. Applying the consecutive moment
vanishings removes the successive top coefficients of the
interpolating polynomial. Nonzero first pool means $P\ne0$,
so $q\ge9$.

There are eight guaranteed active flank hits, at physical
3,4,6,7 and 11,12,14,15. Let $k$ count the active fifths
5 and 13, and $m$ the active inner rows among 8–10. The
endpoints and carriers are dormant. Thus $n=8+k+m$ is the
number of active rows. Removing the $k$ active fifths does
not change the label set since they repeat their own plateau.
Hence $q\le8+m\le11$. In particular $q=11$ forces all eleven
base hits distinct; $q=10$ has at most one collision among
the base hits after deleting the fifths.

The genuine pure vector
$$
 S=P(C)F^{\odot2}-Q_*(C)F
$$
has grade at most $q-3$, and vanishes both on dormant rows and
on every singleton active label. Its same-clock ordinary pool
is zero. Its weighted response pool is
$$
 \eta_x=\sum_{c_i=x} b_iF_iS_i
       =D'(x)(\nu_x\tau_x-\mu_x^2).
$$
On a pair with live ordinary weights $u_1,u_2$ and active
responses $f_1,f_2$, the determinant before multiplying by
$D'(x)$ is
$$
 \nu_x\tau_x-\mu_x^2=u_1u_2 f_1f_2(f_1-f_2)^2.
$$
The paid moments of $\eta$ are $0\le j\le10-q$, from the
actual product $C^j F S$. Thus at $q=9$ a nonzero $\eta$ needs
at least three repeated labels; at $q=10$ it needs at least two.
In particular at $q=9$, if there are at most two repeated
labels, all two-row active groups are flat (their responses
are equal). No similar flatness is inferred for a triple.

## 2. A two-clock Jacobi gate at $q=9$

Now $P$ is a nonzero constant and all $\nu_x$ are nonzero.
Set $Q=Q_*/P$, of degree at most three, so
$\mu_x=\nu_xQ(x)$. There is a singleton active label since
$n\le13<18$; at it $Q(x)=F_i\ne0$, so $Q$ is not the zero
polynomial. The actual grade-three pair with model $Q$,
$$
 T=Q(C)\mathbf1-F-Q(\theta)s ,
$$
vanishes on the carriers and every flat active group. Thus
it is supported only on dormant noncarriers and nonflat
active groups. At a repeated label, at least two active
coordinates of $T$ are nonzero if any are: their weighted
response pool $\sum b_iF_iT_i=Q(x)\nu_x-\mu_x$ vanishes
and each active coefficient $b_iF_i$ is live.

If the clock support of $T$ outside 0,1 has at most one
label $p$, then $C(1-C)(C-p)T$ is a literal zero vector of
grade at most six with model $X(1-X)(X-p)Q(X)$.
Pairing with clock degrees through four and using the
nonsingular rational weight-$X(1-X)$ Gram forces
$(X-p)Q=0$, impossible over characteristic zero. If there
are two possible nonendpoint support labels $p,r$, use
both masks instead. The zero grade-seven vector yields
$$
 R(X)=(X-p)(X-r)Q(X)\ \in\
 \operatorname{span}\{R_4,R_5\},\qquad
 R_4=42X^4-84X^3+56X^2-14X+1,\quad
 R_5=132X^5-330X^4+300X^3-120X^2+20X-1 .
$$
Here $R$ is orthogonal to degrees through three for
$w(X)=X(1-X)$. The four rational Gram tests are independent;
the exact moments and distinct degrees verify the stated
basis. The clock pair $p,r$ is therefore subject to
$$
 R_4(p)R_5(r)-R_5(p)R_4(r)=0 .
$$

Over an ordered field pass to a real closure. The exact sign
intervals in the replay interlace four simple interior roots
of $R_4$ with all five simple interior roots of $R_5$.
For any combination with a nonzero $R_4$ coefficient its
signs alternate at consecutive roots of $R_5$. Thus every
nonzero pencil member $R$ has degree 4 or 5, all simple real
roots, at least four strictly interior. The pure $R_5$ member
has all five. Let $r_i$ be these roots and $\lambda_i$ their
weight-$w$ Lagrange weights. Polynomial division by $R$
and the four paid moments give quadrature exact through
$\deg R+3$. In particular
$\lambda_i=\int w\,\ell_i^2>0$ for the degree-$(\deg R-1)$
Lagrange basis $\ell_i$. The positivity is that of a rational
weighted-square Gram, which extends to each ordered field.
For $u$ a root, write
$$
 M_u=\int w(X)\frac{R(X)}{X-u}\,dX
     =R'(u)\lambda_u\ne0 .
$$

### A true endpoint-supported grade-five pair

If the literal support of $T$ away from physical 1 and 17 lies
on the two nonendpoint clocks $p,r$, then
$V=(C-p)(C-r)T$ is a true vector in both grade-five spaces:
$T$ used only the common low pure and scalar spaces.
It is physically supported on 1 and 17 and has the
nonzero model $R=(X-p)(X-r)Q$. Grade-five model
separation makes it nonzero. Each literal first-eleven
front reads its own $E_5$ injectively, so both endpoint
coordinates are live: an endpoint-only vector missing
the first coordinate of either orientation would vanish
on that entire front. Here $V_1=R(0)$ and $V_{17}=R(1)$
by the true dormant endpoint reads.

Pair $V$ with any forward pure grade-five vector. That
vector is zero at the origin, so its paid annihilation
of $V$ forces its physical-17 value zero. Pair instead
with the reverse pure space using the mixed grade-five
annihilator to get reflected grade-five point exactness
at physical 1. In particular the
[weighted reversal theorem](ERK11-ONE-SPARE-WEIGHTED-TRANSPOSE.md)
now earns ordinary reverse order eleven in this
literal two-label support chart. This argument is
characteristic zero and does not assume that there
are no clock aliases at other sites: it requires
the stated *physical* support of $T$.

Write $R=\lambda R_4+\mu R_5$. The paid products with the
ordinary clock and its complement give, respectively,
$$
 b_{17}=\frac{\lambda/30+\mu/42}{\lambda+\mu},
 \qquad
 b_1=\frac{\lambda/30-\mu/42}{\lambda-\mu}.
$$
Both denominators are live by the measured endpoint
coordinates. In particular this applies to the
$n=13$ two-plateau-triple chart below, even before
its single-mixed specialization.

## 3. Isolating a physical row is impossible

Suppose in the two-label situation that $U=(C-p)T$ is
supported on the two physical endpoints and just one
internal physical row $i$ at $\zeta=r\ne0,1,p$. The local
pool property above implies this row is response-zero; a
sole active nonzero coordinate of $T$ at its label is impossible.
Thus $U_i=(\zeta-p)Q(\zeta)=R'(\zeta)\ne0$.

Use the actual grade-four square-clock vectors $V_L,V_R$,
both zero through the seventh row of their own front. Their
models are $V_a=X^2(X-a)^2$ and $V_b=(1-X)^2(X-d)^2$.
Let $P_a=J V_a$ and $P_b^\star=\bar J V_b$ be their left
and right primitives. The literal $AV_L$ is zero through
physical 8, and $A^\star V_R$ is zero from 10 onward.
Any actual forward and reverse grade-at-most-five factors
pair to their scalar model product: the reverse pure part
annihilates forward $E_5$, and the reverse clock model can
be tested by the original order-eleven rule. This is the
mixed payment behind the two-front Gram, not reverse
ordinary order eleven.

The true read of $C(1-C)U$ gives
$$
 M_\zeta=b_i\zeta(1-\zeta)U_i .
$$
The forward product $(1-C)U\odot AV_L$ has grade ten.
Its model integral is
$$
 \int (1-X)(X-p)Q P_a
 =\frac{P_a(\zeta)}{\zeta}\,M_\zeta :
$$
divide the polynomial $P_a/X$ by $X-\zeta$, and its degree-three
quotient is killed by the weight-$w$ orthogonality of $R$.
The literal product is supported only at $i$ (the origin
is killed by strictness and the terminal by $1-C$).
Consequently $(AV_L)_i=P_a(\zeta)$. The mixed grade-$5+5$
product $CU\odot A^\star V_R$ in the same way gives
$(A^\star V_R)_i=P_b^\star(\zeta)$, dividing the polynomial
$P_b^\star/(1-X)$ by $X-\zeta$. All canceled factors are
independently live. For instance
$$
 P_a(x)/x=x^2\left[\tfrac15(x-\tfrac54a)^2+\tfrac{a^2}{48}\right]
$$
is positive for ordered $x\ne0$, and the reflected formula is
positive for $x\ne1$. This excludes $i\le8$ or $i\ge10$ by
the literal primitive zeros.

If $i=9$, the paid two-primitive product is supported only
on physical 9. Its value would be
$$
 \int P_a P_b^\star=b_iP_a(\zeta)P_b^\star(\zeta)
  =\lambda_\zeta f(\zeta),\qquad
 f=(P_a/X)(P_b^\star/(1-X)).
$$
The last equality follows from $M_\zeta=R'(\zeta)\lambda_\zeta$
and $U_i=R'(\zeta)$. But $f$ is nonnegative at every real
node and strictly positive at every interior node, with
positive leading coefficient $1/25$. If $\deg R=5$, the
left integral is $\int w f=\sum\lambda_i f(r_i)$ by
degree-eight exactness. It is strictly larger than the
single $\zeta$ term. If $\deg R=4$, subtract the positive
leading multiple of the squared monic hull; the same
quadrature sum is exact on the remainder, and the error
is a strictly positive weighted-square norm. The same
contradiction follows. This ordered argument is entirely
independent of the ordinary signs of the tableau weights.

More generally, without isolating a single physical row:
if the nonzero reads of $U$ away from the physical endpoints
have just the one nonendpoint clock $r$, the same two primitive
tests give their $b_iU_i$-weighted means $P_a(r),P_b^\star(r)$.
Thus some nonzero $U$ read is at physical $\ge9$ and some
at physical $\le9$. No point-exactness is inferred in this
multirow case.

## 4. Two complete overlap exits

**Coincident plateaus $a=d$, ordered scope.** The common
plateau has at least $2+k$ active occurrences, so it consumes
$1+k$ repeat incidences. The total available is $n-9=k+m-1$,
hence $m\ge2$. If $m=3$, there is at most one additional
pair group. The two paid $\eta$ moments make that group
flat. All other possible nonzero $T$ reads are at the
endpoints or plateau (including any inactive fifths).
The one-clock characteristic-zero contradiction applies.
If $m=2$, the plateau consumes the entire repeat budget.
Mask it out. Outside the physical endpoints the only possible
nonzero read is the single inactive middle row. Its clock
must be different from $0,1,a$ by the one-clock test.
The isolated-row ordered proof excludes it. This covers
all fifth-row activity choices, not just the full plateau
pairs.

**Both mixed overlaps $a=e,h=d$, characteristic-zero scope.**
These force $a=b=2/3,d=1/3$. The two calibration groups
have two guaranteed hits each before the optional fifths,
so together consume at least $2+k$ repeat incidences.
Thus $m=3$ and there are no other repeats; the only
internal dormants are fifths, at those same two clocks.
The two-clock Jacobi determinant is impossible, since
$$
 R_4(1/3)=R_4(2/3)=-1/27,\qquad
 R_5(1/3)=-7/81,\quad R_5(2/3)=7/81 .
$$
This argument needs neither ordered quadrature nor any
assumption about the responses within the two repeated
groups.

## 5. Refined $q=9$ census and a remaining single-mixed chart

These deductions use the ordered isolated-row exit when
indicated. Before it, the pure count and $\eta$ conditions
hold over characteristic zero.

* $n=9$ requires $k=0,m=1$ and all active labels singleton.
  $n=10$ requires $k=0,m=2$ and one flat active pair.
  Indeed a full plateau at $n=10$ could only be an unequal
  pair, impossible with one repeated label. At $n=10$ the
  one inactive middle clock avoids $0,1,a,d$ and its
  $Q$ value is nonzero. For a collision with a plateau,
  mask that plateau and isolate the other dormant fifth.
  If the middle clock is 0, the same right primitive test
  with $C$ kills it and isolates the already zero primitive
  at physical 13. If it is 1, the left $(1-C)$ test does
  the reflected job at row 5. Any collapsed nonendpoint
  support is already covered by the one-clock contradiction.
  A zero $Q$ at the middle likewise leaves only the two
  plateau fifths to isolate.
* $n=11$, $k=1,m=2$ requires a nonflat triple at the
  full plateau and no other repeat, by flatness of any
  pair when there are at most two repeated groups.
  The dormant middle cannot share that full plateau:
  otherwise masking it isolates the other dormant fifth.
  With $k=0,m=3$, two flat pairs or a flat triple leave
  only the two dormant fifths and endpoints in $T$,
  impossible by isolation. The only repeat is a nonflat
  triple at a clock distinct from $0,1,a,d$: a plateau
  collision isolates the other fifth; an endpoint collision
  is killed by the one-sided primitive mask as above.
  The option $k=2,m=1$ would have two unequal plateau
  pairs but no third charged label, and is impossible.
* $n=12$ requires $k=1,m=3$ or $k=2,m=2$ and exactly
  three unequal active pairs. If there were at most two
  repeated labels, each full plateau group would have
  to be a triple. Two full plateaus would exceed the
  repeat budget. With one full plateau all other groups
  are flat and the only dormant fifth is isolated after
  masking the nonflat plateau. The three-pair case has
  every $\eta$ nonzero and proportional to the ordinary
  three-site barycentric weights.
* $n=13$ has two full plateaus. The repeat multiplicities
  are two triples at the plateaus, one triple plus two
  pairs, or four pairs. The last two require at least
  three nonzero $\eta$ groups by a full plateau pair.
  In the two-triple case $T$ is supported at endpoints
  and the two plateaus. Each plateau must have nonzero
  $T$ reads on both sides of physical 9 in the weak
  sense $\le9$ and $\ge9$. Thus the third occurrence
  at $a$ is at physical $\ge9$ and the third at $d$
  at physical $\le9$, with nonzero deviation there.

In that last two-triple case, a single mixed overlap
$a=e$ sets $d=2a-1$. The two-clock determinant gives the
following degree-eight equation, since $a\ne1$:
$$
 44352a^8-221760a^7+474432a^6-564984a^5+
 407346a^4-180576a^3+47432a^2-6592a+353=0.
$$
The opposite single mixed overlap gives the reflected
equation in $b$. This is a finite width projection only.
The six guaranteed nonplateau reads retain their actual
front calibrations; no cancellation of a nonflat triple is
inferred. For a triple with three distinct responses, the
zero determinant $\nu\tau-\mu^2$ describes its three
$b_iF_i$ shares as Lagrange evaluation of quadratics at
$Q(x)$. In particular none of the three responses can
equal $Q(x)$ with all shares live. If exactly two responses
coincide, their pooled $b_iF_i$ share is zero and the
remaining response equals $Q(x)$; the actual same-clock
rows are not deleted.

The small standalone replay checks the exact weighted
Jacobi moments, rational Gram pivots, interlacing sign
intervals, mixed-overlap determinant and degree-eight
specialization. The actual tableau, graded support and
ordered quadrature arguments are the mathematical proof.

Replay: `python3 -B replay_erk11_nonzero_nine_overlap_scalars.py`.
See the [exact output](ERK11-NONZERO-NINE-OVERLAP-EXACT.log).
No new native Lean theorem is claimed in this packet.
