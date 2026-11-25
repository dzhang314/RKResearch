# Interval-contained same-gap moves: a real-window and component test

A first condition for interval-constrained rational quadrature is
a real open set of split cubics whose three new roots are **strictly**
inside the interval. A separate condition is that rational points
approach this open set on the ordered elliptic curve. Positive rank
alone does not give density in every real component.

The criterion below and two exact prescribed moves from the published
12-site interval seed give **13 interval sites at exact order 15** and
**14 at exact order 16**. Weights need not be positive. There is no
claim of indefinite interval propagation or an RK stage bound.

## 1. Exact real-window test

Use a genuine rational rule for \(\mathcal I\) on \(n\) distinct
contributing sites in \([0,1]\), exact order \(n+2\). Write \(P\)
for its monic nodal polynomial,
\(C_i=\mathcal I(P/(X-x_i))\), \(h=\mathcal I(X^2P)\ne0\),
and \(k=\mathcal I(X^3P)\). For sites \(u<v\), put
\(\ell=v-u\), \(B=(X-u)(X-v)\), and
\[
 R_u=h/(C_u\ell),\qquad R_v=-h/(C_v\ell),\qquad
 F(X)=X+\frac{R_u}{X-u}+\frac{R_v}{X-v}.
\]
The [paid one-step pencil](../two-shift-elliptic-transfer/elliptic-transfer.md)
is
\[
 G_\tau(X)=(X-\tau)B(X)+R_u(X-v)+R_v(X-u).
\]
Its finite roots are not poles and are exactly the solutions of
\(F(X)=\tau\).

**Four cuts.** A real parameter with three simple roots in
\((0,1)\) exists if and only if there are four rational cuts
\(0\le d_0<d_1<d_2<d_3\le1\) at which \(G_\tau\) has strict signs
\(-,+,-,+\) for some common real \(\tau\).
Sufficiency is the intermediate value theorem plus degree three.
For necessity take cuts in the four gaps of a monic cubic with
three distinct interior roots. The four sign tests are affine in
\(\tau\); their intersection is a real open interval (possibly
unbounded), and the coefficients and finite endpoints are rational
for rational seed data. At a nonpole the signs can use
\(G_\tau(d_i)=B(d_i)(F(d_i)-\tau)\); at a pole use its fixed value
directly. This tests an **open** interior window, not an isolated
parameter at which one or more roots lie exactly on the boundary.

Equivalently split \((0,1)\) at the poles and at the real roots there
of
\[
 (X-u)^2(X-v)^2-R_u(X-v)^2-R_v(X-u)^2=0 .
\]
The open images of the resulting strictly monotone branches are
intervals. A nonempty intersection of any three distinct branch
images gives exactly such a window; conversely three simple
interior roots lie in three branches and give that intersection.
Either description permits exact sign enclosures without solving
a large rational root problem.

## 2. Which real windows are arithmetically reachable

Assume the ordered-root elliptic curve \(E\) is smooth, with the
earlier distinguished infinity difference \(D\) nontorsion over
\(\mathbb Q\). Let \(S\subset\mathbb P^1(\mathbb R)\) be the open
locus of parameters with three distinct **real projective** roots,
and \(S_\infty\) its connected component containing \(\tau=\infty\).
The latter fibre is \((u,v,\infty)\) in its six orderings.
Then
\[
  \{\tau\in S:\text{some ordering lies in }E(\mathbb R)^0\}
              =S_\infty .                                  \tag{1}
\]
Indeed over \(S\) the orderings are a six-sheeted real covering.
Any path in \(S_\infty\) lifts from the elliptic origin. Outside
the closure of \(S\) there is no real ordered point: the coordinates
of a real ordering must all be real. The discriminant zeros
bounding split components are simple because a smooth cubic
pencil here has no triple root, and two distinct ramification
points cannot share a degree-three fibre. Thus distinct components
of \(S\) do not have intersecting closures. The connected image of
\(E(\mathbb R)^0\), which contains infinity, cannot reach another
split component. This proves (1).

The identity component of the real elliptic group is a circle.
The infinite-order point \([2]D\) lies in it because the component
group has order at most two, and its integer multiples are dense
there. Indeed an infinite cyclic subgroup of a circle has whole
circle as its closure. Therefore every open real window meeting
\(S_\infty\) can be populated by rational ordered triples. On another
real component the same is true if a rational offset \(R\) in it is
known: use \(R+[2]\mathbb ZD\). Without such a rational offset, positive
rank and a real window in that other component do not prove anything
about rational completions there.

The cofinite algebraic tests for collision with a retained site,
nonzero old cofactors and \(h_{\rm next}\ne0\) can all be imposed
inside an accessible real window. They remove only finitely many
points by the [fixed-functional ladder proof](../same-gap-seed-ladder/seed-ladder.md).
One can also impose a prescribed nontorsion fresh pair whenever its
explicit arithmetic test is known to be nonidentically zero by
specialization at an ordered infinity. No moment of the uniform
functional is changed.

**Endpoint-pair obstruction.** If the two removed sites are \(0,1\),
neither is a root of any finite cubic in the pencil. On a connected
split branch the number of finite roots in \((0,1)\) cannot change
except through a root reaching an endpoint, which is impossible
at a finite parameter. Near the simple infinity fibre one root
is unbounded. Hence a finite window with all three roots in
\((0,1)\), if it exists, is disjoint from \(S_\infty\).
In this situation all six infinity orderings are on the component
above \(S_\infty\): a separate admissible split component must be
covered by the other real component, and there are at most two.
Thus the previously known infinity points alone, including a
nontorsion \(D\), cannot seed that other window. This is an exact
obstruction to using their multiples, not a rational nonexistence
result in the second component.

## 3. A tractable sufficient class and a two-step criterion

Suppose \(0<u<v<1\) and both \(R_u,R_v<0\). Then
\(F'(X)=1-R_u/(X-u)^2-R_v/(X-v)^2>0\) on each pole-free interval.
It maps each of \((-\infty,u),(u,v),(v,\infty)\) strictly increasingly
onto the real line. Thus \(S=\mathbb P^1(\mathbb R)\). All three
finite roots are strictly inside \((0,1)\) exactly when
\[
 F(0)<\tau<F(1), \qquad
 F(1)-F(0)=1+\frac{R_u}{u(1-u)}+\frac{R_v}{v(1-v)}>0 .
\]
There is no inaccessible second split component. With a smooth
nontorsion pair this simple inequality certifies an interval
continuation after the finite exclusions.

Let \(L,M,R\) denote the three ordered new roots (left, middle,
right) for such a move. The cofactor identity from the earlier
ladder is \(C_x(P_{\rm next})=h/B(x)\) at each new root.
Since \(B(L),B(R)>0>B(M)\), exactly one adjacent fresh pair
has both residues negative: choose \((L,M)\) when
\(\delta=h_{\rm next}/h<0\), and \((M,R)\) when \(\delta>0\).
This is a sign guarantee, not an automatic positive-width guarantee.
For new adjacent pair \(x<y\), the actual residues are
\[
             R_x'=\delta B(x)/(y-x),\qquad
             R_y'=-\delta B(y)/(y-x).
\]

Here is a **two-step sufficient condition**. In addition to a
smooth nontorsion negative-pole pair and a positive interval window,
suppose the rational parameter
\(\tau_0=k/h-u-v\) lies strictly within that window. At \(\tau_0\)
the next defect would vanish, since
\(h_{\rm next}/h=\tau_0-\tau\).
Choose \(\tau\) close to, but not equal to, \(\tau_0\), staying on
one side. The new roots remain distinct and away from the endpoints.
The adjacent negative residues above tend to zero as \(\tau\)
tends to \(\tau_0\), so the next interval width tends to 1 and is
positive near \(\tau_0\). The selected adjacent pair's nontorsion
test is algebraically cofinite: for \((L,M)\) specialize at
\(\tau\to+\infty\), where these roots approach \((u,v)\);
for \((M,R)\) specialize at \(\tau\to-\infty\), where those
roots approach \((u,v)\). Those are ordered infinity charts of
the same integral elliptic curve, and the exact normalized
parameter and affine nontorsion specialization from the
fixed-functional proof applies to either chart. Consequently
rational density in the first window supplies a first exact
rule that has a smooth nontorsion negative-pole pair with
positive width for one more interval move.

This argument does not assert the next \(\tau_0\) lies in its own
window: an ensuing ratio \(k_{\rm next}/h_{\rm next}\) may become
large just where the first \(\delta\) was made small. It does not
give unconditional indefinite interval iteration.

## 4. Exact prescribed checks from the verified interval seed

Use the [12-site exact order-14 interval seed](../uniform-interval-same-gap-seed/interval-seed.md)
and its four prescribed centered rank-free replacements. Take
all coordinates here in \([0,1]\) after \(X=(1+Y)/2\).

On the endpoint pair \((0,1)\), the exact normalized parameters
are enclosed by
\[
 a\in[7726,7727]\,10^{-6},\qquad
 b\in[13726,13727]\,10^{-6}.
\]
At \(\tau=1/2\) the cubic signs at \(0,1/4,3/4,1\) are
\(-,+,-,+\). So there is a real interior window, but the
endpoint-pair obstruction excludes it from the infinity
component. Its known mod-31 nontorsion result does not change
that fact.

The different, fixed interior pair
\[
 u=1/3,\qquad v=(1+3927397/16686208)/2
\]
has certified negative residues
\(10^6R_u\in[-59874,-59873]\) and
\(10^6R_v\in[-45552,-45551]\). Its interval width
\(F(1)-F(0)\) is enclosed by \([537675,537676]\,10^{-6}\).
Also the zero-defect parameter is strictly between the two
window endpoints, by the bounds
\[
 10^6 F(0)\in[253367,253368],\quad
 10^6 \tau_0\in[451262,451263],\quad
 10^6 F(1)\in[791042,791043].
\]
The exact affine nontorsion test at \(q=2147483647\) passes
for this pair. Thus the abstract two-step condition applies.

For more than existence, use its one prescribed rank-free
triple, in formula order \((x_a,x_b,x_c)\). It already lies
inside, with \(10^6\)-scaled enclosures
\[
 ([852361,852362],\ [139230,139231],\ [502326,502327]).
\]
Its exact defect is nonzero mod \(q\), equal to \(621252393\).
The retained plus new sites are all distinct mod \(q\) and all
cofactors nonzero, giving **13 distinct contributing sites at
exact order 15**. Since \(\delta<0\), the next pair is the
adjacent \((x_b,x_c)\). Its negative-pole width is
\([784747,784748]\,10^{-6}\), and its nontorsion certificate
passes at the same prime. The prescribed rank-free triple
for that pair has \(10^6\)-scaled enclosures
\[
 ([581645,581646],\ [77201,77202],\ [449347,449348]).
\]
Its defect mod \(q\) is \(1366411467\ne0\), and every cofactor
and distinctness test passes. This gives **14 distinct
contributing interval sites at exact order 16**. Neither
move removes the original endpoints.

The [checker](verify-interval-pencil.py) uses fixed 288-bit
dyadic enclosures with outward rounding (no wide rational
expansion), plus one fixed prime residue calculation for
nonzero and arithmetic tests. All input and SLP denominators
are checked to be units when reduced. The exact two paid
moment shifts follow algebraically from the rank-free cubic
identity, not from zero residues. Interpolation then pays
every required scalar moment; the nonzero next defect proves
exact order. Only the two named additional moves were tested,
with no grid or later-order scan. This is mathematical exact
verification, not a Lean claim, positive-weight certificate,
interval result above order 16, or stage table change.

Run `python3 verify-interval-pencil.py` for the frozen
[exact enclosure and arithmetic trace](exact-check.txt).
