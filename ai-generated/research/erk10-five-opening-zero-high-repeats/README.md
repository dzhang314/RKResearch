# High zeros and eight visible labels: the remaining multiplicities

Use the [literal five-opening continuation](../erk10-five-opening-nonsplit-kernel/README.md),
ten physical high rows, the actual order-ten short word budget,
only the opening origin optionally scored, and endpoint \(x=1\)
first in reverse. Write \(r\) for the number of high zeros and
\(m\) for the number of distinct **nonzero** high forward labels.
There is no sign, physical-score, or pooled-score condition.

* \(r=1,m=8\) with an endpoint repeat is impossible over every
  field with \(10!\ne0\).
* \(r=1,m=8\) with the unique endpoint and one ordinary pair
  is impossible over \(\mathbb Q\). All branches but one are
  excluded over every paid field; the last uses the previous
  rational nonic.
* \(r=2,m=8\), or \(r=3,m=7\), is impossible over every paid
  field. In these two cases all visible labels are singletons.

Together with the [nine-visible theorem](../erk10-five-opening-zero-high-largest/README.md),
this covers all \(m\ge8\), and also \(r=3,m=7\).
For \(m\le6\) the [two-endpoint scalar floor](../rational-endpoint-moment-nine/README.md)
already rules out \(\mathbb Q\): the scalar allowed sites are the
distinct visible labels together with the origin, and include
both endpoints even if their weights vanish.
The \(m=7,r=1,2\) variants with visible repeats are not part of
this packet. Nothing here changes the unrestricted ERK10 bound.

Keep the notation and variable-score rank ledger of the
[nine-visible theorem](../erk10-five-opening-zero-high-largest/README.md).
In particular \(K=B^T\) in strict reverse order,
\(\boldsymbol y=\boldsymbol 1-\boldsymbol x\),
\(\boldsymbol w\) holds the actual scores, and \(D_4\) has dimension
at most three. The pure kernel \(S\) is taken only over nonzero
forward labels, on vectors zero at the first reverse endpoint.
A row at high \(x=0\) has reverse \(y=1\), not zero. At most one
of the at least five live visible pools is the endpoint; thus
there are always enough actual live normal singleton rows
for the applications below. The early contrast witness uses
two distinct **visible** labels in the reverse suffix.

## One high zero and an endpoint repeat

All seven visible interiors are singletons. The pure kernel
\(S\) is the line on the invisible coordinate, since a pure
vector's first endpoint slot is zero and the two endpoint
slots sum to zero. If \(\boldsymbol u\) leaks visibly, it has
a nonzero cofactor on all eight visible labels, including the
endpoint pool. Its first two marks give \(D_4\), and degree
forces the \(D_3\) multipliers to be affine. Use the
[sole repeated endpoint argument](../erk10-five-opening-nine-label-endpoint-repeat/README.md).
Its first possible consecutive endpoint block \(0,0\) is
already an early contrast, since both \(\boldsymbol u\)
entries there are zero by strictness with no positive-degree
donor. In the prefix \(0,a,0\) the nonzero jump forces the
half-strength relation and the
[exact subsequent determinant](../erk10-five-opening-first-endpoint-jump/README.md#the-next-compatibility-determinant-and-the-only-remaining-head)
requires an interior repeat, which is unavailable. For all
later jump positions the old distinct head and causal
\(\kappa=0,1/2\) exits apply. Their \(X\)-based moments
vanish on the high zero, the ghost has nonzero reverse
ordinate, and none of their raw local read equations require
nonzero forward coordinate. No rational nonic is needed.

Otherwise \(\boldsymbol u\) is pure and nonzero. The same
dimension argument as for nine visible labels gives: \(D_2\)
is pure (a leaking vector and its marks consume three
independent aggregates); \(D_3\) visible aggregate dimension
is at most one (a full affine-cofactor space and its marks
would consume three too); and \(\boldsymbol h=K\boldsymbol u\)
must leak. Indeed, if pure it is zero by its vanishing at the
sole ghost, and the first live normal row cannot pay its
first primitive using the sole earlier live nonendpoint
ghost without giving nonzero \(h\). Therefore
\(D_4=\langle\boldsymbol u,\boldsymbol h,
\boldsymbol y\odot\boldsymbol h\rangle\), with the same
pure-ghost \(\boldsymbol g,\boldsymbol k,K\boldsymbol h\)
identities.

The first row after endpoint must be the live ghost \(a=1\):
a normal row there is blind, while an added endpoint there
has \(u=h=0\) and is a blind contrast against the first
endpoint. After the ghost, an added endpoint before any
normal row has zero \(h\) since \(K(\boldsymbol w\odot
\boldsymbol y)=0\) there kills the sole ghost tap. If the
first normal row \(b\) comes first, its same one-donor
payment fixes \(\beta=(4b-6a)/(3a)\). At a second endpoint
after \(b\), the two normal scalar primitive equations
for taps \(A,B\) on \(a,b\) are
\(aA+bB=0,\ 2abA+3b^2B=0\), using
\(h=-a^2 A/2\) and the \(\beta\) identity. Thus \(h=0\).
If the two distinct normal rows \(b,c\) both precede
the added endpoint, the
[cleared pure-ghost determinant](../erk10-five-opening-zero-high-largest/README.md#nine-distinct-visible-high-labels-pure-ghost)
at \(z=0\) forces \(h_z=0\) again. Each of these is an
early contrast between the endpoint rows; at least two
visible labels remain after the first five physical rows.
Finally, if a third normal row follows \(b,c\) before the
added endpoint, its distinct nonzero label has \(w=h=0\)
by that same determinant, so is blind. This exhausts all
positions of the added endpoint in the pure case.

## One high zero, unique endpoint, and one visible interior pair

Set \(a=1\) for the invisible ordinate and \(b_*\) for the
ordinary paired ordinate. Now \(S\) has two modes: the
single ghost coordinate and the ordinary opposite pair.
All grade-two profiles belong to \(S\), and the grade-three
aggregate kernel on the seven visible interiors is one
cofactor line.

### If grade three is entirely pure

Then \(D_3=S\). To rule out rank one, the nonzero
\(\boldsymbol u\) and its first mark would otherwise
force its support to one of the two labels \(p=a,b_*\).
All \(\boldsymbol g,\boldsymbol h\) would then be
proportional to \(\boldsymbol u\). Before the first live
different nonendpoint label, all live scalar donors with
nonzero \(y\) are at \(p\), and the identity
\(g=p u+p^3w/6\) makes their scores proportional to
\(\boldsymbol u\). The zero \(K\boldsymbol u\) value at
that live different row kills its necessary scalar tap,
contradiction. This proves \(D_3=S\), whether the first
live different physical row is visible or is the ghost.

For the next step an ordinary target is a live visible
interior singleton or the closing copy of a nonzero-mass
visible pair. Sum each target's evaluations and divide
by its nonzero pooled score. The ghost is never an ordinary
target, but its score can be nonzero. At least two distinct
ordinary targets \(z,x\) exist from the visible support.
Before \(z\), the scalar taps at the ghost are tracked by
a fixed multiple of the ghost mode of \(D_3\).
At the pair they are tracked by a fixed multiple of the
opposite mode of \(D_3\): only the first copy is available
unless it has closed with zero total, in which case the
two weights are opposite as well. This includes a zero
first score (the tracking coefficient is just zero).
No earlier zero-score singleton can be a scalar or
\(D_3\) donor. The endpoint contributes zero to all
positive-degree scalar inputs.

The functional at \(z\) on \(D_4/S\) is nonzero, since its
paid \(Y\) primitive requires a nonzero scalar tap tracked
by \(K\) of one of these two \(D_3\) modes. Thus the quotient
\(D_4/S\) is one-dimensional. The two tracked taps and the
\(\boldsymbol k\) difference at \(x\) are a common multiple
\(\ell\) of their values at \(z\), apart from one additional
scalar tap \(T\) at the label \(z\). This extra tap is from
the live singleton itself, or the amount not tracked by the
opposed mode at the closing pair \(z\). Any other pair
closure before \(x\) has zero total and stays tracked;
the ghost's actual score is always tracked, even if its
physical row has only just appeared. The first two exact
primitive equations and the calibrated cubic error at
\(x\) now give
\[
 z^2\ell+2zT=x^2,\quad
 z^3\ell+3z^2T=x^3,\quad
 z^4\ell+4z^3T=x^4 .
\]
They force \(x^2(x-z)^2=0\), impossible. This branch
uses neither inverses of physical ghost scores nor an
assumed zero-total invisible pool.

### If grade three leaks

A nonzero grade-three cofactor and its first mark give two
independent visible aggregates. Since \(\boldsymbol u\)
is nonzero and pure, \(D_4\cap S=\langle\boldsymbol u\rangle\);
its mark then confines it to exactly one of the two labels.
In either case \(\boldsymbol h\) must leak. If pure, it is
proportional to \(\boldsymbol u\), hence zero by its first
live nonendpoint entry. Before the first live different
nonendpoint label, all positive-degree scalar donors are
the earlier copies of the sole active label \(a'\).
The strict submatrix \(N\) on those copies obeys
\(\boldsymbol h_*=a'(N-a'I/2)N\boldsymbol w_*=0\),
forcing \(N\boldsymbol w_*=0\). Therefore
\(\boldsymbol u_*=-{a'}^2\boldsymbol w_*/2\), which
makes the target's two paid \(Y\) and \(K\boldsymbol u\)
reads inconsistent. This argument includes a single
ghost copy (then \(N=0\)).

Hence \(D_4=\langle\boldsymbol u,\boldsymbol h,
\boldsymbol y\odot\boldsymbol h\rangle\), and the first
nonendpoint is the live active opener by early blindness.
If the active label is the visible pair, the
[raw single active pair head](../erk10-five-opening-nine-label-one-pair/README.md#if-the-grade-two-aggregate-is-zero)
applies: every other physical nonendpoint label is a
singleton, including the high zero. The three closure
positions or the next distinct row all force a contrast or
a repeat of an unaffiliated singleton. That proof uses
\(u=0\) on all these singleton rows and the actual reads
there, not the value of their aggregate coefficient.

If the active label is the ghost \(a=1\), the next row
\(p\) must be a different live label as in the pure ghost
head. A repeated \(p\) immediately next would have
\(h_z=w_z a z^2(2z-3p)/(4p)\) at \(z=p\), giving
the same two \((w,h)\) ratios and an early contrast.
So a different \(q\) follows \(p\), and the two-read
determinant then confines the next row to \(p\) or \(q\).
At \(p\) the coefficient factors \(2q-p,p+q\) cannot
both vanish; they would again make the old and new
scores proportional in \((w,h)\). At \(q\) the
corresponding common factor is \(2p-q\). Thus only
the physical head \(0,a,p,q,q\), \(q=2p\), can remain.
This uses the [cleared repeat factors](../erk10-five-opening-zero-high-largest/README.md#reproduce)
without dividing by the new repeated row's score.

For this last head let \(c,d,e,f,g\) be the five remaining
physical ordinates, all distinct, nonzero, and different
from \(a,p,q\). At \(c\), the cubic read still uses only
the three scalar labels \(a,p,q\), with the \(\boldsymbol u\)
input solely at \(a\). The preceding first read for its
\(h_c\) has coefficient
\(-p(c-q)/a\) and scalar right hand side
\(-w_c c^2(c-q)^2/4\). It gives
\(H_c=w_c c^2(c-q)/4\) with
\(\boldsymbol H=(p/a)\boldsymbol h\); also
\(H_p=-w_p p^3/4\). No division by \(w_c\) is needed.

Let \(M(Y)=Y^2(Y-q)^2\) and \(G(Y)=Y(Y-p)(Y-q)(Y-c)\).
The two actual physical donor vectors
\[
 \boldsymbol G_*=\boldsymbol w\odot G(\boldsymbol y)
                            +2G(a)\boldsymbol u/a^2,\quad
 \boldsymbol Z_*=(\boldsymbol y-q)\odot\boldsymbol H-
        \boldsymbol w\odot M(\boldsymbol y)/4-(a-q)^2\boldsymbol u/2
\]
vanish on the first six rows. At the ghost this follows
from \(u=-w a^2/2\) and \(H=0\); at \(p,c\) from the
anchors and at \(q\) from the factors (on both copies).
The grade-five tests
\(K\boldsymbol G_*-\boldsymbol w\odot JG\) and
\(K\boldsymbol Z_*+\boldsymbol w\odot JM/4\)
annihilate the first four positive forward powers by the
real word budget; the added \(K\boldsymbol u\) terms are
lower paid defects. This is the
[raw terminal adapter](../erk10-five-opening-eight-label-pairs-zero/README.md#raw-terminal-adapter-for-both-heads),
now with only one active ghost and no future active closure.

Put \(\nu=(Y-1)(Y-e)(Y-f)(Y-g)\).
Blind tests give \(I(\nu JG)=I(\nu JM)=0\), since
\(d\) reads only zero donor entries and the other three
tail rows are killed. Include the origin factor \(Y-1\)
once: the high ghost and the opening origin share this
single scalar site, and the tests kill both. Let
\(P_9=(Y-d)\nu G\), \(\mu_z=I(P_9/(Y-z))\).
Then \(W_z=\mu_z/P_9'(z)\) by scalar precision nine,
with the combined origin score at \(Y=1\).
The seven visible-interior cofactor for \(\boldsymbol H\)
is \(-L z/P_9'(z)\) for a constant \(L\ne0\): the forward
\(X=1-Y\) factor removes the invisible root, and the
first endpoint \(Y=0\) is omitted from the cofactor.
The \(p,c\) anchors now give
\(c(c-q)\mu_c=-p^2\mu_p\).
Thus nodal evaluation gives \(I(\nu(Y-d)M)=0\), and
\(4JG=(Y-c)M-JM\) gives \(I(\nu(Y-c)M)=0\).
Subtract and get \(I(\nu M)=I(\nu YM)=0\).
The same three-site \(p,c,d\) interpolation cofactor
then gives \(d(d-q)\mu_d=c(c-q)\mu_c\), hence
\(Z_*(d)=0\) (the ghost correction is zero at \(d\)).
Now \(U=(Y-1)(Y-f)(Y-g)\) is a further blind test at
grade five: it gives \(I(U JM)=0\), hence \(I(YU JM)=0\)
from \(\nu=(Y-e)U\). These are exactly the
[verified rational quartic pivot and nonic exit](../erk10-fifteen-two-pair-rational-closure/README.md#the-unconditional-collapse-and-rational-exclusion),
with small parameter \(p\) and \(q=2p\).
All visible sites are distinct and different from \(Y=1\);
the high zero introduced no additional divided factor.
The projectively rootless rational nonic excludes this
last branch over \(\mathbb Q\).

## Two or three high zeros and no visible repeats

For \(r=2,m=8\) the visible endpoint is unique and all
grade-two aggregates are zero. Here \(S\) is just the
two high-zero coordinates, at one reverse label \(a=1\);
the grade-three aggregate kernel is at most a cofactor line.
If grade three is pure, the
[single donor nilpotent and feedback exit](../erk10-five-opening-fourfold-interior/README.md#the-first-live-singleton-forces-a-two-dimensional-nilpotent-block)
applies. It needs only \(D_3\) supported on one nonzero
reverse label, strict causality, and two subsequent live
different singleton labels. It does not use an aggregate
condition on the repeated label's own coordinates. The
first and second live normal singleton rows exist by
visible Hilbert support, and any intervening unscored
normal rows have zero scalar and \(D_3\) donor input.

If grade three leaks, \(D_4\cap S=\langle\boldsymbol u\rangle\)
by the two aggregate directions. The same strict-lower
single-label argument forces \(\boldsymbol h\) to leak,
then the active two-copy head calculations exclude every
possible early pattern. Indeed the ghost's two copies at
\(a=1\) are the sole active repeated label and all other
nonendpoint labels are physical singletons. The old
[raw head comparisons](../erk10-five-opening-eight-label-pairs-zero/README.md#grade-three-leakage-no-inverse-scores)
at \(0,a,a,b\), \(0,a,b,a\), or \(0,a,b,c\) require no sum
condition at the active \(a\) copies: they compare exact
\(K\boldsymbol u,K\boldsymbol h\) and primitive tap
columns at each individual row. They force a same-label
contrast or a repeat of the singleton \(b\) or \(c\).
Thus this branch cannot occur over a paid field.

For \(r=3,m=7\), the unique visible endpoint removes
one site from the grade-three kernel and there are only
six remaining visible sites. Accordingly \(D_3\subseteq S\)
is already pure and supported on a single reverse label
\(a=1\), now with three physical copies. The same nilpotent
and feedback argument applies, again without any score
condition at the ghost label.

## Replay and scope

Run `python audit.py` with SymPy and compare to `exact-audit.txt`.
The rational nonic, active-pair chronology determinants,
and single-label nilpotent receipts remain independently
replayable through the cited packets. These exclusions
are mathematical reductions of the actual word budget;
the scalar arithmetic is portable Lean where indicated,
not a native end-to-end tableau floor.
