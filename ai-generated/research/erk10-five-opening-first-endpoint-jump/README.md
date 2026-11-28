# The first separated repeat of the reverse endpoint is impossible over Q

**Theorem.** Use the
[literal five-opening order-ten reverse word budget](../erk10-five-opening-nonsplit-kernel/README.md)
with ten physical high rows, all high forward clocks nonzero,
and only the opening origin as a possibly scored opening row.
Assume exactly two high forward clocks equal \(1\), and the
first three physical reverse ordinates are \(0,a,0\), \(a\ne0\).
Then there is no rational continuation of this form, for arbitrary
physical and grouped scores.

The structural proof for \(m\ge7\) distinct high labels is valid
over every field with \(10!\ne0\). Only the \(m=8\) leaking case
requires the final rational nonic. For \(m\le6\) the
[two-endpoint degree-nine scalar floor](../rational-endpoint-moment-nine/README.md)
already excludes rationality. This is an architectural condition,
not a new unrestricted stage bound.

## Raw observers, aggregates, and the no-jump branch

Use \(K=B^T\) in reverse coordinates and the
[actual weighted defects](../erk10-five-opening-contiguous-endpoint-repeat/README.md)
\(\boldsymbol v,\boldsymbol u,\boldsymbol g,\boldsymbol h,
\boldsymbol k\) of grades \(1,2,3,3,4\), where
\(\boldsymbol v=K\boldsymbol w-\boldsymbol w\odot\boldsymbol y\)
and \(\boldsymbol h=K\boldsymbol u\). Rank of \(D_4\) is at
most three, by the shifted Hilbert nominal span and two forward
residual witnesses. If an additional annihilator of the observed
space is supported within the first few reverse rows here, the two
forward residuals are still independent off its support: at least
two distinct physical labels are later in reverse. Such a contrast
is impossible in the rank-three case, and otherwise gives
\(\dim D_4\le2\). This condition is not about the scores of the
first two distinct forward rows.

The aggregate of \(\boldsymbol v\) at all \(m\le9\) labels is
zero, by the eight positive forward tests when \(m\le8\), or the
rank-three mark obstruction to a nonzero nine-label cofactor when
\(m=9\). In particular its two endpoint values are each zero,
because the first is literally zero. There are at least five live
scalar high labels by the shifted Hilbert determinant. At the
first live physical interior row, \(\boldsymbol u\ne0\), since all
earlier scalar scores at nonzero reverse ordinates vanish. This
argument allows the first interior row \(a\) itself to be score zero.

First assume \(\boldsymbol u\) has zero aggregate at *every*
high label. Its second endpoint entry is then zero, its first
being zero. If \(w_a\ne0\), the literal weighted \(u\)-payment
at the second endpoint forces its tap to \(a\) to vanish, since
that is its only possible nonzero-ordinate scalar donor.
If \(w_a=0\) and \(v_a=0\), then at the first interior row
\(a\) all positive-length observers vanish: the two grade-one
actions are zero there, all longer \(K\) actions can read only
zero positive grades at the first endpoint, and the clock
actions keep them zero.

The remaining possibility \(w_a=0,v_a\ne0\) must also force
the second endpoint's tap to \(a\) to vanish, as follows.
For \(m=9\) there is no interior repeat, so the hypothesized
zero aggregate would make all of \(\boldsymbol u=0\), impossible
regardless of this score. For \(m=8\) there is one interior pair;
both \(\boldsymbol v,\boldsymbol u\) are supported on its
one opposite direction, so \(v_a\ne0\) would force
\(u_a\ne0\), contrary to \(w_a=0\).
For \(m=7\), \(K\boldsymbol v\) is grade two and its seven
positive tests make it aggregate-exact on all seven labels.
It is zero at the first endpoint, hence also the second.
It can read only \(v_a\) there (the first endpoint \(v=0\)),
forcing the tap to \(a\) zero.

Consequently in all remaining no-jump cases every actual
positive-length word vanishes on both endpoint physical rows.
Grade one vanishes there by \(\boldsymbol v\) and the zero clock.
For longer words the first endpoint has no earlier donors, and
the second either does not read \(a\) or reads only zero
positive grades at \(a\).
The two endpoint coordinates give a nonzero contrast on the
constant score column (also if its total or both scores are zero),
and all higher nominal powers vanish there. This gives
\(\dim D_4\le2\), by the two actual forward witnesses outside
the first three physical reverse rows.

We may now use the same interior aggregate count as in the
[leading contiguous endpoint-block proof](../erk10-five-opening-contiguous-endpoint-repeat/README.md#exactly-two-leading-endpoint-copies-a-paid-dimension-loss):
\(m=8\) has just one interior opposite mode; grade-three leakage
would add two aggregate directions once the endpoint coordinates
are zero, so it is excluded and the one-label primitive contradiction
applies. For \(m=7\), grade three is aggregate-exact on the six
interior labels, and the same one-label contradiction rules out
rank one. Thus \(D_3=D_4\) is the two-dimensional interior
zero-sum space; the exact cubic single-donor argument for one
triple and the tracked-pair primitive argument for two pairs both
apply verbatim. These arguments use precisely the two endpoint
observer zeros and the paid dimension loss, not contiguity itself.
This completes the no-jump branch.

## Leaking grade two: a nonzero jump fixes \(\kappa=1/2\)

A nonzero aggregate of \(\boldsymbol u\) requires \(m=8\) or
\(m=9\). The grade-two positive tests are the seven
powers \(X,\ldots,X^7\): on the \(m\) distinct high labels their
annihilator is the interpolation cofactor times a polynomial of
degree at most \(m-8\). Thus a nonzero aggregate has support at
at least eight distinct labels. Its first two clock marks and
itself form a basis of \(D_4\). Every grade-three defect is an
affine multiplier of \(\boldsymbol u\), because its first mark
still belongs to \(D_4\) and a quadratic term would produce a
new cubic multiplier on at least four distinct supported labels.

The initial interior \(a\)-row must be live, otherwise \(w=u=0\)
there and the row would be early blind. Scale its reverse ordinate
to \(1\), with scaled coordinate \(Y=y/a\), operator \(K/a\) and
defects divided by their corresponding powers of \(a\). Keep their
names below. The scalar interval is \([0,H]\), \(H=1/a\), with
integration \(I(F)=H^{-1}\int_0^H F\); paid tests vanish at
\(Y=H\). The reverse prefix is now \(0,1,0\).
Write
\[
 K\boldsymbol u=\kappa(\boldsymbol Y-1)\odot\boldsymbol u,\quad
 K(\boldsymbol Y\odot\boldsymbol u)=Q(\boldsymbol Y)\odot\boldsymbol u,\quad
 \boldsymbol g=P(\boldsymbol Y)\odot\boldsymbol u,\quad
 \boldsymbol k=R(\boldsymbol Y)\odot\boldsymbol u
\]
with degrees \(1,2,1,2\) respectively. The first \(1\)-row
has \(u=-w/2,\ h=0\).
The second endpoint's \(u\)-value must be nonzero: otherwise
both endpoints would have only the score-column restriction,
producing an early contrast against rank three.
Let \(j\) be that nonzero value, the **endpoint jump**.
It comes solely from its weighted tap to the first \(1\)-row,
so \(h=-j/2\) there, whence \(\kappa=1/2\).
This is a literal exception to the other chart's causal argument
that cancelled \(Y\): the jump is nonzero at \(Y=0\).
The same first three rows give
\[
 P(Y)=1-Y/3,\quad Q(0)=-1/2,\ Q(1)=0,\quad
 R(0)=1,\ R(1)=1/2 .
\]
In fact the second endpoint's actual \(g,k\) both equal \(j\)
since their scalar donor \(Y=1\) is the same, and its marked
\(K(Yu)\) equals \(h\).

The next physical row cannot be another \(1\): its two
\(\boldsymbol u\)-reads \(K\boldsymbol u\) and \(K(Yu)\)
would be zero and kill both forms of earlier \(u\) at distinct
labels \(1,0\). Its \(w,u\) would then look proportional to
the first \(1\)-row. Thus write its label \(b\ne0,1\).
If \(u_b=0\), the same two reads kill both its taps and give
\(w_b=0\), early blindness. Hence \(u_b\ne0\).
A scalar tap from only \(Y=1\) pays all its primitive moments.
Put \(L_i=w_i/u_i\) at the known nonzero-\(u\) donors.
Since its first two scalar primitive reads come from that same
tap, they give
\[
 L_1=-2,\qquad L_b=\frac{2}{b(2b-3)},\quad b\ne3/2 .
\]
Concretely \(L_b(b^3/3-b^2/2)=b/3\).
The \(K(Yu)\) and cubic primitive reads at \(b\) now fix
\[
 Q(Y)=(Y-1)\!\left(\frac12-\frac{Y}{2b-3}\right),
 \qquad
 R(Y)=1-\frac Y2-\frac{(b-1)Y(Y-1)}{2(2b-3)} .
\]

## The next compatibility determinant and the only remaining head

At the next proposed interior row \(z\), the previous endpoint
jump can contribute to \(K\boldsymbol u\) but not to \(K(Yu)\)
or to any positive scalar primitive. Use the latter four
equations, with unknowns the taps on the \(u\)-coordinates at
the physical \(1,b\) (without dividing by \(u_z\)) and the
score \(w_z\), plus \(-u_z\). Their homogeneous matrix is
\[
 \begin{pmatrix}
 1&b&0&Q(z)\\
 L_1&bL_b&-z^2/2&1\\
 L_1&b^2L_b&-z^3/3&P(z)\\
 L_1&b^3L_b&-z^4/4&R(z)
 \end{pmatrix},
\]
with determinant
\(z^3(z-b)^2(b-1)(z-1)/(2b-3)^2\).
Any new distinct nonzero label would therefore have \(w=u=0\)
and be blind, a contradiction.

For \(z=1\), the first-three-column minor on rows 1,3,4
equals \(b(b-1)/(2b-3)\ne0\).
For \(z=b\), the minor on rows 1,2,3 equals
\(-4b^3(b-2)(b-1)/[3(2b-3)]\), nonzero unless \(b=2\).
With a full column rank the repeated score and \(u\) must be
proportional to the earlier row of that label: its old
solution, with subsequent taps zero, solves the four equations
for the same homogeneous right side. This does not assume
\(u_z\ne0\). Such proportionality gives an early contrast.
Therefore the \(m=9\) chart (no interior repeats) is already
excluded over every paid field. The \(m=8\) chart can only
remain in the physical head \(0,1,0,2,2\), with the one
interior pair at \(2\). No pooled score is assumed.

## Terminal transfer for \(0,1,0,2,2\)

Here \(P(Y)=1-Y/3,\ R(Y)=1-Y^2/2\).
Let the five remaining distinct singleton ordinates be
\(c,d,e,f,g\), chronologically. At the first of them \(c\),
scalar donors of positive degree still have only clocks \(1,2\).
Their cubic powers are \(Y^3=3Y^2-2Y\). Using the exact
actual moment reads gives
\[
 w_c\,c^2(c-2)^2/4-u_c\,c(c-2)/2=0 .
\]
Thus \(w_c/u_c=2/[c(c-2)]\), where \(u_c\ne0\) by the
eight-site cofactor and \(c\ne0,2\). The same ratio holds
at the first \(1\)-row.

Let \(M(Y)=Y^2(Y-2)^2\) and \(G(Y)=(Y-c)M'(Y)/4\).
The two literal high donor vectors
\[
 \boldsymbol Z=\boldsymbol w\odot M(\boldsymbol Y)
                  -2\boldsymbol Y\odot(\boldsymbol Y-2)\odot\boldsymbol u,
 \qquad
 \boldsymbol G=\boldsymbol w\odot G(\boldsymbol Y)
\]
vanish on the first six physical rows:
at both endpoints and both \(2\)-copies by their factors,
and at \(1,c\) by the ratios and the roots of \(G\).
Here \(M'/4=Y(Y-1)(Y-2)\).
The degree at most two in the \(\boldsymbol u\) coefficient
is within the grade-five budget after applying \(K\).
Thus \(K\boldsymbol Z-\boldsymbol w\odot JM\)
and \(K\boldsymbol G-\boldsymbol w\odot JG\) are actual
grade-five tests.

Take \(\nu=(Y-H)(Y-e)(Y-f)(Y-g)\). The first remaining
row \(d\) reads only zero contributors, while \(e,f,g\)
are killed. Also the degree-five primitives may be integrated
by scalar precision nine, since the opening origin at \(Y=H\)
is killed. This proves \(I(\nu JM)=I(\nu JG)=0\).
Hence \(4JG=(Y-c)M-JM\) gives \(I(\nu(Y-c)M)=0\).

For the raw nodal collapse, put
\(P_9=(Y-d)\nu G\) and
\(\mu_z=I(P_9(Y)/(Y-z))\).
Cardinal exactness gives \(W_z=\mu_z/P_9'(z)\).
The grade-two cofactor is now on all eight high labels,
**including zero \(Y\)**, so
\[
              U_z^{(2)}=-\ell/P_9'(z)
\]
for a common nonzero \(\ell\). This differs from the
high chart that excluded the endpoint from this cofactor:
here there is no extra factor \(z\) in its numerator.
The two actual ratios \(w_z/u_z\) at \(z=1,c\) imply
\(\mu_z z(z-2)=-2\ell\).
The scalar test \(\nu(Y-d)M\) has possible contributors
only at \(1,c\); the two constant numerators sum with
opposite interpolation coefficients. Hence
\(I(\nu(Y-d)M)=0\).
Subtracting the previous nodal moment gives \(I(\nu M)=0\),
and then \(I(\nu YM)=0\). The three-site cofactor for the
contributions at \(1,c,d\) to \(I(\nu M)\) now forces
\(\mu_d d(d-2)=-2\ell\) as well. Thus the **raw**
\(Z_d=0\); no division by its score is required.

Finally \(U=(Y-H)(Y-f)(Y-g)\) tests
\(K\boldsymbol Z-\boldsymbol w\odot JM\).
The last two rows are killed, and all prior nonzero test
rows have only zero donors through \(d\). Therefore
\(I(U JM)=0\); also \(I(Y U JM)=0\) via \(\nu=(Y-e)U\).
After rescaling \(Y/H\) these are exactly the
[existing rational nonic equations](../erk10-fifteen-two-pair-rational-closure/README.md#the-unconditional-collapse-and-rational-exclusion).
Their small parameter is \(1/H=a\) and their large node
is \(2/H\). The same quartic pivot and the projectively
rootless modulo-11 nonic exclude a rational solution.
The argument leaves other placements of the second
endpoint outside the stated theorem.

## Replay

    python3 -B audit.py
    # From the overlay or repository root:
    sha256sum -c ai-generated/research/erk10-five-opening-first-endpoint-jump/sources.sha256

The package replays the exact augmented and repeated-row determinants
and the two-site primitive and nodal collapses. Portable Lean scalar
evidence is separate from the physical observer and chronology proof.
