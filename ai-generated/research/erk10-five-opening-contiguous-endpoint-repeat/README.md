# A leading block of repeated endpoint rows cannot rescue rational ERK10

**Theorem.** Use the
[actual five-opening order-ten short-word budget](../erk10-five-opening-nonsplit-kernel/README.md),
exactly ten physical high rows, and only the opening origin as
a possibly scored opening row. Suppose all high forward clocks
are nonzero, and all the physical high copies of the forward
endpoint \(1\) form a single leading block in reverse order,
with at least two copies. Then there is no rational continuation
of this form. Physical and grouped scores can be arbitrary,
including zero or signed scores.

The physical argument excludes every case with at least seven
distinct high labels over **any field with \(10!\ne0\)**. The
rational obstruction for at most six labels is the
[two-endpoint scalar degree-nine floor](../rational-endpoint-moment-nine/README.md):
the allowed scalar sites include the opening origin \(0\), and
include \(1\) even if its total score is zero. In particular
it does not require either endpoint score to be live.
This is not an unrestricted bound on fifteen-stage ERK10.

## True rank ledger and live-score supply

Write \(K=B^T\) in reverse coordinates,
\(\boldsymbol y=\boldsymbol 1-\boldsymbol x\), and use score-weighted
raw profiles. Suppose \(r\ge2\) initial reverse rows have
\(y=0\), and let \(m\) be the number of distinct high labels.
The score vector is \(\boldsymbol w\). Use actual defects
\[
 \boldsymbol v=K\boldsymbol w-\boldsymbol w\odot\boldsymbol y,\qquad
 \boldsymbol u=K(\boldsymbol w\odot\boldsymbol y)
                         -\boldsymbol w\odot\boldsymbol y^{\odot2}/2,
 \qquad
 \boldsymbol g=K(\boldsymbol w\odot\boldsymbol y^{\odot2})
                         -\boldsymbol w\odot\boldsymbol y^{\odot3}/3,
 \qquad
 \boldsymbol h=K\boldsymbol u .
\]
Their grades are \(1,2,3,3\); multiplying by a clock or
applying \(K\) raises the grade by at most one. Grade \(j\)
annihilates forward powers \(X,\ldots,X^{9-j}\). Denote by
\(D_j\) the span of all defects up through that grade.

The five nominal weighted powers through degree four are
linearly independent modulo \(D_4\): their pairing against
\(X,\ldots,X^5\) is the invertible shifted Hilbert matrix,
after changing between reverse and forward polynomial bases.
The determinant is
\(1/(2^{12}3^7 5^5 7^4)\), so the entire claim is paid-field
valid. In particular the same scalar matrix factors through
the distinct high scalar labels with nonzero pooled weights,
so at least five such labels are live, irrespective of
individual signs or score zeros. This fact follows without
the physical proof and the original opening origin contributes
zero to these positive tests.

The two independent forward residuals for
\(f=X,\ldots,X^4\), namely \(BEf-EJf\), annihilate the
actual grade-four observers and the five weighted nominal
powers, as in the
[forward residual rank proof](../erk10-five-opening-three-pair-all-open/README.md#actual-profiles-and-the-three-dimensional-constraint).
The first forward high label \(a\ne0\) and first different
high label \(b\ne0\) give independent rows of these residuals:
otherwise \((b/a)^2,(b/a)^3,(b/a)^4\) would be affine in the
exponent, making \((b/a)^2(b/a-1)^2=0\). This argument uses
only physical clocks and strict predecessors, not the scores
at those rows. For \(m\ge7\) the rows occur in the forward
prefix of nonendpoint labels, because that suffix in reverse
contains at least two different clocks. Thus these two
residuals are independent even upon removing *all* the initial
reverse endpoint coordinates. In particular \(\dim D_4\le3\).

The grade-two defect \(\boldsymbol u\) is always nonzero:
at the first live physical interior row, all earlier
nonzero-ordinate scores were zero, so its value is
\(-w_i y_i^2/2\ne0\). The two endpoint weights do not affect
this calculation. At least one live interior physical score
exists by the shifted Hilbert support bound.

## Exactly two leading endpoint copies: a paid dimension loss

There are at most nine distinct high labels. The grade-one
aggregate of \(\boldsymbol v\) is zero. If \(m\le8\), this
is the Vandermonde on the \(m\) distinct nonzero-\(x\) labels,
using the first \(m\) of the eight positive forward tests.
If \(m=9\), any nonzero aggregate is the one-dimensional
cofactor, nonzero at all nine labels by deleting a column
in that Vandermonde. Its first three clock marks would give
four independent aggregate directions in \(D_4\), impossible.
This includes the endpoint group in both counts.

The first physical endpoint has \(v_1=0\) by strict causality.
With exactly two endpoint copies, zero aggregation implies
\(v_2=0\) as well. Thus \(K\boldsymbol w\) is zero on both.
Since both are initial rows with \(y=0\), induction on words
in \(K\) and the clock diagonal now proves that *every
positive-length actual word* is zero on these two coordinates.
A clock mark kills them, and each \(K\) action there uses only
already zero earlier endpoint coordinates. Their nominal
positive powers vanish too, so all grade-at-most-four defect
coordinates on them are zero.

There is a nonzero contrast supported on the first two
physical coordinates annihilating their \(\boldsymbol w\)
values, even if one or both scores, or their sum, vanish.
It kills every nominal power and \(D_4\). It is independent
of the two forward residual annihilators just verified on
the complement of the endpoint block. Thus the observed
space has dimension at most seven, and
\[
                              \dim D_4\le2 .
\]
This is a real dimension loss from the two physical copies,
not an informal stage deletion or a division by their total
score.

We can now count the interior excess \(10-r-(m-1)=9-m\)
for \(r=2\).

* **\(m=9\)**: eight interior scalar labels are all singletons.
  The grade-two \(\boldsymbol u\) vanishes on the endpoint
  block and has the one-dimensional cofactor on the eight
  interior sites by seven positive tests. Since it is nonzero,
  it and its first two marks have three independent aggregate
  directions in \(D_4\), contrary to the paid dimension loss.
* **\(m=8\)**: among seven interior labels only one is a pair.
  \(\boldsymbol u\) has zero aggregates by seven positive
  tests, hence is the nonzero pure opposite-pair direction.
  If a grade-three aggregate leaked, that vector and its
  first mark would add two independent aggregate directions
  (the six-test cofactor is supported on all seven labels),
  once again contradicting \(\dim D_4\le2\).
  Thus \(D_3\) is supported on the single pair and has
  dimension one. The one-label argument below excludes it.
* **\(m=7\)**: there are six distinct interior labels and
  either one triple or two pairs. Every grade-at-most-three
  defect has zero on the endpoint block and zero aggregate
  on the interior labels (six positive tests). Let \(S\) be
  the two-dimensional zero-sum interior space of the triple
  or two pairs. If \(D_3\) had dimension one, clock marking
  of the nonzero \(\boldsymbol u\) would confine it to one
  label, and the one-label argument below would apply.
  So \(D_3=S\). The rank loss then implies \(D_4=S\) as
  well; all grouped primitive payments through the cubic
  input are exact.

Here is the **one-label argument** just used. If
\(D_3=\langle\boldsymbol u\rangle\) and
\(\boldsymbol u\) is supported at \(a\), pick the first
live physical row of any other interior label. There is
one by scalar support. Before it, the only nonzero-ordinate
scalar inputs are from \(a\) (singleton or paired ghost
scores at other labels are zero). On the old \(a\)-copies
\(g=a u+a^3w/6\) by the actual scalar primitive definitions.
As \(\boldsymbol g\) is proportional to \(\boldsymbol u\),
their old scores are proportional to their \(\boldsymbol u\)
coordinates. The first live distinct row is \(D_3\)-clean:
its first primitive needs a nonzero weighted scalar tap
into \(a\), but its composed \(\boldsymbol h\) requires
the same proportional \(\boldsymbol u\) tap to be zero.
This is impossible. No group mean at a zero-sum label is
used.

It remains \(m=7,D_4=S\). With just one repeated triple,
take the first live singleton \(z\). The only possible
earlier nonzero-ordinate scalar donor is at the triple
\(a\); its exact first three scalar primitive reads would
require \(z=3a/2\) and \(z^2=2a^2\), impossible. With two
pairs, call a live singleton or the closure of a live-mass
pair an *ordinary* target. At least one exists by scalar
support. Before the first such target, zero-score singletons
supply zero scalar and \(D_3\) input. A zero-total pair, if
already closed, has opposite scalar scores and opposite
\(D_3\) values, so both columns fold by subtraction on those
inputs. Each still-open pair supplies only its first copy.
On every scalar donor pair there is thus a pure \(D_3=S\)
mode tracking its available scalar scores (or its scalar
tap is zero identically). The \(K\)-image of each such mode
has grade four, hence zero mean at the first ordinary
target, forcing every scalar nonzero-ordinate tap to be
zero. This contradicts the first primitive with nonzero
target ordinate and group weight.

## Three or more leading endpoint copies

For \(r\ge3\) and \(m\ge7\) the count is even smaller:
the interior excess is \(10-r-(m-1)=11-r-m\le1\).
The three relevant profiles \(\boldsymbol u,\boldsymbol
g,\boldsymbol h\) are zero on the entire initial endpoint
block **regardless of the grade-one defect there**:
both scalar input vectors \(\boldsymbol w\odot\boldsymbol y\),
\(\boldsymbol w\odot\boldsymbol y^{\odot2}\) vanish on this
block and strict causality gives zero there after \(K\).
Then \(K\boldsymbol u\) also vanishes there.

The possible counts with at least seven labels are
\((r,m)=(3,8),(3,7),(4,7)\).
If all interior labels are singletons, their number is at
most seven and the actual grade-two positive tests force
\(\boldsymbol u=0\), contradiction. The only other case
is \((3,7)\) with one interior pair, six interior labels.
Then grade two and grade three impose zero group sums on
the actual \(\boldsymbol u,\boldsymbol g,\boldsymbol h\)
using the interior Vandermonde, precisely because those
three vectors vanish throughout the initial endpoint block.
They are supported only at the opposite pair, and
\(\boldsymbol g,\boldsymbol h\) are proportional to
nonzero \(\boldsymbol u\). The one-label argument above
uses only these three vectors (not \(\boldsymbol v\))
and gives the contradiction. This completes the contiguous
endpoint-block theorem.

## Replay and scope

    python3 -B audit.py
    # From the overlay or repository root:
    sha256sum -c ai-generated/research/erk10-five-opening-contiguous-endpoint-repeat/sources.sha256

The exact replay checks the counted cases, the shifted Hilbert
pivot and the first-two-residual and single-donor arithmetic.
A portable scalar Lean receipt is separate from the actual
tableau and rank argument. Noncontiguous endpoint repeats,
zero high clocks and absence of an endpoint are not treated
here.
