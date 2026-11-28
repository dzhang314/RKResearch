# Eight high labels, two pairs: no rational tableau even with zero scores

**Theorem.** Use the
[actual five-opening short word budget](../erk10-five-opening-nonsplit-kernel/README.md)
at order ten, with ten physical high rows, eight distinct nonzero
forward labels, and unique forward clock \(1\) at the first
reverse row. The seven nonzero reverse labels consist of two
pairs and five singletons. Then no such continuation exists over
\(\mathbb Q\), for **all** physical and pooled output scores and
arbitrary chronology. In particular both pair totals may be
zero, and individual output-zero stages are not removed.

The algebraic proof before the last nonic is over any field with
\(10!\ne0\). The rational obstruction does not exclude those fields
uniformly; the known 17-adic witness is in the protected scope.
This is an architecture restriction, not a general 15-stage
ERK10 lower bound. No rational upper bound changes.

## Raw grade facts

Use the raw reverse \(K=B^T\), with \(\boldsymbol y=\boldsymbol1-
\boldsymbol x\) and weighted profiles rather than dividing by
physical scores. The definitions, grade tests, shifted Hilbert
matrix, and early contrast principle are as in the
[eight-label one-triple chart](../erk10-five-opening-eight-label-triple/README.md).
They depend on the number of interior labels, not the
multiplicity shape. In particular the opposite pair space \(S\)
has dimension two; \(\boldsymbol u\in S\) by the seven positive
grade-two moments; grade-three aggregates are contained in one
cofactor line nonzero at all seven interior labels; and
\(\dim D_4\le3\). There are at least four live interior pooled
scores because at least five distinct high pools are live, and
only one is at the endpoint. The raw primitive defects
\(\boldsymbol u,\boldsymbol g,\boldsymbol h,\boldsymbol k\)
have grades \(2,3,3,4\), with \(\boldsymbol h=K\boldsymbol u\).

## All grade-three aggregates exact

Suppose \(D_3\subseteq S\). Then \(D_3=S\).
Indeed \(\boldsymbol u\ne0\) at the first live interior
physical row, before any earlier written nonzero-ordinate
score, and so that row is at a pair label \(p\).
If \(D_3\) had rank at most one, the first clock mark of
\(\boldsymbol u\) would confine its support to label \(p\),
and \(\boldsymbol g,\boldsymbol h\) would be proportional
to \(\boldsymbol u\). At the first live physical row of
any other interior label, these three defects would all
vanish. Before it the only live scalar label is \(p\), and
on all earlier \(p\)-copies \(g=p u+p^3w/6\).
Proportionality would make those earlier scalar scores a
multiple of \(\boldsymbol u\), contradicting the difference
between the required nonzero scalar \(p\)-tap and the
vanishing of the composed \(K\boldsymbol u\) read.

Use separate opposite modes \(V_a,V_b\) on the two pairs.
Call a target *ordinary* when it is a live singleton or the
closing copy of a live-mass pair. At least two exist by scalar
support. A zero-score singleton has no scalar or \(D_3\)
input. Both copies of any already closed zero-total pair
fold by the same \(K_{i,j_1}-K_{i,j_2}\) on scalar and \(D_3\)
inputs, since all these coordinates are opposite there.
This is a local equality on low input columns, not a stage
deletion.

Both pairs have opened before the first ordinary target \(z\).
Otherwise only one label \(a\) can supply a nonzero scalar
tap. Its first physical score is live because before this
target that pair is open or has zero total. The first live
interior score at that label gives \(u_{a_1}=-w_{a_1}a^2/2\),
and hence the available \(a\)-profile of \(\boldsymbol u\)
is a nonzero multiple of its scalar scores: either just the
first copy is available, or the zero-total pair has already
folded. Then the zero ordinary mean of \(K\boldsymbol u\)
kills that sole scalar tap, contradiction.

At \(z\), normalize each of \(V_a,V_b\) to its first score
if that score is nonzero. Its \(K\)-mean equals the
weighted scalar tap through that label up to closing, and
through both copies if the pair closed with zero total.
A zero first score gives no available scalar tap at that
label, though its mode may not be zero. At least one scalar
tap is nonzero by the first paid primitive at \(z\).
Thus its \(K\)-mode of grade four leaks; \(D_4/S\) is
one-dimensional and the mean at \(z\) is a nonzero
functional on it.

At the next ordinary target \(x\), the same mode controls
every available scalar tap **except for possible new input
at \(z\)**, either a live singleton or the second physical
copy of a live-mass pair. Any other previously unclosed
zero-total pair that closes before \(x\) tracks both copies;
a score-zero singleton still contributes nothing. Thus the
old taps and the mean of \(\boldsymbol k\) scale by a common
quotient coefficient \(\ell\), plus one unchecked scalar tap
\(T\) at \(z\). The first two actual primitive payments and
the scaled cubic defect give
\[
 z^2\ell+2zT=x^2,\quad z^3\ell+3z^2T=x^3,\quad
 z^4\ell+4z^3T=x^4 .
\]
They imply \(x^2(x-z)^2=0\), impossible. This proof includes
both-active and one-active \(\boldsymbol u\) branches at once,
without assuming a positive or even nonzero physical score.

## Grade-three leakage: no inverse scores

Now a nonzero grade-three aggregate and its clock mark
give two independent aggregates in \(D_4\).
Since \(\boldsymbol u\ne0\), it is supported at one pair
only, which is the *active* pair \(a\): otherwise its mark
would add a second opposite direction, giving four
dimensions. The other pair is *dormant* only for
\(\boldsymbol u\), not necessarily \(\boldsymbol h\).
Exactly as in the one-triple leakage proof,
\(\boldsymbol h\) must itself leak. Otherwise it is a
multiple of \(\boldsymbol u\), zero by the earliest live
interior value. Before the first live scalar label distinct
from \(a\), all scalar inputs on prior \(a\)-copies are
from their own strict nilpotent submatrix \(N\). The equations
\(N\boldsymbol u=0\), \(\boldsymbol u=aN\boldsymbol w-
a^2\boldsymbol w/2\) force \(\boldsymbol u=-a^2\boldsymbol
w/2\) there. This contradicts the first live different
row's \(u=0\) payment and \(K\boldsymbol u=0\).
Thus \(D_4=\langle\boldsymbol u,\boldsymbol h,\boldsymbol
y\odot\boldsymbol h\rangle\).

The first interior physical row must be a live copy of
the active pair: any other label has \(u=0\) and only the
endpoint available, implying \(w=h=0\), an early blind
coordinate. The same blind contradiction applies if
the first active copy has zero score. Consequently the
actual identities are
\[
 \boldsymbol g=(2a/3)\boldsymbol u+\beta\boldsymbol h,\quad
 \boldsymbol k=(a^2/2)\boldsymbol u+\phi(\boldsymbol y)\odot\boldsymbol h,
 \quad K\boldsymbol h=\psi(\boldsymbol y)\odot\boldsymbol h
\]
with \(\phi,\psi\) linear, as proved in the one-triple chart.
At any early physical nonactive row, \(u=0\); if \(w=h=0\)
it is similarly blind, even if a different copy of its
label has nonzero aggregate. If two early copies at the
same dormant label have \((w,h)\) proportional, their
rank-one restriction gives a nonzero early contrast.
All such uses below occur by the fifth reverse row, with
at least two distinct labels later in reverse; hence the
two forward residual rows are independent away from the
contrast support. We need no normalization at a dormant
score-zero row.

### The active pair closes immediately

If the second nonzero-ordinate physical row is the active
closure at \(a\), its raw scalar tap \(A\) into the first
copy satisfies \(aA=a^2 W_a/2\) by the summed \(u=0\)
payment. If \(A=0\), both active rows look proportional
on \((w,u,h)\), impossible by early contrast. Hence
\(W_a\ne0\), \(\beta=-2/3,\phi(a)=-a,\psi(a)=0\),
and on the active pair \(h=-a u/2-a^3w/4\).
Let \(b\) be the next distinct label (not yet assumed
dormant). Its first two primitive reads give
\(h_b=w_b b^2(2b-3a)/4\). If \(w_b=0\) it is a blind
coordinate. If \(2b-3a=0\) with \(w_b\ne0\), then
\(h_b=0\) but its prescribed cubic error using only
scalar label \(a\) is nonzero, contradiction. Thus \(b\)
is live and \(2b-3a\ne0\).

The exact two-read determinant from the
[one-triple replay](../erk10-five-opening-eight-label-triple/README.md#leading-two-a-copies-are-impossible)
applies to every possible next row, since it is nonactive.
A new distinct label would force \(w=h=0\); the next
row must be \(b\), so \(b\) is indeed the dormant pair.
At \(b\), the two left coefficients multiplying \(h\)
in the two-read system are
\(b(2a-b)/[3(3a-2b)]\) and twice this.
If \(b\ne2a\), the two actual \(b\)-rows satisfy the
same nonzero-coefficient relation between \(h\) and \(w\),
because the old \(b_1\) had a smaller predecessor set.
They would be proportional. Thus the first head is
\(0,a,a,b,b\), \(b=2a\). No condition was imposed on
the physical scores at the closing \(a\) or \(b\), or
on the pooled dormant score.

### A different label precedes active closure

Let \(b\) be the first physical row after a single
active \(a_1\). Its first primitive gives scalar tap
\(w_b b^2/(2a)\) and \(h_b=-a w_b b^2/4\).
If \(w_b=0\) it is blind; hence \(b\) is live.
Then \(\beta=(4b-6a)/(3a),\phi(b)=b^2/a-2a,\psi(b)=0\).

If the following physical row closes the active pair,
the raw \(a_2\) calculation from the one-triple proof
applies without taking its group mean: the two scalar
taps \(A,T\) from \(a_1,b\) must have
\(A\ne0,\ 3b-2a\ne0,\ T/A=2a(a-b)/[b(3b-2a)]\);
otherwise it is an early active contrast.
It gives the same \(\phi,\psi\) and \(h\)-input on
\(0,a_1,b,a_2\) as in that computation.
The next nonactive row is forced to \(b\) by the same
two-read determinant. At \(b\) the two left coefficients
are \(b(2a-b)/(3a),(a+b)/3\), not both zero. Hence
the two \(b\)-rows are proportional, impossible.
This excludes the early closure branch independent of
its own score and pooled score.

If the following physical row immediately repeats \(b\),
then the first two scalar equations and the sole
\(\boldsymbol u\) input at the first \(a\) give
\(h_z=w_z a z^2(2z-3b)/(4b)\). At \(z=b\) the two
\(h,w\) columns are proportional, again impossible.

The only remaining third interior row is a different
label \(c\), with \(a\) still open. The same actual
first/second calculation gives \(h_c=w_c a c^2
(2c-3b)/(4b)\), and \(b\)-tap \(w_c c^2(c-b)/b^2\).
If \(w_c=0\) it is blind. If \(2c-3b=0\) then
\(h_c=0\) but \(K h_c=-a w_c c^2(c-b)/4\ne0\),
impossible. The \(0,a,b,c\) input identities and the
two-read determinant of the
[one-triple chart](../erk10-five-opening-eight-label-triple/README.md#two-distinct-singleton-labels-before-a_2)
apply as written, regardless of whether \(b,c\) will
repeat. An active closure there is ruled out by that
chart's raw, invertible \(3\times3\) tap system (the
active row's raw weight cancels), which would give the
first two active rows proportional. Any nonactive row
must have label \(b\) or \(c\), or else it is blind.

At \(b\) the two left coefficients are
\(b(2c-b)/(3a),(b+c)/3\), not both zero, and repetition
is forbidden by contrast. At \(c\) the two coefficients
are
\[
 \frac{bc(2b-c)}{3a(3b-2c)},\qquad
 \frac{2c(2b-c)}{3(3b-2c)}.
\]
Unless \(c=2b\) the same contrast follows. Thus the
only second head is \(0,\alpha,p,q,q\) with
\(q=2p\), where \(\alpha=a\) is still open, \(p\) is
a singleton and \(q\) is the dormant repeated label.
This exhausted all early physical chronologies while
allowing every later score to be zero.

## Raw terminal adapter for both heads

We use the same terminal algebra as the
[one-triple raw collapse](../erk10-five-opening-eight-label-triple/README.md#terminal-arithmetic-for-0abaaa2b)
and the
[guarded two-pair nonic](../erk10-fifteen-two-pair-rational-closure/README.md).
Denote the small early label \(p\), the large label
\(q=2p\), and the next physical label after the first
five rows by \(c\). In the first head \(p=a,q=b\)
and \(c\) is a singleton; in the second \(p,q\) have
the meanings just used and \(c\) may be the active
closure. The final four physical rows have four
distinct labels \(d,e,f,g\). If the active pair is
still open after the sixth row, its remaining copy is
at one of those labels, each still distinct from
\(p,q,c,0,1\).

Set \(M(Y)=Y^2(Y-q)^2\), \(G(Y)=Y(Y-p)(Y-q)(Y-c)\).
In the first head take \(\boldsymbol H=\boldsymbol h\).
The actual aggregate at the small label is
\(H_p=-W_p p^3/4\) by the scalar tap at the first
closure (the first active copy has zero \(h\)).
The live \(c\) cubic read from the two scalar labels
\(p,q\) gives \(H_c=W_c c^2(c-q)/4\); if the
score at \(c\) were zero then its nonzero cofactor
would be impossible. Use the actual donor vectors
\[
 \boldsymbol G_*=\boldsymbol w\odot G(\boldsymbol y),\quad
 \boldsymbol Z_*=(\boldsymbol y-q)\odot\boldsymbol H
       -\boldsymbol w\odot M(\boldsymbol y)/4-(p^2/2)\boldsymbol u .
\]
They vanish on the first six physical rows.
At the first active copy this is direct; at the second
the sum over the active pair is zero by the displayed
aggregate. At \(q\) both nominal terms are zero and
\(u=0\); at \(c\) use its actual read.
No individual score was needed for this verification.

In the second head take
\(\boldsymbol H=(p/\alpha)\boldsymbol h\).
Then \(H_p=-W_p p^3/4\) on the first singleton.
For the sixth physical label \(c\), use a single row
if it is a singleton or sum the two active rows if
it closes \(\alpha\). In either interpretation the
target \(\boldsymbol u\) sum is zero. On the previous
five physical rows the sole \(\boldsymbol u\) input
is the active opener, exactly equal to
\(-\alpha \boldsymbol w\odot Y(Y-p)(Y-q)/
[2(\alpha-p)(\alpha-q)]\) there. This is also a valid
input identity when both target rows are summed, by
strict causality. In the true cubic equation use the
three-donor reduction from the first two \(p,q\) moments
and the \(K\boldsymbol u\) read as above. Its left
coefficient is \(-p(c-q)/\alpha\), and its scalar
right is \(-W_c c^2(c-q)^2/4\), forcing
\(H_c=W_c c^2(c-q)/4\) without dividing by \(W_c\).
Here \(c\ne q\), since the dormant pair has closed.
In particular nonzero cofactor makes this pool live
even if it is the just-closed active group.

Use the raw corrected vectors
\[
 \boldsymbol G_*=\boldsymbol w\odot G(\boldsymbol y)
                             +2G(\alpha)\boldsymbol u/\alpha^2,\qquad
 \boldsymbol Z_*=(\boldsymbol y-q)\odot\boldsymbol H-
       \boldsymbol w\odot M(\boldsymbol y)/4
                         -(\alpha-q)^2\boldsymbol u/2 .
\]
The first active copy has weight \(w_1\ne0\), \(H_1=0\),
\(u_1=-w_1\alpha^2/2\). Both corrected vectors vanish
there. At a later active closure the values of these
vectors are **exactly the raw pooled values**
\[
  G_*(\alpha_2)=W_\alpha G(\alpha),\qquad
  Z_*(\alpha_2)=(\alpha-q)H_\alpha-W_\alpha M(\alpha)/4,
\]
because \(u_2=+w_1\alpha^2/2\) and \(H_2=H_\alpha\).
Thus they vanish also at that closure if \(c=\alpha\),
using the preceding sixth-row equation. The other early
rows are covered by the actual \(p,c\) reads and the
factor \(Y-q\). Hence both vectors vanish on the first
six physical rows in either second-head timing.
The pooled formulas remain valid if \(\alpha_2\) is
one of the last four rows, even when \(W_\alpha\) or
its own score is zero.

In both heads the actual grade-five tests, modulo lower
paid directions, are
\[
                    K\boldsymbol G_*-\boldsymbol w\odot JG,\qquad
                    K\boldsymbol Z_*+\boldsymbol w\odot JM/4 .
\]
The extra actions of \(\boldsymbol u\) are multiples of
\(\boldsymbol h\) and therefore lower paid directions.
With \(\nu=(Y-1)(Y-e)(Y-f)(Y-g)\) they give
\(I(\nu JG)=I(\nu JM)=0\) by strict causality and the
zero donors. The two anchor values \(H_p,H_c\) yield
the same cofactor relation
\(c(c-q)\mu_c=-p^2\mu_p\), where
\(\mu_z=I(P_9(Y)/(Y-z))\), \(P_9=(Y-d)\nu G\).
As in the one-triple proof, integrate \(\nu(Y-d)M\)
using its only contributing labels \(p,c\); the cofactor
anchor equation gives zero. Also
\(4JG=(Y-c)M-JM\); hence \(I(\nu M)=0\).
The three possible contributions at \(p,c,d\) to
\(I(\nu M)\) then give
\(d(d-q)\mu_d=c(c-q)\mu_c\), by the same three-term
partial fraction cofactor. Thus the raw pooled \(Z_d=0\).
If \(d\) is the delayed active closure, its physical
\(Z_*\)-entry is exactly this raw pooled value, as
proved above, with no scaling by a split.
Finally test \(K Z_*+\boldsymbol w JM/4\) with
\(U=(Y-1)(Y-f)(Y-g)\). It kills the last two rows and
the remaining rows read only zero donors through \(d\).
It gives \(I(U JM)=0\), together with \(I(YU JM)=0\)
from the \(\nu\) test. These are precisely the prior
rational pressure conditions with small parameter \(p\);
the same verified quartic pivot and projectively
rootless modulo-11 nonic give the contradiction.
No score on \(d,e,f,g\) was assumed.

## Replay

    python3 -B audit.py
    # From the overlay or repository root:
    sha256sum -c ai-generated/research/erk10-five-opening-eight-label-pairs-zero/sources.sha256

Use the one-triple Lean scalar gates for the reused \(3\times3\)
determinant and the already archived nonic arithmetic for the final
rational obstruction. Physical grade/chronology and the raw
terminal adapter themselves are mathematical.
