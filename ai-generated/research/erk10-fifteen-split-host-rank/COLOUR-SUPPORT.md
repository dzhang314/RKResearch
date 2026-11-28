# A split host is either monochromatic or visits at least seven clocks

In the [rational split-host chart](README.md), retain
the assigned clocks and strict width-eleven pure word
budget, exact first reverse primitive, and the true
\(\boldsymbol d\) silent through length five.
Let \(V\) be the combined grade-four/nominal
annihilator, of dimension three. No assumption on
the signs, liveness or distinctness of individual
scores is made below. The last original physical
row is the live endpoint, as proved in the main note.

## At most one independent single-clock direction in V

A vector \(\boldsymbol z\in V\) supported at one
clock can be cut at its earliest pivot. Use
\(Q=I-\boldsymbol z\boldsymbol e_j^T/z_j\)
to identify its annihilating slice and retain the
principal survivor coordinates. All pure words of
length at most four are unchanged by inserting
\(Q\) from right to left: each difference pairs
\(\boldsymbol z\) with an unmodified reverse prefix
of length at most four. It is silent against these
actual words, because the words of length at most
four on \(\boldsymbol w\) are sums of \(D_4\) and
the five nominal columns. The cut commutes with all
clock marks. The cut block is strictly lower:
input-coordinate correction uses only the earliest
nonzero pivot and affects outputs strictly after it.
More explicitly, restrict \(QBQ\) to the slice,
whose omitted input coordinate is zero; the
subtracted pivot output accesses only earlier
columns, and affects only later supported coordinates.
The new score functional is the restriction of
the old one because \(\boldsymbol w^T\boldsymbol z=0\).
The old first reverse primitive remains exact:
\(\widehat{\boldsymbol w}^{\,T}\widehat B
=\boldsymbol w^T B\iota
=\boldsymbol w^T (I-C)\iota\), where \(\iota\) is
the zero-pivot inclusion. Projected eval flags
are updated at the cut clock by
\(\varepsilon_i-z_i\varepsilon_j/z_j\).
Diagonal rescaling of each nonzero flag makes it
\(1\), and exact zeros are carried as blind flags.
The computation therefore permits nonzero physical
scores and taps on blind coordinates. It preserves
the masked positive scalar and word tests. For the
scalar constant the same projected eval flags give
\(\widehat{\boldsymbol w}^{\,T}\widehat E_\varepsilon 1
=\boldsymbol w^T E_\varepsilon 1\); so the same external
origin score remains valid. If one is restoring an
unmasked scalar rule and choosing to include blind
high zero scores in its constant, its external origin
score can instead be shifted by exactly their sum
with the opposite sign. No positive test detects
that origin score.
The observer rank cannot increase: by length-four
erasure, the new actual word score columns are
the restrictions of the old observer columns and
likewise the new nominal columns (with the same
diagonal rescaling).

Two independent such directions permit two successive
cuts, even if they share their clock. The projection
of the second is still nonzero, supported at one
clock, and silent through length four. The result
would be masked width nine with exact first primitive,
actual grade-four rank at most three, and the full
masked length-four budget. This width nine is
impossible, **without** an extra off-prefix condition:
in the [masked-width proof](../erk10-fifteen-tilt-fullmark-closure/MASKED-WIDTH.md),
the off-prefix condition is used only to contradict
a blind coordinate or a contrast between two
coordinates of the *same* clock (including the
reference proofs of the early endpoint and
all-distinct heads). Each such contrast is itself a
nonzero single-clock direction invisible to the whole
observer space. Apply the same cut once more to
width eight, which has an unconditional closure
there. All the other branches of the masked argument
already need no off-prefix condition. This strengthens
that dimension-nine lemma only when the true raw
first reverse primitive is exact, as here.

Consequently \(V\) contains at most one independent
single-clock direction in total. In particular \(d\)
cannot use exactly two clocks: the two components of
\(\boldsymbol d\) are independent combinations of
\(\boldsymbol d,C\boldsymbol d\).

## Count the dirty colors when there are at most six

From the true source and its marks,
\[
             \boldsymbol w^T C^j\boldsymbol d=0
                             \qquad(0\le j\le5).
\]
If the support uses at most six clock labels,
Vandermonde inversion gives \(\sum_{i:x_i=a} w_i d_i=0\)
at each dirty label \(a\). Let \(m\) count distinct
nonzero raw clocks (endpoint included) and let \(r_0\)
count physical high zero rows. Exact scalar quadrature
with allowed endpoints \(0,1\) has at least six
ordinary live labels by the
[rational anchored scalar floor](../rational-endpoint-moment-nine/README.md).
Thus at most \(m-7\) ordinary labels are dead
(total score zero). The first live endpoint
means a singleton endpoint cannot be dirty.
Every other dirty nonzero label is either a dead
ordinary singleton or a repeated group, of which
there are at most \(11-r_0-m\).
The zero group contributes at most \([r_0>0]\).
Hence there are no more than
\[
            (m-7)+(11-r_0-m)+[r_0>0]\ \le4
\]
dirty colors. In particular counts five and six are
already impossible. The estimates allow dead repeated
groups, zero individual weights at live groups,
and endpoint weights that cancel within a repeat.

## Three colors

Each individual color direction
\(\boldsymbol d_a\) is a quadratic clock projection
of \(\boldsymbol d\). It therefore annihilates the
actual \(D_3\) by length-five silence; it annihilates
every nominal column by its own zero pooled weighted
mass. Because it has a single clock, it also
annihilates any clock mark of an individual defect
it annihilates.

Let \(S\) denote the vectors whose sums at each
nonzero clock vanish (unprobed \(x=0\) is allowed).
If the grade-two seed \(\boldsymbol u\) leaks out
of \(S\), its seven positive moment tests give at
least eight visible aggregate sites. Its first
two marks and itself are independent and span
\(D_4\) by the rank-three cap. All three color
directions then lie in \(V\), contradiction.
Otherwise if some \(\boldsymbol \xi\in D_3\) leaks,
its six positive moment tests give at least seven
sites. Modulo \(S\), \(\boldsymbol\xi,C\boldsymbol\xi\)
are independent. Together with
\(0\ne\boldsymbol u\in S\) they span \(D_4\) and give
the same contradiction. Nonvanishing of
\(\boldsymbol u\) follows from the strict invariant
plateau (or the actual first live nonendpoint).
Thus \(D_3\subseteq S\), and
\(\dim D_3\ge2\); otherwise \(D_2=D_3\subseteq S\)
is an impossible pure invariant plateau.

All positive-grade defects vanish at the first
reverse (live endpoint) coordinate. Their available
pure physical space has dimension \(11-m-\epsilon\),
where \(\epsilon=1\) if the endpoint is repeated
(and zero otherwise); in a singleton endpoint the
first-coordinate zero is automatic. If \(m\ge10\)
this is already at most one. Otherwise at least
\(3-(m-7)-\epsilon=10-m-\epsilon\) of the dirty
colors are live ordinary labels or \(x=0\). Each
such color imposes an independent nonzero constraint
on this pure physical space: at a live ordinary
pool a nonzero dirty vector of weighted mass zero
cannot be constant (the total score is nonzero),
so some opposite pair detects it; at \(x=0\) the
nonzero direction detects a free coordinate. These
constraints are supported on disjoint labels and
hold on \(D_3\). They give \(\dim D_3\le1\), a
contradiction.

## Four colors

The individual color directions now are cubic clock
projections and annihilate \(D_2\), in particular
\(\boldsymbol u\), and the nominal space. Again if
\(\boldsymbol u\) leaks, its first two marks
span \(D_4\) with it, impossible because the four
single-clock directions would be in \(V\).
Suppose instead \(\boldsymbol u\in S\). The count
above must be sharp: \(r_0\le1\), every repeated
nonzero group is a dirty pair, and there are
exactly \(m-7\) dead ordinary singletons. All
repeated ordinary groups are therefore live. In
each such pair the dirt values are unequal by
the zero weighted mass; orthogonality to that
direction kills the sole opposite-pair component
of \(\boldsymbol u\). Any high zero coordinate is
individually killed by its nonzero dirt value;
every nonzero singleton coordinate vanishes by
purity. At an endpoint pair the first coordinate
vanishes by strictness and \(Y=0\), hence the
second as well by purity. This gives
\(\boldsymbol u=0\), contradiction.

## What survives in the single-color case

Cut \(\boldsymbol d\) at its first host coordinate.
This **particular** cut preserves the full length-five
budget, by the stronger literal source silence.
If all nonzero-clock surviving coordinates had
nonzero normalization, the cut would yield the
already excluded unmasked width-ten pure words.
It follows that there is a surviving blind copy
at the host clock \(r\), with old \(d_i=1\).
This is not an assertion that that copy is
unscored.

Moreover \(B\boldsymbol d\ne0\). If it were zero,
the projected residual on \(U_0\) would vanish
by \(T(f)=-J_r(f)\boldsymbol d\).
At the first flagged nonzero label \(a\) after the
cut, this would give \(J_a=0\) on the two-dimensional
\(U_0\). At the next distinct flagged nonzero label
\(b\), it would give \(J_b\in\langle E_a\rangle\)
on \(U_0\). But
\(X(X-a)(X-a/2)\in\ker J_a=U_0\), with
\(E_a=0\), \(J_b=b^2(b-a)^2/4\ne0\).
This contradicts exactness. The required two
flagged labels exist by the shifted Hilbert
support with the unchanged positive scalar tests.
Since \(B\boldsymbol d\) has zero first entry, it
would be independent of \(\boldsymbol d\) if
nonzero, and thus cannot be supported only at
\(r\). The first flagged distinct nonzero read
of \(P\) is exact (the correction term contains
\(P(r)=0\)); in particular its clock is a
nonzero root of \(JP\). By the host-gates proof
the second actual raw row is already a distinct
nonzero \(h\); when dirt is monochromatic it is
flagged and \(JP(h)=0\).

The monochromatic case with blind copy, and the
multicolor case with at least seven colors, are
not excluded by these counting arguments.
