# The triple-and-pair exit permits arbitrary physical score zeros

The [regular proof](README.md) extends to **all physical weights**
when the two pooled scores at \(a\) (triple) and \(b\) (pair) are
nonzero. The field, unique first reverse endpoint, and literal
five-opening word assumptions are unchanged. Zero pooled scores
are not included in this note.

Retain the same \(D_3,D_4,S\), primitives and ordinary targets.
In particular before the first ordinary completion the possible
physical repeated-label donors are still \(a_1,a_2,b_1\), and there
are at least two live singletons. The first nonzero-score interior
physical row belongs to a repeated label: otherwise its singleton
\(\boldsymbol u\)-entry could not vanish. Its \(u\)-entry is
\(-w_i y_i^2/2\ne0\), since there is no earlier nonzero-ordinate
scalar source.

## No leakage and one-mode leakage cases

The exact first three primitives make the first ordinary group
impossible with at most one scalar donor label. If that group is
a repeated label, the same double-root argument in the main proof
applies regardless of the physical scores.

If it is a singleton, each label \(a,b\) must have previously
supplied a nonzero-score donor. If the rank of \(D_3\) restricted
to all old physical donors were at most one, it would be exactly
one by the first live \(\boldsymbol u\)-entry. Its clock mark
then implies that this restriction of \(\boldsymbol u\) is
supported only on its first live label \(p\); otherwise the mark
would be independent. Every restricted \(\boldsymbol g,\boldsymbol
h\) entry is proportional to \(\boldsymbol u\). Consider the
first live opener at the other label \(q\): it is clean in all
three profiles and its positive scalar taps can come only from
\(p\). On old \(p\)-copies before that row,
\(\boldsymbol g=p\boldsymbol u+(p^3/6)\boldsymbol w\).
The two defect profiles restricted there must then yield
\(\boldsymbol w\) proportional to \(\boldsymbol u\).
This is impossible because the first primitive of the clean
\(q\)-row requires a nonzero weighted tap, whereas \(K\boldsymbol
u\) vanishes there. Thus \(D_3\) supplies two independent
old directions, and the same old-three/proportionality proof
in the main note excludes the second ordinary target.

In leakage, the case where \(D_3\) is supported at only one
label uses the same cyclic nilpotence proof. Replace the
“first copy of the other label” test target there by its
**first nonzero-score** copy. Earlier score-zero copies
at that clean label have no source in either \(D_3\) or
the scalar powers. There are still two distinct live clean
targets outside the supported label by the two live singletons.
Between the two selected targets, all live scalar donors
are at the original supported label or the first clean
ordinate, so the two equations and the feedback induction
are unchanged.

## Two-mode leakage setup

The separate \(a,b\) modes in \(D_3\) follow exactly as before:
the earliest live \(\boldsymbol u\)-entry is nonzero, and
marks separate distinct supported labels or force a third
direction in \(D_4\cap S\). In this two-mode case **each**
mode label must support at least one of \(\boldsymbol u,
\boldsymbol g,\boldsymbol h\). Otherwise pick the earliest
live row outside the other, active label (a singleton or
nonzero-score copy of the clean repeated label).
Its first two primitives and \(K\boldsymbol u=0\) force
two independent old \(\boldsymbol u,\boldsymbol g\)
restrictions at the sole earlier label by the same one-donor
formula. That is incompatible with the separate rank-one
directions. In particular any physically score-zero row
before the first live interior score has zero mode
coordinate: its \(\boldsymbol u,\boldsymbol g,\boldsymbol h\)
entries all vanish because no previous weighted nonzero
ordinate was available (and all earlier \(\boldsymbol u\)
entries are zero).

If a label's available mode entries agree with its
scores after normalization, then its \(K\)-image tracks
the scalar tap there. If all available scores at a label
are zero, there is no scalar tap to track, even if its
mode is nonzero. At the first ordinary target \(z\), if
every scalar label tracks or is silent, at least one
tracked scalar tap is nonzero. Its mean calibrates the
one-dimensional grade-four quotient. Any next target
only adds a free scalar input at \(z\), unless the
second triple copy \(a_2\) is still to appear.
If \(a_2\) does appear before the second ordinary target,
use the same virtual row
\[
 \operatorname{ev}_{a_2}-\nu \operatorname{ev}_{a_1},
 \qquad \nu=V_a(a_2)/V_a(a_1),
\]
whenever \(V_a(a_1)\ne0\). The result is clean in \(D_3\).
If its score \(w_{a_2}-\nu w_{a_1}\ne0\), the primitive
square at this virtual target forces \(a=z\), impossible
since \(a_2\) was not present at \(z\). Thus this score
is zero. For a label with \(w_{a_1}=0\), it says the
intervening \(a_2\) also has zero score. For a live earlier
\(a_1\), it says the mode tracks both eventually available
scores. There is then no extra new scalar input away
from \(z\). At the second ordinary target the same
reference-square gate rules out the distinct clock.

Below these prerequisites are checked for every zero-opening
pattern except a single explicit exception, which yields
the same square by direct algebra.

### Zero score on \(b_1\)

The \(b\) mode cannot be zero at \(b_1\) since \(b\) is a pair
and the mode is nonzero. So \(b_1\) cannot occur before the
first live \(a\) score. Before the first ordinary target all
available \(b\)-scores are zero. At least one \(a\)-score
must already be live, to pay the first primitive.

If the first live \(a\)-score is \(w_{a_2}\), then \(a_1\)
was an earlier zero-mode ghost and the \(a\)-mode at \(a_2\)
is nonzero by its \(\boldsymbol u\)-entry. Thus tracking on
the previously appearing \(a\)-rows holds.
If \(a_1\) is live, normalize its mode to \(w_{a_1}\).
On any \(a_2\) preceding \(b_1\) the relation
\(g=a u+(a^3/6)w\) gives tracking as in the regular proof.
On any \(a_2\) after \(b_1\) and before the first ordinary
target there is still no nonzero scalar tap on \(b_1\).
Since all \(a\)-defects have rank one and \(a_1\) is
the first live scalar donor, \(g=(2a/3)u\) on \(a\).
At \(a_2\), this gives \(a^2 S/3=0\) for its scalar
tap \(S\) onto \(a_1\), so \(V_a(a_2)=w_{a_2}\) here
too. The result is unchanged if \(a_2\) itself is zero score.
If \(a_2\) has not yet appeared, \(a_1\) is necessarily live,
so the virtual-row test has a nonzero mode pivot.
Thus the calibrated proof above applies in all cases.

### Zero score on \(a_1\), with \(b_1\) live

If no \(a\)-score is live before the first ordinary target,
only the scalar \(b_1\)-tap is nonzero. It tracks and pays
the \(Y\) moment. If \(a_2\) still has to appear before
the second target, \(V_a(a_1)\ne0\) is forced:
otherwise the only earlier nonzero entry available to
the \(K\boldsymbol u\) mean at the first target would
be the nonzero \(u_{b_1}\) reading on the sole live scalar
donor, contradiction. Thus the virtual row test applies
and prohibits an untracked new scalar value at \(a_2\).
If \(a_2\) is already present and zero score there is
no such new input either. This proves the required exit
whenever the first ordinary target had no \(a\)-scalar donor.

Suppose next that \(a_2\) is live before the first ordinary
target. If \(a_1\) precedes \(b_1\), it is a zero-mode ghost;
the \(a\) mode can be normalized to the score of \(a_2\).
Its mode value is nonzero: if \(a_2\) is earlier than \(b_1\),
its \(\boldsymbol u\) is nonzero by lack of any earlier
nonzero-ordinate scalar input; if later and clean in all
low defects, its one \(b\) donor cannot satisfy the exact
\(K\boldsymbol u\) payment. Thus both \(a\)-copies track.

If the order is \(b_1,a_1,a_2\), let
\(\alpha=K_{a_1,b_1}w_{b_1}\) be the weighted tap
at the score-zero \(a_1\). If \(\alpha=0\) all its
\(\boldsymbol u,\boldsymbol g,\boldsymbol h\) entries
vanish, so its mode value is zero and \(a_2\) again
provides a nonzero mode pivot as above. The only exception
is \(\alpha\ne0\). Normalize \(V_a(a_1)=1\) and let
\[
 U=b\alpha,\quad G=b^2\alpha,\quad H=-b^2\alpha/2 .
\]
These are the defect multipliers on the \(a\) mode.
Normalize \(V_b(b_1)=w_{b_1}\); then the coefficient of
\(\boldsymbol u\) on the \(b\) mode is \(-b^2/2\)
and the \(\boldsymbol h\)-coefficient is zero.

At \(a_2\) let \(T\) be its scalar tap on \(b_1\)
and \(Q=(K\boldsymbol V_a)_{a_2}\). The \(a_1\) score
is zero, so \(u_{a_2}=bT-w_{a_2}a^2/2\) and
\(g_{a_2}=b^2T-w_{a_2}a^3/3\). Since \(G=bU\),
setting their difference to zero gives \(a=3b/2\).
The identity \(H/U=-b/2\) now gives
\[
 UQ= b a^2 w_{a_2}/4\ne0
\]
from the \(\boldsymbol h\) entry at that row.
The vector \(K\boldsymbol V_a\) vanishes at \(b_1,a_1\)
and is nonzero at \(a_2\), so it spans the grade-four
quotient. After subtracting the first-copy mode
multiples from \(\boldsymbol k\), its remaining \(a_2\)
coordinate is
\(w_{a_2}[(b^2a^2)/2-a^4/4]\).
At an ordinary target with only \(b_1\) available as
a \(b\)-donor, the group \(\boldsymbol h\) identity gives
\(\operatorname{mean}(K\boldsymbol V_a)=b^2 B/(2U)\),
where \(B\) is its actual scalar \(b\)-tap.
The resulting relation is
\[
 \operatorname{mean}(\boldsymbol k)
       =\frac b2(2b^2-a^2) B
       =\frac{b(a-b)(a-2b)}2 B ,
       \qquad a=3b/2 .
\]
This is exactly the regular exceptional coefficient.
The first ordinary target is therefore forced to be
the triple completion at \(a\), and the second again at
\(a\), impossible.

If both opening scores were zero, the first live repeated
score before the first ordinary target would have to be
\(a_2\). With \(b_1\) before that score, its zero mode
entry would contradict the nonzero pair mode, as above.
If \(b_1\) is later than \(a_2\) its case is already
covered under “zero score on \(b_1\)”, which permits
\(a_1=0\). Therefore the extension is exhausted.
