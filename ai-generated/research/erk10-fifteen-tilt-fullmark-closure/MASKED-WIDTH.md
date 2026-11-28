# Width eight or nine with raw model-blind coordinates

The data in this note are a strictly explicit high block
of width at most nine with assigned clocks \(\boldsymbol x\),
score vector \(\boldsymbol w\), exact raw
\(K\boldsymbol w=Y\boldsymbol w\), and input vectors
\[
                E_\varepsilon f=(\varepsilon_i f(x_i))_i,
                   \qquad \varepsilon_i\in\{0,1\}.
\]
The scalar moments including the opening origin are exact
through degree nine. Pure short words through length four
on these inputs have their usual nominal values. In width
nine assume there is one annihilator of the combined \(D_4\)
and nominal observers nonzero outside every early reverse
prefix with two distinct nonzero surviving labels later
in reverse. This is the actual witness obtained by the
directional cut in the main packet; no witness is needed
in width eight. We prove these data impossible over
\(\mathbb Q\).

In the usual grade arguments, positive probes have
entries \(\varepsilon_i x_i^k\), and the literal raw
observers still use the *whole* score vector, not the
masked score. Marking an input commutes with the mask,
so the standard word duality gives all grade \(j\le4\)
positive tests through degree \(9-j\). It gives the
shifted Hilbert \(5\) for nominal columns modulo \(D_4\).
The weak-flag rank floor is still three because
the first positive probe of \(Y\boldsymbol w\) is
\(1/6\). Thus \(D_4\) has dimension exactly three:
the ambient dimension bound gives this in width eight,
and the stipulated annihilator gives it in width nine.
A blind coordinate or proportional same-label pair
on the observed space is impossible in width eight,
and impossible in any early supported prefix in
width nine by that annihilator. This is the needed
replacement of the old two-witness argument.

Strip the initial reverse run of score-zero rows if
there are any (equivalently final forward unused rows).
All adjoint words vanish there by strictness; the
remaining word budget, actual \(v=0\), dimensions
and off-prefix property are unchanged. The first live
reverse row has \(y=0\) by \(v=0\), even if it is
model-blind. All positive-grade defects vanish
at that coordinate. The scalar allowed sites
are the two anchors \(0,1\) and the distinct
**visible ordinary** labels \(x\ne0,1\) carrying
a flag-one evaluation. Anchor \(1\) is allowed
even if all its flags vanish (a zero scalar weight).
Thus at least six visible ordinary labels exist.
If exactly six exist, their grouped scalar masses
are all nonzero: dropping a zero one would violate
the [rational anchored floor](../rational-endpoint-moment-nine/README.md).
The actual first live nonendpoint has
\(u=-wy^2/2\ne0\), whether its flag is zero or one.

Throughout this proof an ordinary target is a live
flag-one nonendpoint singleton or the closing copy
of a visible ordinary pair with live total score.
A same-clock blind coordinate is not part of the
group mean on its visible label. Raw \(\boldsymbol u,
\boldsymbol g,\boldsymbol h,\boldsymbol k\) and the
strict order are never masked.

## Seven or eight visible ordinary labels

With eight, all rows besides the first endpoint are
physically distinct visible ordinary labels. The
grade-two cofactor on those eight labels is nonzero
(\(\boldsymbol u\ne0\)), and its two clock marks
span \(D_4\). Then \(D_3=\boldsymbol u\mathcal P_1(Y)\)
since a mark of a genuine quadratic multiplier
would give rank four. The
[paid fourth-distinct head contradiction](../erk10-five-opening-nine-label-one-pair/TEN-DISTINCT.md)
uses exactly these physical readings, the off-prefix
contrast, and the final positive pairing with \(X\)
(or \(XY^k\)). The pairing still has the same
nonzero scalar value with flags. Thus it excludes
this case. If width eight and seven ordinary labels,
they are all physical singletons, so the seven
grade-two tests force \(\boldsymbol u=0\), impossible.

With seven and width nine, there is at most one
extra row besides the first endpoint and seven
ordinary representatives. If it is a second
**visible** endpoint, grade two either has a
nonzero eight-site cofactor including this endpoint,
or vanishes (a first model-blind endpoint still
has its defect zero). So only the leaking case
occurs; use the
[paid sole-duplicate-endpoint argument](../erk10-five-opening-nine-label-endpoint-repeat/README.md).
Its first contiguous placement is immediately
a contrast. Its first separated placement is
excluded by the [four-column determinant](../erk10-five-opening-first-endpoint-jump/README.md#the-next-compatibility-determinant-and-the-only-remaining-head);
later placements are excluded by its two marked
causal identities. This uses no terminal grade-five
moment. If instead the extra row is a **blind**
endpoint, \(\boldsymbol u\) is supported on that
endpoint only by the seven ordinary tests, impossible
at the first live nonendpoint.

For any other extra, the grade-two tests are exact
on all seven ordinary pools. Its support consists
of one opposite pair (if a repeated visible
ordinary label) or one blind coordinate (including
\(x=0\)). In particular this is a line at a single
nonzero reverse ordinate \(a\). If grade three
is also pure, it is confined to the same line and
impossible by the first different-live-ordinate
argument below. If it leaks, its aggregate space
is a cofactor line, and its mark with the pure
\(\boldsymbol u\) saturates \(D_4\). The composed
defect \(\boldsymbol h=K\boldsymbol u\) must leak:
otherwise it is proportional to \(\boldsymbol u\),
zero at its first live point, hence zero globally.
On the strict \(a\)-block before the first different
live label, \(K u=0\) and
\(u=aNw-a^2w/2\) force \(Nw=0\); its nonzero needed
scalar tap at the different label would then give
nonzero \(h\), contradiction.

Thus \(D_4=\langle u,h,Yh\rangle\) in vector notation.
The same
[raw single-active-pair chronology](../erk10-five-opening-nine-label-one-pair/README.md#if-the-grade-two-aggregate-is-zero)
now applies. The active label may have two physical
copies if the blind coordinate shares a visible
label, with its other entry constrained to zero
in \(\boldsymbol u\); the old proof does not impose
opposed sums at that active pair. It uses raw
\(g,k,Kh\) and no aggregate division at that label,
as checked in the
[one-high-zero head transfer](../erk10-five-opening-zero-high-repeats/README.md#two-or-three-high-zeros-and-no-visible-repeats).
If there is no second active copy it simply cannot
be the next row. In either case a required repeated
*different* nonzero ordinate is unavailable. So no
configuration with seven visible ordinary labels
survives.

## Six visible ordinary labels

At most two physical rows are available in addition
to their six representatives and the first endpoint.
Grade two aggregates are exact on all visible ordinary
labels and the possible endpoint, by seven positive
tests. If there are two late endpoint copies and
no extra ordinary or blind nonendpoint, there is no
possible support for \(\boldsymbol u\) at its first
live nonendpoint. If there is one late **visible**
endpoint and at most one extra at a positive reverse
ordinate, grade-three aggregate can be nonzero on
the six ordinary plus endpoint visible labels. The
pure physical support of \(\boldsymbol u\) is again
one ordinary pair mode or one blind-coordinate
mode at \(a\ne0\); both endpoint \(u\) coordinates
are zero. In the leaking case, the same strict
one-label proof forces \(\boldsymbol h\) to leak and
\(D_4=\langle u,h,Yh\rangle\) in vector notation.
Before the added endpoint the raw head must either
close its sole active pair or require a nonexistent
dormant repeat; any possible added endpoint by this
forced early horizon has \(h=0\) by the homogeneous
two-read equations (and has \(u=0\)), producing
the same actual early contrast. These are precisely
the
[paid pure-\(u\) endpoint-head computations](../erk10-five-opening-eight-label-endpoint-repeat/README.md#zero-grade-two-aggregate-the-late-endpoint-cannot-have-the-required-jump),
which use only the actual reads and allow the active
single/paired ghost as above. If grade three is
pure in this case, its one-dimensional support
fails as below. A physically extra zero-ordinate
blind slot with no positive support again makes
the literal first-live \(u\) impossible.

In all remaining cases there is no late visible
endpoint. The six grade-three moment tests give
pure support. Its physical space \(S\) has dimension
at most two: each extra ordinary repeat contributes
one opposite direction, and each blind coordinate
or high \(x=0\) contributes one separate coordinate,
apart from the first endpoint where all defects
vanish. These are counts of physical axes; a blind
row may share a clock with any visible row.

### First-live and local one-label exits

If \(D_3\) has rank at most one, its nonzero
\(\boldsymbol u\) and its mark force support at one
label \(a\ne0\), and \(\boldsymbol g,\boldsymbol h\)
are proportional to \(\boldsymbol u\). Before the
first live different nonendpoint the prior
positive scalar sources are all at \(a\). On those
\(a\) rows one has \(g=a u+a^3w/6\), so their scores
are proportional to \(u\). The \(K u=0\) read at
the different live target contradicts its nonzero
weighted \(Y\)-tap. This also proves \(D_3=S\)
in the remaining rank-two case.

If both dimensions are at the same positive label,
the [single-label strict nilpotent and feedback proof](../erk10-five-opening-fourfold-interior/README.md#the-first-live-singleton-forces-a-two-dimensional-nilpotent-block)
does not use opposed sums among copies at that
label. It applies verbatim to one or more blind
copies there. There are at least two distinct live
other labels from scalar support. If the first
two distinct target ordinates include multiple
physically live clean copies of the first one,
take their total scalar tap: the feedback proof
uses only that total, and both low profiles vanish
at every such clean copy.

### Two mode labels away from zero reverse ordinate

Each mode is either an individual blind coordinate
or the opposed pair of visible rows at one label.
At the first ordinary target \(z\), its positive
scalar reads can come only from these modes.
The actual weight on a blind coordinate tracks
that mode irrespective of its score, and only
the first visible paired copy is available until
its live closure. Here all six visible groups are
live, so no earlier zero-total closure needs a
separate convention. The group-mean on \(D_4/S\)
is nonzero at \(z\): its nonzero \(Y\)-tap is
tracked by \(K\) of one of the two modes. The
quotient is one-dimensional.

At the next ordinary target \(x\), old tracked
scalar taps and \(\boldsymbol k\) scale by a
common factor \(\lambda\), with just one extra
scalar tap \(T\) at the first target's label
(a new singleton, or the second pair copy's
untracked amount). A blind coordinate whose clock
coincides with that target is still tracked
independently. All other earlier live inputs
are tracked, and no weight is inverted except
the actual live group mass of each selected
target. The three primitive equations give
\[
 z^2\lambda+2zT=x^2,\quad z^3\lambda+3z^2T=x^3,\quad
 z^4\lambda+4z^3T=x^4,
\]
hence \(x^2(x-z)^2=0\), contradiction.

### One endpoint-blind mode and one positive-ordinate mode

The endpoint-blind mode occupies a single later
coordinate at \(Y=0\); the other active label
\(a\ne0\) has one blind coordinate or one genuine
visible pair. At the first ordinary target \(t\),
only scalar ordinate \(a\) can contribute positively.
Thus \(t=3a/2\) by the first two primitive reads,
so \(t\) is not the closure of the \(a\)-pair or a
singleton of that same label. It is an actual live
visible singleton. There is a single earlier
live \(a\) source (the first pair copy or blind
coordinate), with \(u=-a^2w/2\). The read
\(h_t=0\) then requires a nonzero earlier
endpoint-blind \(u\)-coordinate, since the \(a\)
tap is nonzero.

Write \(\boldsymbol u=\boldsymbol U_a+\boldsymbol U_E\)
for its two mode components. Their first values
at the live \(a\) source and at the only earlier jump
give
\[
 \boldsymbol g=(2a/3)\boldsymbol U_a+a\boldsymbol U_E,\quad
 \boldsymbol h=-a\boldsymbol U_E/2,\quad
 \boldsymbol Q=K\boldsymbol U_E.
\]
The actual \(\boldsymbol k\) then equals
\((a^2/2)\boldsymbol U_a+a^2\boldsymbol U_E-a\boldsymbol Q/4\).
Indeed compare the \(a\) source, endpoint jump,
and \(t\): the first two \(\boldsymbol Q\) entries
are zero, while \(Q_t=a^2S_t/2\ne0\) with
\(S_t\) the weighted ghost tap onto \(a\).
The nominal \(t=3a/2\) first-primitive relation
gives \(k_t=-aQ_t/4\).
These three coordinates are injective on \(D_4\).

If a second \(a\)-copy from an opposed visible
pair occurs between \(t\) and the next different
live label, let its \(a,t\) taps be \(S,T\).
Use \(g=(2a/3)u,\ h=0,\ k=(a^2/2)u-aQ/4\)
there. Their two homogeneous equations are
\(S/3+5T/4=0,\ 5S+21T=0\), so \(S=T=0\).
It also tracks its own score by \(u=-a^2w/2\).
If instead a blind \(a\)-source has a visible
singleton at the same label appearing before the
next different live target, that singleton is
clean in \(u,g,h\); the corrected cubic below
already excludes it (take \(x=a\ne t\)).
Thus at the next live label \(x\notin\{a,t\}\)
the only positive inputs come from \(a,t\), with
all \(a\) scores tracked. At this actual clean
row \(Q_x=a^2 S/2\) and \(k_x=-a^3 S/8\).
The first two and corrected cubic primitive
reads are
\[
 2(aS+tT)=w_x x^2,\quad
 3(a^2S+t^2T)=w_x x^3,\quad
 9a^3S+8t^3T=2w_x x^4.
\]
The standard fraction-free elimination gives
\(2w_x x^2(x-t)^2=0\), impossible.
This closes the masked-width proof in all cases.
