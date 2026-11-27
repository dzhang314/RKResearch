# ERK10 cannot have its sole zero weight at the physical origin

Over a characteristic-zero field, there is no strict explicit
14-stage rooted-order-ten tableau with \(b_1=0\) and all other
weights live. Equivalently, the branch \(b_1=0\) is closed
**under injectivity of \(B=\operatorname{diag}(b)\) on old \(F_4\)**:
the [injectivity theorem](ERK10-ZERO-WEIGHT-INJECTIVE-F4.md)
already forces that to be the sole ghost. The case \(b_1=0\)
with additional internal ghosts and **noninjective** \(B|_{F_4}\)
is **not covered** here. In conjunction with the
[all-live theorem](ERK10-ALL-LIVE-COMPLETENESS.md), any possible
14-stage method has at least one internal zero weight at
physical 2–13. The unrestricted interval remains 14–15.

This is a transfer audit of the exact scalar obstructions, not
an assertion that the 13-live-row reduced reverse has ordinary
order ten. Its ordinary order already fails at six by the
[proved alias](ERK10-ZERO-WEIGHT-INJECTIVE-F4.md); it is
nonetheless exact for the distinct **shift-one weighted**
size-nine output used below.

## 1. Transport, measure, and low local contacts

The sole omitted index is physical 1.
Write \(A^\vee=B_I^{-1}(A_{I,I})^\mathsf{T}B_I\) in unpermuted
coordinates, \(I=\{2,\ldots,14\}\). Its genuine clock is
\(1-c_I\), and its pure and numerical flags agree with the
old projected flags through grade four, with the same
polynomial models in the original variable. Its exact
weighted output \(\beta=b_I C_I\) integrates through reverse
rooted grade eight with weight \(1-y\) in variable \(y=1-X\).
The weighted floor is 13. Thus any literal duplicate in
the actual reduced reverse could be merged, preserving the
weighted tests, to contradict that floor. The ordinary old
forward 14-stage floor likewise forbids any old literal
duplicate. These are two different minimum-size arguments.

The old ordinary scalar clock measures, in both variables,
are exact through degree nine:
\[
 \sum_{i\in I} b_i P(c_i)=\int_0^1P(X)\,dX,\qquad
 \sum_{i\in I} b_i P(1-c_i)=\int_0^1P(y)\,dy.
\]
The second identity is just reflection of the first.
Neither asserts ordinary reversed rooted order.
In particular the ordinary scalar support needs at least
six distinct sites as long as the potential support used
in the argument includes the physical anchor 1.
If there were at most five, its other-site hull of
degree at most four times \(1-X\) would give a
nonsingular anchored Gram contradiction. The use of
the physical label 0 in a support polynomial is legal
even though its **origin weight is zero**. It is an
anchor factor, not a nonzero measure assumption.

By the injectivity theorem the quadratic defect has one
clock \(\theta\ne0,1\) and constant nonzero amplitude.
Write \(s\) for its indicator and \(r=As\).
The actual old \(F_3,F_4\) are
\(\langle s,r\rangle,\langle s,r,Cr\rangle\).
The shifted-nine frontier and the literal entrance
make physical 2 and 13 carriers, both live.
All low-degree first/second active and fifth-row
calculations of the
[two-carrier contact](ERK10-DEPENDENT-TWO-LABEL-EXCLUSION.md)
are algebra in precisely these pure flags and strict rows.
The original first two active \(r\)-rows 3 and 4 have
distinct nonzero clocks. The reverse analogues use the
same rank-three pure profile and the independently
established no-duplicate property of the weighted
reverse; they do not use its ordinary order six or higher.
The first five reversed positions correspond to actual
physical rows 14,13,12,11,10, unaffected by the missing
origin, which is at the end of reverse chronology.

For every *actual old* pair of grade \(a\) whose numerical
origin entry is zero, and actual reduced reverse pair of
grade \(g\), their paid mixed product at \(a+g\le9\)
equals the integral of their model product by the
[origin mixed theorem](ERK10-ZERO-WEIGHT-INJECTIVE-F4.md#3-origin-only-exact-mixed-recursion-and-weighted-size-nine).
In particular every grade-four companion model **anchored
at original \(X=0\)** below gives a valid context for the
one additional grade-five reversed read. Nothing is
deduced from an unpaid product of two grade-five profiles.

## 2. Carrier and active-label census with 13 live sites

Let \(m\) count carriers. They are all live and their
ordinary pooled weight at \(\theta\) is zero.
Since \(b(s r^j)=0\) for \(j=0,1,2\) (grades \(2,5,8\)),
the carrier contribution to the first two active
moment families vanishes. Thus on noncarrier active
sites we have \(br\) through clock degree six and
\(br^2\) through degree three, exactly as in the
[old pooled census](ERK10-THREE-CARRIER-EXCLUSION.md).
At most \(13-m-1\) live noncarriers are \(r\)-active
(the one live physical endpoint 14 is inactive).
The other original endpoint is still a physical row,
but \(b_1=0\).

If \(m\ge4\), a nonzero \(br\) pool would require eight
distinct active clocks. This forces \(m=4\) and eight
singleton rows with no other live noncarrier site except
physical 14. As in the old endpoint proof, the eight-site
Vandermonde and \(br^2\) moments interpolate their literal
\(r\)-values by a nonzero cubic-or-less \(R\).
The paid \(br\) moment for \(X(1-X)Q(X)\), \(\deg Q\le3\),
then makes \(R\) orthogonal to all such \(Q\) under
\(X(1-X)\), a nonsingular Gram contradiction. If the
pool is zero, every label needs two rows and there
are at most four labels, so \(br^2\) pools zero too.
Every two-row active group cancels ordinary mass.
With at least two distinct active labels the ordinary
support bound is \(13-m-2q\le5\), contradiction.
Thus \(m=2\) or 3.

At most three live carriers, their three amplitude
moments of \(r\), and \(r_2=0\) at a **live** carrier
now force \(r\) identically zero at all carriers:
each distinct value group would have to have zero mass
separately, requiring two physical rows per group.
Thus \(b r^3=0\) really is the noncarrier cubic charge.
The live reverse pure response \(r^\vee=A^\vee s_I\)
is a nonzero multiple of \(r|_I\): it lies in the common
pure \(F_3\) and has value zero at physical 13, where
\(s=1,r=0\), killing its \(s\)-coefficient.
Consequently all paid \(br^j\) clock moments also hold
for the reflected response up to the same nonzero scale.
These reads always come from original order ten and
the common actual **low** response, never from a high
ordinary reversed output.

With \(m=3\), a nonzero pool has at most nine active
rows, and the three possibilities are exactly the old
\((q,n)=(8,8),(8,9),(9,9)\) obstruction:
eight singleton means or a sole (zero-variance) repeated
pair, and the nine-singleton one-pole case.
The entire argument uses original \(br,br^2,br^3\),
ordinary scalar moments, and the true forward
one-dormant grade-nine product if needed.
That mask \(T=R(c)-r-R(\theta)s\) can include the
physical zero-weight origin; its numerical support
and strict crossover are just as before. No step
uses a nonzero value of \(b_1\).
With zero pool, \(q\le4\) and both pooled first
and second moments vanish. Support at least six
forces \(q\le2\) from \(13-3-2q\ge6\).
Then \(F_4=\langle s,r,Cr\rangle\) is clock-invariant,
because \(s\) is an eigenvector and \(r\) is supported
at just those at most two labels. This contradicts
the reviewed incoming gain already in the old
separated grade-four tableau. Thus only \(m=2\) remains.

There are exactly two carriers, physical 2 and 13.
In either orientation the fifth stage cannot be a
carrier because the local quadratic/cubic equations
with its already zero outgoing \(r\)-response would
make it a literal duplicate of the first carrier.
Thus the genuine low-rank
[fifth-head contact](ERK10-FIFTH-HEAD-CONTACT.md)
and [doubled entrance](ERK10-DOUBLED-ENTRANCE-TRIPLET-EXCLUSION.md)
give the actual equal-clock groups 4/5 at \(p=2c_3\)
and 10/11 at \(q'=2c_{12}-1\), with live incoming
repeat taps. Here \(q'\) is a clock, not a count.
These proofs use only actual primitives through
grade four and the no-duplicate circumstances above.
If one later repeat row is dormant, the
genuine Simpson coefficients are likewise low-grade.

## 3. Zero-pooled \(br\): audit of both five-pair topologies

A zero pool has at most five active labels.
If at most four, the four \(br^2\) moments cancel
it sitewise too; the support bound \(13-2-2q\ge6\)
would force \(q\le2\), already impossible by
\(F_4\)-noninvariance. So there are exactly five
active labels in ten physical rows, each an unequal
pair of nonzero ordinary pooled weight, by the
five-node square-moment kernel. If those square
masses were all zero, the pairs and the carriers
would all cancel and only physical 14 would give
ordinary support. The physical \(7|7\) cut and
the actual complete 4/5 and 10/11 pairs thus give
exactly the one- and three-crossing alternatives.

The [one-crossing exclusion](ERK10-FIVE-PAIR-ONE-CROSSING-EXCLUSION.md)
uses only:
* a common grade-four origin-anchored left mask
  and a right mask anchored at physical 14;
* the actual forward \(J P_L\cdot P_R\) and
  \(J^2B_L\cdot P_R\) zero products, both old
  grades \(5+4=9\);
* their reflected analogues, if needed to rule out a
  wholly right initial clock. The reversed unary
  factors of grade five pair with the **original**
  grade-four left mask \(P_L\), which is zero at the
  physical ghost origin because its polynomial has
  factor \(X\). Thus both reflected scalar zero
  identities are paid by the mixed theorem, not by
  ordinary reversed order.
All subsequent ordinary quadrature calculations
use only pooled active weights and anchors, and the
finite degree-six norm uses no assumption \(b_1\ne0\).
Its potential support argument already admits
cancellation at endpoint labels.

The [three-crossing exclusion](ERK10-FIVE-PAIR-THREE-CROSSING-EXCLUSION.md)
uses the true forward one/two-step seams with a
grade-four right lift, then only the actual reversed
one-step \(A^\vee B_R\) at grade **four**, transferred
to the original common flag before multiplying the
old grade-five advance. Its endpoint/clock and
barycentric square-mass checks are ordinary
quadrature identities. If an active label hits an
endpoint, the same potential six-site and fixed
Lobatto argument (or the smaller support
contradiction) is valid without a nonzero origin
weight. The norm uses only that scalar data.
Thus both crossing topologies are closed.

## 4. Nonzero pooled \(br\): audit of all high-label exits

The pooled first-moment kernel gives at least eight
active labels. The old \((8,9)\) one-variance and
\((9,9)\) one-pole cases again use only original
moments and scalar supports and are already gone.
At ten active stages the two forced repeats exclude
nine or ten labels. The only remaining possibilities
are \((8,8)\) and \((8,10)\).

### Eight singleton actives

The literal repeat clocks force both dormant rows
to be physical 5 and 10, since physical 4 and 11
are active. If the two dormant clocks share \(\zeta\),
the low-grade scalar fit gives
\(R=L_4/(X-\zeta)\) by the anchored degree-nine
original moments (the endpoint case is already the
plain endpoint Gram contradiction).
For \(T=R(c)-r-R(\theta)s\), the actual grade-four
\(U=(C-\zeta)T=e_1+e_{14}\) has model \(L_4\).
Consequently \(b_1+b_{14}=\int L_4=1/15\) and
\(b_{14}=\int X L_4=1/30\), forcing \(b_1=1/30\).
This uses only the **first two** original scalar
reads from the [shared dormant packet](ERK10-SHARED-DORMANT-PURE-PORT.md);
we do not use its later common \(F_5\) or endpoint
order-five conclusions.

If the dormant clocks differ, the complete
[distinct-dormant exclusion](ERK10-DISTINCT-DORMANT-SEAM-EXCLUSION.md)
transfers as stated:
* its ordinary \(R\)-weighted quadrature mask and
  endpoint collapses use the physical clocks, not
  an individually nonzero endpoint mass;
* both actual outer contacts and Simpson equations
  use only common genuine grade-four profiles;
* its singleton residue is derived from ordinary
  scalar clock quadrature, whose endpoint kernel
  vanishes at both original 0 and 1;
* its decisive ordinary seam \(\int J P_L P_R=0\)
  is an entirely old forward grade-five by grade-four
  zero product. Its two polynomial lifts and strict
  supports include the old origin even when that
  coordinate has weight zero.
The verified field-valued finite norm thus applies.

### Ten actives, two unequal repeats

The pair moment mean and variance use only the
**original** \(br,br^2,br^3\) moments; the same
polynomial can be reflected because \(r^\vee\) is
proportional to \(r|_I\).
The [paired seam packet](ERK10-FORCED-TWO-ACTIVE-PAIR-SEAMS.md)
needs precisely the following grade-five reads:
1. \(A P_L\) paired with \(P_R\): entirely original,
   grades \(5+4=9\).
2. \(A^2 B_L\) paired with \(P_R\): entirely
   original, grades \(5+4=9\).
3. \((A^\vee)^2 B_R\) paired with \(P_L\): genuine
   reversed grade five. The left \(P_L\)-lift has
   old grade four and **origin coordinate zero**,
   so it is exact by the mixed theorem. The literal
   product is zero because the two reverse steps
   cannot reach the old left half.
The old/reversed linear models agree only through
grade four; this is exactly enough for the corresponding
lifts. The singleton residue, exterior affine norm,
and every anchored quadrature test use old exact
ordinary scalar clock moments, not ordinary high
reversed elementary weights.

The [endpoint/linear exit](ERK10-FORCED-TWO-PAIR-FINITE-EXITS.md)
uses just these contacts, seams, and scalar residue.
The [degree-two norm](ERK10-QUADRATIC-MEAN-EXCLUSION.md)
uses the same three seams and residue, taking their
two exact affine-in-middle-clock eliminands; none
adds a new reverse-order premise.
The [cubic endpoint exit](ERK10-CUBIC-MEAN-ENDPOINT-EXIT.md)
uses the forward two-step seam for \(R(1)=0\)
and the just-paid reflected seam for \(R(0)=0\),
with identical singleton-residue and field checks.

Finally the [cubic crossover exclusion](ERK10-CUBIC-MEAN-CROSSOVER-EXCLUSION.md)
adds one origin-anchored degree-four input in each
direction to the previous two-step forward/reverse
seam. In the reflected zero products its grade-five
unary pairs with the old degree-four **left** mask,
again zero at original physical 1, so these products
also are legitimately paid by the mixed theorem.
In either orientation the split endpoint cancellation
uses the ordinary scalar clock measure and the already
paid \(br\) clock products, not an ordinary grade-nine
reversed tree test. A possibly zero original endpoint
weight is simply a zero contribution in that
cancellation. This kills the literal central response
in both directions. The last three mixed moments
use the actual right response only in **grade four**,
converted to its same-model old lift, before the
original ordinary grade \(8,9,9\) tests.
The characteristic-zero Bézout contradiction therefore
also applies in this last cubic case.

This exhausts all established low-rank carrier and
active-label possibilities for the **sole origin** ghost.
The new algebraic interface is the origin-zero mixed
induction checked in
[ERK10ZeroInjectiveF4Gate.lean](../lean/RKCert/ReviewedNative/ERK10ZeroInjectiveF4Gate.lean);
the finite arithmetic for these specific exits is that
of the linked original packets. No ordinary exactness
of the reduced reverse beyond its stated low grades,
and no nonzero origin weight, is assumed anywhere in
this transfer.
