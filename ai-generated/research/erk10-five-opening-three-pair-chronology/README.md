# Arbitrary post-open timing and the early two-opener exit

This strengthens the [consecutive-closure result](../erk10-five-opening-three-pair-all-open/README.md).
Use the same actual five-opening decoder word budget, ten high rows,
seven distinct nonzero forward clocks, unique first reverse ordinate
\(y=0\), three disjoint paired interior labels and three interior
singletons.

**Post-open theorem.** If the first three reverse interior rows
open the three distinct pairs, no continuation is possible over a
field with \(10!\ne0\) when at most one pair has zero total score.
There are no restrictions on the physical scores or on any later
ordering. Over \(\mathbb Q\) the zero-pool restriction follows from
the [origin-anchored degree-nine scalar floor](../erk-origin-degree-nine-scalar-floor/README.md),
which permits signed and zero weights at every site.

**Full chronology with live openers.** Over a field with \(10!\ne0\),
if the three opening scores and three pair masses are nonzero, no
reverse chronology is possible in this chart. The endpoint,
closing-copy and singleton scores can be zero. This result does
not assert the same arbitrary chronology when an opener or
pair total is zero.

All of these are **conditional architecture exclusions**; no
unrestricted fifteen-stage lower bound follows.

## Skip silent completion targets, not stages

The actual grade definitions and \(D_4\) rank bound are those of the
[main proof](../erk10-five-opening-three-pair-all-open/README.md).
Let \(D_3\) denote its grade-at-most-three subspace, contained in
the opposite-pair space \(S\). Thus every grade-at-most-three
defect at a singleton is zero, irrespective of its score.

Call a completion *ordinary* if it is either a nonzero-score
singleton or the second copy of a nonzero-mass pair. Compare its
group means, dividing by the group score. Zero-score singletons
may be skipped as targets in the comparison: for scalar inputs
\(\boldsymbol w\odot f(\boldsymbol y)\) and the independent
\(D_3\) defect inputs, they contribute zero as donors. There is
no assertion that these physical rows have zero higher defects.

If a zero-total pair has already closed, its two column
coefficients in a \(K\)-row functional combine by subtraction
for **both** scalar and \(D_3\) inputs. Indeed its two physical
scores are opposed (possibly both zero), and the two \(D_3\)
entries are opposed. In other words use \(K_{i,t_1}-K_{i,t_2}\)
against the first-copy coordinate at \(t\), where a missing
column is zero by causality. This rule applies to an ordinary
group mean even if its earlier physical member precedes the
zero-total closure. It is a local identity for the tests, not an
unproved whole-tableau quotient.

## Post-open, no leakage

Use the opening order \(0,a,b,c\) and let \(s,t\) be the first
two ordinary completions, named by their distinct ordinates.
There are always two, as at least two pairs have nonzero mass.
Assume \(D_4\subseteq S\). Then every group mean primitive
payment for \(Y,Y^2,Y^3\) is exact; also \(K\) of any \(D_3\)
input has zero group mean. All earlier donors up to \(s\)
reduce to the opening three nonzero labels, by the preceding
rules.

If at most one opening score is nonzero, the first ordinary
group could only pay its three primitive moments with at most
one nonzero scalar donor label. The first moment then either
fails outright or the second and third assert \(s=3p/2\)
and \(s^2=2p^2\) for the same sole nonzero donor \(p\), impossible.
We may therefore assume at least two live opening scores.
Then \(\dim D_3\ge2\): the first live interior opener \(p\)
has \(u_{p_1}=-w_{p_1}p^2/2\ne0\). If a second label is active
in \(\boldsymbol u\), its clock mark is independent. Otherwise,
at the next live opener the \(Y\) primitive must be paid via
the sole preceding live scalar donor \(p\), creating a nonzero
\(\boldsymbol h=K\boldsymbol u\) entry at that distinct label.
In all cases restriction of \(D_3\) to the three first-copy
coordinates is injective, since its full vectors are opposed
on all pairs.

### First ordinary completion is a pair

Now \(s\in\{a,b,c\}\). Name the other labels \(j,k\).
At the second target \(t\), a second physical donor at \(s\)
is possible but does not add a new scalar label. Nonzero-mass
labels \(j,k\) have only their first physical copy as a donor
at the two comparisons. A zero-total one is treated by the
column-difference rule. Thus the effective scalar taps into
\(j,k\) on the two targets are exactly the entries from the
cubic primitive interpolation
\[
R_j(x)=\frac{x^2}{j(j-s)(j-k)}
       \left(\frac{x^2}{4}-\frac{(s+k)x}{3}+\frac{sk}{2}\right),
\]
and likewise \(R_k(x)\). Here \(t\) can be either a later
closing label or an entirely new singleton. The broader
two-row determinant is
\[
R_j(s)R_k(t)-R_k(s)R_j(t)
=\frac{t^2s^3(t-s)^2}{24jk(s-j)(j-k)(s-k)}\ne0.
\]
Consequently the \(j,k\) opening scores are both nonzero:
otherwise the respective scalar tap column would vanish at
both targets.

Choose a nonzero vector of \(D_3\) whose first \(s\) entry
is zero, possible since \(\dim D_3\ge2\). Both its \(s\)
entries then vanish. Its \(K\) means at \(s,t\) are zero.
Thus the two remaining \(j,k\) entries, divided only by
their now-known nonzero opening scores, are killed by the
nonzero determinant. This holds even if a zero-total
\(j\) or \(k\) already closed, by its same opposite-column
rule. The full \(D_3\) vector would be zero, contradiction.

### First ordinary completion is a singleton

At the first ordinary target \(s\), the row functional
on the three raw opening coordinates annihilates \(D_3\),
and is nonzero by the first primitive payment.
At the second ordinary target \(t\), there is at most one
new scalar donor label \(s\). It has zero \(D_3\) input,
so the old-three part of that row functional again
annihilates \(D_3\). This assertion uses the actual raw
column coefficients, combining any closed zero-total pair
by subtraction; it does not require nonzero scores at its
old columns. The annihilator on the three opener
coordinates is at most one-dimensional, so the old-three
part is a scalar \(\ell\) times the first target's row.
Consequently its contributions to the first three scalar
primitive payments are \(\ell(s^2/2,s^3/3,s^4/4)\).
The new singleton tap contributes \(T(s,s^2,s^3)\).
The three resulting equations force \(t^2(t-s)^2=0\)
by the same fraction-free square combination. This
contradicts the distinct nonzero ordinates.

## Post-open, leakage

If \(D_4\not\subseteq S\), the local **opening** analysis of
the [zero-score addendum](../erk10-five-opening-three-pair-all-open/ZERO-SCORES.md)
applies to the same first four rows, and depends only on the
vanishing of low-grade group sums, not of scores.
With at least two live openers it either deletes a zero-score
inert stage while preserving dimension three, already impossible,
or gives two grade-at-most-three opposite modes at \(a,b\) and a
clean \(c_1\) of nonzero score. Use the group-mean calibration
against \(c_1\) from the main proof. Until an ordinary completion,
the only possible preceding changes are the zero-donor target
omissions described above. They do not affect the scalar tap
calibration: a newly duplicated \(a,b\) has zero total and thus
is matched by the corresponding opposed mode, while a newly
duplicated \(c\) adds only a second copy of the same label.
Therefore the square identity forces the first ordinary target
to have clock \(c\), and it must be the ordinary closure of \(c\).
At the second ordinary target \(a,b\) still add no nonzero-total
closed mode, so the same square again demands clock \(c\).
Contradiction.

If no opener is live, even an earlier zero-total completion
does not provide a live donor, so the first primitive payment
at the first ordinary target fails. If just one opener \(p\)
is live, odd profiles at \(p\) track its scalar tap even if
its zero-total pair has closed. At the first ordinary target
the exact \(Y,Y^2\) payments force a nonzero effective scalar
tap from \(p\). Vanishing of the \(K\boldsymbol u\) mean requires
a second active \(\boldsymbol u\) label, since
\(u_{p_1}=-w_{p_1}p^2/2\). This is precisely the local
inert-third-opener argument of the zero-score and zero-total
addenda; its deletion contradiction does not depend on
whether the ordinary target was a singleton or a pair.
This completes all post-open timing cases.

## Chronologies with an early ordinary completion, live openers and pools

Now assume all three opening scores and group masses are nonzero,
but do not assume the chronology starts with all three openings.
We may skip zero-score singleton appearances as donors for the
actual \(D_3\) and scalar tests, as explained above. Let \(z\)
be the first ordinary completion (which can be a new live
singleton or a pair closure). If all three pairs already opened,
the post-open proof applies unchanged: any intervening zero-score
singletons have neither scalar nor low-grade defect input, and
the original first-copy formulas and all subsequent arguments
are unchanged by omitting those inputs.

If there is no preceding pair opener, the first scalar
positive-degree primitive can't be paid at \(z\).
If there is just one preceding opener \(a\), its known
\(u_{a_1}=-w_{a_1}a^2/2\ne0\) and the grouped
\(K\boldsymbol u\) test kill the only effective scalar tap.
Again the first primitive payment fails. This applies even
if \(z\) closes \(a\): only the first \(a\)-copy could have
contributed to its group mean.

It remains that the first ordinary completion \(z\) is
preceded by **two** openers \(a,b\). Their two opening
scores are live. If \(D_4\subseteq S\), the two exact tests
on \(K\boldsymbol u\) and \(K(\boldsymbol y\odot\boldsymbol u)\)
at \(z\) kill the tap into \(a_1\): use its nonzero
\(u_{a_1}\), and the two distinct labels \(a,b\).
A single remaining donor \(b_1\) cannot pay
\(Y,Y^2,Y^3\) as above.

In the leakage case the chronological first two openers
\(a,b\), both live, force two separate modes at \(a,b\).
Indeed if \(\boldsymbol u\) has two active labels, it
and its mark separate them, while inactivity of \(b\)
would supply a third direction from \(h_{b_1}\ne0\)
if those two active labels were \(a,c\). If only \(a\)
is active, \(h_{b_1}\ne0\), and any further support of
\(\boldsymbol h\) at \(c\) gives two separate \(b,c\) modes
using its mark. These are exactly the earlier local
arguments and require only that no other live score or
defect donor preceded the first \(a,b\). Hence there are
a pair mode at each of \(a,b\), of grade at most three,
and any third opener \(c_1\) is clean in the \(\boldsymbol
u,\boldsymbol g,\boldsymbol h\) profiles.

At \(z\), the actual first two positive moments are
exact and at least one scalar tap is nonzero. These taps
are the group means of \(K\) of the two modes normalized
to the opening scores, because no pair has yet closed.
It follows that the mean at \(z\) is a nonzero functional
on the one-dimensional \(D_4/\operatorname{span}
(\boldsymbol V_a,\boldsymbol V_b)\), even if \(z\) is
itself the first closure. Use this mean as a reference.
As the next target \(x\), take the earliest of the
third opener and the next ordinary completion. It has
nonzero score if an opener, nonzero mean divisor
otherwise, and all its first and second primitive
payments are exact (clean \(c\) if it is an opener).
A target necessarily exists since there remain
unclosed nonzero-total pairs.

At \(x\), all scalar taps on the original \(a,b\) other than
at label \(z\) are thus determined by the same quotient
coefficient \(\ell\) times their taps at the reference \(z\).
This is true because those respective donors still have
only their first copies. If \(z\) is a singleton, its
new scalar tap is not calibrated, as its two pair
modes are zero there. If \(z\) closed \(a\) or \(b\), the
total tap at its duplicated label can differ from its
calibrated reference tap by a scalar \(T\). In either case
the only unrestricted scalar correction is \(T\) at label
\(z\). The reference's \(\boldsymbol k\) mean also scales
by \(\ell\) because it belongs to \(D_4\). Subtracting it
reduces the three primitive equations to
\[
 z^2\ell+2zT=x^2,\qquad z^3\ell+3z^2T=x^3,\qquad
 z^4\ell+4z^3T=x^4 .
\]
The same square forces \(x=z\), impossible. No new
coefficient restriction, such as positivity or a
normalized scoring ratio, has been used.

## Replay

    python3 -B audit.py
    # From the repository root:
    sha256sum -c ai-generated/research/erk10-five-opening-three-pair-chronology/sources.sha256

The scalar cross determinant, quotient cancellation and rank-one
donor factors have independent exact arithmetic checks. The full
physical-chart bridge is mathematical rather than a Lean endpoint.
