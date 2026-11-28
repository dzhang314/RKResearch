# Full five-opening seven-label, three-pair chart exit

The [paid-field extension](ALL-PAID-FIELDS.md) removes the pair-total
restriction in the original proof below and gives a consequence over
commutative rings with \(10!\) invertible.

**Theorem.** Take the actual five-opening decoder reverse word budget
at order ten. Suppose the ten high rows have exactly seven distinct
nonzero forward clocks, with the unique clock 1 in the first reverse
row. Three of the other six clock labels occur twice and the other
three are singletons. Then the chart is impossible over **\(\mathbb Q\)**,
with no assumptions on ordering, individual weights, or pooled
weights. Over any field with \(10!\ne0\), the proof covers all orders
and scores provided at most one of the three pairs has zero total
score. These are architectural exclusions, not unrestricted ERK10
stage floors.

Indeed, in the rational situation at most one pair can have zero
total, by the [origin-anchored quadrature parity floor](../erk-origin-degree-nine-scalar-floor/README.md).
Two vanishing pools leave at most six permitted scalar sites
including the opening origin; parity excludes this even with signed
or zero weights at all remaining locations.

We build on the exact short words of the
[five-opening decoder](../erk10-five-opening-nonsplit-kernel/README.md),
the [score-weighted scalar gates](../erk10-five-opening-three-pair-all-open/README.md),
and the [post-open two-target argument](../erk10-five-opening-three-pair-chronology/README.md).
The new steps handle every zero-score or zero-total timing pattern
when the first live completion is early, and allow actual ghost taps
in the late-completion case. No division by a physical zero score is
used.

## Notation: actual observers and effective columns

Use raw reverse \(K=B^T\), clocks \(\boldsymbol y=\boldsymbol
1-\boldsymbol x\), scores \(\boldsymbol w\), and the grade-one
defect \(\boldsymbol v=K\boldsymbol w-\boldsymbol w\odot\boldsymbol y\).
The defects \(\boldsymbol u,\boldsymbol g,\boldsymbol h,\boldsymbol k\)
are as in the earlier proof, with grades \(2,3,3,4\).
Let \(D_3,D_4\) be the corresponding full defect spaces through those
grades and \(S\) the three-dimensional opposite-pair space.
Actual short tests give \(D_3\subseteq S\), \(\dim D_4\le3\).
Applying \(K\) or a clock mark increases the grade by at most one.

Call a completion *ordinary* if it is a nonzero-score singleton or
the second copy of a nonzero-total pair. There are at least two
ordinary completions, since at least two pairs have nonzero total.
Define the group mean at an ordinary completion by summing and
dividing by its nonzero total. A row-mean may include both members
of its pair even though only the first can be a donor at that stage.
Unavailable donor columns are zero by strict causality.

A zero-score singleton has zero coordinate in every actual reverse
observer through grade three: its nominal terms have a score factor,
and its \(D_3\) defects vanish since \(D_3\subseteq S\).
It can therefore be skipped as a **donor for the low tests**; this
does not delete a physical stage or suppress its higher-order
defects. If a zero-total pair has already closed, its two coefficients
combine by subtraction for all scalar and \(D_3\) inputs. Their
coordinates are opposite, both for its two scores and for every
\(D_3\) vector. We use this effective first-copy coefficient even
when the pair has two zero physical scores. An unclosed pair
contributes only its first copy. Before the first ordinary
completion, these are all the possible nonzero-ordinate donors.

## No leakage

Suppose \(D_4\subseteq S\). Every ordinary group has its first three
primitive moments \(Y,Y^2,Y^3\) exact, and \(K D_3\) has zero mean
there. If fewer than three pairs have opened at the first ordinary
completion, there are at most two distinct nonzero-ordinate donors.
With two nonzero opening scores \(a,b\), the exact tests
\(K\boldsymbol u\) and \(K(\boldsymbol y\odot\boldsymbol u)\) kill the
individual effective coefficient into \(a_1\), since
\(u_{a_1}=-w_{a_1}a^2/2\ne0\) and \(a\ne b\). This holds even
if the earlier \(a\) or \(b\) is a folded zero-total pair.
There is now at most one nonzero scalar donor, as there also is
when the original live donor count is below two. With no such
donor the first moment fails. With only one, \(p\), the first two
moments force the target \(z=3p/2\), whereas the first and third
force \(z^2=2p^2\), impossible.

If all three pairs have opened before the first ordinary target,
at least two of their opening scores must therefore be nonzero.
The first live opener has nonzero \(\boldsymbol u\).
If any other label is \(\boldsymbol u\)-active, its mark makes
\(\dim D_3\ge2\). Otherwise the second live opener, to have its
exact \(Y\) moment, must have a nonzero effective tap into the
first live opener, producing a nonzero \(\boldsymbol h=K\boldsymbol
u\) and the same rank. Any earlier folded zero-total pair and
zero-score singleton is accounted for by the effective columns.

Apply the [post-open no-leakage argument](../erk10-five-opening-three-pair-chronology/README.md#post-open-no-leakage).
It uses only the first two ordinary target groups and those three
effective opener coordinates: if the first target is a pair, the
free second-target two-column determinant is nonzero; if a
singleton, the old-three part of both group functionals belongs
to the one-dimensional annihilator of \(D_3\), and the extra
singleton tap yields a nonzero square. Neither proof needs the
earlier physical openers to be consecutive, since the effective
column rules here remove every intervening donor. Thus no
no-leakage timing is possible.

## Leakage, first ordinary completion before all pairs open

Suppose \(D_4\not\subseteq S\), so \(\dim(D_4\cap S)\le2\).
Under this assumption a first ordinary completion cannot have
zero live preceding scalar labels, by its \(Y\) moment. If only one
pair has opened, its first score must then be nonzero, with
nonzero \(\boldsymbol u\) at that opening. Whether open or folded,
the grouped \(K\boldsymbol u\) test kills its unique scalar tap,
contradicting the same \(Y\) moment.

It remains that two pairs \(a,b\) have opened before the first
ordinary completion \(z\). Their separate pair modes in \(D_3\)
are forced, with either number of live opening coefficients:

* If both opening scores are live, the first opener \(a\) has
  nonzero \(\boldsymbol u\), and the second has either nonzero
  \(\boldsymbol u\) or, if not, nonzero \(\boldsymbol h\) by its
  \(Y\)-moment payment from \(a\). That payment remains valid if
  \(a\) already closed with zero total. The first \(a\)-entry of
  \(\boldsymbol h\) is zero, hence so is its second. The
  [two-mode argument](../erk10-five-opening-three-pair-all-open/README.md#branch-2-grade-four-leakage)
  shows here that \(a,b\) carry separate modes: if \(\boldsymbol u\)
  is active on two labels, they must be \(a,b\), else
  \(\boldsymbol h\) gives an independent \(b\) mode; if only \(a\)
  is active, the mark of \(\boldsymbol h\) rules out any additional
  \(c\)-support. Three active \(\boldsymbol u\) labels are impossible
  by its two marks.
* If just one opener \(p\) is live, its first copy has nonzero
  \(\boldsymbol u\). It supplies the sole available scalar label
  for the exact \(Y\)-moment mean at \(z\). The same effective tap
  times \(u_{p_1}/w_{p_1}\ne0\) appears in the \(K\boldsymbol u\)
  mean. Thus the other score-zero opener must be active in
  \(\boldsymbol u\), to cancel that mean. Its first copy alone or
  its folded zero-total pair supplies that possibility.
  The two clock labels in \(\boldsymbol u\) supply separate modes
  with its grade-three mark; no third active label is possible.

In either case the \(a,b\) modes occupy \(D_4\cap S\). Every
\(D_3\) defect at the still-unopened \(c\) pair is zero.
At the reference group \(z\), normalization of the mode on each
live opener to its first score tracks its scalar tap via \(K\).
This remains true for an already closed zero-total pair, and the
scalar tap on a zero opener is simply zero. At least one such
tracked tap is nonzero by the \(Y\) payment, so the reference mean
is nonzero on the one-dimensional \(D_4/S_{ab}\), where
\(S_{ab}\) is the span of those two modes.

Choose the next target to be the earliest of the next ordinary
completion and the first nonzero-score copy of the still-unopened
label \(c\) **if this is its opening copy**. Such a target exists:
there are at least two ordinary completions in total. A score-zero
opener \(c_1\) can instead be skipped: all its scalar and \(D_3\)
inputs are zero, and any later nonzero-total \(c\) closure itself
counts as ordinary. A zero-total \(c\) can also close in between
when both its scores are zero, without adding any such input.
If the target is \(c_1\) with nonzero score, it is clean at
\(\boldsymbol u,\boldsymbol g\) and we divide by that score.
Otherwise its \(Y,Y^2\) group means are exact in the usual way.

The target has ordinate \(x\ne z\). Until then no new uncontrolled
scalar donor label other than \(z\) can intervene: a zero-total
completion of \(a\) or \(b\) is still matched by its opposed mode,
and zero-score singletons have no low inputs. If \(z\) was a pair
closure, the second copy there can change its total scalar tap;
if \(z\) was a singleton, its added scalar tap is freely available.
Write that one extra amount \(T\) at \(z\). Every remaining effective
scalar tap from \(a,b\) scales by a common quotient coefficient
\(\ell\), from comparing the \(D_4/S_{ab}\) means of \(K\) of
the unique mode at each nonzero-score opener. A zero opener at a
different label still has no scalar tap. The \(\boldsymbol k\)
mean also scales by \(\ell\). The resulting three equations are
\[
 z^2\ell+2zT=x^2,\qquad z^3\ell+3z^2T=x^3,\qquad
 z^4\ell+4z^3T=x^4.
\]
Their fraction-free combination gives \(x^2(x-z)^2=0\),
contradicting the distinct nonzero target.

## Leakage, first ordinary completion after all three pairs open

Write the opener order as \(a,b,c\), disregarding intervening
zero-score singleton donors and any folded zero-total closure.
If no opener is live, the first ordinary \(Y\) moment fails.
If exactly one opener \(p\) is live, its nonzero mean \(Y\)-tap
forces another \(\boldsymbol u\)-active opening label \(r\) by
the exact \(K\boldsymbol u\) mean, as in the early case. This
includes the possibility that \(p\) or \(r\) is a closed zero-total
pair. The \(p,r\) modes therefore occupy \(D_4\cap S\), and the
last score-zero opener \(q\) is zero at every \(D_3\) profile.

If at least two openers are live, the following elementary
local cases exhaust the possible score zeros. All effective
taps here allow earlier pairs of zero total by subtraction.

* If \(a,b\) are live, the preceding two-live-opener argument
  gives their separate modes. If \(c\) is live it is the clean
  reference; otherwise \(c\) is a score-zero opener with all
  \(D_3\) entries zero.
* If \(a\) is score-zero and \(b,c\) are live, \(u_{a_1}=0\) and
  \(u_{b_1}\ne0\). If \(u_{c_1}\ne0\), the two clock modes are
  \(b,c\). Otherwise its exact \(Y\) primitive comes solely from
  \(b\); this gives \(h_{c_1}\ne0\), with \(h_{a_1}=h_{b_1}=0\).
  The same two modes occupy \(D_4\cap S\) and \(a\) is invisible
  to all of \(D_3\).
* If \(b\) is score-zero, \(a,c\) are live. If \(u_{b_1}\ne0\),
  the two \(\boldsymbol u\) modes are \(a,b\) and \(c\) is the
  clean live reference. Otherwise \(u_{b_1}=0\) kills the
  effective \(Y\)-tap to \(a\), hence \(h_{b_1}=0\).
  Either \(u_{c_1}\ne0\) directly, or exactness of its \(Y\)
  primitive from the sole scalar donor \(a\) gives
  \(h_{c_1}\ne0\). Thus \(a,c\) are the two modes and \(b\)
  is the invisible opener.

In the clean-live-\(c\) case, the earlier
[post-open leakage square](../erk10-five-opening-three-pair-chronology/README.md#post-open-leakage)
applies starting at \(c_1\). Its predecessor \(a,b\) scalar
taps are calibrated by their modes even through any zero-total
closure (or are zero on a zero opener), and ghosts have no
low inputs. The first ordinary completion is forced to be
\(c\), and the second then would be \(c\) again, impossible.

In the remaining cases there is an opener \(q_1\) with zero score
and zero at every \(D_3\) profile, while \(\dim D_4=3\).
We do **not** claim that its full row of \(K\) vanishes. Instead
we show that its first-copy coordinate is zero in every actual
observer through grade four.

At \(q_1\), before any ordinary completion, contributions from
earlier zero-score singleton ghosts are already zero on all
scalar and \(D_3\) inputs. If two other openers were live, the
equalities \(u_{q_1}=g_{q_1}=0\) kill their earlier effective
coefficients by the two distinct \(Y,Y^2\) equations (if only
one is earlier, the first equation suffices). If just one \(p\)
was live, \(u_{q_1}=0\) kills its earlier coefficient when present,
and \(h_{q_1}=0\) then kills the earlier coefficient at the sole
other score-zero opener \(r\) when present, since \(u_{r_1}\ne0\).
These are effective coefficients: if an earlier zero-total pair
has both physical copies, cancellation by subtraction applies
to **every** one of the low inputs, including \(\boldsymbol u\).
Finally \(v_{q_1}=0\) kills the remaining endpoint contribution
\(K_{q_1,0}w_0\), without dividing by \(w_0\). The endpoint has
zero \(D_3\) entries and only its constant nominal profile is
potentially nonzero.

It follows that \(K\) of every actual observer through grade
three vanishes at \(q_1\); a final clock mark also vanishes
there, and so does the nominal grade-four profile because
\(w_{q_1}=0\). Thus the coordinate functional at this row
annihilates the actual grade-four observer space and the
nominal powers.

This functional is independent of the two forward residual
annihilators. Indeed at least two distinct nonzero-total pair
closures have yet to occur after all three openers, so the
reverse suffix strictly later than \(q_1\) contains at least two
distinct clocks. In forward order the first clock and first
different clock are therefore both away from \(q_1\), in that
suffix. The forward two-row independence proof for \(BEf-EJf\)
works on those same coordinates. Hence there are two residual
annihilators whose joint span contains no nonzero multiple of
the \(q_1\)-coordinate functional. This is an extra third
annihilator of an observer space of dimension at least
\(5+\dim D_4=8\) in ten rows, contradiction. This last step is
why a physical tap into a zero-score ghost cannot rescue the
proof branch. All timing and score patterns are now exhausted.

## Reproduce

Replay the [three-pair arithmetic](../erk10-five-opening-three-pair-all-open/audit.py)
and [free second-target arithmetic](../erk10-five-opening-three-pair-chronology/audit.py).
A [standalone symbolic verification](audit.py) in this packet also
checks the ghost-blind two-label determinant, the folded modes
including zero scores, and the forward residual dot-product ledger.

    python3 -B audit.py
    # From the overlay/repository root:
    sha256sum -c ai-generated/research/erk10-five-opening-three-pair-complete/sources.sha256

No claim is made that the rank/chronology reduction as a whole is a
native theorem on the RK tableau predicate.

The [portable scalar lemmas](../../lean/RKCert/ReviewedNative/ERK10FiveOpeningThreePairScalars.lean)
check the cleared primitive tap and consecutive two-closure determinant,
the live determinant exit, and the leakage square on Lean 4.34.1,
4.35.0, 4.36.0 and 4.37.0-rc1. The arbitrary chronology proof above
is mathematical; the scalar formalization does not substitute for it.
