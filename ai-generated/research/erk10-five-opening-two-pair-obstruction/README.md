# Two-pair ten-high obstruction from actual reverse defect rank

This rules out two classes of high blocks in the
[five-opening decoder](../erk10-five-opening-nonsplit-kernel/README.md):
two active paired first-primitive defects, or only one active
pair when both raw grade-three defects have zero grouped sums.
The result uses the **actual** reverse word budget proved there,
not additional high co-order assumptions. It does not exclude
a one-active pair with grade-three aggregate leakage, other scalar
site counts, or an arbitrary 15-stage ERK10 tableau.

Use a field with \(10!\ne0\). The ten physical high rows have
eight distinct nonzero scalar forward clocks, one being the
unique \(1\) in the **first reverse row**. Exactly two interior
labels occur twice and all other labels are singletons. Every
physical high output share is nonzero, and the grouped masses of
the two pairs are nonzero. No sign assumption is made. Use the
literal high weighted transpose \(L\), write \(y_i=1-x_i\),
and take scalar quadrature from the high scores and the opening
origin exact through degree nine. The scope includes any high
block with the word budget regardless of how it was constructed;
in particular the high forward cubic gate need not be used again
in the obstruction.

## The rank bound paid by actual forward errors

Let the weight-scaled reverse operator be \(K\), so that
\(K(\boldsymbol w\odot \boldsymbol v)=
\boldsymbol w\odot L\boldsymbol v\). Reverse word defects of
grade at most four are the differences between actual words
in \(K\) and clock marks acting on \(\boldsymbol w\) and their
nominal integral-model vectors. Each annihilates
\(X,\ldots,X^5\) by the order-ten word budget. They are disjoint
from the five-dimensional nominal space
\(\boldsymbol w\,\mathcal P_4\): the pairing of the latter with
\(X,\ldots,X^5\) is the shifted Hilbert moment matrix
\((1/(i+j+2))_{0\le i,j<5}\), with determinant
\(1/(2^{12}3^7 5^5 7^4)\).
The origin mass contributes zero to these moments.

Every forward residual \(T_f=BEf-EJf\), for \(f\) among
\(X,X^2,X^3,X^4\), annihilates all actual reverse words through
grade four. Indeed, pair its two terms with each word and use
the paid tests on \(Jf\) and on \(f\) after one primitive;
the two nominal integrals coincide and both total degrees
are at most nine. The span of \(T_f\) has dimension at least
two. At the first forward high clock \(h\) the residual row
is \(-J_h f\). At the first different clock \(z\), earlier
rows can supply only \(h\), with total tap \(\gamma\), so
the residual row is \(\gamma f(h)-J_z f\).
If these were proportional, writing \(r=z/h\), the
three powers \(r^2,r^3,r^4\) would be affine in their
exponents. Their second difference is \(r^2(r-1)^2\ne0\).
This also covers multiple earlier copies of \(h\).

It follows that actual observers through grade four have rank
at most eight, and their defect subspace therefore has rank
at most **three**. Neither a fixed output placement of the
pairs nor literal raw \(L\boldsymbol1=\boldsymbol y\) is needed.

## Paired directions and one aggregate line

Write the raw first and second reflected defects and the actual
composed defect as
\[
 \boldsymbol u=L\boldsymbol y-\boldsymbol y^{\odot2}/2,\quad
 \boldsymbol g=L\boldsymbol y^{\odot2}-\boldsymbol y^{\odot3}/3,
 \quad \boldsymbol h=L\boldsymbol u .
\]
Their weight-scaled grades are \(2,3,3\). At the initial
reverse row \(y=0\), every one of them is zero. At grade two
the seven nonzero forward moments \(X,\ldots,X^7\) make every
group sum of \(\boldsymbol u\) zero, by the Vandermonde on the
seven interiors. Thus \(\boldsymbol u\) is supported only
on the two pairs and either pair's vector is either zero or
opposed in its two weighted coordinates. Say it is *active*
if nonzero. The first reverse interior must be at an active
pair, because it can read only \(y=0\) and has
\(u=-y^2/2\ne0\).

If both pairs are active, the two marked profiles
\(\boldsymbol w\odot\boldsymbol u\) and
\(\boldsymbol w\odot\boldsymbol y\odot\boldsymbol u\)
span the entire two-dimensional pair-difference space.
Any nonzero aggregate of a grade-three defect would be
the seven-site cofactor line (only \(X,\ldots,X^6\)
must vanish), supported at all seven distinct labels.
It and its clock mark have independent aggregates,
since the labels differ. With the two paired directions
they would give grade-four rank at least four, impossible.
In particular \(\boldsymbol g,\boldsymbol h\) have zero
grouped sums. In this case every pair is an exact grouped
first/second/composed read; every singleton is exact
individually. All grade-four defects have **at most one**
independent aggregate, since two dimensions are occupied
by the opposed pair directions.

The same last conclusion holds in the other case examined
below: only one active pair, but the grouped \(\boldsymbol g\)
and \(\boldsymbol h\) sums are zero. There we will find the
second opposed direction in \(\boldsymbol h\) itself.

## Two active pairs: all early placements

Let \(a,b\) be the two paired reverse ordinates. After the
first interior occurrence at \(a\), its pair cannot close
before a different nonzero ordinate appears. If it did,
its first and second grouped reads would satisfy
\((L\boldsymbol y^{\odot2})_a=a(L\boldsymbol y)_a\),
inconsistent with \(a^3/3\) and \(a^2/2\).
Nor can the next interior be a singleton: its only available
nonzero-clock donor would have \(u=-a^2/2\), and requiring
\(L\boldsymbol u=0\) at the singleton kills that tap.
Thus the first two interior physical rows are first copies
of the two pairs.

If the next row completes one pair, call its ordinate \(a\)
(swapping names if necessary), and let \(b\) be the open
pair. Consider the grade-four defects
\(\boldsymbol k=L\boldsymbol y^{\odot3}-\boldsymbol y^{\odot4}/4\)
and \(\boldsymbol q=L((\boldsymbol y-a)\odot\boldsymbol u)\).
Here \(\boldsymbol q\) reads only the open pair's \(\boldsymbol u\).
On the completed group and on the next physical group
(a singleton or completion of the open pair), the only
earlier reverse ordinates are \(0,a,b\); among copies
at \(b\), only the first can be read. Consequently the
group means of the two defects, at either relevant
ordinate \(z\), are
\[
 \frac{k_z}{z^2}=-z^2/4+(a+b)z/3-ab/2,\qquad
 \frac{q_z}{z^2}=\frac{u_{b,1}}{6b}(2z-3a).
\]
The first identity uses \(y^3=(a+b)y^2-ab y\) on earlier
clocks. The second reads the coefficient on the unique
earlier \(b\) from \(Ly^2-aLy\); its \(u_{b,1}\ne0\).
It applies equally to both rows of a group when their
earlier supports are smaller. These two aggregate
vectors would have to be proportional. Their two-by-two
minor at the completed \(a\) and the next \(z\) is a
nonzero multiple of \(-a(z-a)^2/24\), as checked in the
[exact determinant replay](exact-audit.txt). This is
impossible. It covers complete interleaving, nested
interleaving, and a singleton before completion of the
other pair.

There remains a first singleton \(t\) **before either
pair closes**. It reads only \(0,a,b\).
The paid first and second moments force taps onto \(a,b\)
of
\[
 \frac{t^2(3b-2t)}{6a(b-a)},\qquad
 \frac{t^2(2t-3a)}{6b(b-a)}.
\]
Neither can be zero: then \(L\boldsymbol u=0\) would
force the other to vanish, as both two first-copy
\(u\)-values are nonzero. In particular
\(2t\ne3a,3b\). Fit the two \(u\)-values by
\(\gamma Y(Y-2t/3)\). This follows by writing their
unique model \(Y(\gamma Y+\delta)\) and applying the
exact helper's \(L\boldsymbol u=0\) along with the two
paid moments. Its value at \(t\) is \(\gamma t^2/3\),
whereas the actual helper has \(u=0\).
Thus at the very next physical row (including the
aggregate if it closes a pair), at clock \(z\),
the paid \(L\boldsymbol u\)-test determines its total tap
onto \(t\) as \(z^2(z-t)/t^2\). All predecessor copies
are still the first at each \(a,b,t\); if the next row
closes a pair, name its label \(a\). On \(t\) and \(z\)
this gives the new normalized functions
\[
\begin{aligned}
 F(z)&=-z^2/4+(a+b)z/3-ab/2+(z-t)(t-a)(t-b)/t,\\
 Q(z)&=(2z-3a)/6-(t-a)(z-t)/t ,
\end{aligned}
\]
for \(\boldsymbol k\) and \(\boldsymbol q\) after removing
the same nonzero scalar row/mode factors as above.
For \(\boldsymbol k\), the extra cubic term is the
literal tap onto \(t\) times \(t(t-a)(t-b)\).
For \(\boldsymbol q\), the extra tap subtracts its
contribution to \(Ly^2-aLy\). These formulas are also
valid at \(z=t\), where the tap on \(t\) is zero.
Their minor \(F(z)Q(t)-F(t)Q(z)\) is
\(-(z-t)^2(2t-3a)/24\), nonzero. This rules out a
first pair closure **or a second singleton** immediately
after the first helper. Every first possible placement
has now been addressed.

## One active pair and exact grouped grade-three reads

Assume only \(a\) is active and both \(\boldsymbol g\)
and \(\boldsymbol h\) have zero group sums. As above the
first pair cannot close before a distinct label. The next
distinct clock \(b\) cannot be a singleton: it has \(u=0\)
and must read \(a\) by \(b^2/(2a)\), causing
\(h=-ab^2/4\ne0\). It is therefore the first copy of the
inactive pair. On group \(a\) the first \(h\)-value is
zero, so both are zero by aggregate opposition and
nonzero shares. Thus \(\boldsymbol h\) is a nonzero
opposed mode supported **only at \(b\)**. With
\(\boldsymbol u\) it occupies two dimensions of the
grade-four defect space, leaving at most one aggregate
line as before.

If \(a\) is completed immediately, use the same
no-helper determinant with \(\boldsymbol q=L\boldsymbol h\).
Its only input is the first \(b\), and its raw mean is
the same polynomial \(z^2(2z-3a)/(6b)\) times
\(h_{b,1}/(b-a)\), a nonzero scale.
If \(b\) is completed before \(a\) and before any
singleton, \(L\boldsymbol u=0\) in its aggregate
kills the total tap onto the sole earlier \(a\)-copy.
On the remaining effective donors \(0,b\) its two
grouped primitive moments are incompatible.

Finally if a first singleton \(t\) occurs before
either closure, \(L\boldsymbol u=0\) kills its tap
onto \(a\), leaving only \(b\). Hence \(t=3b/2\).
At the very next physical row (possibly closing either
pair), that same paid \(\boldsymbol h\)-test again
kills the **mean** tap onto the only earlier \(a\)-copy,
including any such read at the other physical occurrence
of a just-completed group. The effective scalar donors
at \(t\) and at this next group are thus \(0,b,t\).
The profile \(L\boldsymbol h\) uses the single earlier
\(b\)-row's nonzero \(h_{b,1}\), with no \(a\) or \(t\)
input. Now the no-helper two-clock determinant applies
using \(t\) as the completed comparison clock, and \(b\)
as the one visible donor mode. It forces the next clock
to equal \(t\), impossible for a singleton. This exhausts
the aggregate-exact one-active case.

## Reproduce

    python3 -B audit.py
    sha256sum -c sha256.txt

The symbolic replay checks the complete scalar arithmetic including
both determinant factorizations and the paid Hilbert pivot. The
separate Lean identities check the two fraction-free determinants.
The filtration, actual observer rank, and chronology are
mathematical conditional results, not native all-tableau floors.
