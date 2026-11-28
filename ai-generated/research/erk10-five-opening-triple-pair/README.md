# ERK10: the regular seven-label triple-and-pair chart is impossible

The [zero-pool closure](ZERO-TRIPLE-POOL.md) now treats all pooled and
physical scores, completing the guarded seven-label census.

The [zero-opening extension](ZERO-OPENINGS.md) removes all individual
score assumptions; only the two nonzero pooled scores are still needed.

**Theorem.** Use the
[actual five-opening reverse word budget](../erk10-five-opening-nonsplit-kernel/README.md)
at order ten, with ten physical high rows and seven distinct nonzero
forward clocks. The unique clock 1 is the first reverse row.
Among the six distinct nonzero reverse ordinates, let \(a\) occur
three times and \(b\) twice, with the other four labels singletons.
Suppose the first scores at \(a,b\), and the two total scores
at those labels, are nonzero. Then the chart is impossible over
every field with \(10!\ne0\), for arbitrary chronology. All other
physical scores, including the second triple copy, may be zero.
Neither signs nor ordering of the field is used.

This is an architecture-specific exclusion. It does not cover a
zero first score or zero grouped score at a repeated label.
The endpoint assumptions are the same as in the
[three-pair](../erk10-five-opening-three-pair-complete/README.md)
and [fourfold](../erk10-five-opening-fourfold-interior/README.md)
exclusions.

## Actual observers and ordinary targets

Use score-weighted raw \(K=B^T\) in reverse order. The force of
the word tests is as in the earlier two packets: the space \(D_3\)
of actual defects through grade three is contained in the
label-sum kernel \(S=S_a\oplus S_b\) (only the repeated labels
can be supported), and the defect space \(D_4\) has dimension at
most three. Write \(\boldsymbol u,\boldsymbol g,\boldsymbol h,
\boldsymbol k\) for the first, second, composed and third
primitive defects of grades \(2,3,3,4\), with
\(\boldsymbol h=K\boldsymbol u\). Clock marks and \(K\) raise
the grade by at most one. A group mean divides a group sum
only by its nonzero total score.

Call a singleton of nonzero score, or the last copy of either
repeated group, an **ordinary target**. Each has exact first
and second primitive moments and \(K\boldsymbol u\) mean.
There are at least two live singletons by the
[shifted Hilbert support factorization](../erk10-five-opening-three-pair-complete/ALL-PAID-FIELDS.md):
at least four distinct interior labels have nonzero total, and
only \(a,b\) are repeated. A zero-score singleton carries zero
scalar and \(D_3\) input and may be omitted as a donor in these
tests. This does not delete any higher-order stage. Before the
first ordinary target the only possible repeated-label donors
are \(a_1,a_2,b_1\), not necessarily all present.

## No leakage

If \(D_4\subseteq S\), the three primitive moments through
source \(Y^3\) are exact at every ordinary target, and \(K D_3\)
has zero mean there. With only one nonzero-ordinate scalar
donor label they are inconsistent: \(z=3p/2\) and \(z^2=2p^2\)
would both be required at the first target.

If the first ordinary target \(z\) has repeated label, its scalar
donor ordinates belong to \(0,a,b\). The cubic primitive of
\(Y(Y-a)(Y-b)\) must vanish at \(z\), which forces \(a=2b\)
when \(z=a\), or \(b=2a\) when \(z=b\).
In either case that primitive has the form
\(-Y^2(Y-z)^2/4\) up to an overall nonzero sign. Thus it cannot
vanish at the second ordinary target: before it still no other
live scalar label could appear. This works even if an intervening
second \(a\)-copy has zero score.

If the first ordinary target \(z\) is a live singleton, both
repeated labels have already opened. The restriction of \(D_3\)
to their old physical donor coordinates has rank at least two.
Here is the short verification. The first opener \(p_1\) is
nonzero in \(\boldsymbol u\) because its score is nonzero.
At the first copy of the other label \(q\), a nonzero
\(\boldsymbol u\) gives the second direction by clock marking;
if instead \(\boldsymbol u\) is zero there but
\(\boldsymbol g\) or \(\boldsymbol h\) is nonzero, it also gives
a second direction. If all three are zero there, the \(q\)
primitive payment requires a nonzero scalar tap onto old
copies of \(p\), annihilating their \(\boldsymbol u\) readings.
On those old copies \(\boldsymbol g=p\boldsymbol u+
(p^3/6)\boldsymbol w\), so these two defect restrictions are
independent: otherwise the nonzero \(\boldsymbol u\) and
\(\boldsymbol w\) readings would be proportional, contrary to
that paid tap. This covers the zero score on \(a_2\).

The actual tap functional at \(z\) on those old physical donors
is nonzero by its first primitive moment and annihilates the
two defect directions. There must be three old physical donors,
not just two. All \(a_1,a_2,b_1\) are thus already present,
and the next ordinary target \(x\) adds only the possible scalar
donor \(z\). The old-three part of its functional again
annihilates the same two directions, since \(\boldsymbol u\)
and all \(D_3\) defects at the singleton \(z\) vanish. Thus it
is a scalar \(\ell\) times the original functional, and the
additional scalar tap \(T\) is at \(z\). The three exact moments
give \(z^2\ell+2zT=x^2\), \(z^3\ell+3z^2T=x^3\),
\(z^4\ell+4z^3T=x^4\), hence \(x^2(x-z)^2=0\).
Distinct target labels make this impossible.

## Leakage with a single supported repeated label

Assume \(D_4\not\subseteq S\). Then \(\dim(D_4\cap S)\le2\).
If \(D_3\) is supported only at one label \(p\in\{a,b\}\),
consider the chronological first of a live singleton or the
first copy of the other label \(q\). Both are clean in
\(\boldsymbol u,\boldsymbol g,\boldsymbol h\); the latter
has nonzero first score by hypothesis. Before this first
clean target \(z\), strictly positive-degree weighted input
can come only from \(p\). The [local nilpotent proof](../erk10-five-opening-fourfold-interior/README.md#the-first-live-singleton-forces-a-two-dimensional-nilpotent-block)
uses exactly this condition and the three coordinate
equalities, not singleton uniqueness. It gives
\[
 z=3p/2,\quad
 \boldsymbol h=p\boldsymbol u-\tfrac32\boldsymbol g,\quad
 \boldsymbol k+\tfrac34 K\boldsymbol g=\tfrac{3p}4\boldsymbol g .
\]
For clarity, the required nonzero evaluation on \(D_4\) is
\((K\boldsymbol g)_z=3p^4w_z/16\), while every \(D_3\) value
there is zero. The two independent old \(p\)-profiles, and
nilpotence of their strict submatrix, prove the global
equalities just as in that proof.

As the next clean target \(x\), take the first live row at
any other label besides \(p,z\): a live singleton or the
unopened \(q_1\). It exists since there are two live
singletons. If \(z=q\) has another copy before \(x\), it
is also \(D_3\)-clean, and simply supplies the same scalar
label \(z\). Until \(x\), the feedback induction in the
fourfold proof kills the total weighted tap from \(z\) for
every intervening \(p\)-row. That calculation uses only a
total weighted tap, not the number of earlier copies at \(z\).
At \(x\) the same corrected cubic moment therefore forces
\(x^2(x-z)^2=0\), impossible.

If the first ordinary target occurs before both repeated
labels even open, it cannot be a completion at its sole
earlier label \(p\), because its first two moments would
require \(p=3p/2\). It is a live singleton. The same local
one-donor calculation proves independent \(\boldsymbol u,
\boldsymbol g\) restrictions on prior \(p\)-rows. If any
\(D_3\) vector then had support at the other label \(q\),
its mark by \(\boldsymbol y-p\) would give a nonzero
\(q\)-only vector in \(D_4\cap S\), independent of the two
old restrictions, contradiction. Thus \(D_3\) is supported
only at \(p\), and the preceding exit applies. With no
earlier live label the first primitive fails outright.

## Leakage with separate modes at both labels

It remains that \(a_1,b_1\) both precede the first ordinary
target and \(D_3\) supports both labels. In this case \(D_3\)
has separate modes \(\boldsymbol V_a,\boldsymbol V_b\),
one at each label. Indeed, if \(\boldsymbol u\) supports
both, its first mark separates them. Otherwise
\(\boldsymbol u\) is supported on its chronological first
live opener's label \(p\), and any \(D_3\) vector with
other-label support yields an independent \(q\)-only
projection in \(D_4\cap S\) by its mark. Its component at
\(p\) must be proportional to \(\boldsymbol u\), else
that projection and two \(p\) modes would give rank three
in \(D_4\cap S\). Subtract the proportional amount to get
the \(q\) mode already in \(D_3\).

Both mode entries at their first copies are nonzero:
at the first opener this is given by \(\boldsymbol u\).
If the other first copy were clean in
\(\boldsymbol u,\boldsymbol g,\boldsymbol h\), the same
one-donor argument produces two independent old \(p\)
restrictions, in conflict with these separate modes.
Normalize \(\boldsymbol V_a(a_1)=w_{a_1}\),
\(\boldsymbol V_b(b_1)=w_{b_1}\), never dividing by \(w_{a_2}\).
The quotient \(D_4/\operatorname{span}(\boldsymbol V_a,
\boldsymbol V_b)\) is one-dimensional.

### Both old mode values track their scalar weights

Let \(z\) be the first ordinary target. Suppose each
available nonzero-ordinate scalar donor's mode entry
equals that donor's physical score. This is automatic for
\(a_1,b_1\) and is one of the possibilities for \(a_2\)
if it already appeared. At \(z\), the scalar taps onto
\(a,b\) are then exactly the group means of \(K\boldsymbol
V_a,K\boldsymbol V_b\). At least one tap is nonzero by
the first primitive moment, so this functional on the
defect quotient is nonzero.

Before the next ordinary target, the only untracked
scalar tap can arise from the new physical row at \(z\)
itself (the new singleton or the just-completed label),
and possibly the not-yet-appeared \(a_2\). Handle the latter
first if it intervenes. Compare the raw \(a_2\) row
evaluation with \(\nu\) times the \(a_1\) evaluation,
where \(\nu=V_a(a_2)/w_{a_1}\). The difference annihilates
both modes, so its first and second primitives are exact
with virtual score \(w_{a_2}-\nu w_{a_1}\). On all old
donors other than \(z\), mode tracking still holds, since
\(a_2\) is not yet a donor for either evaluation row.
Their only new untracked scalar tap is at \(z\).
If its virtual score is nonzero, divide by that score and
compare the three primitive moments with the reference
mean at \(z\), using the quotient for \(K\boldsymbol V_a,
K\boldsymbol V_b,\boldsymbol k\), exactly as in the
[early square](../erk10-five-opening-three-pair-complete/README.md#leakage-first-ordinary-completion-before-all-pairs-open).
It gives \(a^2(a-z)^2=0\), impossible: \(z\) could not
have completed the triple before \(a_2\) appeared.
So the virtual score is zero, i.e. \(V_a(a_2)=w_{a_2}\),
even for a zero-score \(a_2\).

At the second ordinary target all old donors away from
\(z\) now track their scores, and any uncalibrated change
is at \(z\) alone. The same square applied to this
ordinary group yields a contradiction.

### Exceptional lack of tracking before the first ordinary target

Only three orderings of \(a_1,a_2,b_1\) are possible prior to
the first ordinary group. If \(a_1,a_2,b_1\) occur in that
order, then on both old \(a\)-copies
\(\boldsymbol g=a\boldsymbol u+(a^3/6)\boldsymbol w\).
Both defects are proportional to the \(a\) mode there;
hence the two weights are proportional to that same mode.
Our normalization at \(a_1\) makes them equal. This is the
tracking case.

The other two chronological orders may initially fail to
track. We derive the same necessary scalar exit for both.
After grouping at a target \(z\), write \(B(z)\) for its
total effective scalar tap into \(b\) (divide by group score).
So long as only the opening \(b_1\) is available, this is
the group mean of \(K\boldsymbol V_b\). All physical
scalar donor labels at the first ordinary target are
still \(0,a,b\).

* **Order \(a_1,b_1,a_2\).** Write \(\alpha\) for the
  normalized scalar tap of \(b_1\) on \(a_1\), and put
  \(U=a\alpha-b^2/2\). On the \(a\)-group,
  \(\boldsymbol u=-a^2\boldsymbol V_a/2\),
  \(\boldsymbol g=-a^3\boldsymbol V_a/3\), and
  \(\boldsymbol h=0\), using the exact values at \(a_1\)
  and rank one there. On \(b_1\), \(u_{b_1}=w_{b_1}U\).
  At \(a_2\) let \(S,T\) denote the actual weighted taps
  on \(a_1,b_1\), without dividing by its score. The two
  relations on \(\boldsymbol g,\boldsymbol h\) give
  \[
     a^2 S/3+b(b-2a/3)T=0,\qquad
     -a^2 S/2+UT=0.
  \]
  If \(T=0\) then \(S=0\) and tracking holds. Otherwise
  \(\alpha=b(a-b)/a\).
  The grade-four vector \(Q=K\boldsymbol V_b\) has zero
  entries at the first \(a,b\) copies and entry \(T\ne0\)
  at \(a_2\), so it spans the quotient. Subtracting the
  appropriate multiples of both modes from \(\boldsymbol k\)
  to make its first \(a,b\) values zero, its \(a_2\) entry
  is
  \[
      \bigl[b(a-b)(a-2b)/2\bigr]T.
  \]
  Thus at a grouped target \(z\), \(k_z\) has mean
  \(\bigl[b(a-b)(a-2b)/2\bigr]B(z)\).

* **Order \(b_1,a_1,a_2\).** Let \(\alpha\) be the
  normalized scalar tap of \(a_1\) on \(b_1\), and put
  \(U=b\alpha-a^2/2\), \(G=b^2\alpha-a^3/3\),
  \(H=-b^2\alpha/2\). These are the proportionality
  coefficients of the three actual defects on
  \(\boldsymbol V_a\), from their values at \(a_1\).
  Write \(\delta=V_a(a_2)-w_{a_2}\). In the raw \(a_2\)
  scalar taps, write \(S\) on \(a_1\), and \(T'\) for the
  tap on \(b_1\) **minus** \(\alpha w_{a_2}\). Then
  \[
    aS+bT'=U\delta,\quad
    a^2S+b^2T'=G\delta,\quad
    US-b^2T'/2=H\delta .
  \]
  If \(\delta=0\), tracking holds. Otherwise, the
  determinant gives
  \(\alpha=a^2(a-b)/(b(2a-3b))\), with \(2a-3b\ne0\)
  (the zero-denominator numerator would be nonzero).
  Moreover \(S=-a(2a-3b)\delta/[6(a-b)]\ne0\).
  The vector \(Q=K\boldsymbol V_a\) has zero first
  \(a,b\) values and \(a_2\) value \(S\), so again spans
  the quotient. Subtracting the first-copy modes from
  \(\boldsymbol k\), its quotient coefficient against
  \(Q\) is \(a^2(a-2b)(a-b)/[2(2a-3b)]\).
  The identity
  \(\boldsymbol h=U K\boldsymbol V_a-(b^2/2)K\boldsymbol
  V_b=H\boldsymbol V_a\) gives at every group the
  \(Q\) mean as \(b^2/(2U)\) times the \(K\boldsymbol
  V_b\) mean. Here \(U=a^2 b/[2(2a-3b)]\ne0\).
  Combining these factors yields the same
  \(\bigl[b(a-b)(a-2b)/2\bigr]B(z)\) mean for
  \(\boldsymbol k\).

For either exception, the exact first two moments at
target \(z\) independently give
\[
 B(z)=\frac{z^2(2z-3a)}{6b(b-a)},\qquad
 \operatorname{mean}_z(\boldsymbol k)=
 z^2\left(-\frac{z^2}{4}+\frac{(a+b)z}{3}-\frac{ab}{2}\right).
\]
Their difference from the required relation factors as
\[
 \operatorname{mean}_z(\boldsymbol k)
       -\frac{b(a-b)(a-2b)}2 B(z)
       =-\frac{z^2(z-a)^2}4 .
\]
Thus the first ordinary target is necessarily the triple
closure \(z=a\), not the \(b\)-closure or a distinct
singleton. At the second ordinary target, only \(b_1\)
can still be a \(b\)-donor, and the new \(a\)-copy adds
no new scalar label. All exceptional equations therefore
apply again, forcing the second target to have clock
\(a\). Contradiction. This completes the theorem.

## Exact replay

    python3 -B audit.py
    # From the overlay or repository root:
    sha256sum -c ai-generated/research/erk10-five-opening-triple-pair/sources.sha256

The exact replay verifies both tracking exceptions without
floating-point arithmetic. The chronology and nilpotent
physical bridge is mathematical.
