# Zero triple total and the complete seven-label census

The [triple-and-pair exit](README.md) in fact covers **arbitrary
physical and pooled weights** over every field with \(10!\ne0\),
under the unchanged five-opening word budget, seven distinct
nonzero high forward labels, and unique first reverse endpoint.
The [zero-opening extension](ZERO-OPENINGS.md) and
[zero pair-total fold](ZERO-PAIR-POOL.md) settle the case with
nonzero triple total. This addendum proves the remaining case
\(W_a=0\), permitting either value of \(W_b\).

The same support factorization supplies at least four live
interior labels, hence at least two live singleton targets.
Call a singleton ordinary when it has nonzero score, or a
closure ordinary when its repeated total is nonzero. In this
case the triple closure never counts as an ordinary target.
Keep every physical copy as a donor; an already closed
zero-total pair \(b\) continues to fold by a single column
difference for scalar and \(D_3\) inputs. If \(W_b\ne0\),
before the first ordinary target only \(b_1\) is available,
and at a target that closes \(b\) only \(b_1\) can contribute
as a same-label earlier donor. Zero-score singleton donors
supply zero on the low scalar and defect inputs.

## No grade-four leakage

If \(D_4\subseteq S\), ordinary targets have their three
primitive moments exact, and \(K D_3\) gives zero group mean.
If the first ordinary target is a repeated label (necessarily
\(b\)), only scalar labels \(0,a,b\) can precede it. The same
cubic nodal primitive \(Y(Y-a)(Y-b)\) forces \(b=2a\)
and has its only nonzero root there with multiplicity two.
Until the second ordinary target there can still be no new
scalar label, since any additional triple copies are at \(a\).
So that target, of distinct label, is impossible.

If the first ordinary target is instead a singleton \(z\),
it needs two genuinely nonzero scalar donor labels \(a,b\);
one cannot pay the three cubic primitive moments.
In particular \(w_{b_1}\ne0\): a zero-total \(b\) with
\(w_{b_1}=0\) has both scores zero, while a nonzero-total
\(b\) has not yet contributed its second copy. The full
\(D_3\) has dimension at least two. Otherwise it is the
span of \(\boldsymbol u\), nonzero at the chronological
first live interior label \(p\); its mark forces all of
\(\boldsymbol u\) to be supported only at that label.
The first live physical row at the other label \(q\)
would be clean in \(\boldsymbol u,\boldsymbol g,\boldsymbol h\).
Before it only the scalar label \(p\) could contribute.
On its earlier \(p\)-copies
\(\boldsymbol g=p\boldsymbol u+(p^3/6)\boldsymbol w\).
Proportionality of \(\boldsymbol g\) to \(\boldsymbol u\)
would make the old \(p\)-scores proportional to
\(\boldsymbol u\); then the required nonzero scalar tap
would contradict the vanishing of \(K\boldsymbol u\) at
the first live \(q\)-row. This argument allows either
number of earlier physical copies, and folds any earlier
zero-total \(b\) automatically.

Consider now the projection of \(D_3\) onto the **three**
physical \(a\)-entries, a subspace of the two-dimensional
sum-zero space \(S_a\).

* If its rank is below two, the map has a nontrivial
  kernel because \(\dim D_3\ge2\). A nonzero kernel
  profile is supported only at \(b\), and its first
  \(b\)-entry is nonzero because the two sum to zero.
  On all available \(b\)-donors this profile is a nonzero
  multiple of the scalar score vector (one live opening
  copy, or both folded copies with opposite scores).
  Thus its zero \(K\)-mean at \(z\) forces the scalar
  \(b\)-tap zero, contrary to the need for two donor labels.
* If projection has rank two, it is onto \(S_a\).
  The full triple score vector belongs to \(S_a\) since
  \(W_a=0\), including when some coordinates are zero.
  Choose \(\boldsymbol f\in D_3\) whose three \(a\)-entries
  are exactly those three scalar scores. For the first
  ordinary target \(z\) and for the second \(x\), its
  \(K\)-mean is zero. At each target, let \(A,B\) be
  the total scalar taps at labels \(a,b\), respectively.
  Then
  \[
       A+\rho B=0,\qquad \rho=f_{b_1}/w_{b_1},
  \]
  at both targets. This remains true if the triple had
  not already closed at \(z\): the matching \(a\) coordinate
  is exact at every available donor separately. No group
  mean is taken at the zero-total triple. At \(b\) the
  first-copy ratio is also the ratio on both folded
  copies if necessary. All intervening singleton donors
  of zero score have zero \(\boldsymbol f\) value. The
  first target \(z\) is itself a singleton, so
  \(\boldsymbol f\) is also zero there.

  Accordingly the two old scalar coordinates \(A,B\)
  at the second target are a common multiple \(\ell\)
  of those at the first, which are nonzero as a row by
  the first primitive. Any added live scalar tap is on
  the singleton \(z\) alone, say \(T\). As before exactness
  of the three primitive moments then gives
  \[
  z^2\ell+2zT=x^2,\quad z^3\ell+3z^2T=x^3,\quad
  z^4\ell+4z^3T=x^4 .
  \]
  Hence \(x^2(x-z)^2=0\), impossible.

This settles no leakage without trying to fold a zero-total
triple into one physical donor.

## Leakage: the third scalar score is an automatic tracking value

If \(D_4\not\subseteq S\) and \(D_3\) is supported on
one repeated label, the local single-label nilpotence and
clean-target feedback proof from the two preceding notes
does not depend on the triple total or on how many live
copies of its sole label appear before the first clean row.
As usual if the first ordinary target precedes the other
repeat's first physical opening, its one-donor calculation
forces two independent old restrictions on the sole label;
marking any support at the other label would then make
three dimensions in \(D_4\cap S\). It thus also reduces to
the single supported label case.

Otherwise the first two supported modes are separate at
\(a,b\), using the first live \(\boldsymbol u\)-entry and the
same clock mark argument. Each label must support some
\(\boldsymbol u,\boldsymbol g,\boldsymbol h\), or a first
clean live row at the other label (or a live singleton)
forces two independent restrictions at the sole donor label.
This is the zero-opening argument and uses only the exact
first two primitives and the vanishing of \(K\boldsymbol u\),
not the number of copies of one old label.

For two modes the two opening-copy calculations in the
[regular proof](README.md#exceptional-lack-of-tracking-before-the-first-ordinary-target)
and the
[zero-opening proof](ZERO-OPENINGS.md#zero-score-on-a_1-with-b_1-live)
still apply literally to \(a_1,a_2,b_1\) in their relative
order. \(a_3\) is strictly later than \(a_2\), so it cannot
affect any of those three equations for \(a_1,a_2\). If it
precedes \(b_1\), the relevant order is \(a_1,a_2,b_1\),
where the two \(a\)-copies already track simply because
before them there was no other available nonzero scalar
label. If \(W_b=0\) fold both \(b\)-columns as in the
prior addendum. The exceptional two-mode branches use
\(Q=K\boldsymbol V_a\) or \(K\boldsymbol V_b\) and establish
\[
 \operatorname{mean}(\boldsymbol k)
   =\frac{b(a-b)(a-2b)}2 B
\]
at the first ordinary target using only aggregate scalar
taps at \(a,b\). An extra \(a_3\) donor does not add a
new scalar label, and the \(b\)-tap is still fixed by its
mode on the first or folded pair. The exceptional residual
\(-z^2(z-a)^2/4\) therefore remains valid. It forces the
first ordinary target to be \(a\), impossible because
\(W_a=0\) and any triple closure is skipped as a target.

In every tracking branch, after \(a_1,a_2\) match their
physical scores the third match follows from the equalities
\[
    \sum_{i\in a} V_a(i)=0=\sum_{i\in a}w_i .
\]
This includes signed and zero scores. If both initial
scores are zero, the third is zero as well and there is
no scalar \(a\)-tap to track. If \(a_2\) is still pending
after the chosen reference group, the virtual-row test
from the main proof makes it match, or prevents a new
nonzero scalar score at that copy when the first was
zero. In particular when \(w_{a_1}=0\) and the first
ordinary target only has a scalar \(b\)-tap, \(K\boldsymbol
u\) requires an already available nonzero \(a\)-mode to
cancel that tap. Thus a pending \(a_2\) has its nonzero
\(a_1\)-mode pivot for the virtual comparison even
though the \(a_1\)-score itself is zero. Once these
first two actual scores are both zero, \(W_a=0\) ensures
all three are zero. No uncompensated new scalar donor
can occur at \(a_3\) in any remaining branch.

Consequently precisely the old calibration away from the
first ordinary target's own new scalar label still holds
at the second ordinary target, and the same primitive
square forces equal ordinary clocks. This completes the
leakage case and the entire triple-and-pair chart.

## Combined seven-label conclusion

For ten physical high rows with seven distinct scalar labels
and one unique endpoint, the three extra repetitions must be
one of the partitions \(1+1+1\), \(2+1\), \(3\). Their placements
away from the endpoint are respectively
[three pairs](../erk10-five-opening-three-pair-complete/ALL-PAID-FIELDS.md),
a triple and a pair (this packet), or
[a fourfold label](../erk10-five-opening-fourfold-interior/README.md).
Thus under the **same actual five-opening short-word budget and
unique first reverse endpoint**, exactly seven distinct nonzero
high forward labels are ruled out over **every paid field**. It
does not cover fewer or more high labels, a zero high forward
clock, a repeated or displaced reverse endpoint, or other
five-opening decoder ranks. This is not an unrestricted
fifteen-stage ERK10 exclusion.

The same label-product nilpotence consequence applies to the
entire seven-label census over \(10!\)-unit rings: invert
all forward labels and label gaps, and specialize to a maximal
residue field if that localization is nonzero. No unconditional
gap over arbitrary rings with colliding residue labels is asserted.
