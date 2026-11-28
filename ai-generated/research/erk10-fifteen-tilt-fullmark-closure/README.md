# No rational fifteen-stage full-mark one-direction tilt

**Theorem.** The regular five-opening architecture of the
[one-direction relaxation](../erk10-five-opening-rank-one-size-five/README.md)
has no rational ERK10 tableau at width fifteen in its
genuine mixed, full-mark branch. The high rows may have
one genuine size-five error direction, arbitrary old
contact preserving high purity through size four, signed
and zero scores, high zeros, and repeated clocks. Full
marks means \(Q+XQ=X\mathcal P_4\) for \(Q=\ker\ell\)
in \(X\mathcal P_3\). In particular this holds for every
nonsplit \(P/X\), and for all split tilts other than a
true single evaluation. The split single-evaluation
tilt at width fifteen is **not** covered by this theorem.
Since the pure-input alternatives were already closed,
only that split evaluation remains at width fifteen
within this precise rank-one opening. The unrestricted
rational stage interval is unchanged.

Use the notation and actual root-source deductions of
the [rank-one packet](../erk10-five-opening-rank-one-size-five/README.md).
Thus the actual early-null \(\widetilde E f\), \(f\in U=X\mathcal
P_3\), is \(Ef+\ell(f)\boldsymbol\delta\). The high block
\(B\) is strict forward, \(C\) is marking by the forward
clocks \(\boldsymbol x\); \(K=B^T\) in reverse coordinates,
and \(Y=I-C\) after the relabeling. The exact pure words
through length four, tilted words through five, and scalar
accuracy through degree nine are earned. If a candidate has
width ten high, the defect space \(D_4\) has dimension three,
and the two-dimensional annihilator \(V\) of \(D_4\) together
with the five nominal weighted powers contains
\(\boldsymbol\delta,C\boldsymbol\delta\) and
\(\widetilde T(f)=B\widetilde E f-EJ f\).
Every vector \(\boldsymbol z\in V\) has
\(\boldsymbol w^T W\boldsymbol z=0\) for every word of length
at most four: the actual adjoint word is its nominal
weighted polynomial plus a true \(D_4\)-defect. The paid
plateau gives \(K\boldsymbol w=Y\boldsymbol w\).

The true first reverse row is live and at endpoint \(1\).
Indeed if any physically last high rows are unscored,
they may be deleted from the actual strictly explicit
tableau without changing any surviving profile or rooted
output. The regular opening and rank-at-most-one
size-five condition survive restriction, and the previous
[rational width-14 exclusion, including split](../erk10-five-opening-rank-one-size-five/SPLIT-EVALUATION.md)
then gives a contradiction. The first reverse-live clock
is one by the paid raw adjoint equality.

## The usable two forward witnesses are still early

Let the forward prefix stop at the first occurrence of
the second distinct nonzero high label \(z\), with \(h\)
the first nonzero label. Then restriction of \(V\) to this
prefix has dimension two. If \(\boldsymbol\delta\) is zero
there, the true \(\widetilde T\) rows at \(h,z\) are the
original unperturbed residual rows; their rank is two by
the affine second-difference argument on \(X,\ldots,X^4\).
Otherwise a one-dimensional restriction is spanned by
\(\boldsymbol\delta\) on that prefix, so the dirt there is
at one clock (because \(C\boldsymbol\delta\) is in \(V\)).
All \(\widetilde T\) there would be proportional to the
same restricted vector. The [rank-one incompatibility](../erk10-five-opening-rank-one-size-five/README.md#rank-one-is-impossible-in-the-nonsplit-chart)
uses exactly these rows and no later row: if all dirt there
is at zero, exact \(h,z\) gives the two-functional
contradiction; if the dirt is nonzero, the first \(h\)
must be that dirty label, and its same-label prefixes
give the equal/different tilt alternative and the
\(P,XP,JP\) contradiction. If \(P(h)=0\), the same
localized proof gives the forbidden rational
\((10h-6z)^2=6z^2\). This proves the rank-two restriction
also in the split full-mark case.

Consequently any early reverse observer contrast
whose later reverse suffix contains two distinct
nonzero high labels is independent of the two actual
annihilators, just as in the earlier reverse census.
This replaces the use of unperturbed length-five
forward witnesses. It does not suppose those full
pure length-five words survive.

## A same-label directional erasure

For a nonzero silent direction \(\boldsymbol d\in V\)
supported at a single forward clock \(a\), choose its
earliest nonzero physical coordinate \(i\), and use
\[
 P_i=I-\boldsymbol d\,\boldsymbol e_i^T/d_i .
\]
Its image is the coordinate slice with pivot \(i\)
zero. It commutes with \(C\). One may do one such
cut, or simultaneous cuts at two different clock
labels if both color directions belong to \(V\)
(their supports are disjoint).
All actual outputs of words through length four
remain unchanged after inserting the projection
between letters and at the input: insert from the
right, and each difference pairs an **unmodified**
prefix with a vector in the removed directions,
which are silent to all those prefixes. In
particular \(w^TP_i=w^T\); the erased *score*
itself need not be zero.

On the slice, take \(P_iB\) followed by restriction.
It is still strictly causal: at a surviving row
\(j\) a nonzero correction subtracts a multiple of
the old pivot row only if \(j>i\), and the pivot
row reads only columns before \(i\). The same
argument applies to two disjoint directions; the
mark remains the literal diagonal on surviving
coordinates. The projected model input at a
surviving row of the affected color is
\(\lambda_j f(x_j)\) with
\(\lambda_j=1-d_j/d_i\), and elsewhere
\(\lambda_j=1\). Normalize each \(\lambda_j\ne0\)
by conjugating with the corresponding diagonal
scale and transferring that scale to the output
score. If \(\lambda_j=0\), retain the physical
coordinate with *model flag zero* and **do not
divide by it or drop its score**. The resulting
model is \(E_\varepsilon f\) with entries
\(\varepsilon_j f(x_j)\), \(\varepsilon_j\in\{0,1\}\).
It is still compatible with the diagonal marking.

These operations preserve scalar moments through
degree nine (including the unchanged old origin
score), pure length-at-most-four words with their
nominal values, and the raw first adjoint equation.
For the latter let \(S\) embed scaled surviving
coordinates in the pivot-zero slice. Then
\[
 \boldsymbol w^T P_i B S
 =\boldsymbol w^T B S
 =\boldsymbol w^T(I-C) S ,
\]
which is exactly the new raw equation. This is a
proof about a smaller raw word system; it does not
claim a literal smaller RK tableau from this cut.

After one cut, a second original annihilator
projected to the slice gives a nonzero annihilator
of the reduced actual observers and nominal powers.
It is nonzero outside any early reverse prefix with
two distinct nonzero surviving labels later in
reverse. Indeed the original forward prefix through
the debut of the second nonzero label lies outside
that reverse prefix (allowing the removed pivot).
The two original vectors were independent on that
prefix. Projecting the second one along the pivot
direction is just subtracting a scalar multiple of
the first vector, so it still has a nonzero
*surviving* coordinate in it. Restriction and
nonzero diagonal scaling preserve this property.
The slope of a model-blind row is not needed here.

If there is only one dirty clock, take its direction
as the one cut. If there are two dirty clock labels,
the two same-label parts of
\(\boldsymbol\delta\) are linear combinations of
\(\boldsymbol\delta,C\boldsymbol\delta\), and both
are silent, so take both cuts. The resulting widths
nine and eight are impossible by the separate
[masked-width proof](MASKED-WIDTH.md), even when a
surviving row has flag zero. Thus any candidate has
at least three dirty clock labels. In particular
assuming generic distinct dirt values within a
repeat group is unnecessary.

## Remaining clock counts

The anchored rational scalar floor with permitted
sites \(0,1\) requires at least six distinct live
ordinary (nonzero, nonendpoint) scalar nodes. The
physical high label count \(m\) of distinct nonzero
forward labels is therefore at least seven. The
[dirt polynomial argument and complete case table](DENSE-JACOBI.md)
now exclude \(m=7,8,9,10\). Only the already
published low grades (at most four) are imported
from the previous high-label census. The new
orthogonality argument replaces its grade-five
terminal nonics, rather than treating tilted words
as if they were pure.

## Replay and proof scope

    python3 -B audit.py
    sha256sum -c ai-generated/research/erk10-fifteen-tilt-fullmark-closure/sources.sha256

The exact audit includes a projection with a nonzero
deleted score and a nonzero-score model-blind
survivor, the sparse clock counts, and the exact
Jacobi matrix and modular check. The physical word
projection and census reductions are mathematical.
See [Lean scope](LEAN.md) for just the scalar receipts.
