# The physical ERK16 weak-four packet is impossible over an ordered field

This is an editable mathematical proof with an exact integer/rational checker,
not a combined Lean theorem. It uses the **same four actual contrast marks**
throughout. It does not assert that the abstract three-reverse-test structure
`WeakFourChronologicalPorts` is impossible without its physical forward source.

## Packet, scope and already established cut

Use the reflected numerical coordinate. Write $a,c$ for the last and
next-to-last contrast rows' clocks and $d,h$ for the first and next-to-first
contrast rows' clocks. They are four distinct marks, none equal to 0 or 1.
Let
$$
 Z(X)\coloneqq (X-a)(X-c)(X-d)(X-h),\qquad F\coloneqq QZ,
$$
where $Q\ne0$, $\deg Q\le4$, $Q(1)\ne0$, and $Q$ is nonzero
at each mark. Integrals are oriented formal-primitive evaluations in the
ordered field. The physical laws are
$$
 \int_0^1 XF T=0\quad(\deg T\le6),\qquad
 \int_0^a XQ=\int_0^a X^2Q=\int_0^c X(X-a)Q=0,
$$
$$
 \int_d^1(1-X)Q=\int_d^1(1-X)^2Q=
 \int_h^1(1-X)(d-X)Q=0.
$$
The global raw degree is at most 15; the local raw degree is at most 6. No
diagonal test, further moment, or positivity of the tableau weights is assumed.

For degree four we use only the following conclusion of the published
[root-count and parity proof](../weak-four-reductions/02-first-root-count.md),
with its [crossing comparison](../weak-four-reductions/01-crossing.md):
**all four roots of $Q$ are simple and strictly between 0 and 1** in an
ordered real closure. That proof excludes the case of three strict interior
roots of a *quartic*, not the genuine degree-three case. We treat the latter
separately below. The exterior-secondary reduction is not needed here.
All our interval tests use only a first pair of local laws and the global law.

The unchanged positive 19-node rule justifies the square tests and sign tests
on proper intervals. Equivalently, all its applications below have rational
polynomial moments and exact degree at most 15. It and the integral identities
transport to an ordered real closure. A contradiction in that extension
excludes the original packet, including over a non-Archimedean ordered field.

## The polynomial families paid by the global law

Let $J,K,L$ denote the rational, positive-leading degree-seven polynomials
in [the checker](check_uniform.py), orthogonal through degree six on the unit
interval for the weights $X,X^2,X(1-X)$, respectively, and put
$$
 J^{\mathrm r}(X)\coloneqq -J(1-X),\qquad
 P_0\coloneqq XK,\qquad P_1\coloneqq(X-1)L,\qquad P_0^{\mathrm r}\coloneqq XL.
$$
The exact rational moment checks use
$$
 \int_0^1 X^{k+1}=\frac1{k+2},\qquad
 \int_0^1(1-X)X^k=\frac1{(k+1)(k+2)} .
$$
The leading coefficients are $6435$ for $J,J^{\mathrm r}$ and $11440$
for $P_0,P_1,P_0^{\mathrm r}$. Direct polynomial comparison gives
$$
 P_1=P_0-J,\qquad J(0)<0<J(1),\qquad J^{\mathrm r}(0)<0.
$$

Any polynomial of degree at most six orthogonal to all such polynomials for
weight $X$ or $1-X$ is zero: test it against itself, and use the positive
interior mesh. Consequently any degree-seven $F$ satisfying the displayed
global law is a nonzero constant times $J$: first match its leading
coefficient, leaving degree at most six. The same argument, matching degrees
eight and seven, writes any admissible degree-eight $F$, after scaling it
to positive leading coefficient $11440$, as
$$
                         F=P_0+uJ .
$$
After reflection the weight is $1-X$ and the corresponding representation
is $F^{\mathrm r}=P_0^{\mathrm r}+vJ^{\mathrm r}$, where
$F^{\mathrm r}(X)\coloneqq F(1-X)$. These are just the at-most-two-dimensional
kernels of the seven global moment equations. No endpoint derivative condition
or evaluation on any fixed physical tableau enters the construction.

Here are all cases the checker needs.

* **Cubic $Q$.** The seven rational disjoint strips for $J$ have opposite
  signs at their two ends, so all seven roots of $F$ are distinct strict
  unit roots. The three $Q$ roots and the four marks are among them. Use the
  first left stop $a$.
* **Quartic $Q$, $-1<u<0$.** The family is the full convex pencil between
  $P_0$ and $P_1$, with parameter $-u\in(0,1)$. Its eight-index
  certificate proves one root of $F$ in each disjoint strip. For this open
  parameter interval $F(0)>0$ and $F(1)>0$, so all eight roots are strict
  unit roots. Use the first left stop $a$.
* **Quartic $Q$, $u\ge0$.** $F$ is a positive multiple of the convex
  combination of $J,P_0$ with parameter $1/(1+u)$. Its seven-index
  certificate gives seven distinct strict unit roots. The remaining root
  $e$ is real by linear division and $e\le0$, since $F(0)\le0$,
  the leading coefficient is positive, and the seven other roots are positive.
  By the established quartic cut, $e$ is a mark, hence cannot be zero. It
  cannot be $a$: for $a<0$ the integrand $XQ$ has a fixed nonzero sign
  on $(a,0)$. Thus $a$ is a strict unit root. Use the first left stop
  without assuming which of the other three marks is exterior.
* **Quartic $Q$, $u\le-1$.** Here $F(1)=(1+u)J(1)\le0$; equality
  is ruled out by the physical packet, though the certificate allows the
  parameter boundary. Change $X$ to $1-X$: the global weight becomes
  $1-X$, the first right stop becomes a first left stop $a'=1-d$, and
  the local laws there are $\int_0^{a'}XQ(1-X)=\int_0^{a'}X^2Q(1-X)=0$.
  In the reflected representation, $F^{\mathrm r}(0)\le0$ gives $v\ge0$.
  Thus $F^{\mathrm r}$ is a positive multiple of a convex combination of
  $J^{\mathrm r},P_0^{\mathrm r}$. The preceding seven-root and wrong-way-stop
  arguments apply, now to $a'$ and the reflected $Q$.

In each case, relabel the selected left stop $a$ and the corresponding fitting
polynomial $Q$. We have $0<a<1$, all $Q$ roots among the listed strict
unit roots, and both actual laws $\int_0^a XQ=\int_0^a X^2Q=0$. There
are at least two $Q$ roots below $a$. Otherwise $Q$ has at most one
sign change on $(0,a)$; a signed constant or linear factor makes a nonzero
polynomial $XQ$ times that factor nonnegative there, contradicting the
two laws on the positive affine rule. This elementary argument is why the
checker admits *every* rank choice with at least two, not just the stronger
three-root chronological constraint from the quartic reduction.

## Why a checked box excludes every parameter in it

Write $G_s\coloneqq(1-s)A+sB$ for the applicable reference pencil; the
cubic simply has $A=B=J$. On each closed rational parameter interval
$[s_0,s_1]$, the checker constructs pairwise disjoint closed rational strips
$[l_i,h_i]$, in increasing order. It checks the two opposite weak signs
of $G_{s_k}(l_i)$ and $G_{s_k}(h_i)$, in the designated orientation, at
**both** $k=0,1$. At either fixed rational abscissa the polynomial value is
affine in $s$; the same inequalities therefore hold for every $s$ between
the endpoints. The polynomial has a root in each strip in the real closure,
including equality at a strip endpoint. The strips are disjoint. The degree
and preceding sign-of-the-extra-root argument identify exactly the indexed
roots. In particular, no tracking of floating-point roots, sample-point
assumption, or monotonic dependence on a physical clock is used.

For a rank choice, let $j$ be the index of the stop and $I$ the set of
the three or four $Q$-root indices, not containing $j$. The proof
enumerates all such choices with at least two indices less than $j$.
The normalized roots $z_i\coloneqq r_i/a$ satisfy
$$
      l_i/h_j\le z_i\le h_i/l_j\qquad(i\in I),\qquad l_j>0 .
$$
Changing $X=aY$ and discarding nonzero constant factors, the two laws give
$$
 H_1(\mathbf z)=H_2(\mathbf z)=0,\qquad
 H_k(\mathbf z)\coloneqq\int_0^1Y^k\prod_{i\in I}(Y-z_i)\,dY .
$$
The vector $(H_1,H_2)$ is affine in each coordinate separately. Throughout
the closed box its value is a convex combination of its corner vectors, by
successive affine interpolation. A degenerate coordinate can simply be
omitted from the interpolation.

For each corner, the checker forms the integer polynomial
$\prod_i(d_iY-n_i)$ for positive denominators and $z_i=n_i/d_i$.
Its two exact integral values multiplied by 420 give the corner vector
times the strictly positive $420\prod_i d_i$. All denominators $k+m+1$
for the coefficient of $Y^m$ divide 420. Independent positive rescaling
of corner vectors does not affect the following cone tests. Either every
corner has the same strict sign in one coordinate, or there is a nonzero
corner $v$ such that all determinants $\det(v,w)$ have one weak sign
and every collinear corner $w$ has $v\cdot w>0$. In the second case a
nonnegative weighted sum equaling zero would have to put weight only on the
collinear corners by taking determinants, but their positive dot products then
exclude zero. Both tests prove the origin is outside the convex hull.
Consequently the two paid zero laws cannot hold anywhere in the cell.

If a rank is not yet excluded, split the interval at its rational midpoint
and check **both** children. The root rational mesh is used only to produce
suggested bounds: each accepted enclosure is directly checked by exact
signs of both endpoint polynomials. A rank excluded at a parent remains
excluded throughout all its children. The following finite recursion covers
the entire ordered-field parameter range, endpoints included.

| Reference family | Admitted rank choices | Terminal intervals | Maximum split depth |
|---|---:|---:|---:|
| Cubic, $J$ | 70 | 1 | 0 |
| All-interior quartic, $P_0,P_1$ | 168 | 13 | 4 |
| Low exterior, $J,P_0$ | 63 | 14 | 10 |
| Reflected low exterior, $J^{\mathrm r},P_0^{\mathrm r}$ | 63 | 1 | 0 |

Thus cubic $Q$ and all the remaining quartic $Q$ cases are impossible.
The branch $\deg Q\le2$ was already excluded by
`WeakFourChronologicalPorts.degree_ge_three`. Alternatively use the global
square test on $F$, since $\deg F\le6$.

## Physical wiring and the separate stage-floor assembly

1. On the ordinary four-site arm of
   [`width24_native_head_dispatch`](../../../lean/RKCert/ReviewedNative/ERKOrder16NativeHeadDispatch.lean),
   take the returned *same* `Width24OrdinaryWeakHead`, the rank-seven
   hypothesis, and the four-site equality. Its
   [`weak_four_remaining_physical_cases` and `weak_four_inactive_unshared_remaining`](../../../lean/RKCert/ReviewedNative/ERKOrder16WeakFourRemaining.lean)
   give carrier dimension three, $Q(1)\ne0$, and exactly four physical
   contrast rows with distinct labels not equal to 1. The physical origin
   is outside the four rows. The actual support identity
   `reverse_contrast_true_support` gives nonzero reflected clocks and nonzero
   $Q$ at all four marks.
2. The construction of [`width24_weak_four_extra_port`](../../../lean/RKCert/ReviewedNative/ERKOrder16WeakFourPorts.lean)
   uses **the actual** `nodalHull (weightedSites ...)` as $Z$, not an
   arbitrary degree-four polynomial. Its reverse first- and second-new-clock
   selections are the last two physical contrast rows because their clocks
   are distinct. Its `firstConstant`, `firstLinear`, `secondMasked`, and
   `weighted` are the left and global laws above.
3. For the first two physical contrast rows in *forward* chronology,
   [`rank_three_forward_mask_with_source` and `Width24RankThreeWeakMask.forward_prefix`](../../../lean/RKCert/ReviewedNative/ERKOrder16WeakRankThreeForward.lean)
   give the right laws in the reflected coordinate. In the forward coordinate
   take $R=X,X^2$ at the first row and $R=X(X-(1-d))$ at the second.
   These annihilate the possible original origin and, where necessary, the
   sole preceding contrast; the terminal is not a predecessor. Reflect
   the primitive and use the mask's $q(x)=Q(1-x)$. This verifies each
   input on the same support instead of adding a forward law to the abstract
   three-reverse-test structure.
4. To use this result for a lower bound, split a putative width-24 tableau
   by `width24_native_head_dispatch`. The ordinary four-site arm is now
   impossible by steps 1–3. On the ordinary five-site arm
   `width24_weak_five_moments_of_ordinary_head` produces the same actual
   [`WeakFive16.Moments` packet excluded separately](../weak-five-complete/PROOF.md).
   The strong arm is excluded by `width24_strong_seventh_rank_ne_eight`.
   Then `StagePadding.strict_stages_gt_of_exact_exclusion` with $n=24,p=16$
   gives $s>24$ for the original strict explicit tableau. This is the
   *direct physical dispatch*, not an application of the stronger abstract
   `WeakFourScalarExclusion` hypothesis in
   [`ERKOrder16OrderedAssembly`](../../../lean/RKCert/ReviewedNative/ERKOrder16OrderedAssembly.lean).
   The joint derivation is a mathematical assembly over ordered fields; no
   end-to-end Lean compilation of the new scalar contradiction is asserted.
