# Off-zero coordinates in saturated strict SDIRK8 with at least seven zeros

Consider a ten-stage strict SDIRK tableau \(A,\mathbf b\) of ordinary order at least eight over a field, with common nonzero diagonal \(\gamma\). Set
\[
 \mathbf c=A\mathbf1,\quad C=\operatorname{diag}(\mathbf c),\quad
 \mathbf g=A\mathbf c-\tfrac12\mathbf c^{\odot2},\quad
 \mathbf h=(A-\gamma I)\mathbf g .
\]
A physical zero means \(g_i=0\) regardless of its weight.

**Characteristic-zero corollary.** If at least seven physical rows have \(g_i=0\), then every physical row with \(g_i\ne0\) has \(b_i=0\) individually. Ordinary zero aggregate alone would not imply this. The statement does not exclude the surviving all-silent configurations or change the unrestricted order-eight stage interval.

**Separate paid-field gate.** Over any field of characteristic zero or greater than seven, if at least two distinct clocks carry physical nonzero residuals, then the first and the second physical residuals are both nonzero. The hypothesis is essential to this proof: at a single off-zero clock, the grade-three pure space is not determined by \(\mathbf g,C\mathbf g\).

## 1. Paid literal row two and the one-clock distinction

At the saturated ten-stage floor, use the [paid flag ranks and support identities](../sdirk-eight-seven-eight-zero-census/README.md). The pure forward \(F_3\) has dimension two, contains \(\mathbf g,C\mathbf g,A\mathbf g\), and the grade-six forward feature space is full. The latter rules out \(c_2=c_1=\gamma\): their first strict tap would vanish, and by rooted-tree induction the first two leaves, products and primitives would agree at those rows on every feature. The first residual is \(\gamma^2/2\ne0\); the second coordinate of \(\mathbf h\) is \((c_2-\gamma)g_1\ne0\) while its first coordinate vanishes. Thus the basis \(\mathbf g,\mathbf h\) is always available.

If two **off-zero** clocks differ, the two columns \(\mathbf g,C\mathbf g\) are independent by their restrictions to those two rows; the determinant is \(g_i g_j(c_j-c_i)\ne0\). They now are another basis of \(F_3\), which therefore vanishes on the physical zero rows. For the first strict tap \(t=A_{21}\), put \(x=c_2=\gamma+t\) and \(d_i=2g_i\). Direct lower-triangular row evaluation gives
\[
 d_1=\gamma^2,\qquad d_2=2(t\gamma+\gamma x)-x^2,\qquad
 (A\mathbf d)_2=t d_1+\gamma d_2 .
\]
The supposition \(d_2=0\) makes \(A\mathbf d\in F_3\) vanish at that row. Hence \(t\gamma^2=0\), so \(t=0,x=\gamma,d_2=\gamma^2\), a contradiction. In particular if there are eight physical zeros and two distinct off-zero clocks, the literal off rows are \(1,2\).

With one off-zero clock it is instead \(C\mathbf g=\gamma\mathbf g\), not a second basis column. The independent \(\mathbf h\) restriction matters. The same full-feature argument gives \(c_2\ne\gamma\), so that row is actually zero in this separate one-clock chart. The [literal first-three equations](../clock-localized-tail/tied-stage-floor/FIRST-THREE-ROWS-AND-PHYSICAL-LEVEL-OBSTRUCTIONS.md) then give \(g_3=0\) as well. This is why the independent \(\mathbf h\) restriction must be retained in the [one-clock census](../sdirk-eight-seven-eight-zero-census/README.md); the clean row-two argument cannot be applied to it.

## 2. Characteristic-zero silence, coordinate by coordinate

The first residual is nonzero, so there are only seven, eight or nine physical zeros in scope. The [paid rank census](../sdirk-eight-seven-eight-zero-census/README.md) and the independent characteristic-zero exclusions cover every placement of possible nonzero weights off the zeros:

| Physical zero count | Off-zero clocks | Why each off-zero weight vanishes |
|---:|---|---|
| 7 | Three distinct | The off rank of \(W_2\) is zero, and \(\mathbf b^\mathsf T\in W_2\). |
| 7 | Two, varying residual at the double | The off rank of \(W_2\) is zero. |
| 7 | Two, equal residual at the double | The only possible activity is a canceled pair at that double. The [two-clock active-pair theorem](../sdirk-eight-seven-zero-two-clock-active/README.md) excludes it over characteristic zero, for all zero-label repetitions. |
| 7 | One | The [active one-clock theorem](../sdirk-eight-half-equal/README.md) rules out seven physical zeros, with either varying or equal off residuals. Its full rank-two \(F_3\) computation and supported-trace proof never assume cubic cleanliness on the zero rows. |
| 8 | Two distinct, or one with two different residuals | The off rank of \(W_2\) is zero. |
| 8 | One with equal residuals | The [active one-clock reduction](../sdirk-eight-half-equal/README.md) leaves only the all-active endpoint pair at \(\gamma=1/2\). The [coprime profile exclusion](../sdirk-eight-half-arithmetic-quadratic/README.md), [shared-root restriction](../sdirk-eight-half-shared-root/README.md), and [last repeated-site exclusion](../sdirk-eight-half-repeated/README.md) eliminate that endpoint pair. |
| 9 | One physical off row | The off rank of \(W_2\) is zero (or use the nonzero residual and single-term pure moment \(\sum_i b_i g_i=0\)). |

The rank-only rows in this table and the multi-clock physical row-two gate require no ordering or real structure; they apply in every paid field. The full ≥7 physical-silence corollary uses the indicated characteristic-zero algebraic exclusions. It asserts neither a positive-characteristic extension of those exclusions nor a structure theorem over arbitrary rings.

## 3. Native boundary

The stock Lean/Mathlib 4.36.0 module `RKCert.Research.SDIRKEightMultiClockRowTwo` verifies the affine rank-two scalar detection, the division-free physical row-two contradiction from the clean cubic implication, and the separate zero-ratio localization identity. The companion `proof-audit.lean` contains the axiom receipts. This scalar type does not assert that the one-clock cubic space is clean, and is not an all-tableau Lean formalization of the combined characteristic-zero census.
