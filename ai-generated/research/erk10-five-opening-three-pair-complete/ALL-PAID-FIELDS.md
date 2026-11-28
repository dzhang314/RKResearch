# The full chart is excluded over every paid field

The [complete chronology exit](README.md) in fact applies over any
field in which \(10!\ne0\), with **no** restriction on the number
of zero-total pairs. This note replaces only the supply of ordinary
completion targets and the stated score scope; the chronology,
physical-defect, and rank arguments remain unchanged.

Let \(\mathcal L\) be the set of distinct high forward clock labels
whose grouped scalar score is nonzero. The scalar order-ten moment
tests through degree nine give
\[
 H_{ij}=\frac{1}{i+j+2}
       =\sum_{x\in\mathcal L}W_x\,x^{i+1}x^j,
 \qquad 0\le i,j<5 .
\]
The opening origin contributes zero because \(i+1\ge1\). Thus the
shifted Hilbert \(5\) matrix factors through \(|\mathcal L|\)
columns. Its determinant
\(1/(2^{12}3^7 5^5 7^4)\) is nonzero in every such field.
In particular \(|\mathcal L|\ge5\). At most one of those labels
is the reverse endpoint. So at least **four distinct interior
labels have nonzero group score**. Each supplies an ordinary
completion as defined in the main proof: a live singleton, or the
closing copy of a nonzero-total pair. The case of three zero-total
pairs is already impossible for scalar support. Two zero-total
pairs can be included in the full proof.

Here are the exact two places where target availability is needed.

1. The first two ordinary targets \(s,t\) always exist and are
   distinct nonzero ordinates. The possible earlier zero-total
   completions can be folded *independently* by
   \(K_{i,j_1}-K_{i,j_2}\) at every such pair \(j\).
   This identity applies separately to each scalar source and each
   \(D_3\) profile, as they are opposite on each zero-total pair.
   Two such earlier completions add no new scalar label. The
   no-leakage determinant, the old-three functional comparison and
   the leakage calibration work without change.
2. When the first ordinary completion follows all three openers,
   every ordinary target is later than any possibly blind opener
   in reverse. This provides at least two distinct physical clocks
   in that reverse suffix. Therefore the first two different
   forward clocks, which witness independence of the two residual
   annihilators even with the blind coordinate removed, are again
   available. It is not necessary that both are closing copies of
   nonzero-mass pairs.

Before the first ordinary completion, folded zero-total closures
still only supply already-open scalar labels. If the blind
opener's prior taps are killed on the effective coordinates, that
proves its blindness to those inputs irrespective of how many
zero-total pairs had closed. Likewise in the leakage comparison,
each normalized mode continues to track that label's scalar tap
independently through its zero-total closure, and a zero-score
pair contributes zero on scalar sources. Hence no proof step
requires the earlier rational parity restriction.

## Ring consequence

Over a nonzero commutative ring inverting \(10!\), let
\(x_1,\ldots,x_7\) be the seven scalar forward labels of this chart
and
\[
 \sigma=\prod_{i=1}^7 x_i\prod_{1\le i<j\le7}(x_i-x_j).
\]
If the actual word-budget chart exists, **\(\sigma\) is nilpotent**.
Otherwise \(R[1/\sigma]\) is nonzero, and map it to any maximal
residue field. Every label and label difference is then nonzero;
the normalized word conditions and strict chronology specialize,
so the resulting paid field chart contradicts the theorem above.
This excludes the chart in every such domain, and in every such
ring whose seven forward labels and pairwise differences are
units. It is not an unconditional arbitrary-ring gap if all
residue fields merge labels.

The shifted Hilbert determinant is replayed exactly in
[the original scalar audit](../erk10-five-opening-three-pair-all-open/audit.py).
The ring localization and observer argument are mathematical.
