# Residue degrees of two fixed fifteen-stage ERK10 tableaux

The two fixed tableaux in the [prime-field density proof](README.md) give
the following exact natural densities among rational primes. The least
degree is the smallest positive degree of a finite field extension over
which **at least one of these two fixed coefficient tuples** specializes
to exact order ten, with finitely many bad primes omitted.

| Least residue degree | Natural density | Percentage |
| ---: | ---: | ---: |
| 1 | 99646543/212336640 | 46.928567298% |
| 2 | 75818719/165150720 | 45.908803183% |
| 3 | 913/82944 | 1.100742670% |
| 4 | 175979/2903040 | 6.061886850% |

The [literal at 181](P181.md) realizes the degree-three class with an exact rooted order replay.

The density of primes covered over the **specified quadratic field**
\(\mathbb F_{p^2}\) is **1347553/1451520 (92.837370481%)**. The
corresponding density over \(\mathbb F_{p^3}\) is
**13001399/23592960 (55.107112461%)**. A place of degree two
does not contribute to the cubic field unless another usable place has
degree one or three. Degree four covers all good primes because the
Stepanov coefficient field has dihedral Galois group of order eight,
whose element orders divide four.

Away from the same finite bad set, each such specialization also
works in the unramified \(p\)-adic extension of the specified degree,
over its ring of integers and every quotient by a power of \(p\).
The two tableaux give a lower bound on the **lower natural density**
of primes at which any fifteen-stage method exists over that
specified field. There is no nonexistence conclusion elsewhere, and
the unrestricted real and rational stage intervals are unchanged.

## Frobenius and admissible places

Use the [previous proof](README.md) of the coefficient fields,
independence of their normal closures, generator recovery, and the
unit order-eleven defect. In the permutation action of Frobenius on
the embeddings of the coefficient field, its orbit lengths are the
residue degrees of the places above \(p\). A place of degree \(r\)
can give a specialization over \(\mathbb F_{p^k}\) precisely when
\(r\mid k\). The converse holds outside finitely many primes because
the actual clocks recover the generators of the coefficient field
with good reduction; auxiliary coordinates are not being counted as
extra coefficients. The unramified local extension of degree \(r\)
embeds into that of degree \(k\) under the same divisibility condition.

Let \(P(r)\) mean an orbit of length \(r\) is usable. In the signed
permutation group on nine pairs, condition on a base permutation.
For a base cycle of length \(j\), the sign product is uniform and
independent of the signs around the other cycles. Positive product
gives two \(j\)-cycles, and negative product gives one \(2j\)-cycle.
Hence the conditional probability of no usable orbit from this cycle
is
\[
 w_j=\tfrac12\bigl(\mathbf 1_{\neg P(j)}+\mathbf 1_{\neg P(2j)}\bigr).
\]
The probability of no usable signed-pair place is the degree-nine
coefficient of \(\exp(\sum_{j=1}^9 w_j z^j/j)\). Indeed, the
probability of a permutation with \(m_j\) cycles of size \(j\) is
\(\prod_j (j^{m_j}m_j!)^{-1}\), and its conditional probability is
\(\prod_j w_j^{m_j}\).

In the regular dihedral action every orbit has the order of the
acting element. Its no-place fraction is
\[
 \tfrac18\bigl(\mathbf 1_{\neg P(1)}+5\mathbf 1_{\neg P(2)}
                       +2\mathbf 1_{\neg P(4)}\bigr).
\]
Multiply the two fractions using the direct product of the normal
Galois groups. Chebotarev applies because usability depends only on
the conjugacy class. Take \(P(r)\) to be \(r\le m\) for the
least-degree table, and \(r\mid k\) for a specified extension. For
\(m=1,2,3,4\) the joint no-place fractions are respectively
\(112690097/212336640\), \(103967/1451520\),
\(175979/2903040\), and zero. Their consecutive differences, starting
from one at \(m=0\), give the table.

## Exact checks

Run `python3 -B verify-residue-degrees.py`. The replay uses three
independent counts: a rational power-series recurrence, enumeration
of partitions of nine, and a direct integer recurrence. For the last,
choose the base cycle containing the first index. If it has length
\(j\) in an \(n\)-element permutation, there are
\((n-1)!/(n-j)!\) orders for its other elements and \(2^{j-1}\)
sign assignments per allowed cycle product; recurse on the
complement. It agrees with the other counts at all least-degree
thresholds and at specified degrees 1 through 12.

The [standalone Lean receipt](../../lean/RKCert/ReviewedNative/ERK10ResidueDegreeDensity.lean)
checks the integer recurrence outputs and the displayed fractions on
Lean 4.34.1, 4.35.0, 4.36.0 and 4.37.0-rc1. The Galois and
Chebotarev arguments are mathematical, not new Lean endpoints.
