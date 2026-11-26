# Weighted quadrature probes for explicit orders eleven through sixteen

These explicit Runge–Kutta methods have exact order \(p\) with coefficients in any nonzero commutative ring in which \(p!\) is a unit. The construction uses the [direct weighted-site criterion](WEIGHTED-SITE-RANK.md). In addition to weighted point values, it uses some old exact reads as linear equations on the missing reverse polynomial.

| \(p\) | Forward rows | Reverse rows | Scalar sites | Extra live probes | Literal merges | Stages |
|---:|---:|---:|---:|---:|---:|---:|
| 11 | 9 | 6 | 11 | 0 | 3 | [23](tableau-11-weighted.json) |
| 12 | 11 | 6 | 11 | 0 | 2 | [26](tableau-12-weighted.json) |
| 13 | 11 | 8 | 13 | 0 | 2 | [30](tableau-13-weighted.json) |
| 14 | 11 | 11 | 13 | 0 | 2 | [33](tableau-14-weighted.json) |
| 15 | 15 | 11 | 15 | 0 | 1 | [40](tableau-15-weighted.json) |
| 16 | 15 | 15 | 15 | 1 | 1 | [45](tableau-16-weighted.json) |

## The small charts

On either side, write \(v=2x-1\) for the centered version of that chart's own clock, and put
\[
H(v)\coloneqq1-v^2,\qquad \omega(v)\coloneqq H(v)^2.
\]
The six- and eight-row reverse charts are the first six rows and all eight rows, respectively, of the [sharp size-five chart](SHARP-PAID-ERK-GRADE-FIVE.md). They decode through sizes four and five. The nine-row forward chart is the one in [Section 2 of the signed reverse construction](CONSTRUCTION.md#2-the-inexpensive-charts-through-tree-size-seven); it decodes through size five.

For the eleven-row chart, start with this nine-row chart and append two primitive rows at centered clocks \(1/3,1/2\), integrating the preceding decoder. This gives a decoder exact through size six. It uses the two endpoints, the old mean, the midpoint, and the two new point readings. For the fifteen-row chart, append four primitive rows from that eleven-row chart at
\[
-1/2,\quad-1/3,\quad1/3,\quad1/2.
\]
Use these four point readings, the two endpoints, and the old contrast
\[
\ell_6(P)\coloneqq
 \sum_{a\in\{0,\,1/3,\,1/2\}}
 \frac{P(a)}
 {\omega(a)\prod_{b\in\{0,\,1/3,\,1/2\},\,b\ne a}(a^2-b^2)}.
\]
The last expression is the leading coefficient of quadratic interpolation after normalizing by \(\omega\) and treating \(a^2\) as the interpolation variable. The actual three inputs are rows 9, 10 and 11 of the eleven-row chart. At size seven, their first primitive error belongs to \(\omega\operatorname{span}(1,v^2)\), as in the [size-seven chart argument](SHORT-GRADE-SEVEN.md). Thus this contrast is exact through size seven. All read coefficients, chart determinants and rooted inputs are checked exactly by the reconstruction.

The fifteen-row chart has one additional exact functional through size eight. Its actual input coordinates are the four last primitive rows and the old clock-one row, in that order. For any data on these five coordinates, let \(P\) be the unique polynomial of degree at most seven with those five values at \(-1/2,-1/3,1/3,1/2,1\) and
\[
P(-1)=P'(-1)=P'(1)=0.
\]
It is obtained by first fitting \((v+1)^2\) times a quartic to the five values, then using the remaining direction
\[
N(v)\coloneqq(v+1)^2(v-1)(v^2-1/9)(v^2-1/4).
\]
Its derivative at 1 is \(8/3\), a unit. Define the new functional on the data to be \(\ell_6(P')\), and denote its scalar version by \(\ell_7\).

To see why this is an exact read, consider a size-eight tree. At a branching root the five actual stage readings are exact. At a unary root any error in those readings is the primitive of a size-seven discrepancy of the preceding eleven-row chart, sampled at the five clocks. This primitive has the three displayed normalization conditions: it vanishes at the origin, and its derivative vanishes at the endpoints. The old clock-one row is the literal whole integral of the preceding chart, so it gives the fifth sample of the same primitive. The contrast \(\ell_6\) annihilates the derivative of this error because it is exact at size seven. Therefore the new read gives the exact scalar value in both cases.

## The weighted recovery

Use the symmetric scalar sites zero and both signs of the indicated radii:
\[
\begin{array}{c|l}
p & \text{positive centered radii}\\ \hline
11,12 & 1/6,2/6,3/6,4/6,6/6\\
13,14 & 1/6,2/6,3/6,4/6,5/6,6/6\\
15,16 & 1/12,2/12,3/12,4/12,6/12,8/12,12/12 .
\end{array}
\]
The pure sites are \(0,\pm1/3,\pm1/2,\pm1\), with \(1/12\) additionally pure at orders 15 and 16. These contain all reverse donor clocks. All other sites are weighted live probes with their original scalar masses. All gaps are units. Cardinal quadrature integrates through degree \(p-1\); where this uses one more degree than ordinary interpolation, it follows from the odd centered nodal polynomial.

For the missing reverse polynomial \(\sigma\), form the weighted evaluations on the whole polynomial space in the next table. An exact high read contributes an extra row with right-hand side zero, since it annihilates \(\sigma\). The extra live probe at order 16 is a separate unit-mass split at centered zero; the original scalar site at zero stays pure.

| Orders | Space before additional reads | Additional exact equation or observation |
|:--|:--|:--|
| 11, 12 | \(H\mathcal P_2\) | The mixed contrast \(\mathcal R\) of the six-row reverse chart is zero. |
| 13 | \((1+v)\mathcal P_4\) | The scalar version of the literal read \(E_7-\tfrac{17}{81}E_5\) is zero. |
| 14 | \(H\mathcal P_4\) | \(\ell_6(\sigma)=0\). |
| 15 | \(H\mathcal P_4\) | None. |
| 16 | \((1+v)\mathcal P_6\) | \(\ell_7(\sigma)=0\), and one actual point value at zero. |

Here \(E_i\) reads the \(i\)-th raw stage coordinate and \(\mathcal P_j\) is the space of polynomials of degree at most \(j\). The left endpoint at \(v=-1\) is the actual origin of the reverse chart. Accordingly the factor \(1+v\) makes no assertion about the other endpoint in the order-13 or order-16 reverse space. The reconstruction checks each additional high row on every rooted column at the needed size.

The exact weighted matrices, including these extra rows, have a Bézout certificate for their maximal minors. In the chronology, a high equation has known right-hand side zero; it creates no new live input. The resulting coefficients on unsplit stage values are multiples of their scalar masses, so the transpose does not invert any such mass. See [the direct rank argument](WEIGHTED-SITE-RANK.md#the-rank-criterion).

## Order and exactness

Take forward sizes \(m=5,6,6,6,7,7\) and reverse word budgets \(r=5,5,6,7,7,8\), so \(p=m+r+1\le2m+2\). The [single-error expansion](WEIGHTED-REGULAR-PROBES.md#every-ordinary-order-condition-through-seventeen) applies. The late correction pairs use interpolation of the reflected forward error: normalize it by \(H\) at orders 11–14 and by \(1-v\) at orders 15–16. The latter factor comes from exactness at the forward origin, reflected to \(v=1\). Use the following late sites:
\[
\begin{array}{c|l}
11 & \pm1/3,\ \pm1/2\\
12,13,14 & 0,\ \pm1/3,\ \pm1/2\\
15,16 & -1,\ 0,\ \pm1/3,\ \pm1/2,\ 1/12.
\end{array}
\]
Each late pair supplies the paired primitive of the missing reverse polynomial. The added scalar term is zero on every ordinary first-excess forward error: use the exact old mean at order 11, \(\ell_6\) at orders 12–14, and \(\ell_7\) at orders 15–16. This gives all rooted conditions through \(p\).

The origin merges in every construction, and the whole forward primitive at clock one is the literal old output row at orders 11–14. At order 11 the pure midpoint also merges: on arbitrary forward data the two consecutive decoders differ by a multiple of the even mean-zero polynomial \(H(v)(v^2-1/5)\). Its integral to the midpoint vanishes, so the new primitive row is the existing forward midpoint row. This is a literal equality of the entire incoming row. No midpoint equality is used at the other orders, and no clock-one merge is used at orders 15–16.

For exactness let
\[
\mathbf d\coloneqq \mathbf c^{\odot2}-2A\mathbf c,
\]
and let \(C\) denote multiplication by the clock vector. Use the forward formal-zero child
\[
\mathbf w\coloneqq
\begin{cases}
C^3 A\mathbf d,&p=11,\\
-72\, C A C^2 A\mathbf d,&12\le p\le14,\\
C A C^3 A\mathbf d,&15\le p\le16.
\end{cases}
\]
Its numerical suffix is zero: before its last clock multiplications the relevant child is already exact through size \(m+1\) on the suffix. The reconstruction keeps the late null term with coefficient \(\eta\) as follows. The scalar read is applied to the forward residual of this child.
\[
\begin{array}{c|rrrrrr}
p&11&12&13&14&15&16\\ \hline
\eta&17280&-320/9&640/9&-1280/9&76800/7&-153600/7\\
\text{read of residual}&1/1080&-9/20&-9/20&-9/20&7/1200&7/1200
\end{array}
\]
Extend this child and adjoin \(r-1\) root leaves. The order-\((p+1)\) raw output is exactly one: the only remaining term is the product of the indicated two entries and \((-1)^{r-1}2^{-(r-1)}\), the top coefficient of the reflected clock power. The exact verifier checks this formal combination on the actual tableau. It also checks individual next-order defects that generate the unit ideal, so exactness survives every nonzero base change under consideration.

For example, run:
~~~sh
python construct.py 14 --verify-reads
python verify.py 14 --all
~~~
The exhaustive option checks every rooted order condition at orders 11–14. At orders 15 and 16 the chart inputs and first-excess reads are exhaustive, and the full-tableau replay samples ordinary conditions and checks the exact next-order defects. The single-error proof supplies ordinary order for all six constructions. These are not Lean certificates.
