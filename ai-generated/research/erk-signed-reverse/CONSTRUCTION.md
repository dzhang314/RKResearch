# A signed reverse construction of exact paid ERK methods, orders 13–20

The table below gives the allocated rows of the original construction. See the [current index](README.md) for smaller literal tableaux, [the additional row identities](ADDITIONAL-ROW-MERGES.md), and [the shorter symmetric grids](SHORT-SYMMETRIC-GRIDS.md) for the current exact order witnesses.

Write \(\mathbb U_p\coloneqq\mathbb Z[1/p!]\). There are explicit Runge–Kutta tableaux of exact order \(p\) with the following allocated physical rows over \(\mathbb U_p\) and after every nonzero commutative base change. In particular all denominators divide powers of \(p!\).

| Order \(p\) | 13 | 14 | 15 | 16 | 17 | 18 | 19 | 20 |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Physical rows | **35** | **41** | **47** | **54** | **60** | **67** | **73** | **81** |

These are absolute upper bounds, not minima. They improve the existing paid order-thirteen bound and the named uniform leapfrog bounds at orders fourteen to twenty. No comparison to the different real-algebraic coefficient table is intended. The last four orders can also all use the same 34-row double-promoted grade-ten forward chart, giving 62, 68, 75 and 81 rows. The better counts at 17, 18 and 19 use a more balanced choice of forward and reverse chart orders.

## 1. A complete suffix from two ordinary charts

For a rooted tree \(t\), define the exact derivative polynomial and the integration operators by
\[
 g_t(x)\coloneqq |t|x^{|t|-1}/t!,\qquad
 I_x f\coloneqq\int_0^x f(z)\,dz,\qquad
 Jf(x)\coloneqq\int_x^1 f(z)\,dz.
\]
All integrals in the order proof are polynomial operations. A grade-\(m\) forward chart \(\Pi_F\) sends actual stage data to polynomials of degree at most \(m-1\) and has \(\Pi_F\boldsymbol{\Phi}_t(A_F)=g_t\) through tree size \(m\), where \(A_F\) is its actual strictly triangular prefix. Assume the prefix has \(s_F\) rows including an actual zero row. No endpoint pin at orders higher than \(m\), and no additional first-excess moment hypothesis, is required for this suffix.

Set \(r\coloneqq p-m-1\), and suppose \(p\le 2m+2\). Take a second actual explicit prefix \(A_R\) with \(k\) rows and a chart \(\Pi_R\) exact through ordinary tree size \(r\), of polynomial degree at most \(r-1\). Use \(y\) for its clock and \(x\coloneqq 1-y\) for the corresponding physical suffix clock. Choose \(p+1\) distinct sites in \(y\) containing every clock of \(A_R\) and the endpoints. Assume all their differences are units of \(\mathbb U_p\). On the reflected physical sites define the scalar mass functional by
\[
 \mathcal Q[x^j]\coloneqq
 \begin{cases}
   1/(j+1),&0\le j<p,\\
   0,&j=p.
 \end{cases}
\]
For each site \(x_i\) let \(\lambda_i\) be \(\mathcal Q\) applied to its ordinary Lagrange cardinal polynomial. This defines weights by paid arithmetic, even when \(p+1\) is an unpaid prime. The final condition is about the actual physical coordinate \(x\), not the centered coordinate. For reference, the corresponding centered value is
\[
 \mathcal Q[(2x-1)^p]=\frac{\mathbf1_{p\,\mathrm{even}}-2^p}{p+1}
\]
as an identity of rational numbers. The defining calculation of that value is a binomial sum in \(\mathbb U_p\) using the prescribed moments above; it never divides by \(p+1\). Setting the centered moment to zero instead would not detect the next bush at odd \(p\).

### The virtual reverse matrix

List the following rows in reverse chronology to define a strict lower triangular matrix \(L\) and virtual masses \(\boldsymbol\beta\):

1. First list all \(k\) actual rows of \(A_R\), with mass \(+1\) each. They are the only allowed donor columns. No row of \(A_R\) is changed.
2. For each of those rows append a copy of its entire incoming row, zero-padded outside the original \(k\) columns, with mass \(-1\). These copies do not themselves act as donor columns.
3. At every chosen reverse site \(y_i\), append one row with incoming coefficients \(I_{y_i}\Pi_R\) on the original \(k\) columns, with mass \(\lambda_i\) for its physical site \(x_i=1-y_i\). These rows are not donor columns either.

In the copy of donor \(j\), the coefficient on each original reverse column \(h<j\) is exactly \((A_R)_{jh}\), and it is zero on every other column. Thus the copy and the donor have the same entire incoming row and the same clock, not merely the same former quadrature weight. Every virtual row has sum equal to its specified \(y\), because \(\Pi_R\mathbf1=1\).

Consider words in the two operations \(L\) and coordinatewise multiplication by the reverse clock, applied to the all-ones vector. A word of length \(d\) on the donor bank is a rooted derivative column of tree size \(d+1\): the letter \(L\) extends a tree and multiplying by \(y\) adjoins a root leaf. Hence \(\Pi_R\) gives its exact polynomial if \(d\le r-1\). At a final receiver, an outer \(L\) uses precisely \(I_y\Pi_R\) on the shorter donor word, so it acts as integration from zero; an outer clock letter multiplies by the actual \(y\). Induction on length proves exact word values at every receiver through length \(r\). This step uses only ordinary rooted accuracy through \(r\) on the donor *chart*, the literal receiver row, and the equality of row sums with the clocks. It does not presume any stronger word property of the individual donors. It also applies to words with multiplication by \(x=1-y\), by expanding that letter. Their exact scalar operations in \(x\) are multiplication by \(x\) and application of \(J\).

In contrast, each donor and its negative copy agree on the value of every word, without requiring the donor itself to be exact at that clock. For the clock letter this follows from equal clocks, and for \(L\) it follows from their equal incoming rows. Their opposite masses therefore cancel in any pairing with a scalar function of the clock. In particular, for any actual reverse word of length at most \(r\), with vector \(\mathbf w\) and exact polynomial \(f_{\mathbf w}\) in \(x\), one has
\[
 \sum_i\beta_i w_i a(x_i)=\mathcal Q[f_{\mathbf w}a]
\]
for every scalar test \(a\) for which the right-hand side is evaluated. The cancellation is between literal same-clock pairs, not a pointwise order assertion on the original reverse donor rows.

### The primal tableau and the row count

Reverse the virtual order to obtain the primal suffix. In terms of reverse labels, the entry from primal predecessor \(i\) to primal row \(j\) is
\[
 T_{ji}\coloneqq
 \begin{cases}
   \beta_i L_{ij},&j\text{ is an original donor},\\
   0,&j\text{ is not an original donor}.
 \end{cases}
\]
This formula is the weighted transpose because every live donor has mass one. It never divides by any \(\lambda_i\); they may be nonunits or zero. The transpose is strict in primal chronology, and satisfies \(\langle \mathbf a,T\mathbf b\rangle_\beta=\langle L\mathbf a,\mathbf b\rangle_\beta\), with \(\langle\mathbf a,\mathbf b\rangle_\beta\coloneqq\sum_i\beta_i a_i b_i\).

Write \(E f\coloneqq(f(x_i))_i\) and \(I f\coloneqq(I_{x_i}f)_i\) on virtual suffix sites. Use \((I-TE)\Pi_F\) as the prefix-to-suffix block. Use zero output weights on the prefix and the virtual masses on the suffix. The resulting tableau is strictly explicit. Its suffix clocks are exactly the physical sites: applying the two blocks to ones gives \((I-TE)1+T\mathbf1=I1\), since \(\Pi_F\mathbf1=1\).

Every negative copy and every final receiver has zero column in \(L\), and hence zero row in \(T\). Its entire primal incoming row is exactly \(I_x\Pi_F\), involving only the forward prefix. At a fixed site these padded primal rows are therefore identical, even when the reverse incoming rows were different. Each group merges by summing output masses and adding any later outgoing coefficients on the identical coordinates. This preserves every tree coefficient by the rooted recurrence. Because all donor clocks are among the chosen sites, a negative copy never requires a new pure site. At physical zero the pure row is identically zero and merges with the actual origin of the forward prefix. Keeping all corrected donor rows, the literal allocated count after these mergers is
\[
 s=s_F+k+(p+1)-1=s_F+k+p.
\]
No merger between a corrected donor and a pure row is assumed. In particular no new forward endpoint is charged or credited when its literal row is absent.

### Every rooted order condition and the exact next defect

For a child \(t\) put
\[
 \rho_t\coloneqq g_t-\Pi_F\boldsymbol{\Phi}_t(A_F),\quad
 \boldsymbol\epsilon_t\coloneqq\boldsymbol{\Phi}_t(A)|_S-Eg_t,
 \qquad K\coloneqq TE-I.
\]
Here \(A\) denotes the full virtual tableau and \(|_S\) its suffix coordinates. Tree extension gives \(\boldsymbol\epsilon_{[t]}=K\rho_t+T\boldsymbol\epsilon_t\). The difference in a child primitive is therefore zero for all \(|t|\le m\), by simultaneous induction using the exactness of the forward chart and the rooted-sum product. A product at a root containing two nonzero child errors would need at least \(1+2(m+1)=2m+3\) vertices, outside the target. Thus each term in the error for a tree of size at most \(p\) is a scalar multiple of \(W K\rho_t\), with \(|t|\ge m+1\) and a word \(W\) in \(T\) and clock multiplication of length \(\ell\le p-1-|t|\). Each unary extension along the path adds one \(T\); each ideal sibling contributes its scalar power of the clock, with exponent equal to its number of vertices. This gives the indicated length bound by counting the vertices outside the source child and its immediate extension.

Move \(W\) to the adjoint side of the pairing, and write \(\mathbf w\) for the resulting reverse word applied to ones, with exact polynomial \(g\). Its length is \(\ell\), and \(L\mathbf w\) has length \(\ell+1\le p-m-1=r\). The tested weighted source is
\[
 \langle \mathbf w,K\rho_t\rangle_\beta
   =\langle L\mathbf w,E\rho_t\rangle_\beta
      -\langle\mathbf w,I\rho_t\rangle_\beta
   =\mathcal Q[(Jg)\rho_t]-\mathcal Q[g\,I_x\rho_t].
\]
Both tested polynomials have degree at most \(\ell+|t|\le p-1\), since the source residual has degree at most \(|t|-1\). Their integrals are equal. This triangular integration identity is valid over the paid ring: for \(g=x^b,\rho_t=x^a\) both sides equal \(1/((a+1)(a+b+2))\), and every integer divided out is at most \(p\). This proves cancellation on the entire actual first-excess polynomial space, independent of the rank of its higher moments; no special residual values at clock one are presumed. Finally the scalar portions have output \(\mathcal Q[g_t]=1/t!\) through order \(p\). Thus the proof verifies the full rooted equations, not just the reverse words or the scalar problem.

For the bush \(B\coloneqq[\bullet]^{\#p}\), of size \(p+1\) and factorial \(p+1\), the full derivative column is the coordinatewise \(p\)th power of the actual clocks. Its raw output is \(\mathcal Q[x^p]=0\), since the two masses in each signed pair cancel on any function of the clock. Its cleared defect is exactly \((p+1)\cdot0-1=-1\). The method has exact order \(p\) after any nonzero paid base change, including when \(p+1\) is not a unit.

## 2. The inexpensive charts through tree size seven

The seven-stage paid order-six seed used below has the following literal predecessor rows and output weights. This is the known checked order-six seed; the order proof of this note uses its established ordinary order six and no unstated local accuracy.

| Stage | Predecessor entries | Output weight | Clock |
|---:|:---|:---|:---|
| 1 | none | \(11/120\) | \(0\) |
| 2 | \(1/3\) | \(0\) | \(1/3\) |
| 3 | \(0,2/3\) | \(27/40\) | \(2/3\) |
| 4 | \(1/12,1/3,-1/12\) | \(27/40\) | \(1/3\) |
| 5 | \(7/4,-9,9/4,6\) | \(1/12\) | \(1\) |
| 6 | \(-3/64,9/8,-9/64,-27/64,-1/64\) | \(-8/15\) | \(1/2\) |
| 7 | \(-65/4,81,9/4,-33,-1,-32\) | \(1/120\) | \(1\) |

The symbol \(y\) denotes the clock in the chart under construction, whether it ends up used as the forward or reverse chart. Append the actual seed output row at clock one (stage 8). It gives exact derivative values there through tree size seven. Let \(M_j\) be the old output weighted by the \(j\)th power of its clocks, with zeros on new coordinates. It is the exact \(j\)th integral moment on tree derivative data at size at most \(6-j\), by adjoining \(j\) root leaves.

First define \(\Pi_4\) by the two endpoints and \(M_0,M_1\). In the centered variable \(v\coloneqq2y-1\), the polynomials of degree at most three vanishing at endpoints have basis \((1-v^2),v(1-v^2)\). The zeroth and first centered moments split them by the units \(2/3,2/15\), so \(\Pi_4\) is paid. At size-five children the residual has zero endpoint values and both moments zero. Its odd part can only be a multiple of \(v(1-v^2)\) and that coefficient is zero by the first moment. Thus the residual is even with integral zero, so its primitive vanishes at the midpoint. As a result stage 9, the literal midpoint \(I_{1/2}\Pi_4\), gives its derivative read through size six. It is a real additional evaluation, not a reused low-accuracy seed midpoint. The chart \(\Pi_5\) uses the two endpoints, \(M_0,M_1\), and stage 9. On the common kernel of the first four reads the generator is \((1-v^2)(v^2-1/5)\), with midpoint value \(-1/5\), a unit. This gives nine physical stages through derivative size five.

Append stages 10 and 11 as \(I_y\Pi_5\) at \(y=2/3,5/6\), respectively. They give genuine evaluations through size six. The grade-six chart uses both endpoints, \(M_0\), and the exact evaluations at \(v=0,1/3,2/3\) from stages 9, 10, 11. The kernel of endpoints and mean on polynomials of degree at most five has basis
\[
 (1-v^2)(v^2-1/5),\qquad (1-v^2)v,\qquad (1-v^2)v^3.
\]
The midpoint divides by \(-1/5\) in the even direction. The other two reads split the odd directions by their nonzero factors \(v(1-v^2)\) and the difference \((2/3)^2-(1/3)^2=1/3\), all units. Thus \(\Pi_6\) has eleven paid rows. All its clock sites lie in \(\{0,1/3,1/2,2/3,5/6,1\}\).

For \(\Pi_7\) append stages 12 through 16 as \(I_y\Pi_6\) at \(y=1/6,1/3,1/2,2/3,5/6\) in that order. These five genuine size-seven reads and the two old endpoint reads are an ordinary paid Vandermonde (all differences divide powers of six times a factor at most five). The old endpoint at one genuinely reaches size seven because its incoming row is the order-six output. The resulting chart has sixteen rows, all at sites \(\{0,1/6,1/3,1/2,2/3,5/6,1\}\).

## 3. The larger charts and their literal clocks

Three established forward constructions supply the other charts. This note uses only the stated prefixes, not their final suffixes.

* **Grade eight, 22 rows.** The 22-row forward portion of [the 32-stage order-twelve method](../erk-eleven-twelve-moment-splice/ORDER-12-IN-32-STAGES.md) takes the 16-row order-nine seed, its actual endpoint, a new midpoint, and four grade-seven primitives at \(1/12,1/4,1/3,1/2\). The chart \(\Pi_8\) uses the exact old quarter contrast in its earlier layer. Its complete distinct clock set is
  \(\{-1/2,0,1/12,1/4,1/3,1/2,2/3,3/4,1,3/2\}\).
  In indices with denominator twelve these are \(-6,0,1,3,4,6,8,9,12,18\).
* **Grade nine, 27 rows, forward.** Use the first 27 rows of [the two-read preparation](TWO-PRIMITIVE-READS.md), ending with its exact grade-nine chart. This uses the four centered clocks \(-1/3,1/3,3/5,-5/3\) followed by \(-8/3,\pm1/3,\pm2\). All of that chart is paid over \(\mathbb U_{17}\). These are forward clocks; they need not occur in the final quadrature. The separately constructed degree-nine-data chart in [the 41-stage order-thirteen method](../erk-thirteen-moment-splice/ORDER-13-IN-41-STAGES.md) could also be used in this role with the same count.
* **Grade ten, 34 rows, forward.** Use the full 34-row chart of [the two-read preparation](TWO-PRIMITIVE-READS.md) without its optional new output endpoint. It keeps the preceding 27 rows and appends the seven stated grade-nine primitive rows. For definiteness the omitted old centered clock in its last interpolation may be \(-8/3\): use the other four, \(\pm1/3,\pm2\), and the three fresh clocks \(0,\pm2/3\). This selects an actual literal chart among the permitted choices.

### A 27-row grade-nine chart with all reverse clocks on the twelve-grid

At orders 19 and 20 we use another variant of the grade-nine chart as the reverse donor. Its first 18 rows and \(\Pi_7\) are those of the 32-stage order-twelve forward prefix. In centered coordinates \(v=2y-1\), take its four next primitive rows at \(-1/3,1/3,1/2,-2\). Set
\[
 Q(v)\coloneqq(v^2-1/9)(v-1/2)(v+2),\quad
 \omega(v)\coloneqq(1-v^2)^2,\quad F\coloneqq(v^2-1)Q,
 \quad J_j\coloneqq\frac12\int_{-1}^1v^j F(v),dv.
\]
The even part of \(Q\) is \((v^2-1/9)(v^2-1)\), and its odd part is \((3/2)v(v^2-1/9)\). Integrating monomials gives
\[
 \tfrac12\int_{-1}^1\omega Q=0,\qquad
 J_0=J_2=16/945,\qquad J_1=-60/945 .
\]
For instance \(\langle \omega\rangle,\langle v^2\omega\rangle,\langle v^4\omega\rangle\) are \(8/15,8/105,8/315\), and \(\langle v^2(v^2-1)(v^2-1/9)\rangle=-8/189\). The endpoint and four-clock evaluations leave \(F,vF\) as the kernel on degree at most seven. Its zeroth and first moment pivots are \(J_0+J_1=-44/945\) and \(J_0-J_1=76/945\): both are units at orders 19 and 20. Thus they give the exact grade-eight chart for the four chosen rows.

The first inaccurate primitive on these rows has degree at most eight, double endpoint zeros and zero mean, by the actual old grade-seven pins. It therefore lies in \(\omega\mathcal P_{\le4}\) with zero mean. The four sites realize the exact mean on \(\omega\mathcal P_{\le4}\): divide the samples by \(\omega\), interpolate a cubic, and integrate against \(\omega\). The only missed term is a multiple of \(\omega Q\), whose mean vanishes. Consequently this linear read, denoted \(\ell\), annihilates the first primitive errors and gives an exact grade-nine derivative read from the old four stages. At the next order only a unary root can have such a size-eight child; every child of a branching root of size nine has size at most seven, which the preceding chart already reconstructs.

Append five grade-eight primitives at centered \(-1/3,1/3,1/2,-2/3,2/3\). Together with both endpoints, the old zeroth moment and \(\ell\), these give \(\Pi_9\) on polynomials of degree at most eight. To verify payment, let
\[
 D\coloneqq(v^2-1)(v^2-1/9)(v-1/2)(v^2-4/9).
\]
The seven point evaluations leave the kernel \(D,vD\). The value \(\ell(D)\) has only the contribution at \(v=-2\), because the other old nodes are among these new point pins. Its weighted-cardinal numerator there is \(\langle\omega Q/(v+2)\rangle=-J_0/2=-8/945\), a unit. All the remaining factors \(\omega(-2),Q'(-2),D(-2)\) are products of paid units. The vector \((v+2)D\) has zero \(\ell\) read, and its zeroth moment is \(J_2-(4/9)J_0=16/1701\), a unit. These pivots give the paid chart. The resulting 27 actual reverse rows have their clocks among
\[
 \{-1/2,0,1/6,1/4,1/3,1/2,2/3,3/4,5/6,1,3/2\}.
\]
In denominator-twelve indices these are \(-6,0,2,3,4,6,8,9,10,12,18\). Every row in the first 16 is the archived order-nine seed; rows 17 and 18 are its genuine output endpoint and the grade-six midpoint. Rows 19–22 and 23–27 are exactly the four and five primitives specified above, in the listed order. Thus all reverse donor coordinates are specified without relying on the forward variant's different clocks.

## 4. Individual targets, paid grids, and stage counts

In the following table a reverse grid consists of all integer indices in the indicated range except the listed indices, divided by the indicated denominator. The physical sites are their reflections \(x=1-y\). The two ideal endpoints are always retained. Each row makes a tableau by the exact same construction in Section 1. The column \(m,s_F\) specifies the forward chart; the column \(r,k\) specifies the reverse donor chart.

| \(p\) | \((m,s_F)\) | \((r,k)\) | Reverse index range and denominator | Omitted indices | Sites | Physical stages |
|---:|:---:|:---:|:---|:---|---:|---:|
| 13 | \((6,11)\) | \((6,11)\) | \(0,\ldots,18\), /18 | \(1,2,4,5,17\) | 14 | \(11+11+13=35\) |
| 14 | \((7,16)\) | \((6,11)\) | \(0,\ldots,18\), /18 | \(1,2,4,17\) | 15 | \(16+11+14=41\) |
| 15 | \((7,16)\) | \((7,16)\) | \(0,\ldots,18\), /18 | \(1,2,17\) | 16 | \(16+16+15=47\) |
| 16 | \((8,22)\) | \((7,16)\) | \(0,\ldots,18\), /18 | \(1,17\) | 17 | \(22+16+16=54\) |
| 17 | \((9,27)\) | \((7,16)\) | \(0,\ldots,18\), /18 | \(1\) | 18 | \(27+16+17=60\) |
| 18 | \((9,27)\) | \((8,22)\) | \(-6,\ldots,18\), /12 | \(-5,-4,-3,-1,13,17\) | 19 | \(27+22+18=67\) |
| 19 | \((9,27)\) | \((9,27)\) | \(-6,\ldots,18\), /12 | \(-5,-4,-3,-2,17\) | 20 | \(27+27+19=73\) |
| 20 | \((10,34)\) | \((9,27)\) | \(-6,\ldots,18\), /12 | \(-5,-4,-3,17\) | 21 | \(34+27+20=81\) |

In the /18 grid for orders 13–16 the only unpaid possible difference numerator is 17, and its two pairs \((0,17),(1,18)\) are removed. For order 17 there is no unpaid difference at distance at most 18, since 18 has prime factors 2 and 3. The needed reverse site indices are contained in \(\{0,3,6,9,12,15,18\}\), none omitted. For order 18 the /12 span has the potential unpaid distances 19 and 23. The six pairs at distance 19 are \((-6,13),(-5,14),(-4,15),(-3,16),(-2,17),(-1,18)\), and the two at distance 23 are \((-6,17),(-5,18)\); each meets the omitted set. The ten grade-eight donor sites listed above are retained. At orders 19 and 20 the only unpaid possible distance is 23, and both pairs are removed by \(-5,17\). All eleven listed grade-nine donor sites are retained. This accounts for every arithmetic pivot in the choice of the geometric quadrature sites. The ordinary order proof applies because each target has \(r=p-m-1\) and \(p\le2m+2\).

For use of the *same 34-row grade-ten forward chart* at all four last targets, take the following alternative prefixes and grids. At order 17 keep the same /18 grid and use the reverse grade-six chart instead. At order 18 use the full /18 grid (all 19 sites) and the reverse grade-seven chart. At order 19 keep its above /12 grid and use the reverse grade-eight chart instead; its site at \(1/12\) is retained. At order 20 the above construction already uses the grade-ten chart. The resulting counts are respectively
\[
 34+11+17=62,\qquad 34+16+18=68,\qquad
 34+22+19=75,\qquad 34+27+20=81.
\]
The exact bush defect remains \(-1\) for every variant. These comparisons do not require rerunning any search or constructive numerical fixture.
