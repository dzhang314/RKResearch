# A sharp eight-row explicit dense chart through tree size five

An eight-stage explicit tableau gives an exact dense derivative decoder through tree size five. This is one fewer than the previously used nine-row chart. The coefficients and decoder below are defined over \(\mathbb Z[1/6]\). The decoder concerns elementary derivative weights, not an order-five step output on the original four rows.

## Literal stage rows and decoders

For a rooted tree \(t\), write
\[
 g_t(X)\coloneqq\frac{|t|}{t!}X^{|t|-1},\qquad
 I_x P\coloneqq\int_0^x P(X)\,dX.
\]
Integrals here are polynomial operations with the indicated denominators invertible. The tree conventions are \(\boldsymbol\Phi_\bullet=\mathbf1\), \(\boldsymbol\Phi_{[t]}=A\boldsymbol\Phi_t\), and \(\boldsymbol\Phi_{t\#u}=\boldsymbol\Phi_t\odot\boldsymbol\Phi_u\). Thus, at any stage with incoming row \(I_x\Pi\), if \(\Pi\boldsymbol\Phi_t=g_t\) through size \(m\), the stage's derivative coefficients agree with \(g_t(x)\) through size \(m+1\), by the product over the children at the root.

Here are the eight chronological predecessor rows, including all nontrailing zero entries:

| Row | Incoming coefficients in the preceding coordinates | Clock |
|---:|:---|:---|
| 1 | empty | 0 |
| 2 | \((1/4)\) | \(1/4\) |
| 3 | \((0,1/2)\) | \(1/2\) |
| 4 | \((1,-2,2)\) | 1 |
| 5 | \((1,0,4,1)/6\) | 1 |
| 6 | \((11,48,-4,-5,4)/162\) | \(1/3\) |
| 7 | \((19,0,-20,3,-2,54)/162\) | \(1/3\) |
| 8 | \((350,0,-328,26,-9,729,0)/3072\) | \(1/4\) |

Let \(E_i\) be the literal read of the \(i\)-th raw coordinate, and define
\[
 M\coloneqq (E_1+4E_3+E_4)/6,\qquad
 R\coloneqq E_6-\frac{64}{81}E_3-\frac4{81}E_4,\qquad
 \mathcal R(P)\coloneqq P(1/3)-\frac{64}{81}P(1/2)-\frac4{81}P(1).
\]
For arbitrary raw data on the first six rows, \(\Pi_4\) gives the unique polynomial of degree at most three with endpoint reads \(E_1,E_5\), mean \(M\), and \(\mathcal R\)-read \(R\). In coefficient form, with the scalar reads evaluated on that data, this polynomial is
\[
 \begin{aligned}
 P(X)&\coloneqq E_1+(E_5-E_1)X+\alpha X(1-X)+\eta X(1-X)(X-1/2),\\
 \alpha&\coloneqq 6M-3E_1-3E_5,\\
 \eta&\coloneqq -27R+\frac{16}{3}E_1-5E_5+4M.
 \end{aligned}
\]
The endpoint conditions leave the final two written basis polynomials. Their means are \(1/6,0\), and the \(\mathcal R\)-read of the second is \(-1/27\). Thus the interpolation works over the stated ring. Integrating this expression at \(1/3\) and \(1/4\) gives the displayed physical incoming rows 7 and 8 respectively; in each case row 7 and row 8 are read with coefficient zero.

The full \(\Pi_5\) is the ordinary degree-at-most-four interpolation at the following five sites, with the raw-data reads indicated:
\[
\begin{array}{c|ccccc}
x&0&1/4&1/3&1/2&1\\ \hline
\text{read}&E_1&E_8&E_7&\dfrac{81}{64}(E_7-\tfrac4{81}E_5-R)&E_5 .
\end{array}
\]
The sites correspond to integer indices \(0,3,4,6,12\) on the twelfth grid. All differences are units in \(\mathbb Z[1/6]\): the positive index differences are drawn from \(1,2,3,4,6,8,9,12\). This specifies every coefficient of the dense decoder, on arbitrary raw data, using the usual cardinal polynomials.

## Exact rooted proof for the mixed observation

On the actual first six rows write \(\mathbf c\coloneqq A\mathbf1\) and let \(C\) be the diagonal matrix with diagonal \(\mathbf c\). Define
\[
 \begin{aligned}
 \mathbf q&\coloneqq A\mathbf c-\mathbf c^{\odot2}/2,&
 \mathbf f&\coloneqq A\mathbf e_2,\\
 \mathbf u&\coloneqq A\mathbf c^{\odot2}-\mathbf c^{\odot3}/3,&
 \mathbf v&\coloneqq A\mathbf c^{\odot3}-\mathbf c^{\odot4}/4 .
 \end{aligned}
\]
Direct multiplication of the six displayed rows gives
\[
 \begin{aligned}
 \mathbf q&=-\mathbf e_2/32,&
 \mathbf f&=(0,0,1/2,-2,0,8/27),\\
 A\mathbf f&=(I/2-C)\mathbf f,&
 \mathbf u&=\mathbf q/6-\mathbf f/48,\\
 \mathbf v&=\mathbf q/32+(C/16-3I/64)\mathbf f,&
 C\mathbf q&=\mathbf q/4,qquad
 \mathbf q^{\odot2}=-\mathbf q/32 .
 \end{aligned}
\]
For example the last row reads \(\mathbf c\) as \(1/18\), \(\mathbf c^{\odot2}\) as \(1/162\), and \(\mathbf c^{\odot3}\) as \(-1/216\). These give the asserted last coordinates of \(\mathbf q,\mathbf u,\mathbf v\). The last read of \(\mathbf f\) is \(4/81\), which equals \((1/2-1/3)8/27\).

The first four rows have ordinary order four for output \(M\) restricted to them. Indeed their output gives moments of \(1,c,c^2,c^3\) equal to \(1,1/2,1/3,1/4\), and it annihilates \(\mathbf q,\mathbf f\). In size three the only other shape differs from its normalized bush by \(\mathbf q\). In size four the corresponding differences are \(\mathbf u,C\mathbf q,A\mathbf q+\mathbf u/2\), all annihilated by \(M\). This proves the ordinary seed order, so the fifth row, with incoming row \(M\) on the seed, gives exact derivative values through size five at clock one. The first row gives exact derivative values at zero.

For every tree through size five, the difference
\[
 \boldsymbol\Phi_t-g_t(\mathbf c)
\]
on the first six rows belongs to the span of \(\mathbf q,\mathbf f,C\mathbf f\). The preceding lists handle sizes up to four. To see the remaining size-five differences, a unary root above size four gives, up to scalar multiples of \(\mathbf v\), the terms \(AC\mathbf q,A\mathbf u,A^2\mathbf q+A\mathbf u/2\). The partitions of the other four vertices among two or more children give \(C\mathbf u,CA\mathbf q+C\mathbf u/2,C^2\mathbf q+\mathbf q^{\odot2},C^2\mathbf q,0\), according to child sizes \(3+1,2+2,2+1+1,1+1+1+1\) (there are two shapes for the size-three child). Each is in the indicated span by the literal identities above.

The read \(R\) annihilates the three vectors: for \(\mathbf f,C\mathbf f\) its subtracted contributions are respectively
\[
 (64/81)(1/2)+(4/81)(-2)=8/27,\qquad
 (64/81)(1/4)+(4/81)(-2)=8/81 .
\]
Consequently \(R\boldsymbol\Phi_t=\mathcal R(g_t)\) through size five, even though the sixth coordinate is not itself an exact point read. Along with the two exact endpoints and the paid ordinary order-four mean, this proves correctness of \(\Pi_4\). Rows 7 and 8 now really give pure derivative evaluations through size five. These, the endpoints, and the mixed relation for \(R\) prove correctness of \(\Pi_5\). No extrapolation of the ordinary seed's order or shape-independence at an unpaid grade is used.

## Consequence for order eleven

The current [shorter scalar rule](SHORT-SYMMETRIC-GRIDS.md) uses eleven sites with the same eight-row reverse chart and nine-row forward chart. Their total before the three literal row merges is 28, so the method uses 25 stages. The [exact witness](witness-11.json) at order twelve has defect −5/33264, a unit whenever 11! is invertible. The longer scalar rule below gives the earlier 26-stage version.

Take the preceding nine-row grade-five forward chart with the literal midpoint and clock-one primitive merges, and use the eight-row chart just proved as the reverse donor. The established signed-reverse identity applies with \(p=11,m=r=5\). The reverse grid consists of \(0,\ldots,12\) divided by 12, omitting index 1. All five reverse clocks above are contained; the physical sites include both endpoints and the midpoint, and all differences are units over \(\mathbb U_{11}\). There are twelve scalar sites. Prescribe the mass moments through degree ten to be \(1/(j+1)\), and the moment of the physical monomial \(X^{11}\) to be zero. This is exactly the signed construction's arbitrary-root test and its cleared next-bush misfit is \(-1\); neither argument requires positivity. The physical count is
\[
 9+8+12-3=26
\]
after the origin, midpoint, and clock-one mergers, which occur on the unchanged forward rows. This improves 27 within the same paid class and does not presume an unverified new forward primitive equality. The next-bush test certifies exact order after every nonzero commutative \(\mathbb U_{11}\)-base change. This section uses the signed reverse theorem and the earlier literal equality, not a runtime rooted replay.
