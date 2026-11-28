# All individual pivot masks in the neighboring chart have finite widths

**Scope.** In the fixed seventeen-stage ordered ERK11 neighboring singleton topology, with all live, half-clock two carriers, both seventh fronts new, \(q=10,n=12\), both full plateau pairs, and sole dormant row \(9\) sharing the active singleton \(s=c_8\notin\{0,1,a,d\}\), take \(K_0(a,b)\ne0\), \(b=1-d\). This confines every individual fixed-moment or raw-affine loss to finitely many algebraic width pairs. It does **not** show that the finite candidates are impossible, or that each admits only finitely many tableaux. The reflected neighboring case transfers. The geometric guards are earned over ordered fields; with these guards the arithmetic is characteristic zero.

## Width-measured fits without the individual fixed pivots

Use actual \(R_9\) on the left, and actual \(L_7\) on the right. In each orientation, retain all five coordinate columns \((\phi,YB_0,YB_1,B_0,B_1)\), treating \(B_f=tA_f\) as a fifth coordinate, not as a known product. The first three rows are the rank-one corrected moments, and the fourth is the actual temporal row. By the [full moment rank proof](ERK11-NONZERO-TEN-TWELVE-NEIGHBOR-FULL-MOMENT-RANK.md), the first three rows have rank three on these five columns. The [endpoint and rank-two proof](ERK11-NONZERO-TEN-TWELVE-NEIGHBOR-ENDPOINTS-AND-FIXED-RANK.md) proves all of the following without an individual sparse pivot:

* both actual endpoint reads of \(Q\) cannot vanish;
* a sole endpoint zero is simple and measures \(Q\) projectively via the corresponding primal width representer;
* each fixed three-column moment block has rank at least two, and its loss of determinant means exactly rank two;
* the full five-coordinate basis has an explicit inverse, by evaluating at the half-clock and the two derivative anchors.

When both endpoint reads are live, if one full \(4\times5\) matrix has rank four, its signed maximal minors measure its true \(Q\) line. Use that \(Q\) in **both** bases, without asking the other matrix to have rank four. Invert the two bases; in each case \(B_f\ne0\) by the live own endpoint, \(A_f\ne0\) by \(B_f=tA_f\), so \(t=B_f/A_f\) and
\[
 P=w\big[U_f+(T_f/t-W_f)(Y-h)\big]
\]
are measured. Reflection to physical \(X\) gives an ordinary first-pool projectivity test. None of these formulas divides by a fixed moment determinant or by a raw affine slope.

The exact replay forms the two fixed determinant polynomials before any fixed-pivot cancellation. The rank-one correction contributes at most one evaluation row to a determinant. Deflate only the actual live widths, slope scales and clock differences. The two factorizations over \(\mathbb Q[a,b]\), with multiplicity one throughout, are:

| orientation | raw fixed bidegree | deflated fixed bidegree | irreducible factor bidegrees |
|---|---:|---:|---|
| Left | \((54,51)\) | \((52,48)\) | \((16,14),(36,34)\) |
| Right | \((49,51)\) | \((44,41)\) | \((21,21),(23,20)\) |

For each exact irreducible factor choose the indicated **actual temporal** matrix to measure \(Q\). The witness has every used width and profile denominator live, and its chosen maximal-minor vector nonzero. Both measured endpoint values are live. Its two first-pool line pairs are oriented before reflection.

| fixed factor bidegree | \((p,a,b)\) | orientation measuring \(Q\) | \(P_L,P_R\) coefficients | physical projectivity |
|---|---|---|---|---:|
| Left \((16,14)\) | \((19,6,18)\) | Right | \((13,12),(13,14)\) | 12 |
| Left \((36,34)\) | \((17,12,3)\) | Left | \((6,10),(12,4)\) | 14 |
| Right \((21,21)\) | \((17,14,1)\) | Left | \((11,0),(12,7)\) | 9 |
| Right \((23,20)\) | \((17,6,8)\) | Left | \((16,11),(4,0)\) | 10 |

These are coefficient witnesses: the indicated fixed factor is zero but the physical projectivity is not. In the first and third rows the own full temporal matrix has **all five** maximal minors zero at the witness; the opposite matrix genuinely supplies the measurement. A finite proof never assumes the chosen width specialization itself could be a tableau.

For each irreducible factor, fix a nonzero maximal minor at the witness and use the stated rational formulas over that factor. Any exact both-endpoints-live candidate either loses a first denominator (including the selected minor) or has zero final physical projectivity. Over \(\mathbb Z_{(p)}\), the polynomial factor is locally primitive and all chosen denominators and final numerator have nonzero value at this witness. Gauss's lemma therefore shows that none is divisible by the exact fixed factor. Each such intersection is finite. This includes widths where neither full temporal matrix can serve, rather than silently discarding them.

## Sole-endpoint zeros use the opposite actual temporal test

Per the [endpoint proof](ERK11-NONZERO-TEN-TWELVE-NEIGHBOR-ENDPOINTS-AND-FIXED-RANK.md), a true \(Q(0)=0\) forces \([\ell_a,R_9]=0\), and measures \(Q\) up to live scale by \(k_L/(X-a)\), \(k_L=[\ell_X,R_9]\). The reflected true \(Q(1)=0\) forces \([L_9,r_d^{\rm ev}]=0\), with measured \(Q=k_R/(X-d)\) up to scale. The off-curve polynomial models used in the replay are divided differences \((k_L(X)-k_L(a))/(X-a)\) and \((k_R(X)-k_R(d))/(X-d)\); they evaluate to the desired quotients on the exact width equations.

On each such model impose the genuinely **opposite** temporal law:
\[
 \left[
 \frac{E(Y)[(w-Y)\ell_1Q(0)-Y\ell_0Q(w)]-w\ell_1 E(0)Q(Y)}{Y}
 \right]_{Y=x}=0.
\]
Here \(E\) is the adjusted representer in the opposite orientation, and \(x=1-z\) for the opposite right, \(x=s\) for the opposite left. The displayed quotient is polynomial even at \(x=0\), exactly the true row multiplied by the live \(\ell_1\); the proof does not discard a centroid clock or an endpoint alias. The correction node is distinct from the measured right outer clock \(1-z\). Clear the width denominator for \(x\) through its third power. After only live deflations the two own-endpoint width equations \(E_L,E_R\) have bidegrees \((16,14),(21,21)\); their opposite temporal equations have bidegrees \((48,44),(58,55)\). The exact **bivariate** gcd of each pair is a unit, with no coefficient specialization argument. Thus single-endpoint candidates are finite without any sparse-pivot assumption. The actual double endpoint-zero case is already empty.

## Raw affine losses

For either orientation \(g_0+t g_1=0\) is the raw full four-row determinant, with no division by the fixed moment inverse. True \(g_1=0\) therefore forces \(g_0=0\). After live deflation the left \(g_0,g_1\) bidegrees are \((36,32),(51,46)\); the right bidegrees are \((43,43),(55,56)\). The exact common factor, up to a nonzero scalar, is exactly \(E_L\) on the left and \(E_R\) on the right, with multiplicity one. Each corresponding common component is already part of the individual fixed-moment case; **do not infer its actual endpoint is zero merely from the width factor's name**. Dividing off that common component on its complement leaves a coprime pair of bivariate polynomials. Their simultaneous exact roots are finite.

Throughout, coprime bivariate polynomials over \(\mathbb Q\) have finite intersection in this two-variable width problem: any common curve, including a whole vertical line at a common algebraic \(a\), would give a common rational factor after conjugating, or equivalently after taking both elimination resultants. This argument covers admissible exact width fields, not just rational or real-number points. The scope ends at finite algebraic widths.

The deterministic standalone arithmetic replay uses python-flint 0.9.0, with no search, no checkpoint and no new Lean diagnostic (reference wall time 2.935 seconds). The table and all polynomial gcds are exact.
