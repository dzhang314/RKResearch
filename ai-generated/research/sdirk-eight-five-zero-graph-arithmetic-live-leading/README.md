# Exceptional leading fibers in the live arithmetic-front graph

This packet treats the live-eighth counterpart of the [silent arithmetic-front chart](../sdirk-eight-five-zero-graph-arithmetic-silent/README.md), but only on the exact exceptional parameter values below. Assume characteristic zero, a strict ten-stage ordinary order-eight SDIRK tableau with exactly five physical quadratic zero rows, genuine degree-two graph support, all off-zero output weights zero, first zero at physical row 4, the literal first three rows off-zero and arithmetic, and physical row 8 live. The five zeros are five distinct live ordinary nodes, as in the linked packet.

**Result.** Every exceptional leading fiber of the live-eighth ordinary moment projection is impossible. The main nonzero-leading projection families are not asserted here.

## 1. Tail and mask

Write the live rear ordinary clocks in physical order \(t_8,t_9,t_{10}\). The two literal weighted reverse phases give
\[
\begin{array}{c|c|c}
 & (t_8,t_9,t_{10}) & \gamma \\\hline
\text{arithmetic}&(m-r,m,m+r)&1-m-r\\
\text{star}&(m+r,m-r,(1+m)/2)&(1-m)/2 .
\end{array}
\]
The gap \(r\) is signed. In particular both reverse star orientations are retained.

Mask the known tail by \(P_3(T)=\prod_{i=8}^{10}(T-t_i)\) and set \(M_j=I(T^j P_3)\) for \(0\le j\le4\). The two other live ordinary clocks give a rank-two sequence, with nonzero \(2\)-by-\(2\) principal Hankel determinant by the [ordinary pivot theorem](../sdirk-eight-ordinary-hankel-pivot/README.md). The \(3\)-by-\(3\) determinant is zero. It is an even polynomial in \(r\), generically of degree six. Its exceptional leading coefficients, including the full scalar factor in the arithmetic case, are
\[
 \frac{(2m-1)(10m^2-10m+1)}{43200}
 \quad\text{and}\quad
 \frac{m(5m^2-3)}{86400}
\]
respectively. The explicit factors are recovered from the degree-seven moments, not from numerical interpolation.

## 2. Arithmetic center

For \(m=1/2\) the entire ordinary \(3\)-by-\(3\) determinant vanishes identically, so it cannot be treated as a finite quartic case. Change ordinary coordinate to centered \(h=T-1/2\). The mask is \(h(h^2-r^2)\); the moments of odd test powers \(h,h^3\) are
\[
 d=\frac1{80}-\frac{r^2}{12},\qquad e=\frac1{448}-\frac{r^2}{80},
\]
and the moments of even tests vanish. The first two chronological zero clocks therefore have centered coordinates \(\pm z\) where \(z^2=e/d\), since the degree-two normal equations have a nonzero pivot \(-d^2\). The signed scaled offset \(S=dz\) gives the exact free quadratic algebra \(S^2=de\), representing both orders.

Use precisely the [arithmetic graph pencil](../sdirk-eight-five-zero-graph-arithmetic-silent/README.md#2-three-supported-equations-in-the-same-arithmetic-pencil), scaled by \(d\). The third early zero clock is physical row 8, with scaled value \(d(1/2-r)\), exactly the scaled common diagonal. Project the two regular and three singular gates by their quadratic norms. Their rational gcds have degrees 100 and 36. Removing only the structural guards gives degrees zero in both cases: the scaling and diagonal product \(d\gamma\), the discriminant \(de\), and the norm of the first ordinary \(L_4\) evaluation are nonzero at every actual configuration. The latter is a norm on both possible orders, and is nonzero because none of the five distinct live ordinary clocks can be Gaussian. Other explicit clock guards remove no factors.

## 3. The other leading drops

For the other three cases, substitute the fixed value or quadratic relation for \(m\) in the literal ordinary Hankel determinant. The residual \(r\) polynomial is degree four in every case:

| Rear | \(m\) guard | Residual degree in \(r\) | Regular and singular gcd degrees |
| --- | --- | ---: | --- |
| Arithmetic | \(10m^2-10m+1=0\) | 4 | 0, 0 |
| Star | \(m=0\) | 4 | 0, 0 |
| Star | \(5m^2-3=0\) | 4 | 0, 0 |

These gcds are with the **full** residual \(r\) polynomial, before removing any factors. For each case, recover the monic quadratic on the two early ordinary clocks by the exact \(2\)-by-\(2\) masked moment system. If its pivot is \(\Delta\), use the two scaled clocks \(a,b\); their sum is a Cramer numerator with sign reversed, and their product is \(\Delta\) times the constant numerator. This yields a monic relation for \(a\), so the graph gates can be evaluated without division in a quadratic algebra over the residual \(r\) algebra. Norming over both orders of the early clocks produces the gcds in the table. Neither the base field nor the \(r\) and \(a\) algebras are assumed real or split. A common solution in any extension would give a common norm root, so all orientations are covered.

Run `python check_center.py` (Python-flint 0.8) and `python check_leading_fibers.py` (SymPy 1.14). The scalar pencil identities are the same as the silent packet; this companion is an independently replayable exact algebraic proof, not a new global stage bound.
