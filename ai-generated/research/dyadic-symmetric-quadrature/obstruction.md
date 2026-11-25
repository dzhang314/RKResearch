# A dyadic obstruction to all fixed-prefix reflection conics at order 20

**Result.** A symmetric 13-site rational quadrature paying order 16 cannot be extended to a symmetric 17-site rational quadrature paying order 20 simply by adding two reflected pairs while retaining all its sites. More generally, fix any six rational squared magnitudes for a centered order-20 completion with the center and eight reflected pairs. Every possible rational completion with two finite, nonzero new magnitudes must lie on a smooth genus-one fixed-prefix curve: all conic degenerations are obstructed already over \(\mathbb Q_2\), and the moment determinant governing factorization never vanishes. There is no claim that symmetric 17-site order-20 quadrature itself is impossible.

## 1. The exact one-row reduction

Write \(Y=2X-1\), \(T=Y^2\), and \(M(T^j)=1/(2j+3)\). The centered uniform moment functional \(L_Y\) satisfies \(L_Y(Y^{2j+1})=0\) and \(L_Y(Y^{2j})=1/(2j+1)\). For a symmetric support \(0,\pm a_1,\ldots,\pm a_r\), let \(H(T)=\prod_i(T-a_i^2)\). Its nodal polynomial is \(YH(Y^2)\). The three nodal shifts for order \(2r+4\) reduce to \(M(H)=0\): shifts zero and two are odd and shift one is \(M(H)\). Exactness additionally requires \(M(TH)\ne0\). These equivalences follow by polynomial division and Lagrange interpolation on distinct sites.

For a six-pair fixed prefix, put \(M_j=M(T^jH)\). After adjoining magnitudes \(x,y\), order 20 is equivalent to
\[
              M_0 x^2y^2-M_1(x^2+y^2)+M_2=0.                 \tag{1}
\]
Here \(H\) may be rescaled by any rational unit of the coefficient field; multiplying all \(M_j\) by a common nonzero scalar does not change (1).

## 2. A general valuation test for a product of rational squares

Work in the 2-adic field and put \(Z=T-1\), \(v=v_2\). Scale each factor arising from a nonintegral magnitude by \(-a_i^{-2}\). Then the three types of factors are
\[
 T-\alpha\quad(\alpha\in4\mathbb Z_2),\qquad
 Z-\epsilon\quad(\epsilon\in8\mathbb Z_2),\qquad
 1-\beta T\quad(\beta\in4\mathbb Z_2).
\]
In order, these are for \(v(a_i)>0,\ v(a_i)=0,\ v(a_i)<0\). Denote the rescaled product again by \(H\). If there are \(a\) factors of the first type and \(b\) of the second, the unperturbed product is \(T^a Z^b\). For all integers \(j,a,m\ge0\) the beta moment identity gives
\[
 M(T^{j+a}Z^m)=
 \frac{(-1)^m2^m m!}
 {\prod_{\ell=0}^{m}(2(j+a)+3+2\ell)}.
\]
For example, substitute \(T=Y^2\) in the integral and integrate by parts \(m\) times. Every denominator is odd. Let \(d_m=m+v(m!)\), so this expression has valuation \(d_m\) independently of the \(T\)-power.

In \(M(T^j Z^\ell H)\), put \(m=b+\ell\). A term using \(h\ge1\) unit-factor corrections has valuation at least \(3h+d_{m-h}\); any correction of either other type adds at least two to its estimate and changes only the nonnegative \(T\)-power. The table uses \(\min_{1\le h\le m}(3h+d_{m-h})\), so it is valid also when some formal corrections are unavailable (the \(\ell\) additional \(Z\)'s have zero correction).
\[
\begin{array}{c|rrrrrrrrr}
m&0&1&2&3&4&5&6&7&8\\\hline
d_m&0&1&3&4&7&8&10&11&15\\
\min_{h\ge1}(3h+d_{m-h})&\infty&3&4&6&7&10&11&13&14
\end{array}
\]
Thus the valuation is exactly \(d_m\) for \(m=0,1,2,3,5,6,7\) (unique least-valuation term), at least 7 for \(m=4\), and at least 14 for \(m=8\). This works with repeated magnitudes or any additional fixed nonnegative \(T\)-power. More generally, unique dominance holds whenever \(2h>v(m!/(m-h)!)\) for every \(1\le h\le m\).

In particular **any** vanishing \(M_j\) for a six-pair prefix forces \(b=4\). Then, writing
\[
 L_1=M(ZH),\quad L_2=M(Z^2H),\quad r=L_2/L_1,
\]
one has \(v(L_1)=8,\ v(L_2)=10,\ r\equiv4\bmod8\). The two algebraic relations are
\[
          M_1=M_0+L_1,\qquad M_2=M_0+2L_1+L_2.                \tag{2}
\]
These relations use the same normalized \(H\); the ratios also hold in the original monic normalization.

## 3. None of the three special conics has an admissible local point

* **\(M_0=0\).** Here \(M_1=L_1\ne0\). Equation (1) is the circle \(x^2+y^2=M_2/M_1=2+r\equiv6\bmod8\). This includes the proposed direct addition to any symmetric order-16/13-site seed, whether exactness was stipulated or not.
* **\(M_1=0\).** Then \(M_0=-L_1\ne0\) and \(M_2=L_1+L_2\ne0\). Equation (1) asks for \((xy)^2=-M_2/M_0=1+r\equiv5\bmod8\), not a square in \(\mathbb Q_2\).
* **\(M_2=0\).** Now \(M_0=-L_1(2+r)\) and \(M_1=-L_1(1+r)\) are both nonzero. For nonzero \(x,y\), the reciprocal circle from (1) is \(x^{-2}+y^{-2}=M_0/M_1=(2+r)/(1+r)\equiv6\bmod8\). If a magnitude is zero, both are zero, not an admissible support.

A nonzero sum of two \(\mathbb Q_2\)-squares has odd unit part \(1\bmod4\): scale both by their minimum power of two, then either one is odd (the sum is \(1\bmod4\)) or both are odd (the sum is \(2\bmod8\)). A value \(6\bmod8\) has odd part \(3\bmod4\). This proves the two circle obstructions. The hyperbola constant is an odd nonsquare because each odd square is \(1\bmod8\). No assumption on the ordinary real signs, interval location, or quadrature weights enters.

The same no-add-two-pairs obstruction holds from every such symmetric gap-three seed with at most seven pairs: any vanishing \(M_0\) still forces \(b=4\), with the same \(L_1,L_2\) calculation. With fewer than four pairs the zero row is already impossible at two.

## 4. The fourth possible degeneration cannot occur

The determinant \(\Delta=M_1^2-M_0M_2\) equals \(L_1^2-M_0L_2\) by (2). In each case for the number \(b\) of unit pairs, the summands have unequal valuations by the previous table:
\[
\begin{array}{c|rrrrrrr}
b&0&1&2&3&4&5&6\\\hline
v(L_1^2)&2&6&8&\ge14&16&20&22\\
v(M_0L_2)&3&5&\ge10&12&\ge17&19&\ge24\\
v(\Delta)&2&5&8&12&16&19&22
\end{array}
\]
Thus \(\Delta\ne0\) for every six-pair rational prefix. If also \(M_0M_1M_2\ne0\), the quotient
\[
     y^2=\frac{M_1x^2-M_2}{M_0x^2-M_1}
\]
has two simple zeros and two simple poles over the algebraic closure, all distinct by \(\Delta\ne0\). The normalization is a geometrically integral double cover of the projective line with four branch points, i.e. genus one. The \((2,2)\) equation itself is smooth: away from the zeros/poles the \(y\)-derivative is nonzero in its suitable affine chart; at a zero or pole the \(x\)-derivative of the relevant numerator or denominator is nonzero. At either infinity the nonzero \(M_i\)'s and the same local charts give the unramified points. Hence every *possible* admissible finite rational completion occurs on a smooth genus-one fixed-prefix fiber. This does not exclude rational curves where three or more of the magnitudes vary jointly.

## 5. What still remains open

The valuation lemma alone does not rule out \(M(H)=0\) for six or eight pairs. For example, if the other magnitudes have exactly three unit squares, the squared magnitude forced by the single moment equation is
\[
      \frac{M(TH)}{M(H)}
       =1+\frac{M(ZH)}{M(H)}\in1+8\mathbb Z_2,
\]
with \(v(M(H))=4,\ v(M(ZH))\ge7\); this is a square in \(\mathbb Q_2\), not necessarily in \(\mathbb Q\). At eight pairs only unit counts 4 and 8 survive the valuation test. Relative to a six-pair prefix, the possibilities for its unit count \(b\) and number of newly adjoined units are therefore \((2,2),(3,1),(4,0),(6,2)\); this is a necessary local filter, not an existence test.

The alternative of dropping one pair from a hypothetical 15-site symmetric order-18 seed and replacing it by two pairs need not hit any of the degenerate conics. If the old dropped magnitude is \(u\ne0\), then \(M_1/M_0=u^2\), since the old nodal equation is \(M(H(T-u^2))=0\). Here \(M_0,M_1,M_2\ne0\): (2) excludes a simultaneous \(M_0=M_1=0\), and if \(M_2=0\) the reciprocal ratio would be \(6\bmod8\), not the inverse of a square. There are four rational infinity points \((\pm u,\infty),(\infty,\pm u)\). They do **not** by themselves supply nontorsion. Taking \(O=(u,\infty)\), the involution changing the sign of \(y\) is \([-1]\). The sign change of \(x\) is \(P\mapsto B-P\), \(B=(-u,\infty)\), because it is an involution with geometric fixed points, and \(B\ne O\) is 2-torsion. The swap \((x,y)\mapsto(y,x)\) is \(P\mapsto C-P\), \(C=(\infty,u)\), also with geometric fixed points (solve the diagonal quartic). The \(x\)-sign change fixes \(C\), so \([2]C=B\). The four infinity points are exactly the cyclic subgroup of order four generated by \(C\). A finite non-torsion point, another rational seed, or variation of more magnitudes would be new work.

All claims here are identities and exact finite valuation comparisons. No individual rational magnitude, prime grid, numerical branching computation, shared edit, held input or Lean tool was used.
