# A determinant-free final DIRK head exclusion on actual stages

This proof excludes the final one- and two-dimensional head configurations in the paid order-18 and order-19 arguments for diagonally implicit Runge–Kutta methods. It takes the stated head and stage geometry as input. It supplies a simpler final step for the existing stage lower bounds of 25 and 27, not a proof of their earlier reductions or a new table entry. No Lean certificate is claimed.

## The common physical input

Work over a field, with reviewed order \(p\ge13\) and lower triangular \(A\). Suppose the earlier true-head argument gives a stable core \(U\subseteq F_5\) and a representative \(\mathbf w\), with
\[
 F_{5+k}=U+\mathbf wP_{<r+k}(\mathbf c)\quad(0\le k\le4),\qquad
 Z=F_9+CF_9=U+\mathbf wP_{<r+5}(\mathbf c),\quad r\in\{1,2\}.
\]
Here \(C\) is the original clock multiplier. Every product of two actual \(F_5\) vectors is in \(Z\), and the top band has at least \(r+6\) escaping clock fibres. The paid localized-head provider (strip length zero for this input) makes a genuine disjoint representative: \(\mathbf w=0\) on the physical support \(T\) of \(U\), and at its nonzero entries \(w_i=P(c_i)\) for a nonzero scalar polynomial of degree at most \(6-r\). This follows by comparing the \(2r-1\) true shifted squares; it does not posit a low-rank model for unrelated tableau rows. Its mixed product closure gives the genuine support indicator \(\mathbf e=\mathbf1_T\in U\). Each individual clock mask of \(\mathbf e\) also belongs to \(U\), so the sum of the weights removed at each clock is zero. Thus removing the support only in the quadrature calculation preserves every scalar moment. No physical rows or input taps are removed.

In particular there are at least five distinct nonzero exterior clocks. Otherwise their monic hull \(V\) of degree at most four would give all paid tests \(I(X VQ)=0\) for \(\deg Q\le\deg V\), contradicting the shifted Cauchy moment kernel. This uses only order 10 and no signs or generic-vector argument.

At an exterior index where \(w_i=0\), every actual defect through \(F_9\) vanishes. For a true scalar lift \(\mathbf x\) of grade \(j\) with numerical prefix zero before \(i\), the genuine Volterra commutator \(CA-AC-A^2\) at \(i\) is \(-a_{ii}^2x_i\). Its discrepancy is in \(F_{j+2}\). If \(x_i\ne0\) at a quiet row and that grade is paid, \(a_{ii}=0\). The actual primitive of \(X^k\) times its scalar profile is then zero at \(c_i\) whenever \(j+k+1\) is within the quiet grade; the input preserves its zero prefix. This is the common causal refund and read, not an assumption of strict triangularity.

## Rank two and a rank-one shortcut

For rank two put \(\boldsymbol\theta=P(\mathbf c)(\mathbf1-\mathbf e)-\mathbf w\). It is zero on both the head and core supports. The first mask \(C\boldsymbol\theta\) still has **grade five**: \(C\mathbf w\in F_5\), the core mask remains in \(U\), and \(XP\) has degree at most five. Nonzero numerical existence is ordinary polynomial separation at order 11. Its first nonzero row has nonzero clock \(u\); the common quiet-pivot rule gives four zero primitive values there. The second mask \((C-u)\,C\boldsymbol\theta\), with profile \(X(X-u)P\), has grade six, is nonzero by order 13, and has its first nonzero row at \(v\notin\{0,u\}\). It gives three more zero values through the same quiet grade nine. The paid quartic 4+3 obstruction from the preceding hidden-core packet now applies in the forward direction, without an additional scalar case.

For rank one the same idea already works if the first nonzero raw contrast and the first nonzero contrast after multiplication by \(X-u\) occur at nonzero clocks. This includes **every** case \(P(0)=0\). Do not assume those two clocks nonzero when \(P(0)\ne0\). In the favorable case use the raw grade-five profile \(P\) and grade-six profile \((X-u)P\). Four and three reads would make \(F=J^4P\) equal to \(X^4(X-u)^4 R\) with \(\deg R\le1\). The second three reads give a triple zero of \(G=(X-u)F'-3F\) at \(v\notin\{0,u\}\), but
\[
 G=X^3(X-u)^4\left((5X-4u)R+X(X-u)R'\right).
\]
The parenthesis is nonzero of degree at most two: its leading coefficient is \(5+\deg R\) times that of \(R\), a paid unit multiple. This is impossible. The general fallback below is independent of \(P(0)\) and covers all remaining rank-one cases.

## Rank-one fallback: two actual paired cuts

Let \(z_1,\ldots,z_5\) be the first distinct nonzero exterior clocks in physical order, \(w_i\) the head read at their actual debut rows, and \(V_k=\prod_{i\le k}(X-z_i)\). The subtractions below are masked by the *same actual* \(\mathbf e\); the array is never projected to its set of exterior stages.

First \(w_1,w_2,w_3\ne0\). If \(w_i=0\) at one of these, the masked scalar \(X V_{i-1}\), considered at grade five, has a genuine nonzero quiet pivot there. Refund the diagonal. The masked scalars \(X^{1+j}V_{i-1}\), \(j=0,1,2\), all still have degree at most five and zero earlier prefix there. Their actual primitive outputs have zero discrepancy at this head-free exterior row. A rescaled paid shifted Cauchy test for \(V_{i-1}\) of degree at most two contradicts its being monic. Also the fifth debut is explicit, whether or not \(w_5=0\): the grade-five masked \(XV_4\) pivots there, and its grade-seven commutator vanishes at the first three old nonzero head entries by ordinary chronology. Its exterior polynomial has degree at most two, hence is identically zero. Its pivot forces the fifth diagonal to vanish.

Before a specified original cutoff, use one linear subspace of compatible head polynomials \(Q\): there must exist a function \(f\) of the clock with \(f(0)=0\) and an actual core vector \(\mathbf u\in U\) so that \(\mathbf w\odot Q(\mathbf c)=f(\mathbf c)+\mathbf u\) on the entire **strict** prefix. This is the stock prefixCompatible, not a count of nonrepeated rows. For \(m\) old exterior clocks and input head degree \(<k\), let \(Q\) lie in this subspace and let \(P\) range over \(XP_{<m+2}\). In addition impose \(P(z_i)=w_iQ(z_i)\) at the \(m\) old measured labels. Those equations force actual agreement at all earlier exterior live labels and at zero, and the stock core correction subtracts the remaining genuine vector on \(T\). Hence there is an actual numerical lift of \(P\) vanishing on the whole prefix. Its primitive differs from a true clock head of degree \(<k+1\) by a core element, and the reported head polynomial satisfies the same strict-prefix compatibility. This applies to every old-row read, and also to the next row if it is refunded. Increasing the head degree by one costs **at most one dimension in that same compatibility subspace**. Accordingly \(m+2\) scalar dimensions minus \(m\) old tests leave a nonzero primitive kernel even when the refunded next observation is included in the output; it does not enlarge the head response space. A relation with \(P=0\) forces \(Q=0\) by the nonzero old head entries (the first three suffice for both cuts).

For the two cuts use
\[
 \Lambda_t(f)\coloneqq\sum_{i\le t}\frac{z_i^2}{w_i}f(z_i),
 \qquad u\coloneqq z_4,\qquad v\coloneqq z_5.
\]
The denominator \(w_4\) is used only after its nonvanishing has been established in the second cut.

1. Cut strictly before the fourth debut, using \(m=3,k=1\) (grades five and six). Read only the three old rows; the fourth diagonal is irrelevant. This gives a nonzero original profile with \(JP=X^2V_3R\), where \(\deg R\le1\). Differentiating at the old knots and comparing the two high coefficients in Lagrange interpolation of its constant head multiplier gives \(\Lambda_3(R)=\Lambda_3(XR)=0\).
2. Cut strictly before the fifth debut, using \(m=4,k=2\) (grades six and seven), and include the refunded fifth in the output. Here \(JP\) is a nonzero multiple of \(X^2V_5\). Its derivatives at the old rows are nonzero, proving \(w_4\ne0\) without assuming it. Comparing the two high interpolation coefficients for the affine head multiplier gives \(\Lambda_4(X-v)=\Lambda_4(X(X-v))=0\).

Both functionals therefore annihilate \((X-v)R\). Their difference at this polynomial is the term for \(u\), whose weight is nonzero. Since \(u\ne v\), it follows that \(R(u)=0\). Thus \(R\) is a nonzero multiple of \(X-u\), and \(\Lambda_3\) annihilates \(X-u\) and \(X(X-u)\). The term at \(u\) vanishes on both polynomials, so \(\Lambda_4\) annihilates them too. Subtracting the two linear and the two quadratic tests for \(\Lambda_4\) shows that \(\Lambda_4(1)=\Lambda_4(X)=\Lambda_4(X^2)=0\).

The three moments have a one-dimensional nullspace on the four distinct knots \(z_i\). Its coefficients are proportional to \(1/V_4'(z_i)\), as follows by comparing leading coefficients in cubic Lagrange interpolation of \(1,X,X^2\). After rescaling the common head, this gives \(w_i=z_i^2V_4'(z_i)\) at its first four debuts.

## Rank-one fallback: symbolic Euler elimination, not a fixed exception test

Put \(u=z_4\), \(V=V_4=(X-u)V_3\), and \(L(X^d)=X^d/(d+2)\). The actual masked \(XV\) reads at the four old rows and masked \(X V_3\) at the first three give
\[
 LV=\alpha V'+\beta V,\qquad
 L V_3=(X-u)D V_3'+E V_3,
\]
with \(\alpha,D,E\) affine and \(\beta\) constant. Indeed the first primitive fit is affine at the old rows after factoring out \(z_i^2V'(z_i)\), and subtracting the resulting polynomial gives the stated divisibilities and degree bounds. The second fit uses its actual three older rows, not a fourth refund. \(\alpha\ne0\), since the distinct paid diagonal multipliers of \(L\) would otherwise make \(V\) a monomial, whereas its constant and leading coefficients are both nonzero.

Set \(\kappa=\alpha'+\beta\). Apply \(X\partial+2\) to the two equations. At each simple nonzero root of \(V_3\), eliminate \(V_3''\) using \(V'=(X-u)V_3'+V_3\). The resulting degree-at-most-two polynomial vanishes at three distinct points:
\[
 \alpha\big((X-u)D'-D+E\big)-\kappa(X-u)D=0.
\]
If \(\kappa\ne0\), the first Euler equation shows that \(\alpha\) shares no root with \(V\). If it is nonconstant, evaluation at its root forces \(D\) proportional to \(\alpha\); if constant, the degree-two coefficient of the displayed identity likewise forces \(D\) constant. Substitution then gives \(L V_3=\lambda LV\), impossible by their different degrees. Thus \(\kappa=0\). The identity forces \(E=D(u)\) constant; comparing degrees in \(L V_3\) makes \(D\) a nonzero constant. Consequently \(L V_3=D V'\). Applying Euler again gives \(V_3=D(XV''+2V')\) and \((1-2\beta)V=\alpha(XV''+2V')\). Cancel \(V_3\). We obtain precisely
\[
 LV=\eta\big((X-u)V'-V\big),\qquad \eta\ne0,
\]
without ever computing the value of \(\eta\), \(D\), or any clock.

Put \(B_1=J(XV)\), \(B_2=J(X^2 V)\). Differentiation and their zero constants now give the denominator-free identity
\[
 (1-4\eta)B_2=(X-2\eta u)B_1-\eta X^2(X-u)V.
\]
The actual masked inputs \(XV\) and \(X^2V\) vanish before the fifth and the fifth is explicit. Their paid discrepancies through grades six and seven give \(B_1(z_i)=w_i Q_1(z_i)\), \(B_2(z_i)=w_i Q_2(z_i)\) for all five, with \(\deg Q_1\le1,\deg Q_2\le2\). At each of the four old rows the nodal remainder vanishes and \(w_i\ne0\). The degree-at-most-two polynomial \((1-4\eta)Q_2-(X-2\eta u)Q_1\) therefore vanishes identically. Substitute the same literal fifth reads in the inhomogeneous identity: \(\eta z_5^2(z_5-u)V(z_5)=0\), impossible. This does **not** divide by \(1-4\eta\) or by \(w_5\), does not rescale the clocks, and handles every admissible field. All Euler tests differentiate polynomials of degree at most seven with paid integers; the only divisions outside these units were at already verified nonzero clocks, head values or clock differences.

The proof uses original stage order throughout, including when some physical clocks repeat or some weights vanish. Its field assumptions come only from the paid order conditions and the stated actual-head geometry. It does not use a numerical determinant or values of the affine coefficients eliminated above.
