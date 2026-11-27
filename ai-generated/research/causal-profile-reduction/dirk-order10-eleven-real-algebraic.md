# Order ten is attained by eleven-stage DIRK over a real number field

The real DIRK10 minimum is **11 stages**. The previously reviewed field lower bound is attained by the explicit exact algebraic construction below. Its real field of coefficients has degree at most 18 over \(\mathbf Q\); it also gives the endpoint over \(\mathbf C\) and any field containing a copy of that number field. This construction does not prove a rational tableau or an eleven-stage upper bound over arbitrary characteristic-zero fields.

The [exact Python replay](check-dirk10-real-algebraic.py) builds the precise tableau through rational polynomial reductions, verifies a real specialization, and checks all **1,205** rooted order conditions separately from the linear solve used to obtain its entries. The cleared condition on the eleven-vertex star fails by a verified unit witness, so this tableau has exact order ten, not just at least ten. The code does not use floating-point root finding, a nonlinear numerical solve, an unverified symbolic factorization, or the separate finite-field tableau.

## Algebraic coefficients and real place

Use the original clock variable \(X\), and put
\[
\begin{gathered}
 a=1/10,\quad b=3/10,\quad u=3/5,\quad \xi=2,\quad
 \Phi=1-14X+56X^2-84X^3+42X^4,\quad H=X\Phi,\quad T=IH,\\
 P=X(X-a)(X-b),\qquad J=IP,\qquad D=(X-u)P,\\
 r=-500/9,\quad c_0=2044/15,\quad e=17264/75,\quad f=-5656/15,
 \qquad M=e+fX .
\end{gathered}
\]
Here \(I\) is the anchored primitive. The full identity
\[
 H=(r+c_0X)D+MJ
\]
is tested by coefficient-by-coefficient rational expansion, including the \(X^2\) term, and independently by 32 exact rational substitutions using the directly evaluated product. No elimination from the earlier incorrect constant-\(L\) note is used. Also \(IJ=XD/25+(6/125)J+XJ/25\), checked as a full polynomial identity.

Take \(k\) a root of \(125k^3-100k^2-87k+1314=0\), and define
\[
 y=\frac{12948+3125k}{21210+7665k},
 \qquad w=-\frac{25(k^2-2k-24)}{3(434+77k)}.
\]
Let \(Q=(1-X)(119-516X+729X^2-336X^3)\). The replay computes this projective polynomial from a four-by-four rational moment inverse; it is equivalent to using the displayed integer polynomial. Let \(\ell\) be affine with values
\[
 \ell(y)=-M(y)Q(y)/\Phi(y),\qquad
 \ell(w)=-M(w)Q(w)/\Phi(w).
\]
Form the monic cubic \(S(X)\) by dividing \(M Q+\Phi\ell\) by \((X-y)(X-w)\) and by its final leading coefficient. The divisions and the zero remainder are checked in the cubic quotient. Write \(r_8,r_9,r_{10}\) for its three roots and order the physical clocks by
\[
 (0,\xi,a,b,u,y,w,r_8,r_9,r_{10},1).
\]
One may use the finite algebra generated successively by \(k\), \(r_8\), and \(r_9\), with quotients by the stated cubic, then \(S\), then \(S(X)/(X-r_8)\). The last root is minus the quadratic coefficient of \(S\) minus \(r_8+r_9\). Each modulus is monic (the first after dividing by 125), so the dimension of this algebra is \(3\cdot3\cdot2=18\). No field or irreducibility assumption is needed at the intermediate algebra level. Whenever an element is inverted, the rational Euclidean replay provides a multiplicative inverse in that exact algebra. Its image under any specialization is therefore nonzero.

To specialize into the reals, take \(k\) in \((-2.04748,-2.04747)\) by endpoint signs; bisection with exact rational signs refines its interval. The suffix cubic has sign changes on the three disjoint rational intervals
\[
 (0.6377,0.6380),\qquad (0.8664,0.8668),\qquad(1.0154,1.0159).
\]
These signs are checked by rational interval evaluation of all cubic coefficients at the refined \(k\) interval. Three distinct real roots exhaust the cubic. Choosing the first two intervals in order gives a homomorphism from the exact quotient algebra into \(\mathbf R\); its image is the indicated number field. The checks also give \(1.187<y<1.188\) and \(0.473<w<0.475\), so these are actual distinct exterior clocks, not merged labels.

## Deterministic exact tableau

The [exact coefficient export](dirk-order10-eleven-real-coefficients.json) contains every lower-triangular entry of \(A\), the weights, the three monic moduli, and a unit certificate for the eleventh-star residual. Each coefficient is given by its rational coordinates in the nested quotient basis, in increasing degree order. The [decimal CSV](dirk-order10-eleven-real-decimal.csv) is for inspection only. Run `python3 -B check-dirk10-real-export.py` to compare the exact export with the deterministic solve below.

The replay specifies the tableau by a full-rank linear system over this exact algebra, with rational division and all residual rows checked. This gives all literal entries, not approximate coefficients or eigenvalue data.

Let \(\mathcal N\) consist of the nine nonterminal exterior labels (all positions other than 2 and 11). Let \(P_9(X)\) be their monic nodal polynomial. On these labels put
\[
 b_j^{\circ}=\frac{M(c_j)^2}{\Phi(c_j)P_9'(c_j)},\qquad
 \rho=\frac{14}{15\sum_{j\in\mathcal N} b_j^{\circ}}.
\]
The output weights are \(b_j=\rho b_j^\circ\) there, with an additional \(1/30\) at the origin, zero at physical stage 2, and \(1/30\) at stage 11. The ordinary moments through degree nine are also checked exactly.

Write \(C=\operatorname{diag}(c)\), \(Y=1-C\), and \(\beta=b^\top\). Define \(g_2=\xi^3/6\), zero elsewhere, and define \(h\) on the nonterminal exterior as
\[
 h_j=\frac{\xi^2}{3(a-\xi)(2b-a)}\,\frac{H(c_j)}{M(c_j)},
\]
zero at 2 and 11. Let \(G_j=\sigma M(c_j)/P_9'(c_j)\) on \(\mathcal N\), zero elsewhere, with \(\sigma\) fixing \(G_{10}=b_{10}(1-c_{10})^3/6\). Use \(F_6=\langle g,h,Ch,C^2h,T(c)\rangle\).

The unknown entries above the diagonal are zero, as are diagonal entries at physical stages 1, 5, 7, 11. The other entries solve the following linear restrictions, where the span conditions are literal equations with unknown scalar coefficients:
\[
\begin{array}{ll}
 A1=c,\quad Ac=c^2/2,\quad Ac^2=c^3/3+g,\quad Ag=(\xi/2)g+h,\\
 Ac^3-c^4/4\in\langle g,h\rangle, &
 Ac^4-c^5/5\in\langle g,h,Ch\rangle,\\
 Ah\in\langle h,Ch\rangle,& A(Ch)\in F_6,\quad Ac^5-c^6/6\in F_6,\\
 \beta A=\beta Y,\qquad \beta YA=\beta Y^2/2,\qquad
 \beta Y^2 A=\beta Y^3/3+G .
\end{array}
\]
The exact pivot count is 79 including the span coefficients, with no free scalar. Recovering these entries is just the reproducible intermediate construction; sufficiency for rooted order is not taken for granted from this system.

## Independent exact order replay

For a rooted tree with immediate children \(t_1,\ldots,t_m\), the replay computes the actual stage vector as the coordinatewise product of \(A\boldsymbol{\Phi}_{t_i}(A)\), starting from the all-ones leaf. It enumerates all child multisets of each total previous size, hence tests every unordered rooted shape of each size 1–10. The counts are \(1,1,2,4,9,20,48,115,286,719\). Every denominator-cleared condition
\[
 \gamma(t)\,\boldsymbol{\beta}\boldsymbol{\Phi}_t(A)=1
\]
is checked by equality of rational polynomial coefficient lists in the exact tower; no floating value is used in this step. These tests include all mixed products. They agree with the reviewed rooted-tree order definition: the order of siblings does not affect products in a commutative algebra. The subsequent real homomorphism preserves them. The next star test has \(11\beta c^{10}-1\) invertible in the algebra; thus its real value cannot vanish. This also avoids assuming that a nonzero quotient element must be nonzero at every real place.

This is the exact mathematical and executable certificate for the real endpoint. It does not claim that the real algebraic calculation or its embedding has already been formalized as a reviewed native Lean theorem.
