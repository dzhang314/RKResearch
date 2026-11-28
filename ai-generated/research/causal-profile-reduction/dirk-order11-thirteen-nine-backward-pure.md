# Pure reverse grades and the four clean rows on the normalized DIRK11/13 r=9 face

Continue the [nine-label census and virtual quadrature](dirk-order11-thirteen-dirty-chronology.md).
There are two interior clean stages \(e,f\) in physical order, true
origin 0, true terminal 1, and nine dirty singletons. Their
cubic values agree with a cubic \(U(c)\) exactly on the dirty
physical rows; \(h=U(c)-g\) is supported on the four clean rows
and is nonzero on each. In particular no division by \(U\) at a
clean site below is an additional assumption. All claims use
actual order eleven and the established normalized ranks.

## The terminal-zero reverse grade five is supported on the dirties

Let \(Z=\operatorname{Ann}E_5\cap\{\ell_T=0\}\). The endpoint debit
gives \(\dim Z=3\) as in the [two-label exclusion](dirk-order11-thirteen-paired-reverse-exclusion.md).
Every row of \(Z\) annihilates \(h,C h,C^2h\) since \(h\in E_3\)
and multiplication by the clock raises grade by one.
On these three tests only the three nonterminal clean coordinates
\(0,e,f\) can contribute. Those clocks are distinct; their
Vandermonde matrix times the three nonzero values of \(h\) is
invertible. Hence every row in \(Z\) vanishes on all four clean
stages, and in fact
\[
                          Z=\beta g\,{\cal P}_2(c).
\]
For the last identity, the three clock multiples of \(\beta g\)
kill \(E_5\) by the grade-ten budget, vanish at the terminal, and
are independent on the nine distinct active dirty clocks.
This establishes **pure reverse grade five** on the clean rows:
both genuine degree-three and degree-four primitive errors and
the actual derivatives of \(\beta g,\beta Cg\) under \(A\) vanish
on those stages. For the primitive errors the terminal-zero
hypothesis is from the true zero terminal column. For the latter
derivatives \(A E_5\subset E_6\) and
\(\beta g,\beta Cg\in\operatorname{Ann}E_6\). No order for a
transposed RK method is needed.

## Exact forced clean diagonal and bridge

Write \(I P(x)=\int_0^xP,\ I^\leftarrow P(x)=\int_x^1P\).
Let \(M\) be the \(4\times4\) principal matrix on the clean stages
\((0,e,f,1)\) and \(m\) their literal weights. Forward clean
primitives, and the forward zero reads \(Ag=A(Cg)=0\) on clean
stages, give
\[
    M U(c_{\rm c})=I U(c_{\rm c}),\qquad
    M(c_{\rm c}U(c_{\rm c}))=I(XU)(c_{\rm c}).
\]
Here \(c_{\rm c}\) is the four-entry clean clock vector; the
notation \(I U(c_{\rm c})\) means evaluate the polynomial \(IU\).
The reverse purity just proved similarly gives the two row
identities
\[
  (m U(c_{\rm c}))^{\mathsf T}M
             =(m I^\leftarrow U(c_{\rm c}))^{\mathsf T},\qquad
  (m c_{\rm c}U(c_{\rm c}))^{\mathsf T}M
             =(m I^\leftarrow (XU)(c_{\rm c}))^{\mathsf T}.
\]
This uses binomial conversion of the reflected monomial primitive
errors and the two \(\beta g,\beta Cg\) derivatives, subtracting
them from the state with clean support \(h\).

Because the clean block is lower triangular, the actual diagonal
taps at the two interior clean rows and their cross tap satisfy
\[
  A_{ee}=\frac{I(XU)(e)}{e\,U(e)},\qquad
  A_{ff}=\frac{I^\leftarrow((1-X)U)(f)}{(1-f)U(f)},\qquad
  A_{fe}=\frac{I(XU)(f)-f U(f)A_{ff}}{e U(e)}.
\]
The origin-to-first-clean tap is additionally fixed by
\(U(0)A_{e0}+U(e)A_{ee}=I U(e)\).
The two diagonal formulas come from \(A(Ch)\) at the first
interior clean and the backward row \(\beta((1-C)h)A\) at the
last interior clean. The indicated denominators are nonzero
by the anchored virtual quadrature check and distinct clean clocks.

## Mix across a consecutive clean pair

If no dirty stage lies physically between \(e\) and \(f\), both
must be nonzero stages and the following single scalar constraint
on the Jacobi pencil is necessary:
\[
 \sum_{\rho:U(\rho)=0} m_\rho
               I(XU)(\rho)\,I^\leftarrow((1-X)U)(\rho)=0 .
\]
Indeed take the literal clean-supported columns \(u=Ch\) and
\(v=(1-C)h\) in \(E_4\). The paid mixed scalar read
\(\langle v,A^2u\rangle_\beta=\int_0^1 I(XU)I^\leftarrow((1-X)U)\)
uses total grade ten. Its discrete cut has no intermediate dirty
coordinate in an \(A^2\) path from \(\operatorname{supp}(u)\) to
\(\operatorname{supp}(v)\): by causality the intermediate can occur
only at \(e\) or \(f\). The two clean block identities give the
two contributions \(m_q I(XU)(q)I^\leftarrow((1-X)U)(q)\) at
\(q=e,f\). The seven-site virtual rule integrates the right-hand
product exactly, also of degree ten; its endpoint contributions
are zero. Subtracting the two clean terms leaves the displayed
three-node condition. This is only a necessary Jacobi gate on
the adjacent chart, not an exclusion of all nine-label schedules.
