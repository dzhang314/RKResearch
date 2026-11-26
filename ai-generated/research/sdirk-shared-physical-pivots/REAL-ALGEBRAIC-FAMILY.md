# A shorter reverse bank with prescribed contributing clocks

Use the notation and construction of SHARED-PHYSICAL-PIVOTS.md. Let \(r\ge3\), \(p=q+r+1\le2q+2\). Set
\[
    g\coloneqq L(r-1),\qquad h_0\coloneqq\left\lfloor\frac{r-1}{2}\right\rfloor+1.
\]
Let \(d\) be the number of distinct clock sites in a chosen minimal Laguerre decoder of grade \(r-1\). Thus \(r-1\le d\le g\): exactness on its bushy trees makes its \(r-1\) clock power columns independent. Assume
\[
                          p\ge d+2h_0-1 .
\]
Then, for any sufficiently small specified negative real algebraic \(\gamma\), there is an exact order-\(p\) strict SDIRK method all of whose diagonal entries are \(\gamma\), with
\[
  L(q)+L(r-1)+d+\left\lceil\frac{p-d}{2}\right\rceil
\]
physical stages. In particular \(p\ge g+2h_0-1\) is a choice-independent sufficient condition. This is a reduction in the previous shared-bank construction, not an assertion of unrestricted table improvements or a rational tableau.

## Reflected word data

Take the actual \(g\)-stage dense decoder \(\widehat D\) at grade \(r-1\) with tableau \(\widehat A\), common diagonal \(\gamma\), and \(\widehat C\) its actual clock diagonal. Let \(P\) reverse stage order and set
\[
  D\coloneqq P\widehat A^{\mathsf T}P^{-1},\quad
  C_Y\coloneqq P(I-\widehat C)P^{-1},\quad \nu\coloneqq\mathbf1^{\mathsf T},
  \quad \mathcal D(u)(X)\coloneqq
                  (\widehat D P^{-1}u^{\mathsf T})(1-X).
\]
Here \(P=P^{-1}=P^{\mathsf T}\). Lower triangularity and common diagonal \(\gamma\) are literal for \(D\).

For \(u_W\) from the companion, transposition reverses the physical multiplication so that \(\widehat A\) implements the left primitive in \(Y=1-X\), and \(I-\widehat C\) implements multiplication by \(1-Y\). This follows from unary extension and attachment of a fresh root leaf to the *actual* rooted columns. Each letter adds at most one vertex. The reflected nominal action is \(J^*\) or multiplication by \(X\), respectively. Thus \(\mathcal D(u_W)=f_W\) for \(|W|\le r-2\). At length \(r-1\) the error belongs to the reflected first-excess space of this decoder, of dimension at most \(h_0\). The scalar terms in \(I-\widehat C\) are paid by lower grades, so they do not enlarge that space. Use this entire space as \(V\), if desired. The same first-excess result for \(D_0\) gives \(\dim U\le\lfloor q/2\rfloor+1\).

## Putting every reference on a contributing node

Every clock of the physical dense preparations is \(\gamma\) times a positive Laguerre root. The \(d\) prescribed reflected labels \(y_a\) are therefore \(>1\), and converge to 1 as \(\gamma\uparrow0\). Define
\[
         F(X)\coloneqq\prod_{a=1}^d(X-y_a),\qquad
         n\coloneqq\left\lceil\frac{p-d}{2}\right\rceil .
\]
Take the monic degree-\(n\) polynomial \(Q_n\) orthogonal for the positive measure \((-1)^d F(X)\,dX\) on \([0,1]\). Its coefficients come from a positive definite rational-function Gram system over the clock field. Its roots are simple and interior by the sign-changing roots proof. They converge to distinct interior roots of the analogous polynomial for \((1-X)^d\,dX\).

If \(d+2n=p\), use the node hull \(FQ_n\). If \(d+2n=p+1\), use \(F(Q_n+\theta Q_{n-1})\) for sufficiently small nonzero rational \(\theta\), followed by small \(|\gamma|\). Interpolatory weights give precision \(p-1\), by division by the node hull and orthogonality against degrees at most \(n-1\) or \(n-2\), respectively. In the first case \(FQ_n^2\) is a degree-\(p\) vanishing test with nonzero integral. In the second case the degree-\(p\) test \(F(Q_n+\theta Q_{n-1})Q_{n-1}\) has integral \(\theta I(FQ_{n-1}^2)\ne0\). These prove exact precision.

All weights are nonzero. At an interior node, test the square of the free-node cardinal numerator times the fixed hull \(F\); it has degree \(d+2n-2\le p-1\), vanishes at all other sites, and has nonzero signed integral. At an exterior node \(y_a\) the numerator of its weight at \(\theta=0\) is \(I((F/(X-y_a))Q_n)\). The limit as \(\gamma\uparrow0\) is nonzero: orthogonality writes \(I((X-1)^{d-1}(Q_n^0)^2)=Q_n^0(1)I((X-1)^{d-1}Q_n^0)\), where \(Q_n^0\) is the limiting polynomial. Its root set is interior and the left integral has constant sign. These numerator gates persist for fixed sufficiently small \(\theta\) and then small \(|\gamma|\). Thus each of the \(d\) regular references is already a genuine contributing quadrature site. The \(g\) auxiliary rows need no additional reference rows.

## The pivot gates, even with coalescing prescribed sites

The first-excess bands of each actual dense decoder scale with its literal \(\gamma\). A basis of its scale-one band can be chosen with distinct leading degrees. On making each scaled polynomial monic, the basis tends to the corresponding distinct monomials in \(X\) for \(U\) and in \(1-X\) for \(V\). These are statements about fixed finite bases and do not involve uniformity in \(p,q,r\).

The normalized evaluation determinant for polynomials in \(X\) is the evaluation determinant divided by the ordinary Vandermonde. It is a polynomial in the site variables and in the polynomial coefficients, because the evaluation determinant is alternating. At coincident nodes, the normalized limit is nonzero precisely when the corresponding evaluations and successive derivative evaluations are independent: factoring the Vandermonde within each equal-node cluster gives the confluent derivative-row determinant, up to nonzero factorial and different-cluster factors. For distinct nonnegative powers of \(X\), a nonzero combination of \(a\) such powers has at most \(a-1\) positive roots counted with multiplicity. Divide by the lowest power and apply Rolle's theorem inductively to the derivative. This proves the normalized limiting determinant is nonzero even at coincident points in any compact positive interval. Its absolute value there has a positive minimum. By convergence of the monic scaled basis, evaluation of \(U\) is therefore injective on any sufficiently large selection of distinct regular nodes, including the exterior pins clustering at 1. This avoids taking a nonzero limit of an unnormalized determinant at repeated nodes.

For \(V\) it is enough to use \(h=\dim V\) of the free nodes, whose distances \(1-X\) have distinct positive limits. The hypothesis gives \(n\ge h_0\). There are \(k=d+n=\lceil(p+d)/2\rceil\) regular nodes. Since \(q+r-1=p-2\) and \(d\ge2\), we have
\[
           k\ge \lfloor q/2\rfloor+1+h_0 .
\]
Thus there are at least \(\dim U\) regular coordinates left before the pivot block. They all lie in a fixed compact positive interval for the chosen fixed \(p,q,r\). These are exactly the two pivot gates in the companion theorem. All subsequent operations are linear algebra over the finite real algebraic field of the selected data.

## Comparison and scope

The prior exact-all-words bank needs a reverse decoder through grade \(r\); here the grade-\((r-1)\) decoder supplies every lower word and its first lost band is shared across the same physical pivots. Including \(d\) exterior pins costs only \(d+\lceil(p-d)/2\rceil\) regular rows, rather than \(p\) interpolatory rows when all the pins are included or one additional reservoir row per missing pin. For a fixed cutoff, this yields the explicit uniform upper
\[
             L(q)+L(r-1)+\left\lceil\frac{p+L(r-1)}2\right\rceil ,
\]
in place of the old generic \(L(q)+\lceil p/2\rceil+2L(r)\) resource bound. It is not claimed that the prior exact-all-words approach could not choose some cheaper special quadrature, or that this beats the best currently known unrestricted bound at each ordinary order.
