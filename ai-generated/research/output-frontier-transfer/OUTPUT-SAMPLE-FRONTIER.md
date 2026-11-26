# Which frontier is paid by already exact output stages?

Let an old Runge–Kutta tableau have order at least \(P\). The order we wish to prove after the Newton extension is \(p=P+2\). Use the normalized stage vectors
\[
 \mathbf N_t\coloneqq
       \left(\prod_{u\text{ immediate subtree of }t}u!\right)
       \boldsymbol\Phi_t(A) .
\]
Then its nominal polynomial is \(X^{|t|-1}\), its exact output is \(I(X^{|t|-1})\), and multiplication by the clock vector corresponds to adding one root leaf. Write \(I(f)\coloneqq\int_0^1 f(X)\,dX\). The integrals are algebraic on polynomial coefficients.

Choose a tree size \(m\le P+1\). The new frontier is the functional \(I(X^b f)\) on nominal polynomials of degree less than \(m\), where
\[
                   b\coloneqq P+1-m,\qquad D\coloneqq m-b .
\]
The old order supplies all smaller moments \(I(X^j f)\) for \(0\le j<b\). Suppose \(r\) actual old stage rows at distinct clocks \(\xi_i\) are locally exact through size \(m\). In particular, an old output-supporting stage can be used if it is individually exact, regardless of its output sign or size. These rows additionally supply the values \(f(\xi_i)\). A raw numerical old row with no such local property is not treated as a polynomial value.

The following characterization is exact for the information provided just by these old moments and samples. The actual old stage equations may also provide other information. Their general condition is the old zero-relation test in the exact-frontier-pin theorem; the test below is a sufficient certificate for the actual tableau and a necessary criterion for inferring it from the specified observations alone.

## An exact nodal test

Let \(\pi_j\) be the monic shifted Legendre polynomial of degree \(j\) and let
\[
                       F(X)\coloneqq\prod_{i=1}^r(X-\xi_i).
\]
For \(0<D\) and \(r<m\), the following conditions are equivalent.

1. The stated observations determine \(I(X^b f)\) for every \(\deg f<m\).
2. There is a monic polynomial \(\rho\) of degree \(b\) such that \(\rho F\) is orthogonal to all polynomials of degrees at most \(m-r-1\).
3. The hull \(F\) divides a monic combination of the consecutive shifted Legendre polynomials
\[
                   \pi_{m-r},\pi_{m-r+1},\ldots,\pi_{b+r}.
\]
An empty band does not contain a monic combination. If \(D\le0\), the old moments alone suffice. If \(r\ge m\), the samples alone suffice.

For the equivalence, determination is the row-span condition
\[
 I(X^b f)=I(Qf)+\sum_{i=1}^r\lambda_i f(\xi_i)
                        \qquad(\deg f<m)
\]
for some \(Q\) of degree less than \(b\). Put \(\rho\coloneqq X^b-Q\). For \(\deg f<m\), the kernel of evaluation at all \(\xi_i\) consists of \(F\) times polynomials of degree at most \(m-r-1\). Hence the displayed condition is exactly the orthogonality in part 2. Expanding in the monic Legendre basis gives part 3. Equivalently the polynomial in part 3 can be found by an exact linear system of its evaluations at the old clocks. Every coefficient and test lies in the old field. Applying the same formula to the actual old stage vectors gives a concrete frontier row: \(I(Qf)\) is read by the known old output decorated with the corresponding powers of the clocks; the other terms are actual old coordinates.

## Limits and exceptional rational patterns

If \(i\) of the \(r\) samples lie strictly inside \((0,1)\), then payment from these observations alone requires
\[
                          r+i\ge D .
\]
Indeed write \(F=F_{\mathrm{out}}F_{\mathrm{in}}\), using the exterior and interior sample factors, respectively. If \(b+i\le m-r-1\), testing \(\rho F\) against \(\rho F_{\mathrm{in}}\) gives \(I(F_{\mathrm{out}}(\rho F_{\mathrm{in}})^2)\), which has a nonzero sign on the interval. This contradicts part 2. Thus exterior samples do not pay this additional moment any sooner than they pay the full decoder. This argument takes place over the reals and applies in particular to the rationals and the real algebraic numbers.

For \(r<D\), payable samplings are nongeneric. Payment forces a nonzero kernel of the square weighted moment matrix
\[
                       \bigl(I(F X^{u+v})\bigr)_{0\le u,v\le b},
\]
because its product with the coefficient vector of \(\rho\) is zero. Its determinant is not the zero polynomial in the clocks, as exterior clocks make it definite up to sign. The actual relation space of a specific old tableau can be smaller than this sample model; its exact frontier may still be paid for other reasons.

If \(D=2j\) and \(r=j\), part 3 is the single polynomial \(\pi_{b+j}\). Consequently every sample must be one of its roots. Over the rationals the only possible shifted Legendre root is \(1/2\), and it occurs only at odd degree. Indeed the usual integer normalization has constant term \(\pm1\), all roots are simple and interior, and its rational root and the reflected root must both have numerator one in lowest terms. This forces the denominator to be two. Thus the theoretical minimum \(r=D/2\) is impossible over \(\mathbb Q\) for \(j\ge2\). When \(D=2j-1\) and \(r=j\), there are two consecutive Legendre terms. In that extremal chart a rational reflected noncentral pair is impossible as well: reflection would make the top Legendre term vanish at the pair, which it cannot do. These are limits on a sample-only certificate, not RK nonexistence statements.

## A sample group that pays several pins without purchasing a full decoder

Suppose \(P=2q-1\) is odd and \(m=q+j\), so \(b=q-j\) and \(D=2j\). Suppose the old tableau already has \(2j-1\) locally size-\(m\) stages: one at \(1/2\), and \(j-1\) reflected exterior pairs. Write the centered variable and radii as
\[
 U\coloneqq X-1/2,\qquad
 S(U)\coloneqq\prod_{\nu=1}^{j-1}(U^2-r_\nu^2),
                   \qquad r_\nu>1/2 .
\]
These need not be the only active output rows. They may be prior protected head rows and can be used without altering any old stage equation.

The kernel of the displayed polynomial observations is one-dimensional and reflection-odd. To see this, decompose a kernel polynomial into its even and odd parts in \(U\). The old moment conditions respect this parity, and the paired sample constraints separately annihilate both parts. The even part vanishes at the midpoint and at all pairs, so is divisible by \(U^2 S(U)\). If it were nonzero, its quotient would have degree at most \(b-1\), and testing with that quotient would give a nonzero constant-sign integral. Thus the even part is zero.

Write the odd part as \(U S(U) R(U^2)\). If \(b=2c\) or \(b=2c+1\), the degree bound \(\deg f\le m-1=b+2j-1\) gives \(\deg R\le c\), and the old odd moment tests give orthogonality of \(R\) to degrees \(0,\ldots,c-1\) for the measure induced by \(U^2S(U)\,dX\). This is definite up to sign, so \(R\) is proportional to one monic degree-\(c\) orthogonal polynomial. Its real roots lie inside \((0,1/4)\). This characterizes the last kernel dimension, including \(c=0\).

If \(b\) is even, the frontier \(I(X^b f)\) on the old kernel reduces to the centered even test \(I(U^b f)\) and is zero. Thus the consumer at target \(p=2q+1\) can release at least \(j\) pins, using a scalar frontier instead of the full decoder through \(m\). If \(b\) is odd, the frontier on the nonzero model relation is nonzero: the leading odd moment of \(U S(U)R(U^2)\) is the first unpaid orthogonal moment for \(R\). One cannot make the same inference from these samples alone in that parity.

There is a useful construction regardless of this last parity. The \(2j-2\) exterior samples already give a full old decoder through \(m-1\), because the moment deficit at that size is \(2j-2\). A single new protected receiver at a distinct exterior time can therefore be pure through \(m\), while it is itself still an output receiver. Its sample annihilates the remaining odd model relation, since the roots of \(R\) lie in \((0,1/4)\). Subsequent protected receivers can be locally exact through \(m+1\). In the favorable parity the full degree-\(m\) decoder is only used after this row exists. This is a direct application of the truncated Newton freedom on the strict early block, not a change to old coefficients.

If all \(2j-1\) prior samples are merged, the \(p-1\)-site chart has room for that completing receiver exactly when \(q\ge2j\); at least one more high outgoing receiver fits when \(q\ge2j+1\). These are useful scheduling thresholds at low orders. An old midpoint can instead be kept as a sample without merging it, leaving its clock available for a new, higher-accuracy midpoint.
