# Preparing the next affine lift by primitive observations

This refines the preparation of rk-source-paid-affine-two-order-lift.md. Let that lift start at a prepared order \(q\), put \(m\coloneqq q-2\), and let its new order be \(p\coloneqq q+2=m+4\). All coefficients are in \(\mathbb U_p\coloneqq\mathbb Z[1/p!]\). The ordinary and exact-order suffix constructions are unchanged. No new family of corrected donor profiles is needed.

## The information supplied by old rows

The completed suffix has a pure row \(I_x\Pi_m\) at every geometric clock. These pure stage-derivative readings are exact through tree order \(m+1\) and therefore give a chart \(\Pi_{m+1}\) at no stage cost by paid interpolation.

For a tree \(t\) of order at most \(m+2\), let \(D_t\) be the polynomial interpolated on \(m+2\) of those pure rows. The outcome of the previous lift gives
\[
 D_t=g_t-P_t,\qquad
 P_t\coloneqq
 \begin{cases}
 I_x\rho_r,&t=[r],\ |r|=m+1,\\
 0,&\text{otherwise}.
 \end{cases}
\]
The primitive nuisance belongs to the module
\[
 \mathcal B\coloneqq x^2(1-x)^2\mathcal P_{\le m-3},
\]
where \(\mathcal P_{\le j}\) denotes polynomials of degree at most \(j\) over the paid ring. Its mean is zero by the two old integral pins on \(\rho_r\). The new order-\(p\) tableau supplies the mean, first and second moments of \(g_t\) for all trees through order \(m+2\). Indeed, the new output read multiplied coordinatewise by the \(j\)th power of the clocks is exact when \(|t|+j\le p\). Subtracting the corresponding integrals of \(D_t\) gives the three moments of \(P_t\).

The already corrected donor rows do not generally give more independent observations. At an exceptional unary tree, their differences from their pure companions, after weighting by their donor masses, form the four coordinates
\[
 d_j\coloneqq\sum_i\beta_i L_{ij}\rho_r(x_i)
\]
on the donor index \(j\). Applying the invertible four-donor read matrix to these coordinates gives the weighted pairings of \(L\mathbf1,L\mathbf y,L\mathbf y^{\odot2},L\mathbf u\) with \(\rho_r\). They are respectively
\[
 0,\quad \tfrac12 I_1((1-x)^2\rho_r),\quad
 \tfrac13 I_1((1-x)^3\rho_r),\quad 0.
\]
The affine and constant defect profiles have disappeared by the old pins. Integration by parts with \(P_t(0)=P_t(1)=0\) shows that the two nonzero expressions are combinations of the first and second moments of \(P_t\). Thus these four donor companions are not four new nuisance coordinates.

## One appended row can observe any paid linear functional

Pad the old chart with zero coefficients on the new stages and define
\[
 C\coloneqq\Pi_{m+1}-\Pi_m.
\]
On tree data through order \(m\) the map \(C\) is zero; on tree data for \(r\) of order \(m+1\) it is \(\rho_r\). Fix an existing pure row at a clock \(z\), and let \(T\) be any paid linear functional on polynomials of degree at most \(m\). An extra explicit row with incoming coefficients
\[
 I_z\Pi_m+T C
\]
has the same order-\((m+1)\) stage derivative reads as that old pure row. At order \(m+2\) their difference is zero at every non-unary tree and \(T\rho_r\) at a unary tree \([r]\). This follows directly from the tree extension and rooted-sum recurrences: every child of a non-unary tree of that order has order at most \(m\). The monitoring rows have zero output weights and do not change the order already proved.

In particular one row can observe any paid linear functional of \(P_t\), by setting \(T\) equal to that functional composed with \(I_x\). This includes arbitrary polynomial coefficients instead of merely point evaluations. A functional on \(\mathcal B\) extends to all polynomials of degree at most \(m+1\) by division by the monic factor \(x^2(1-x)^2\). One can take \(z=0\), in which case the old pure companion is the literal zero row and the appended row still has clock zero.

With no interior pins, the three known moments suffice for the coefficients of degree at most two in \(P_t/(x^2(1-x)^2)\), once the higher coefficients have been read by the appended rows. The small moment matrix is paid: for the weight \(x^2(1-x)^2\) its monic orthogonal polynomials through degree two have unit pairings with the corresponding monomials. Indeed, the derivative of order \(j\) of \(x^{j+2}(1-x)^{j+2}\), divided by the weight and normalized to be monic, gives such a polynomial by integration by parts. Its leading factor and its pairing with \(x^j\) only use factorials through \(2j+5\le9\). For \(m=4\), only degrees zero and one are present and the factorials stop at seven. Thus the unpinned count is at most \(\max(0,m-5)\), without a mixed quadrature determinant.

More generally, let \(Z\) record any prescribed homogeneous conditions on \(P_t\), including derivative or double pins at actual old primitive rows. Over the paid ring, the kernel of \(Z\) is a saturated free summand: the quotient is isomorphic to its torsion-free image in a free module over this localization of the integers. Therefore zero constraints can be used without inverting a nonunit minor of \(Z\). To count nonzero observed moments as independent free data, their map on the kernel must also admit a paid right inverse. If these conditions hold, a complementary basis and the arbitrary observer rows above recover the remaining coordinates. This is optimal for linear recovery on the unrestricted nuisance module with these free observations, by comparing ranks over the rationals. It is not a lower bound on actual trees or on methods using other old rows.

## Literal old rows give genuine double observations

Suppose a usable existing stage at \(z\) has a literal incoming row \(W_z\) and stage order at least \(m+1\). Stage order here means exact stage-value coefficients through that tree order, not merely exact stage-derivative coefficients through it. The already existing value read and primitive row then can both be pinned to \(\Pi_m\) at no row cost. If
\[
 E_z\Pi_m=E_{\mathrm{stage},z},\qquad I_z\Pi_m=W_z,
\]
then the new source residual at tree order \(m+1\) vanishes at \(z\) and has zero primitive there. Hence \(P_t(z)=P_t'(z)=0\). If the available stage has only stage order \(m\), its value still gives the derivative zero but the primitive zero does not follow.

Here is a paid simultaneous patch for actual old rows when a chart did not yet have those pins. Let \(C_0\) denote all relevant clocks including zero and one, and write \(B_z(x)\coloneqq\prod_{w\in C_0\setminus\{z\}}(x-w)^3\). Define
\[
\begin{aligned}
 R_{E,z}(x)&\coloneqq\frac{(x-z)^2B_z(x)}{2B_z(z)},\\
 R_{I,z}(x)&\coloneqq\frac{(x-z)B_z(x)}{B_z(z)}
     \left(1-(x-z)\frac{B_z'(z)}{B_z(z)}\right).
\end{aligned}
\]
For \(q_E=R_{E,z}''\) and \(q_I=R_{I,z}''\), the pairs \((E_zq_E,I_zq_E)\) and \((E_zq_I,I_zq_I)\) are \((1,0)\) and \((0,1)\). Their evaluations and primitives at every other pin are zero, and \(I_1(xq_E)=I_1(xq_I)=0\) by integration by parts. Add \(q_E(E_{\mathrm{stage},z}-E_z\Pi_m)+q_I(W_z-I_z\Pi_m)\) to the chart. These differences are zero through the chart grade, so its existing exactness is unchanged. The degree bound is \(3(|C_0|-1)\le m-1\), and all normalization factors are paid.

It is not enough to promote a lower-grade row by declaring another chart. One attempted creation of a high stage would first move \(m-1\) ordinary pure rows forward to make \(\Pi_{m+1}\), then try to preserve their literal incoming rows while adjusting \(\Pi_m\) at an additional primitive clock. The primitive of a chart adjustment has degree at most \(m\). To preserve those rows it vanishes at their \(m-1\) clocks and both endpoints, already \(m+1\) distinct roots, so it is zero. This obstruction concerns the all-literal preservation route, not the double-pinning lemma above.

## Uniform zero-cost pins combined with all three moments

The following particular symmetric pins improve the guaranteed count without presuming any old higher-stage-order interior rows. A moved ordinary pure row has stage order \(m\), so it provides a derivative zero. It costs no physical row: move it ahead of the suffix, pin \(\Pi_m\) to its derivative read while preserving the literal row \(I_z\Pi_m\), and merge its pure suffix labels. The four corrected donors remain the same.

The quadrature can retain these pins without increasing \(n\). Take \(D\) to be the smallest multiple of six at least \(n-1\). From the grid of denominator \(D\), retain \(n\) nodes symmetrically, protecting the endpoints, midpoint, thirds, and, when needed, sixths. The only possible unpaid distance is \(D-1\), since \(D\le p+3\) and \(D,D-2,D-3\) are smooth. If that distance is unpaid, omit indices \(1,D-1\); there is enough surplus because then \(D>n-1\). In the cases using sixths the protected sixths are distinct from these discarded indices. The remaining surplus is discarded in symmetric pairs. This retains the paid differences and the symmetry that supplies degree \(p-1\).

Use the centered coordinate \(u\coloneqq 2x-1\), set \(t\coloneqq u^2\) in the calculations below, and let \(\omega(u)\coloneqq(1-u^2)^2\). A correction polynomial is constructed as the derivative of a centered primitive with double zeros at \(\pm1\), zeros at the interior pins, and zero mean. Its derivative can have any prescribed values at the pins by the constructions below. Changes of scale between \(x\) and \(u\) are units. The primitive zeros preserve the literal incoming rows, and its mean preserves the first clock-weighted output read. The basic evaluation identity is
\[
 \frac18\left(\frac12\int_{-1}^1\omega(u)t^j\,du\right)
 =\frac1{(2j+1)(2j+3)(2j+5)} .
\]

### One, two, or three pins

For one pin at the midpoint, the correction \(4x(1-x)(1-5(2x-1)^2)\) has value one there and integral zero both on \([0,1/2]\) and on \([0,1]\); it preserves the clock-weighted moment by symmetry. It has degree four.

For two pins at \(u=\pm1/3\), let \(a\coloneqq1/3\). The odd primitive \(u\omega(u)(t-a^2)\) has equal unit derivatives at the pins and automatic zero mean. The even primitive \(\omega(u)(t-a^2)\) has opposite unit derivatives at the pins. Correct its mean by a multiple of \(\omega(u)(t-a^2)^2\), whose mean is \(128/8505\), a unit. This does not change its derivatives at the pins. The derivatives of both correction primitives have degree at most seven.

To add the midpoint to those two pins, use the odd primitive \(u\omega(u)(t-a^2)\) and its multiple by \(t\). Their derivative data at \(0,1/3\) form a unit triangular matrix. For the even primitive use \(t\omega(u)(t-a^2)\), correcting its mean with \(t\omega(u)(t-a^2)^2\), whose mean is \(128/18711\). This gives arbitrary antisymmetric derivative data and zero derivative at the midpoint. The correction polynomial now has degree at most nine.

These one to three derivative constraints are independent over the paid ring even after fixing all three moments. The following odd and even examples are moment-free:
\[
 P_3\coloneqq\omega(u)(u^3-u/3),\quad
 P_4\coloneqq\omega(u)(u^4-6u^2/11+1/33),\quad
 P_5\coloneqq\omega(u)(u^5-5u/33).
\]
In particular \(P_3'(0)=-1/3\), \(P_3'(1/3)=64/729\), and \(P_4'(1/3)=-3584/24057\). The last two results give opposite parity components for the two symmetric derivative constraints, both units. Also \(P_5'(0)=-5/33\), \(P_5'(1/3)=-128/8019\), so the determinant for the odd-profile derivatives at \(0,1/3\) is \(448/24057\), a unit. This gives all three constraints with the paid free moments.

### Five pins

For \(m\ge14\), use \(u=0,\ \pm1/3,\ \pm2/3\). Define
\[
 K(t)\coloneqq(t-1/9)(t-4/9),\qquad
 \Omega(u)\coloneqq t\,\omega(u) K(t)^2.
\]
Odd primitives \(u\omega K\) times degree-at-most-two polynomials in \(t\) give arbitrary symmetric derivative values at the three nonnegative pins by their paid Vandermonde. Even primitives \(t\omega K\) times degree-at-most-one polynomials in \(t\) give arbitrary antisymmetric derivative values at the two positive pins. They can be adjusted to mean zero by a multiple of \(\Omega\), without changing any primitive value or derivative at a pin. The identity above gives
\[
 \frac18\left(\frac12\int_{-1}^1\Omega(u)\,du\right)
  =\frac{3920}{3^9\cdot5\cdot7\cdot11\cdot13}.
\]
Its numerator is \(2^4\cdot5\cdot7^2\). The correction derivatives therefore have paid coefficients and degree at most thirteen.

To show that these derivative constraints can be combined with all three moments, first prescribe the derivative data by ordinary paid Hermite interpolation with zero values at the five pins and double boundary zeros. The required degree is at most thirteen. It remains to split the moment map on the derivative-zero subspace. Its odd and even parts may be treated separately. On the odd part use \(u\Omega\) and
\[
 O(u)\coloneqq u^3\omega(u)\bigl(t^2-73t/81+4/27\bigr).
\]
Their derivatives vanish at all five pins. The first centered moments, divided by eight, are
\[
 \frac{144592}{3^{10}\cdot5\cdot7\cdot11\cdot13\cdot17},
 \qquad
 \frac{-194}{3^6\cdot5\cdot7\cdot11\cdot13}.
\]
The remaining numerators \(1291\) and \(97\) after removing paid factors are coprime, so a paid linear combination realizes any odd first moment.

On the even part \(\Omega\) has unit mean, and its second moment divided by its mean is \(\mu\coloneqq1291/1785\). Define \(E_2\) and \(E_3\) by
\[
 E_2\coloneqq\omega(t^2-2t/27+5/81),\qquad
 E_3\coloneqq\omega(t^3+10t/81+41/729).
\]
Their derivatives vanish at all five pins. The corresponding functionals given by the second centered moment minus \(\mu\) times the mean, divided by eight, are
\[
 \frac{-70768}{3^6\cdot5^2\cdot7\cdot11\cdot17},\qquad
 \frac{-56685916}{3^8\cdot5^2\cdot7^2\cdot11\cdot13\cdot17}.
\]
The remaining numerators \(4423\) and \(14171479\) are coprime (the latter has residue \(187\) modulo \(4423\)). These are the desired paid pivots by Bézout. The degree of all odd and even test polynomials is at most \(m+1\), and all denominators are paid because \(p\ge18\). These moment calculations use the displayed beta identity and the two simple derivative tests: for even \(\omega C(t)\) the interior test is \((1-t)C'-2C\), and for odd \(u^3\omega C(t)\) it is \(2t(1-t)C'+(3-7t)C\), at \(t=1/9,4/9\).

## Row bound and scope

One can use \(k=0\) for \(m=4,5\), \(k=1\) for \(m=6,7\), \(k=2\) for \(m=8,9\), \(k=3\) for \(10\le m\le13\), and \(k=5\) for \(m\ge14\). The preparation then uses at most \(\max(0,m-5-k)\) observer rows and one new endpoint, with the old two output reads repinned as before. In particular it uses four observers for the lift ending at order eighteen and six for the lift ending at order twenty, if another prepared lift is wanted. Existing genuine double pins can improve this count when their remaining observed moment map splits.

Together with the unchanged \(n+2\)-row exact lift, the prepared-to-prepared cost is at most \(n+3+\max(0,m-5-k)\) new stages. The last lift still only needs \(n+2\) rows. This is a portable relative bound and a literal replacement of point-only preparation. It does not claim a smaller absolute stage count for a specific existing tableau.
