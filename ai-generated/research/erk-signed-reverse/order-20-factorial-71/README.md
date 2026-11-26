# A 71-stage explicit formula of exact order 20 over \(\mathbb Z[1/20!]\)

The [71-stage tableau](tableau-20-factorial-71.json) gives an explicit Runge–Kutta method with coefficients in any nonzero commutative ring in which \(20!\) is a unit. Its order is exactly 20 over \(\mathbb Z[1/20!]\) and over every nonzero commutative algebra over that ring. This improves the published factorial-unit construction by one stage. It is distinct from the [earlier 71-stage tableau](../order-20-localized-71/README.md), which inverts additional primes.

## It suffices to recover the needed pairings

Consider the signed reverse architecture with forward chart accurate through size \(m\). Put \(g\coloneqq p-m-2\), and assume \(p\le2m+2\). At the last reverse test length \(g\), the only ordinary forward source that can contribute is the first discrepancy, from a tree of size \(m+1\). Let \(w_1,\ldots,w_h\) generate the reflected scalar polynomials of those discrepancies, using the Butcher weight vectors multiplied by the product of the factorials of the subtrees immediately below the root. Let \(\sigma_1,\ldots,\sigma_k\) generate the reverse missing polynomials at length \(g\). Either set of generators may be replaced by a proven containing set for a sufficient test.

Write \(v=2y-1\) for the centered reverse clock. For a polynomial \(f\), define its mean and reverse primitive by
\[
 \mu(f)\coloneqq\tfrac12\int_{-1}^1f(v)\,dv,\qquad
 (\mathcal I f)(v)\coloneqq\tfrac12\int_{-1}^v f(z)\,dz.
\]
These are operations on polynomial coefficients. All ordinary pairing degrees are covered by the exact scalar rule.

Let \(M\) be the measurement matrix on the reverse generators, with a row \((\lambda_a \sigma_j(a))_j\) for a live site of mass \(\lambda_a\). It may also include exact old readouts and unit split observations. Let \(\mathcal S\) be the late pure sites, and define
\[
 X_{ai}\coloneqq w_i(a),\qquad B_{ij}\coloneqq\mu(w_i\,\mathcal I\sigma_j),
 \qquad a\in\mathcal S.
\]
If the late correction sends the measured vector through a paid matrix \(J\), the required identity is exactly
\[
                         X^{\mathsf T}JM=B.
\]
Indeed the left side is the actual paired contribution of the correction, and the right side is the missing contribution of the triangular polynomial primitive. Earlier reverse lengths have zero missing polynomial. The late rows are not themselves read as reverse inputs, so these corrections do not change the inputs of \(M\). This identity is sufficient in the checked finite proof; it is also the necessary equality for a correction using these fixed measurements and sites to supply the stated pairings on these generator spans. It is not a lower-bound criterion for general explicit methods.

In particular, recovering every coefficient of \(\sigma\) or all polynomials in a forward envelope is unnecessary. Over a field, a left/right factorization exists exactly when \(\ker M\subseteq\ker B\) and \(\operatorname{im} B\subseteq\operatorname{im}X^{\mathsf T}\). Over the paid ring the equation itself is required. Equivalently, after unimodular Smith changes for its two outer matrices, a transformed entry of \(B\) on pivot indices \(i,j\) must be divisible by the product of their two corresponding diagonal factors, and every other entry must vanish. Field ranks alone do not imply this divisibility.

## Seven old pure sites suffice on the left

Here \(m=g=9\). Retain the published 27-row forward and 27-row reverse base charts. Let
\[
 H(v)\coloneqq1-v^2,\qquad
 \mathcal S\coloneqq\{0,\pm1/3,\pm1/2,\pm2\}.
\]
The actual top forward discrepancies lie in \(H\mathcal P_7\), where \(\mathcal P_7\) consists of polynomials of degree at most seven. On the coefficients of the quotient by \(H\), in ascending powers, they satisfy the exact equation with row
\[
 \ell\coloneqq(-2487,-6632,1473,3928,5433,14488,9393,25048).
\]
The receipt checks this on every one of the 25 first-excess forward feature generators. It uses the reflected forward polynomial in the reverse variable \(v\).

Define the degree-seven nodal polynomial
\[
 Q_{\mathcal S}(v)\coloneqq\prod_{a\in\mathcal S}(v-a).
\]
Its read is \(\ell(Q_{\mathcal S})=-31616=-2^7\cdot13\cdot19\), a unit. If \(L_a\) is the ordinary cardinal polynomial of \(a\) on \(\mathcal S\), set
\[
 E_a(v)\coloneqq H(v)\left(
 \frac{L_a(v)}{H(a)}
 -
 \frac{\ell(L_a/H(a))}{\ell(Q_{\mathcal S})}Q_{\mathcal S}(v)
 \right).
\]
The \(E_a\) are cardinal at the seven sites, and their divided coefficients satisfy \(\ell=0\). An element of \(H\mathcal P_7\) with all these site values zero is a multiple of \(H Q_{\mathcal S}\). The unit read on that direction proves
\[
 w=\sum_{a\in\mathcal S}w(a)E_a
 \quad\text{for every }w\in H\mathcal P_7\text{ with }\ell(w/H)=0.
\]
Consequently the correction at \(a\) needs only the paired functional \(\mu(E_a\mathcal I\sigma)\). There is no correction at the previously reserved pure site \(+1/6\).

## All ten live sites suffice on the right

The same 19 scalar quadrature sites and masses are used. Make \(+1/6\) live, as well as \(-1/6\), and remove the split at zero and its canceling copy. The ten live sites have absolute radii \(1/6,2/3,5/6,7/6,4/3\). None is an old reverse donor clock. The missing degree-nine reverse polynomials vanish at both endpoints, so their quotient by \(H\) has degree at most seven.

For each of the five radii, omit both signs of that radius. The remaining eight sites have paid gaps and paid endpoint factors. Their cardinal interpolation after multiplying by the product of the eight masses uses no inverse of an individual mass: the coefficient on the measured value at \(a\) has its usual divided-\(H(a)\) cardinal, multiplied by the product of the seven other masses. The parts of the five reduced mass numerators not paid by \(20!\), in the above order, are
\[
 31280779,\quad1034700137,\quad14485811,\quad41464901,\quad86775809.
\]
They are pairwise coprime. Thus the five products of eight masses generate the unit ideal, and the supplied Bézout combination of their scaled cardinal inverses recovers the quotient from the weighted values. The independent verifier checks an actual \(8\)-by-\(10\) left inverse against the \(10\)-by-\(8\) measurement.

Use the same signed factored transpose as in the published method. If \(N\) denotes the normalized reverse taps and \(\boldsymbol\beta\) the signed masses, the two suffix matrices satisfy
\[
 L_{ij}=N_{ij}\beta_j,\qquad T_{ij}=\beta_jN_{ji}.
\]
This avoids dividing by a mass after base change. The lower-left block is \((I-TE)D_F\), using the forward scalar chart \(D_F\), suffix monomial evaluations \(E\), and their primitives \(I\).

## Full ordinary order and exactness

The receipt gives the actual pre-fold arrays and every finite closure identity used in the native-tree proof. It checks all 20 scalar moments, all 194 dual transitions, and all 394 forward attachment identities through size ten. The 1,264 early source zeros and all 875 top residual pairings are checked on the actual matrices. The single-error expansion applies because \(20=2m+2\), one below the smallest tree size with two active errors at a root. Consequently the exact pairing through the first-excess forward span and the dual tests proves all ordinary order conditions, not just a sample.

There are 27 forward plus 87 virtual suffix rows. The owner fold compares all 8,094 incoming coefficients summed over owner fibers and the folded output weights. It gives the attached 71 physical rows, distinct and strictly explicit. The stage denominator is \(1043590153068105809388558336000000000\), dividing \((20!)^4\), and the weight denominator \(3250948100400000\) divides \((20!)^2\). No additional prime is inverted.

For an independent exactness certificate, the receipt includes two actual size-21 trees with cleared defects
\[
 -\frac{70966736237}{14383483401830400},
 \qquad
 -\frac{199266697037}{14383483401830400}.
\]
Their integer combination with respective coefficients \(573153567120018608040345600\) and \(-204122608674290916551884800\) is one. Their exact computation is on the attached 71-row literal, not on an approximating model. Ordinary rational order descends by the cleared integer polynomial identities after any allowed base change, and the unit combination of actual next defects gives failure at order 21.

The two formal-zero combinations explaining the improvement also have actual raw outputs \(57445/1997706028032\) and \(-39955501009/97088512962355200\). Let \(w=CAC^2\mathcal V\) be the published size-eleven forward formal combination. The two expressions are \(C^8A^2w\) and \(A^{10}w\). The seven-site projection differs from the identity on its residual by \((3465/3952)\,H Q_{\mathcal S}\). Pairing this direction with the missing polynomials for reverse words \(LC^8\) and \(L^9\) gives the displayed outputs; any later source from these formal combinations sees a reverse word of shorter length and vanishes. Their integer coefficients \(-1910834258198528885450342400\) and \(-133516500603057781639372800\) also give a raw combination equal to one. Each four-tree constituent and its semantic size is included and checked separately.

## Verification scope

The constructor operates on a private copy of the pinned published order-20 upper geometry. It uses fixed five-block cardinal recovery, not a new grid or tree search. The independent checker does not import the constructor, and its exact arithmetic covers the full finite proof obligations and the specified next tests. The earlier 72-stage factorial-unit and 71-stage larger-localization literals were opened read-only and their hashes match. The proof is a finite exact arithmetic check, not a Lean certificate.

From this directory, run the checker with Python 3.10 or later, without the optimization flag:

~~~sh
python3 check.py .. tableau-20-factorial-71.json receipt-20-factorial-71.json \
  ../order-20-localized-71/tableau-20-localized-71.json
~~~

The checker uses only the Python standard library. The optional constructor uses SymPy and writes into a separate output directory:

~~~sh
python3 build.py .. output
~~~

Both the receipt and the tableau reproduced byte for byte.
