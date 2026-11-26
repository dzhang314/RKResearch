# A 65-stage explicit method of exact order 19

The [65-stage tableau](tableau-19-factorial-65.json) gives an explicit Runge–Kutta method of exact order 19 over \(\mathbb Z[1/19!]\) and every nonzero commutative algebra over that ring. This is one stage fewer than the previous factorial-unit method. The [previously published 66-stage tableau](../tableau-19-weighted.json) and the order-20 literals are unchanged.

## The 21-row reverse chart

Write \(y\) for the reverse clock and \(v=2y-1\) for its centered coordinate. Keep the 27 forward rows and all 19 scalar quadrature sites of the previous construction. Let
\[
 \mathcal S\coloneqq\{0,\pm1/3,\pm1/2,\pm2\},
 \qquad
 \mathcal S_6\coloneqq\mathcal S\setminus\{-1/3\}.
\]

The reverse bank starts with the 15-row grade-seven chart of the published order-15 construction. Its additional read \(\ell_7\) is exact through size eight. The independent verifier checks the old chart identity and that read on all 41 generators of the prior normalized forward feature spaces through size eight.

Append six rows, in increasing order of \(a\in\mathcal S_6\), obtained by integrating the old degree-six decoder from zero to \(y=(1+a)/2\). Every attached child of a tree of size at most eight has size at most seven. Thus the six new rows give the exact elementary derivative weights at their clocks through size eight. Combine the six exact readings with the original origin and the old \(\ell_7\) read. The seven point readings leave one coefficient undetermined at degree seven, namely the coefficient of
\[
 R(v)\coloneqq(1+v)\prod_{a\in\mathcal S_6}(v-a).
\]
The exact value \(\ell_7(R)=-150\) determines this coefficient over the paid ring. The eight reads therefore define the decoder for the complete 21-row reverse bank. The verifier checks the actual incoming coefficients of the six appended primitive rows and the result of all eight scalar equations on each of the 21 data columns of the new decoder.

At the first missing reverse word length, which is eight, the discrepancy has degree at most eight. The origin remains exact, so that discrepancy belongs to \((1+v)\mathcal P_7\), where \(\mathcal P_7\) is the space of polynomials of degree at most seven. Neither the right endpoint nor a mean condition is needed at that length. All reverse donor clocks still belong to \(\mathcal S\cup\{-1,1\}\).

## Paid weighted recovery for the actual pairing

The reflected forward first-excess discrepancies use the unchanged 27-row chart. They lie in \(H\mathcal P_7\), where \(H(v)\coloneqq1-v^2\). Their divided coefficients satisfy the functional
\[
 \ell\coloneqq(-2487,-6632,1473,3928,5433,14488,9393,25048)
\]
in ascending powers, with value zero. The verifier checks both assertions for all 25 normalized size-ten forward feature generators. If
\[
 Q_{\mathcal S}(v)\coloneqq\prod_{a\in\mathcal S}(v-a),
\]
then \(\ell(Q_{\mathcal S})=-31616=-2^7\cdot13\cdot19\), a paid unit. Thus evaluation on the seven old pure sites determines each forward discrepancy in the kernel of \(\ell\). In detail, let \(L_a\) be the cardinal polynomial for \(a\in\mathcal S\) on those sites, and define
\[
 E_a(v)\coloneqq H(v)\left(
 \frac{L_a(v)}{H(a)}
 -
 \frac{\ell(L_a/H(a))}{\ell(Q_{\mathcal S})}Q_{\mathcal S}(v)
 \right).
\]
The \(E_a\) are the cardinal basis of that kernel. A discrepancy is the sum of its values at \(a\) multiplied by the corresponding \(E_a\). The late correction at \(a\) therefore only needs the paired functional
\[
 \mu(E_a\,\mathcal I\sigma),\qquad
 \mu(f)\coloneqq\tfrac12\int_{-1}^1 f(v)\,dv,\qquad
 (\mathcal I f)(v)\coloneqq\tfrac12\int_{-1}^v f(z)\,dz.
\]
Here \(\sigma\) is the reverse missing polynomial. The integrals denote polynomial-coefficient operations, with paid denominators.

There is no late correction at \(+1/6\), so that scalar site becomes a weighted live observation. The ten donor-free weighted sites now have radii \(1/6,2/3,5/6,7/6,4/3\). In the divided basis their measurement entries are \(\lambda_a(1+a)a^j\) for \(0\le j\le7\), where \(\lambda_a\) is the scalar mass at that site. The factors \(1+a\) and all site gaps are units. The parts of the five mass numerators not paid by \(19!\) are respectively
\[
 31280779,\quad1034700137,\quad14485811,\quad41464901,\quad86775809.
\]
They are pairwise coprime. Omitting both signs of each radius in turn leaves eight sites. The five products of the corresponding eight masses generate the unit ideal. A Bézout combination of the mass-scaled cardinal inverses gives the full weighted left inverse without dividing by an individual mass. The verifier checks the \(8\)-by-\(10\) inverse against the actual measurements.

The scalar sites and masses are unchanged, and no split is needed. In primal order, let \(N\) be the normalized reverse tap matrix, \(L\) the actual reverse matrix, \(T\) the primal suffix, and \(\boldsymbol\beta\) the signed suffix masses. The construction and verifier use
\[
 L_{ij}=N_{ij}\beta_j,\qquad T_{ij}=\beta_jN_{ji}.
\]
The weighted adjoint equality is consequently valid without division by a mass after any base change.

## Complete ordinary-order and literal verification

The normalized forest proof has \(m=9\), \(g=8\) and \(p=m+g+2=19\). The first contribution of two active errors is at size \(2m+3=21\). Thus ordinary order needs the forward closure through size ten, the signed dual tests through length eight, and the checked pairing on the first-excess forward generators. The same proof uses the forward-to-suffix block \((I-TE)D_F\), where \(D_F\) is the forward chart and \(E,I\) are suffix evaluation and primitive of monomials. The late correction is tested only against the reachable forward discrepancies.

The independent verifier checks the actual array, all 19 scalar moments, 138 dual column transitions, 394 normalized forward attachments, 886 early source zeros and all 725 top residual pairings. It checks the 27 forward plus 75 virtual suffix rows against the owner fold with 6,630 scalar equalities. The resulting 65 physical rows are pairwise distinct and strictly explicit. The payment amounts are
\[
 d\coloneqq745421537905789863848970240000000000,\qquad
 e\coloneqq3250948100400000.
\]
Here \(d\) is the common stage denominator and \(e\) is the common output-weight denominator. The exact receipts show \(d\mid(19!)^4\) and \(e\mid(19!)^2\). The stored structural matrices have separate checked paid denominators. Ordinary rational order therefore descends to every indicated ring by clearing the integer polynomial identities.

## Exact order

The actual 65-row tableau has the following cleared size-20 defects on the two named trees in the receipt:
\[
 \delta_0\coloneqq\frac{1511360952889}{27528197898240000},
 \qquad
 \delta_1\coloneqq\frac{90845819092109}{578092155863040000}.
\]
The verifier evaluates both on the literal and checks
\[
 (-13444897292083132781018480640000)\delta_0
 +4697210644414489899461836800000\,\delta_1=1.
\]
The corresponding integer numerator combination equals \(e d^{19}\), a unit after payment. Thus failure at order 20 holds over every nonzero allowed base change, without any separate use of the next tree size as a denominator.

The same checker also evaluates all four rooted constituents of each of the two proposed formal-zero grafts. If \(w=CAC^2\mathcal V\) is the size-eleven formal combination from the [paired order-20 proof](../order-20-factorial-71/README.md), the two raw outputs for \(C^8Aw\) and \(C^7A^2w\) are respectively
\[
 -\frac{714545927}{172051236864000},
 \qquad
 \frac{1827349}{1290384276480}.
\]
Their respective integer coefficients \(151027081033701869568000\) and \(442919438019217815552000\) give an independent raw blend of one. All actual tree shapes and coefficient choices are fixed in the receipt. There is no high-order tree enumeration.

## Reproduction

From this directory, run the checker with Python 3.10 or later, without the optimization flag:

~~~sh
python3 check.py .. tableau-19-factorial-65.json receipt-19-factorial-65.json \
  ../order-15-certificate/receipt-15.json
~~~

The checker uses only the Python standard library. The optional constructor uses SymPy and writes into a separate output directory:

~~~sh
python3 build.py .. output
~~~

Both the tableau and the receipt reproduced byte for byte. This is an exact arithmetic proof, not a Lean certificate.
