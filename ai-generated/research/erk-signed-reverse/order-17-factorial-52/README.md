# A 52-stage explicit method of exact order 17

The [52-stage tableau](tableau-17-factorial-52.json) gives an explicit Runge–Kutta method of exact order 17 over \(\mathbb Z[1/17!]\) and every nonzero commutative algebra over that ring. It improves the former 53-stage factorial-unit construction by one stage. The [53-stage tableau](../tableau-17.json) is unchanged.

## Two existing charts and one existing grid

The construction uses the 22-row forward chart of the order-18 method and the 15-row grade-seven chart of the order-15 method as the reverse chart. The verifier compares both blocks with their published finite receipts. In particular it checks the seven-coefficient reverse decoder on the 27 existing normalized feature generators through size seven. No new chart or scalar grid is searched.

Let \(y\) be the reverse clock and write \(v=2y-1\). The corresponding primal clock is \(x=1-y\). The scalar sites are those of the order-18 method. Their centered values are zero and both signs of
\[
 1/5,\quad 1/3,\quad 1/2,\quad 2/3,\quad 1,\quad 3/2,\quad 2,\quad 5.
\]
Their masses integrate through degree 16, as checked directly. The primes inverted by \(17!\) and by \(18!\) are the same.

The reverse donor clocks in the centered coordinate consist of \(-1,1\) and the five interior sites
\[
 \mathcal S\coloneqq\{0,\pm1/3,\pm1/2\}.
\]
The late correction will use only those five interior sites. Thus it requires no extra pure stage at a donor-free scalar site.

## Recovering the necessary forward pairings

Set \(H(v)\coloneqq1-v^2\). The actual reflected forward residuals at first excess are formed using each Butcher weight vector multiplied by the product of the factorials of the subtrees immediately below its root. They lie in \(H\mathcal P_6\), where \(\mathcal P_6\) is the space of polynomials of degree at most six. On the ascending coefficients of their quotient by \(H\), two readouts vanish:
\[
 \Lambda_0\coloneqq(-1200,5,-192,5,-48,5,0),\qquad
 \Lambda_1\coloneqq(105,0,21,0,9,0,5).
\]
The verifier checks both vanishing conditions and the endpoint zeros on every first-excess generator.

Define
\[
 Q_{\mathcal S}(v)\coloneqq\prod_{a\in\mathcal S}(v-a).
\]
Sampling a quotient of degree at most six at the five sites leaves the two directions \(Q_{\mathcal S},vQ_{\mathcal S}\). The two readouts on those directions give
\[
 \begin{pmatrix}
  10/3&12\\
  0&7/3
 \end{pmatrix}.
\]
The determinant \(70/9\) is a paid unit. For \(a\in\mathcal S\), let \(L_a\) be its cardinal polynomial on \(\mathcal S\), and define
\[
 E_a(v)\coloneqq H(v)\left(\frac{L_a(v)}{H(a)}
             +(\eta_{a,0}+\eta_{a,1}v)Q_{\mathcal S}(v)\right).
\]
The two coefficients \(\eta_{a,0},\eta_{a,1}\) are uniquely determined by requiring both readouts on \(E_a/H\) to vanish. Since the correction vanishes at the five sites, \(E_a\) has value one at \(a\) and zero at the other four sites. These polynomials reconstruct every forward residual under the two readouts. The verifier checks the actual cardinal basis and its pin equations.

For a missing reverse polynomial \(\sigma\), the correction at \(a\) therefore needs only the pairing
\[
 \mu(E_a\,\mathcal I\sigma),\qquad
 \mu(f)\coloneqq\tfrac12\int_{-1}^1f(v)\,dv,\qquad
 (\mathcal I f)(v)\coloneqq\tfrac12\int_{-1}^v f(z)\,dz.
\]
The expressions are polynomial-coefficient operations with all denominators paid.

## Paid right recovery

The grade-seven reverse chart is exact before the first missing word length, seven. The missing polynomial at that length has degree at most seven and vanishes at the reverse origin \(v=-1\). It therefore belongs to \((1+v)\mathcal P_6\). The ten donor-free scalar sites provide the rows \(\lambda_a(1+a)a^j\), \(0\le j\le6\), where \(\lambda_a\) is the actual scalar mass. Their five absolute radii are \(1/5,2/3,3/2,2,5\). The factors \(1+a\) and site gaps are paid units. The parts of the five mass numerators not paid by \(17!\) are respectively
\[
 792809,\quad1579243,\quad482561,\quad3307,\quad616087.
\]
They are pairwise coprime.

For each radius, omit both of its sites and keep the first seven of the remaining eight in increasing order. Multiplying their cardinal inverse by the product of the seven masses makes every coefficient on a weighted measurement a paid polynomial coefficient. The five products generate the unit ideal by pairwise coprimality of the mass cores and the chosen omissions. A Bézout combination yields the actual paid \(7\)-by-\(10\) left inverse. The verifier multiplies it by the measured matrix. In the selected reconstruction nine normalized tap columns are nonzero; the \(+5\) observation column is zero, but its scalar quadrature mass remains present at its single row.

In primal order let \(N\) be the normalized taps and \(\boldsymbol\beta\) the signed suffix masses. The exact matrices satisfy
\[
 L_{ij}=N_{ij}\beta_j,\qquad T_{ij}=\beta_jN_{ji}.
\]
Thus the weighted adjoint relation survives all allowed base changes without dividing by a scalar mass after specialization.

## All ordinary order conditions and the physical count

Here \(m=8\), \(g=7\), and \(p=m+g+2=17\). A forward residual can first occur at size nine, and the suffix derivative is exact through size nine. The product of two active errors at the same root cannot occur before size \(2m+3=19\). Moving the remaining single source across the signed transpose gives the finite dual tests. The late correction supplies exactly the missing pairing, and the finite moment identities supply the scalar part. The proof uses the whole forward feature closure through size nine and the dual closure through length seven, not representative high-order trees.

The independent checker tests every virtual block, 17 scalar moments, 96 dual transitions, 231 forward attachments, 559 early source zeros, 697 lower-chart entries, and all 399 top residual pairings. The exact literal count is 22 forward plus 57 virtual suffix rows, with 27 actual aliases. The two extreme pure rows agree with the forward origin and the prior forward whole-primitive row even before folding: in zero-based full virtual indices, row 32 equals row 0, and row 38 equals row 16. The checker verifies both incoming-row equalities and all 4,108 owner-fibre scalar equations. The folded 52 rows are pairwise distinct and strictly explicit.

The stage and weight denominators are respectively
\[
 d\coloneqq13533124052016628899840000000000,\qquad
 e\coloneqq10170998716342464000.
\]
Both divide \((17!)^4\), and all structural receipts have separate checked payments. The cleared integer order identities descend to every allowed coefficient ring.

## Exact order

For a tree \(t\), its cleared defect is \(t!(\boldsymbol b\cdot\boldsymbol\Phi_t(A))-1\). The two actual size-18 trees specified in the receipt give
\[
 \delta_0\coloneqq 415/10178784,\qquad
 \delta_1\coloneqq -907203421/44910028800.
\]
The independent checker evaluates both on the literal and verifies
\[
 601560290149378560000\,\delta_0+
 1214143481898547200\,\delta_1=1 .
\]
Their integer numerator blend is \(e d^{17}\), which is a unit after payment; hence the method cannot have order 18.

The verifier also evaluates both prespecified four-tree formal-zero combinations on the same literal. The raw outputs are \(-415/12602304\) and \(639167/441080640\), with respective integer multipliers \(100988059011840\) and \(2294942569920\) giving one. These are the two combinations obtained from the projected forward residual and the reverse words \(C^7\) and \(LC^6\) in the source design. It verifies all their constituent raw outputs, not merely their model values.

## Reproduction

From this directory, run the checker with Python 3.10 or later, without the optimization flag:

~~~sh
python3 check.py .. tableau-17-factorial-52.json receipt-17-factorial-52.json \
  ../order-18-certificate/receipt-18.json ../order-15-certificate/receipt-15.json
~~~

The checker uses only the Python standard library. The optional constructor uses SymPy and writes into a separate output directory:

~~~sh
python3 build.py .. output
~~~

Both the literal and the receipt reproduced byte for byte. This is an exact arithmetic proof, not a Lean certificate.
