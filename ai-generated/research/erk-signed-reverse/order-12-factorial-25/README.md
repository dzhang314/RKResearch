# A 25-stage explicit method of exact order 12

The attached tableau is strict explicit with 25 stages. It has exact order 12 over \(\mathbb Z[1/12!]\) and every nonzero commutative algebra over that ring. It improves the previously published 26-stage construction by one stage. In particular, no inverse of 13 is needed.

## Reusing the two grade-five charts

Use the nine-row forward chart of the published order-11 method and the sharp eight-row reverse chart used in the published order-13 method. The ordinary proof uses \(m=g=5\), so its order is \(p=m+g+2=12\). Keep the published order-12 scalar grid, whose centered sites are zero and both signs of \(1/6,1/3,1/2,2/3,1\).

Write \(v=2y-1\) for the centered reverse coordinate; the primal clock is \(x=1-y\). Define
\[
 H(v)\coloneqq1-v^2,\qquad
 \mathcal S\coloneqq\{-1/2,-1/3,0\}.
\]
Those are the three interior donor clocks of the sharp reverse chart. Every first-excess normalized forward residual \(\rho\) lies in \(H\mathcal P_3\), and \([v^2](\rho/H)=0\). The pinned order-11 receipt gives this relation on the actual forward generators, and the checker tests it again on the new basis. There is no need to reconstruct the rest of \(H\mathcal P_3\).

The three points in \(\mathcal S\) leave a single direction in the divided interpolation:
\[
 Q_{\mathcal S}(v)\coloneqq v(v+1/2)(v+1/3).
\]
Its \(v^2\) coefficient is \(5/6\), a paid unit. If \(L_a\) is the cardinal polynomial of \(a\) on \(\mathcal S\), then
\[
 E_a(v)\coloneqq H(v)\left(
    \frac{L_a(v)}{H(a)}
    -\frac{[v^2](L_a/H(a))}{5/6}\,Q_{\mathcal S}(v)
 \right)
\]
is an exact paid cardinal for those residuals. All required missing reverse pairings can therefore be integrated using the three existing pure sites.

## Four reverse directions from six weighted measurements

The sharp reverse chart is exact at all lengths below five. At length five let \(\sigma\) be its missing polynomial. The actual augmented orbit verifies both
\[
 \sigma(-1)=0,\qquad
 R(\sigma)=0,\qquad
 R(f)\coloneqq f(-1/3)-\frac{17}{81}f(1).
\]
Since \(R(1+v)=20/81\), a paid unit, correct \(v^j(1+v)\) for \(1\le j\le4\) by subtracting multiples of \(1+v\) to satisfy the second condition. These four polynomials are the measurement axes.

The available donor-free scalar sites, in measurement order, are
\[
 -2/3,\quad-1/6,\quad1/6,\quad1/3,\quad1/2,\quad2/3.
\]
Let the measurement at site \(a\) be its polynomial value multiplied by the actual scalar mass \(\lambda_a\). The receipt clears the common denominator 86625 of this \(6\)-by-\(4\) matrix. On zero-based row sets \((0,1,2,5)\) and \((1,2,3,4)\), the signed integer determinants are
\[
 \Delta_0\coloneqq-103787694643500000000,\qquad
 \Delta_1\coloneqq50612116826880000000.
\]
They satisfy the paid identity
\[
 \frac{110539}{229635000000}\Delta_0+
 \frac{307033}{311040000000}\Delta_1=1.
\]
Thus a paid combination of the two adjugates gives the left inverse. The verifier evaluates both determinants independently and checks the full matrix product. The normalized taps multiply each scalar mass rather than divide by it. In primal suffix order the actual matrices obey \(L_{ij}=N_{ij}\beta_j\) and \(T_{ij}=\beta_jN_{ji}\), where \(N\) denotes those taps and \(\boldsymbol\beta\) the signed weights.

## Ordinary order and literal stage count

The normalized forward feature closure is checked through size six. At this grade the suffix derivative is already exact, so a product of two errors cannot enter before size \(2m+3=13\). The signed reverse dual closure moves each single source to the verified pairings. The checker verifies all 12 scalar moments, 42 dual transitions, 38 forward attachment identities, 171 early source zeros, 144 lower-chart entries, and all 72 top residual pairing equations. These are the full finite ordinary-order tests, not samples of trees.

There are nine forward plus 33 virtual suffix rows, with 17 literal aliases. In particular the pure origin, midpoint and whole-primitive rows agree with the old forward rows before any folding: full virtual row 15 equals row 0, row 16 equals row 8, and row 19 equals row 7, in zero-based indices. The independent checker tests these three row equalities and all 1,050 owner-fibre coefficients. The folded rows are strict, pairwise distinct, and number 25.

The common stage and weight denominators are respectively
\[
 d\coloneqq33530112000,\qquad e\coloneqq138600.
\]
The actual divisibilities are \(d\mid(12!)^2\) and \(e\mid12!\). All structural arrays also have separately checked paid denominators. Cancellations in the cleared integer polynomial identities therefore give ordinary order over every allowed coefficient ring.

## Exactness without inverting 13

For a tree \(t\), define its cleared defect by
\[
 \delta(t)\coloneqq t!\,\boldsymbol b\cdot\boldsymbol\Phi_t(A)-1.
\]
The two actual size-13 trees in the receipt have defects \(1789/6842880\) and \(599/855360\). In that order, coefficients \(-513216000\) and \(191600640\) form an integer blend equal to one. At the integer-numerator level the blend is \(e d^{12}\). Modulo 13 this unit has residue 7 and the two numerators both have residue 6.

For a second check, write \(C\) for coordinatewise stage clock multiplication. Define the formal-zero expressions
\[
 \mathbf d\coloneqq\mathbf c^{\odot2}-2A\mathbf c,\qquad
 \mathbf w\coloneqq C^3A\mathbf d.
\]
The actual two-tree combination \(C^5A\mathbf w\) has raw output \(-1/622080\). Multiplying its coefficients by \(-622080\) gives a raw unit witness. Dividing the resulting coefficients by the child-factorial products \(t!/13\) gives a paid defect combination equal to 13, not a division by 13. The actual size-13 bush has cleared defect \(13u-1\), where \(u\) is its paid raw output. Multiplying the first combination by \(u\) and subtracting the bush defect gives one. The independent checker verifies this second identity directly.

## Reproduction

Run the following from this directory. The first command enumerates all 7,813 rooted trees of order at most 12 and checks their order conditions directly against the literal tableau, using exact integer arithmetic. It also checks the integer combination of the two order-13 defects. It needs only Python's standard library.

~~~sh
python verify_all_rooted.py
python check.py .. tableau-12-factorial-25.json receipt-12-factorial-25.json \
  forward-reference-11.json reverse-reference-13.json
python build.py .. /path/to/output
~~~

The second command verifies the smaller structural certificate; it imports neither the builder nor its arithmetic helper. The third reproduces the tableau and structural receipt. The [earlier 26-stage tableau](../tableau-12-weighted.json) is unchanged. These are exact arithmetic checks, not Lean certificates.
