# A localized 59-stage explicit method of exact order 18

Define
\[
 P\coloneqq59\cdot739\cdot2137\cdot8179,\qquad
 B\coloneqq18!\,P,\qquad U\coloneqq\mathbb Z[1/B].
\]
The [59-stage tableau](tableau-18-localized-59.json) gives an explicit Runge–Kutta method of exact order 18 over \(U\) and every nonzero commutative \(U\)-algebra. This is one row fewer over the larger coefficient ring. The [60-stage method](../tableau-18-weighted.json) still applies over \(\mathbb Z[1/18!]\).

## The unchanged charts and the missing polynomial

The construction uses the published 22-row forward chart and 22-row reverse chart, the same 17 scalar quadrature sites, and the same seven late sites. Write \(v=2y-1\) for the centered reverse clock and set
\[
 H(v)\coloneqq1-v^2,\qquad \omega(v)\coloneqq H(v)^2.
\]
The two old endpoint conditions, together with the mean and the promoted read, leave a five-dimensional space of degree-at-most-eight reverse missing polynomials. More explicitly, define
\[
 \mu(f)\coloneqq\tfrac12\int_{-1}^1 f(v)\,dv,\qquad
 \mathcal C\coloneqq\{-1/3,1/3,-1/5,5\}.
\]
For \(a\in\mathcal C\), let \(L_a\) be its cardinal polynomial on \(\mathcal C\). The promoted scalar read is
\[
 \ell_4(f)\coloneqq\sum_{a\in\mathcal C}
              \frac{\mu(\omega L_a)}{\omega(a)}\,f(a).
\]
The first missing polynomial is a multiple of \(H\), has zero mean, and has zero \(\ell_4\). The verifier compares the two actual base banks with the published 60-row receipt and verifies the reverse endpoint, mean and promoted-read identities directly. It applies the clock and primitive actions to the actual augmented span at each depth, without enumerating reverse words.

The two constraints \((\mu,\ell_4)\) on \(H,vH\) have determinant \(-1/378\), a paid unit. Correct \(v^jH\), for \(2\le j\le6\), by subtracting a combination of \(H,vH\) to meet these constraints. This gives the five coordinates used for recovery. No split point constraint at \(-1/3\) is imposed.

## Recovering the five coordinates from six weighted sites

Delete the live split at centered \(-1/3\) and its negative copy. The ordinary scalar site there is retained. The six already weighted live sites, in order, are
\[
 -5,\quad-3/2,\quad-2/3,\quad1/5,\quad2/3,\quad3/2.
\]
If \(q_j\) is one of the five corrected polynomials and \(\lambda_a\) the scalar mass at site \(a\), the corresponding entry of the measurement matrix is \(\lambda_a q_j(a)\).

The four row sets below use zero-based indices in that site order. The integer matrix is obtained by clearing the common denominator \(11124529845999570000\). The table gives the absolute determinant parts after removing factors paid by \(B\).

| Row set | Unpaid part of determinant |
|---|---:|
| \(0,1,2,3,4\) | 172419079389199 |
| \(0,1,2,3,5\) | 488439318383 |
| \(0,1,2,4,5\) | 8822981927 |
| \(1,2,3,4,5\) | 465378883 |

The gcd is one. The supplied paid linear combination of the four signed integer determinants is exactly one. The corresponding combination of adjugates gives a left inverse over \(U\). The independent verifier computes all four determinants and multiplies the supplied \(5\)-by-\(6\) inverse by the exact \(6\)-by-\(5\) measurement matrix. No scalar mass is inverted individually.

The rest of the published signed construction is unchanged. In primal order, if \(\boldsymbol\beta\) is the suffix weight vector and \(N\) is the normalized tap matrix, the actual reverse and primal suffix matrices satisfy
\[
 L_{ij}=N_{ij}\beta_j,\qquad T_{ij}=\beta_jN_{ji}.
\]
Thus the weighted adjoint relation survives every paid base change. The late corrections still pair the missing primitive with the actual forward residual, and the published null term is retained.

## Ordinary order and the literal

The finite proof uses \(m=g=8\), with \(g=18-m-2\). A normalized forest feature can first have a forward residual at size \(m+1\), while the suffix derivative is exact through that size. The smallest tree containing two active errors at the same attachment has size \(2m+3=19\). At ordinary sizes only one error term can contribute. The signed reverse actions move its factors to the verified dual tests; the checked scalar moment and top-residual identities make every such term zero. This proves the order conditions from finite spanning equations, not a sample of high-order trees.

The independent receipt verifies every block of the actual virtual tableau, all 18 scalar moments, 140 dual column transitions, 231 forward attachment equations through size nine, 827 early source zeros, 738 lower-chart entries, and 513 top residual tests. The 22 forward plus 75 virtual suffix rows fold to 59 distinct strict physical rows. The verifier checks all 5,723 incoming owner-fiber coefficients and the folded output.

The exact stage denominator is
\[
 d\coloneqq2570857282896634592100013488102355968000000000000,
\]
and the output-weight denominator is
\[
 e\coloneqq10170998716342464000.
\]
The verifier checks \(d\mid B^6\) and \(e\mid B^4\). The stage denominator factors as
\[
 2^{22}3^9 5^{12}7^5 11^2 13^6 17^2\,59^2\cdot739\cdot2137\cdot8179.
\]
In particular, the part outside the prime support of \(18!\) is \(44962783798057\), and 19 is not present. Descent of the cleared integer order conditions proves the ordinary order over the stated ring.

## Exactness without inverting 19

The same two fixed size-19 trees as in the 60-stage method have the following cleared defects, reevaluated on the new literal:
\[
 \delta_0\coloneqq-\frac{4239294682043}{3243833049600},
 \qquad
 \delta_1\coloneqq-\frac{83318450057501}{22706831347200}.
\]
They satisfy
\[
 (-227848257804894134728320000)\delta_0
   +81151429829876370136972800\,\delta_1=1.
\]
The integer numerator blend is \(e d^{18}\). Modulo 19, the base \(B\), denominators \(d,e\), and scale \(e d^{18}\) have respective residues \(1,3,3,3\), and both integer next numerators are \(16\). Thus no part of the argument requires 19 to be a unit.

There is also an independent check using the four-tree formal-zero graft from the published proof. The actual linear combination of its cleared defects, with each coefficient divided by its corresponding child-factorial product, is 19. The size-19 bush has defect \(19u-1\), where \(u\) is its actual paid raw output. Multiplying the first identity by \(u\) and subtracting the bush defect gives 1. This check also does not divide by 19.

## Reproduction and scope

From this directory, run the checker with Python 3.10 or later, without the optimization flag:

~~~sh
python3 check.py .. tableau-18-localized-59.json receipt-18-localized-59.json \
  ../order-18-certificate/receipt-18.json
~~~

The [60-stage receipt](../order-18-certificate/README.md) pins the original charts. The optional constructor uses SymPy and writes into a separate output directory:

~~~sh
python3 build.py .. output
~~~

Both the tableau and the receipt reproduced byte for byte. This is an exact arithmetic proof, not a Lean certificate.
