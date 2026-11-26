# Recovering reverse polynomials from existing Runge–Kutta stages

The signed reverse construction gives explicit Runge–Kutta methods of exact orders 17–20 with coefficients in any nonzero commutative ring in which the corresponding \(p!\) is a unit.

| Order | Forward rows | Reverse base rows | Scalar sites | Additional probes | Final stages |
|---:|---:|---:|---:|---:|---:|
| 17 | 27 | 11 | 17 | 0 | [53](tableau-17.json) |
| 18 | 22 | 22 | 17 | 1 | [60](tableau-18-weighted.json) |
| 19 | 27 | 22 | 19 | 0 | [66](tableau-19-weighted.json) |
| 20 | 27 | 27 | 19 | 1 | [72](tableau-20-weighted.json) |

The previous construction used weighted moments of the reverse error. Here we use the weighted point values themselves. They give a rectangular matrix that has a left inverse even though no individual quadrature mass need be a unit. The real-algebraic upper bounds are unchanged.

## The rank criterion

Write \(U_p\coloneqq\mathbb Z[1/p!]\). Let \(\sigma\) be the missing polynomial of a reverse word, as in the [regular-probe proof](WEIGHTED-REGULAR-PROBES.md). The exact old reads and any added unit-mass probes determine a particular polynomial \(\sigma_0\). The difference \(\sigma-\sigma_0\) lies in a polynomial space with a specified basis \(q_1,\ldots,q_d\).

For each scalar site \(a\) used as a live probe, let \(\lambda_a\) be its ordinary quadrature mass. Define the measurement matrix by
\[
M_{aj}\coloneqq\lambda_a q_j(a).
\]
The column of measured values \(\lambda_a(\sigma(a)-\sigma_0(a))\) equals \(M\) times the column of unknown coefficients. This measurement recovers those coefficients over \(U_p\) exactly when the maximal minors of \(M\) generate the unit ideal. To see sufficiency, multiply each square row submatrix by its adjugate to obtain its determinant times the identity. A Bézout combination of these determinants equal to one gives a left inverse of \(M\). Necessity follows by applying the Cauchy–Binet formula to a left inverse times \(M\).

Equivalently, the matrix must have full column rank modulo every prime greater than \(p\). After reducing modulo such a prime, a row with nonzero mass is an ordinary evaluation multiplied by a nonzero scalar. For example, at order 17 the seven live sites have absolute centered indices \(2,4,5,6\) on the grid with denominator 9, with only the negative site used at radius 6. The factors of the four mass numerators remaining after removing primes at most 17 are
\[
15844219,\quad10425517,\quad23370799,\quad148546873 .
\]
They are pairwise coprime. Thus at most two of the seven rows disappear modulo any unpaid prime, and the remaining five points determine a polynomial of degree at most four. Their differences and the endpoint factors are units.

The reconstruction computes the exact minors, removes factors that are units, and combines the remaining integers by the Euclidean algorithm. The resulting left inverse acts on the **weighted** measurements. Consequently the coefficient on each raw probe value is explicitly \(\lambda_a\) times an element of \(U_p\), even after base change in which \(\lambda_a\) becomes zero. This is the factor required in the signed weighted transpose.

## The four choices of polynomial space

Let \(v\) be the centered reverse clock, \(H(v)\coloneqq1-v^2\), and let \(\mu\) be the mean over \([-1,1]\). The base charts, scalar grids, and pure late sites are those of the [earlier weighted constructions](WEIGHTED-ORDERS-18-20.md), with these changes.

- **Order 17.** All seven donor-free sites of the original 17-point grid are live. No split probe is needed. Both endpoint values are exact at the missing grade, so use \(Hv^j\) for \(0\le j\le4\). No additional old scalar read is needed.
- **Order 18.** Use the reverse chart with first four new centers \(-1/3,1/3,-1/5,5\). The six sites not used by its donors are live. Take a single split probe at \(-1/3\). The remaining polynomials are multiples of \(K(v)\coloneqq H(v)(v+1/3)\) of degree at most eight, with zero mean and zero promoted \(\ell_4\) read. On \(K,vK\) the determinant of these two reads is \(-2/243\). Subtract combinations of \(K,vK\) to impose the reads on the fitted polynomial and on each of \(v^jK\) for \(2\le j\le5\). The four latter polynomials after subtraction form the basis. The seven late sites remain the old interior sites before the \(-1/5,5\) additions.
- **Order 19.** Reserve \(1/6\) as pure and use the nine other donor-free sites as live probes. No split probe is needed. The endpoints and mean are exact at the missing grade. A basis is obtained from \(Hv^j\) for \(1\le j\le6\) by subtracting multiples of \(H\) to give zero mean.
- **Order 20.** Use the symmetric 27-row reverse chart. Reserve \(1/6\) as pure, but use \(-1/6\) as a live probe, giving nine live sites. A single split probe at zero, together with the two endpoints, leaves the basis \(Hv^j\) for \(1\le j\le7\). The eight late sites are the old seven interior sites and \(1/6\).

For orders 17, 18, 19, and 20 respectively, the exact routine obtains a unit from 6, 5, 7, and 8 maximal minors. It verifies by multiplication that the resulting left inverse times \(M\) is the identity, and checks every denominator. The same routine also checks the unit determinants of both base charts and all their required rooted reads, including the extra endpoint and scalar reads just used.

## Ordinary order and exactness

A live probe gives its model word value through the first missing reverse length, by applying the exact lower chart to its shorter inputs. Subtracting the model value from the base chart at the same clock gives the point discrepancy. Late signed pairs use the recovered polynomial to supply its missing paired primitive. The order proof is the [single-error argument](WEIGHTED-REGULAR-PROBES.md#every-ordinary-order-condition-through-seventeen): every rooted source error through order \(p\) pairs with a reverse word short enough for this reconstruction. Integrating the two polynomial primitives gives equal contributions, and there cannot be two errors at a root at these orders. The same proof retains the late term that is zero on ordinary first-excess sources but evaluates to one on the [specified next-order combination](WEIGHTED-ORDERS-18-20.md#5-exactness-at-the-next-size). The two endpoint merges and the signed-pair merges are literal equalities of predecessor rows. Thus the counts are the sums in the table minus two.

To check order 20, for example, run:
~~~sh
python construct.py 20 --verify-reads
python verify.py 20
~~~
The first command rebuilds the literal tableau and checks the finite inputs to the proof. The second checks the actual next-order combination, whose raw output is one, and checks an independent list of individual next-order defects generating the unit ideal. It also tests a sample of ordinary rooted conditions; the all-tree argument, rather than those samples, supplies order \(p\). None of these is a Lean certificate.
