# Eleven explicit stages at order eight over local rings and in positive characteristic

**Later result.** A [single exact eleven-stage tableau](../erk-eight-dispersed/README.md) over the factorial localization now supersedes the universal upper bound discussed here. It uses seven active sites and a dispersed defect space.

Two new rational tableaux and the [first rational certificate](../erk-eight-rank3-four/README.md) form a three-chart denominator portfolio. Let \(D_0,D_1,D_2\) be their positive common denominators. They have 531, 3837 and 588 bits, and
\[
 \gcd(D_0,D_1,D_2)=6970199040=2^{10}3^4 5\,7^5 \;\mid\; (8!)^5 .
\]

**Consequences.** Eleven stages suffice for exact ERK order eight over every local commutative ring and every nontrivial commutative ring of positive characteristic in which \(8!\) is a unit. No field, reducedness, ordering, or algebraic-completeness assumption is needed. In particular the local theorem subsumes all fields, while the positive-characteristic theorem includes composite characteristics and nilpotents. These are **upper bounds**, not a new unrestricted 11-stage lower bound over non-ordered coefficients.

## Checked literal data

* [Two complementary literal matrices and weight vectors](portfolio.json), in addition to the previous rational tableau.
* **python3 replay_portfolio.py** independently verifies all 600 order conditions using literal denominator-cleared integer arithmetic on rooted trees. For each chart it enumerates the 286 ninth-order trees and verifies that the normalized defect numerators generate the unit ideal in \(\mathbb Z\). This independently certifies exactness after denominator specialization.
* **lake build RKCert.ReviewedNative.ERK8LocalPortfolio** builds the two new integer certificates and the specialization theorem. Lean 4.36.0 checked **RKResearch.Certified.ERK8LocalPortfolio.local_exact** and **positive_characteristic_exact** using only the standard axioms. The proof of not-order-nine uses the already reviewed arbitrary-ring order-nine floor of 12, so it has no new exceptional defect primes. A [sparse replay helper](../../lean/RKCert/ReviewedNative/ERKSparseIntegerReplay.lean) skips zero taps before evaluating child profiles; its equivalence with the established exact integer checker is also proved in Lean.

The new charts use degree-seven quadrature on \(0,1\) and four interior-or-exterior sites. Their centered interior coordinates (in the normalization where endpoints are \(-1,1\)) were found by two independent routes: parabola intersections on the quadratic-discriminant fiber for the 11-adic repair, and an exact bounded small-fraction pair scan for the 13-adic repair. The literal data are what the certificate consumes.

## How selection and transfer work

The Lean theorem **denominator_bezout** checks an explicit integer combination of \(D_0,D_1,D_2\) equal to 6970199040. If \(8!\) is a unit in a local ring, this sum is a unit; the sum of nonunits in a local ring is a nonunit. Hence one summand, and thus one denominator, is a unit. Inverting that denominator exactly specializes its reviewed rooted-tree certificate.

In positive characteristic \(n\), \(8!\) being a unit forces \(\gcd(8!,n)=1\). At each prime divisor \(p\mid n\), select a denominator that is nonzero modulo \(p\); it remains a unit modulo the full \(p\)-power dividing \(n\). Take the corresponding tableaux coordinatewise and transfer through the Chinese remainder ring isomorphism to \(\mathbb Z/n\mathbb Z\). The slots are shared, so the stage count stays 11. Finally specialize from \(\mathbb Z/n\mathbb Z\) to the given coefficient ring. No Hensel lifting of an approximate tableau is needed.

## Scope of this earlier local portfolio

This finite portfolio is not a single tableau over \(U=\mathbb Z[1/210]\). None of the three denominators is a unit there, and the local/CRT argument does not globalize a choice on this connected characteristic-zero base.

There is a useful precise integrality test in the rational rank-three chart. Keep the pure-head chronology of the first construction, let \(h\) be its original nonzero pure clock, let \(\alpha\) be the original first nonzero raw clock, and write \(x=c_6/h\) for the novel dirty clock in head-normalized units. The explicit solved head entries are
\[
   A_{3,2}=\frac{h^2}{8\alpha},\qquad
   A_{6,4}=h x^2\left(-\tfrac76+\tfrac{10}3x-2x^2\right).
\]
At any prime \(p\notin\{2,3,5,7\}\), write \(t=\nu_p(h)\) and \(v=\nu_p(c_6)\). If the whole chart is \(U\)-integral, necessarily \(\nu_p(\alpha)\le 2t\) and \(4v\ge3t\). For the latter, if \(v<t\) the \(x^4\) term is the unique lowest-valuation term because its coefficient \(-2\) is a unit; the second displayed entry then has valuation \(4v-3t\). If \(v\ge t\), the inequality is automatic since \(t\ge0\). Thus a non-factorial prime dividing \(h\) but not \(c_6\) is an actual obstruction for this chart, not merely an avoidable pole in the formulas. This does not rule out the necessary common divisibility pattern. No general nonexistence over \(U\) is claimed.
