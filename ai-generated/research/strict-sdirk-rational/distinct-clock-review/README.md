# Distinct clocks: endpoint units, a symmetry obstruction, and a bounded scan

The universal five-stage question is still open. This packet gives proofs of sharper necessary unit conditions, excludes one symmetric chronology, and records a failed bounded exact search. None of them proves unrestricted nonexistence.

## Two Lean-checked endpoint units

For any five-stage common-diagonal tableau of order five over a commutative ring, the last weight \(b_5\) and the first clock gap \(c_2-c_1=A_{21}\) are units. The [native Lean proof](../../../lean/RKCert/ReviewedNative/SDIRKFiveEndpointUnits.lean) checks the actual stage-vector recursion \(\boldsymbol\Phi_t\). It deletes a final row of zero weight and merges two initial identical stages when their first tap is zero. Both reductions preserve every tree condition and the common diagonal. A nonunit lies in a maximal ideal, so the naive reductions in its residue field would violate the checked four-stage obstruction. No sign, field structure on the original ring, or nonsingularity of the common diagonal is required for these two unit tests.

## Two further unit tests over \(S=\mathbb Z[1/30]\)

For a strict candidate over \(S\), **the penultimate weight and the final clock gap are units too**. These source-level deductions use the rational order-five normal form, clearing denominators *before* specialization. Retain the original \(A\), the forward defect \(\mathbf q=A\mathbf c-\mathbf c^{\odot2}/2\), and the reflected defect covector
\[
 \boldsymbol{\beta}=\mathbf b^\mathsf T Y A-\tfrac12\mathbf b^\mathsf T Y^2,\qquad
 Y=\operatorname{diag}(\mathbf 1-\mathbf c).
\]
Both \(D(1)\), \(\mathbf b^\mathsf T A=\mathbf b^\mathsf T Y\), and the cleared identity
\[
 q_5\boldsymbol{\beta}=(\gamma^2/2)\,\mathbf b^\mathsf T\operatorname{diag}(\mathbf q)
\]
hold over \(S\). The latter follows from the rational proportionality and its last coordinate, using \(c_5=1-\gamma\). Neither formula introduces a weighted transpose over a residue field.

Reduce at any prime \(p>5\). The diagonal and \(b_5\) stay nonzero. The fourth column of \(D(1)\) gives \(b_5 A_{54}=(c_5-c_4)b_4\). If \(b_4=0\), then \(A_{54}=0\), so elementary tree recursion allows deleting stage 4: none of the remaining stages use it and its output weight is zero. This contradicts the universal five-stage floor. Thus \(b_4\) is a unit in \(S\).

If \(c_4=c_5\) modulo \(p\), again \(A_{54}=0\), and \(\beta_4=b_4\gamma^2/2\). The cleared identity implies \(q_4=q_5\) even if the individual defect values vanish modulo \(p\). Let \(U\) be the span of \(\mathbf 1,\mathbf c,\mathbf c^{\odot2}\) in the residue field. Its weighted Gram matrix is the paid \(3\times3\) Hilbert matrix, of determinant \(1/2160\). The nonzero \(\mathbf q\) is orthogonal to \(U\). Hence \(U+\langle\mathbf q\rangle\) has dimension four and, under the assumed terminal clock and defect ties, is exactly the hyperplane in which coordinates 4 and 5 agree.

Let \(R=\operatorname{diag}(\mathbf c)A-A\operatorname{diag}(\mathbf c)-A^2\). Then \(\mathbf b^\mathsf T R=-2\boldsymbol{\beta}\) by \(D(1)\), and \(\boldsymbol{\beta}\) annihilates \(U+\langle\mathbf q\rangle\): over \(\mathbb Q\) it is a multiple of the weighted defect covector, whose pairings with \(U\) and \(\mathbf q\) vanish by order five. These are equalities in \(S\) and so persist in the residue field. The fourth and fifth entries of \(\mathbf b^\mathsf T R\) are \(-\gamma^2 b_4\) and \(-\gamma^2 b_5\), since \(A_{54}=0\). Annihilating the hyperplane forces \(b_4=-b_5\). Their aggregate weight is then zero. The first three sites alone must pay the full moment Gram matrix; this requires distinct first three clocks and nonzero weights. On these three sites the equations \(\langle\mathbf q,U\rangle_{\mathbf b}=0\) now force each of the three defects to be zero by Vandermonde invertibility, contradicting \(q_1=\gamma^2/2\). Thus the final gap, and consequently \(A_{54}=b_4(c_5-c_4)/b_5\), are units. These conclusions do not assume that the first three weights are units.

## Fully reflection-symmetric distinct chronology is impossible over \(\mathbb Q\)

Suppose the centered chronology is \((a,u,0,-u,-a)\), all distinct. The weights are symmetric by interpolation uniqueness. Reversal preserves the weighted bilinear form and the space \(U\) of degrees zero through two. Its nondegenerate orthogonal complement decomposes into an even line and an odd line: in the even physical subspace of dimension three the constraints are degrees zero and two; in the odd subspace of dimension two the constraint is degree one. The two lines are orthogonal and individually nondegenerate. A nonzero isotropic defect therefore has both a nonzero even part \(\mathbf e\) and a nonzero odd part \(\mathbf o\).

The archived opposed-defect normal form gives \((q_1,q_2)=\lambda(q_5,q_4)\), because the first and reflected second clock data coincide. Consequently \((1-\lambda)(e_1,e_2)+(1+\lambda)(o_1,o_2)=0\). If \(\lambda=\pm1\), one of the lines has both paired coordinates zero and hence is zero (for the even line use its degree-zero condition at the center). Otherwise the paired vectors are proportional and nonzero. But their moment constraints have coefficients respectively \((b_1 a^2,b_2 u^2)\) and \((b_1 a,b_2 u)\), independent because \(a u(u-a)b_1 b_2\ne0\). This contradicts proportionality. This excludes that chronology, not arbitrary arrangements of a reflection-symmetric support.

## Bounded, reproducible scan

From this directory run:

    g++ -std=c++17 -O3 sieve.cpp -o /tmp/rk-distinct-five-sieve
    /tmp/rk-distinct-five-sieve 120 | python3 solve-quadratic.py

For \(H=120\), the three scanned rational parameters are the common diagonal \(\gamma\), the first gap \(d=c_2-c_1\), and the centered fourth clock \(w=2c_4-1\). Each has reduced denominator at most \(H\), numerator of absolute value at most \(3H\), and magnitude at most \(4,5,5\), respectively. The first two are \(S\)-units, while \(w\in S\). The newly proved last-gap and penultimate-weight unit filters are **not** needed for the recorded run. The third centered clock \(v\) is not height-bounded: the necessary reflected equation is solved exactly as a polynomial of degree at most two in \(v\).

For each of ten primes \(7,11,13,17,19,23,29,31,37,41\), the finite gate allows any middle-clock residue. It tests the moment equations of the hull of the distinct residue sites, and uses the cleared identities of the [distinct-clock gate](../order-five-paid-distinct-clock-gate.md) with \(H_i=I(\prod_{j\ne i}(t-t_j))\) and
\[
 L_i=(u-t_i)H_1+\kappa(u)(t_i-a)H_2 .
\]
The necessary relation is \((u-a)H_i\widehat q_i=L_i\); hence \(H_i=0\) forces \(L_i=0\), without any inversion of \(H_i\). It always tests \(L_4 H_5=\kappa(-w)L_5 H_4\). Only if all sites are distinct in the residue field does it divide by the hull derivatives: there the last weight is nonzero, and the norm condition is \(\sum_{H_i\ne0}L_i^2/(H_iP'(t_i))=0\). Terms with \(H_i=0\) have zero weight in that case. Collisions are not rejected simply because the original chart has distinct rational sites.

The recorded scan considered 1,170,914,400 triples. 6,674 passed these necessary modular filters; none of their nondegenerate reflected polynomials had a rational root. There were no identically zero reflected polynomials among the four-distinct-clock survivor triples. Nothing is inferred about parameters outside the box. The arithmetic remains an unbounded paid-integer problem despite this finite evidence.


## Exact gate still open

The search can now be organized by three \(S\)-units \(\gamma,d_f,d_b\) rather than two units and a general fourth clock. Set \(a=2\gamma-1\), \(u=a+2d_f\), and \(w=-a-2d_b\). Seek \(v\in S\) such that \((a,u,v,w,-a)\) are all distinct. The forced Lagrange weights must belong to \(S\), with \(b_4,b_5\) units. The initial affine defect conditions give \(\widehat{\mathbf q}\) exactly as in the distinct-clock gate; impose the reflected scalar condition and the zero square. Finally the unique rational triangular reconstruction must have all entries in \(S\). These tests are necessary, and together are sufficient by the rational normal form and the injection \(S\hookrightarrow\mathbb Q\). Any such five-stage order-five tableau has exact order five, by the existing six-stage common-diagonal floor at order six.
