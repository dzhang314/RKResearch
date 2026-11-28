# No-active-literal arithmetic rear: exact degree and two exceptional exclusions

This is an exact projection refinement for the [finite no-active-literal arithmetic chart](../sdirk-eight-silent-one-seven-distinct-coprime-no-front-arithmetic/README.md). It applies to a ten-stage strict SDIRK8 tableau over a characteristic-zero field, with sole first physical nonzero quadratic defect, that stage individually weight-zero, detected cubic defect, seven distinct ordinarily active clocks, neither literal front active, coprime nonconstant affine profile, nonzero tail \(k\), and active arithmetic eighth. **It excludes the actual tail-leading-zero and actual fourth-leading-zero branches only.** It does not exclude the regular chart or change the unrestricted **10–11** interval.

The exact tail polynomial \(R(\gamma,u)\) has generic \(u\)-degree 5 and \(\gamma\)-degree 6; let \(\ell(\gamma)\) be its \(u^5\) coefficient. The fourth profile \(\Phi\) is cubic in the fourth normalized clock \(s\), with \(u\)-degree at most 3 and \(\gamma\)-degree 10. The padded fifth determinant \(J\) has \(s\)-degree \(m=21\) for a star literal front or \(m=23\) for an arithmetic front, \(u\)-degree 9, and \(\gamma\)-degree 30. The required diagonal equation is the **padded polynomial**
\[
G=\operatorname{Res}^{5,D}_u\left(R,\operatorname{Res}^{3,m}_s(\Phi,J)\right),
\qquad D=3m+27.
\]
Both resultants use fixed Sylvester sizes, so an actual common root still implies zero even on a reduced-degree specialization. In particular, no leading division is needed to conclude \(G(\gamma)=0\). For computing \(G\) away from \(\ell=0\), it equals \(\ell^D\) times the multiplication norm of the inner resultant in the monic degree-five tail quotient.

Normalize \(R,\Phi,J\) respectively by powers \(6,10,30\) at \(\gamma=\infty\). Their top terms, and the tail's normalized leading coefficient, give an exact degree-five algebra over \(\mathbb Q(t)\), \(t^2=1/2\). The fixed-degree \(s\)-pseudo-remainder of \(J\) by \(\Phi\) carries the predicted leading multiplier. If \(Z\) is this degree-at-most-two pseudo-remainder, the determinants satisfy
\[
\operatorname{Res}^{3,2}_s(\Phi,Z)
   =\Phi_3^{\,2m-4}\operatorname{Res}^{3,m}_s(\Phi,J).
\]
This identity is exact over the generic coefficient field and extends by polynomial identities. In the normalized degree-five algebra both the multiplication norm of the left side and of \(\Phi_3\) are nonzero, checked exactly at the top coefficient and independently at the reduction \(1103,t=161\). Hence \(G\) has exact degree **2040/2176** respectively, with top reduction \(808,318,616,195\) in the four physical orientations. Exact reduction preserves that degree.

The optional complete reconstruction uses \(w=2t\), \(w^2=2\), clearing the input denominators separately by positive integers \(r,p,j\). In the \((1,w)\) basis, the sum of absolute \(1\)-coefficients plus twice the sum of absolute \(w\)-coefficients is a submultiplicative polynomial norm. With integral inputs \(R',\Phi',J'\), a bound on the coefficients of the exact padded integer resultant is
\[
B=(D+5)!\,\lVert R'\rVert^D
 \left((m+3)!\,\lVert\Phi'\rVert^m\lVert J'\rVert^3\right)^5 .
\]
At split primes \(p_0\equiv7\bmod 8\) evaluate at both square roots of 2 and recover the two integral coefficient coordinates by CRT. Once the prime product exceeds \(2B\), centered reconstructions are unique. The checked exact leading coefficient and independent entire reduction at 1103 agree after division of the input scaling \(r^D p^{5m} j^{15}\). No coefficient caches or trusting guessed reconstruction stability are needed.

## Exact lower-degree branches

* If \(\ell(\gamma)=0\), the actual nonzero diagonal guards leave an exact squarefree degree-four support. There the actual \(u\)-degree of \(R\) is four, checked before reduction. In every orientation the specialized \(u\)-leading and actual fourth leading coefficients are units in the finite residue algebras. Use the fourth equation and three pairwise padded resultants of the two actual fifth pure-four reads and a pole-free nodal moment test. The resultant ideal contains a unit in every reduced component.
* If \(\ell(\gamma)\ne0\) but the **actual value** \(\Phi_3(\gamma,u)=0\), its exact guarded squarefree diagonal support has degree 50 and is disjoint from the two exact Gauss-tail contact supports. On that diagonal support, exact pseudo-gcd retains the degree-one \(u\)-carrier of the actual vanishing \(\Phi_3\), with a degree-four coprime complementary carrier. Only the actual leading-zero carrier is treated here. At its \(u\), the fourth equation has lower degree two with leading a residue unit, and the same actual fifth residual test again excludes every component. The other four \(u\) roots at the same diagonal are **not** excluded here.

In both cases the nodal fifth gate is constructed by expanding Newton divided differences of the polynomial \(L_4\) and the pole-free moment's Bézout numerator at the four actual pegs \(1-\gamma,\ 1-\gamma-\gamma u,\ 1-\gamma-2\gamma u,\ \gamma s\). The last peg \(\gamma y\) contributes the fifth Newton row. This construction uses polynomial operations, not inversion of a possible coincident residue difference. It may be weaker after reduction, which does not invalidate an exclusion. The genuine fifth \(y\) need not itself be integral: the characteristic-zero padded resultants already vanish at the actual fourth and gap if such a common fifth exists. Those resultant values, unlike \(y\), descend through the monic diagonal, tail, and fourth algebras. Verified units in the resulting residue ring exclude simultaneous vanishing. All denominators specialized in these calculations are checked as units.

The [native guard lemma](../../lean/RKCert/ReviewedNative/SDIRK8GuardedFiber.lean) checks retention of an actual root through an exact pseudo-factor removal and preservation of polynomial degree with a surviving leading coefficient. These algebraic implications are Lean/Mathlib 4.36.0 kernel-checked; the concrete long CRT and residual calculations are Python exact checks. The earlier [native norm projection](../../lean/RKCert/ReviewedNative/SDIRK8NormProjection.lean) gives the root-evaluation determinant implication.

## Replay

Run `python3 check_nofront_arithmetic_degree.py` from this directory in the sibling research proof tree, with `sympy==1.14.0` and `python-flint==0.9.0`. The command verifies all four exact degrees and eight leading-zero cases; append `--crt` to reconstruct and verify the entire exact padded resultant in each orientation using the certified height bound. The latter takes several minutes. The regular fourth-leader branch, the other \(u\) roots at Gauss-tail contacts or fourth-leading diagonals, and the genuinely nonliteral one-active-literal placements remain outside this packet.
