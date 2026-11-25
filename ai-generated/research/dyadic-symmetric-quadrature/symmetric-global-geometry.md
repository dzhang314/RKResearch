# The global ordered geometry of the actual seven-pair forced-square chart

**Results.** The ordered symmetric 17-site order-20 chart has a smooth geometrically integral projective compactification of dimension seven and trivial canonical bundle. Its rational families cannot dominate, even after dominant rational reparametrization of the seven initial magnitudes. For a one-parameter substitution the precise test is the odd divisor of its forced ratio. A generic path moving \(j\) magnitudes by independent Möbius functions has a smooth double-cover model of genus \(2j-1\): genus one for one moving magnitude, and finitely many rational parameters by Faltings for \(j\ge2\). None of these statements excludes exceptional rational points, nor is there a global rational witness here.

## 1. Compactification and smoothness, including the boundaries

In centered coordinates the support is \(0,\pm a_1,\ldots,\pm a_8\). Using \(T=Y^2\), put \(M_\alpha(T^i)=1/(2i+\alpha)\); the actual one-row requirement uses \(\alpha=3\). For a general positive odd \(\alpha\), define
\[
 X_r(\alpha)=
 \left\{ M_\alpha\left(\prod_{i=1}^r(Tv_i^2-u_i^2)\right)=0\right\}
       \subset(\mathbb P^1)^r,\qquad a_i=[u_i:v_i].
\]
The actual chart is the open of \(X_8(3)\) with all magnitudes finite and nonzero, distinct squares, and the ordinary weight and exactness checks. It is a compactification of ordered supports, not a claim that all projective points are contributing rules.

We prove \(X_r(\alpha)\) smooth over the algebraic closure. At any putative singular point, let \(c\) magnitudes be zero, discard the constant factors at infinity, and write the remaining product \(R(T)=\prod_{i=1}^k(T-z_i)\) with \(z_i\ne0\). Multiplication by \(T^c\) changes the functional to \(\Lambda=M_{\alpha+2c}\). There must be at least one finite nonzero root, since \(\Lambda(1)\ne0\). At this point \(\Lambda(R)=0\), and differentiation in each nonzero finite magnitude gives
\[
             \Lambda(R/(T-z_i))=0 .
\]
Indeed the derivative scalar is the nonzero \(-2a_i\); this remains valid for repeated \(z_i\). The infinity and zero derivative directions need not be used.

Write \(\beta=\alpha+2c\). For every polynomial \(S\) and integer \(j\ge0\) there is the elementary identity
\[
 \Lambda\left((\beta+2j)T^j S-(\beta+2j+2)T^{j+1}S
                   +2T^{j+1}(1-T)S'\right)=0 .
\]
It follows by checking a monomial \(S\), when the two coefficients cancel their literal denominators. If \(\Lambda(T^iR)=0\) for \(0\le i\le j\), divide \(T^{j+1}\) and \(T^{j+2}\) by each \(T-z_i\); using the cofactor equalities and summing gives
\[
       \Lambda(T^{j+1}R')=0,\qquad
       \Lambda(T^{j+2}R')=k\Lambda(T^{j+1}R).
\]
The identity with \(S=R\) now yields
\((\beta+2j+2+2k)\Lambda(T^{j+1}R)=0\). Induction makes all the moments of \(R\) vanish, impossible by the nonsingular Cauchy moment matrix. Explicitly if \(R=\sum_i c_i T^i\), the rational function \(\sum_i c_i/(W+2i)\) would have \(k+1\) distinct zeros \(W=\beta,\beta+2,\ldots,\beta+2k\) but numerator degree at most \(k\); its partial fractions would force \(R=0\). Thus there is no singular point, including collisions, magnitude zero or infinity.

For \(r\ge2\), geometric connectedness follows from the sequence for the single multidegree-\((2,\ldots,2)\) equation: \(H^1((\mathbb P^1)^r,\mathcal O(-2,\ldots,-2))=0\) by Künneth. Smoothness then gives geometric integrality. Adjunction gives \(K_{X_r}\cong\mathcal O_{X_r}\), since the ambient canonical bundle is \(\mathcal O(-2,\ldots,-2)\). The same sequence gives \(H^i(X_r,\mathcal O)=0\) for \(0<i<r-1\). In particular \(X_2\) is genus one and \(X_3\) is a K3 surface.

These facts also apply to generic frozen-prefix slices with at least two moving magnitudes. Specializing every frozen magnitude to zero shifts \(\alpha\) by twice the number frozen, so the preceding nonsingularity certifies a nonempty good open of frozen choices by properness of the remaining projective factors. On that open the same degrees and adjunction apply. This says no generic rational parametrization of the genus-one, K3 or higher-dimensional ordered slices, not that rational points are absent.

## 2. Exact branch divisors on the seven-pair base

Write \(K=\prod_{i=1}^7(Tv_i^2-u_i^2)\), \(A=M_3(K)\), \(B=M_3(TK)\). Both are sections of \(\mathcal O(2,\ldots,2)\) on the seven-pair projective base. The last magnitude is governed by
\[
                    v_8^2 B-u_8^2 A=0 .
\]
The divisors \(A=0\) and \(B=0\) are \(X_7(3)\), respectively \(X_7(5)\), and both are smooth. They meet transversely: if their differentials were dependent at a common zero, select \([u_8:v_8]\) over the algebraic closure making \(v_8^2\,dB-u_8^2\,dA=0\). The last-coordinate derivatives already vanish there; this would be a singular point of \(X_8(3)\). In particular the divisors are distinct. Off their intersection, projection to the base is a degree-two cover (where \(A\ne0\), \(a_8^2=B/A\)) ramified simply exactly along these divisors. Over their intersection the projective last coordinate is free. For an actual finite rational seven-pair tuple the prior dyadic valuation test excludes simultaneous \(A=B=0\): \(A=0\) forces exactly four unit magnitudes, and \(M_3((T-1)K)\) then has its unique leading valuation at exponent five.

As \(X_8\) has a nowhere-zero top form, no dominant rational map from a rational variety can land in it. Indeed in characteristic zero the pullback of that form by a dominant rational map from projective space is nonzero generically; properness extends the map at each codimension-one point and hence extends the pulled-back differential. Projective space has no such form. More generally \(X_8\) is not covered by a dominating family of rational curves: on a smooth base times \(\mathbb P^1\), the pulled-back regular differential would have no component in the \(\mathbb P^1\) direction, whereas a generically dominant map nonconstant on the general fiber must give one by contracting the volume form. This argument concerns the ordered site chart. Arbitrarily parametrizing rational coefficients or square variables does not parametrize rational magnitudes.

On the affine finite-coordinate open the ratio \(B/A\) is not a square in the rational function field, as its divisor has multiplicity-one zero and pole components. The set of rational seven-tuples with rational last magnitude is therefore thin (the rational image of a generically degree-two cover, plus possible excluded boundary loci). By Hilbert irreducibility its complement is Zariski dense. This remains true after any dominant rational reparametrization of the seven-tuple: if the pulled-back ratio became a square as a rational function, the reparametrization would lift to a dominant rational map into \(X_8\), which has just been excluded. Thin does not mean finite or not Zariski dense; it is not a rational nonexistence theorem.

## 3. A complete branch-count criterion for one-parameter substitutions

Substitute any specified rational functions of \(t\) for the seven magnitudes, and reduce the nonzero forced ratio \(\rho(t)=B(t)/A(t)\). Suppose we are not identically in the boundary or an identically invalid collision. If \(A\) is identically zero but \(B\) is not, no finite last magnitude can pay; if \(B\) is identically zero but \(A\) is not, the last magnitude is zero. Otherwise the specialization problem, away from finitely many zeros, poles and other excluded parameters, is exactly the curve \(z^2=\rho(t)\).

Count the number \(b\) of geometric points of \(\mathbb P^1\) at which the valuation of \(\rho\) is odd, including infinity. Common factors and all even parts must be removed before the count.

* If \(b=0\), \(\rho\) is a constant rational square class: factor it in \(\mathbb Q(t)\) as \(c\,g(t)^2\). When \(c\) is a square this gives a rational family, subject to the usual open exclusions. When \(c\) is not a square there is no admissible rational specialization.
* If \(b>0\), the normalized double cover is geometrically integral and has genus \(b/2-1\) by Riemann-Hurwitz. At \(b=2\) it is a conic (remove square factors and retain a polynomial of degree one or two). Its having a rational point is decided by the Hasse-Minkowski criterion over \(\mathbb R\) and **every p-adic field \(\mathbb Q_\ell\)**. A rational point parametrizes the conic, so open real interval conditions and finitely many exclusions can then be imposed if the admissible real arc is nonempty. Reduction over a finite field \(\mathbb F_\ell\) is not itself that local condition.
* At \(b=4\) it is genus one. There is no nonconstant rational parametrization; rational points may exist, and their arithmetic is separate.
* At \(b\ge6\) there are finitely many rational points by Faltings and hence only finitely many candidate rational parameters. This is not an effective enumeration or a proof that the list is empty.

For **generic** simultaneous one-parameter motion of \(j\) of the seven magnitudes by independent Möbius maps, the branch count is exactly \(4j\). First freeze the other coordinates in the good Zariski-open where the two branch divisors restrict to smooth transverse divisors on \((\mathbb P^1)^j\). This open is nonempty by setting the frozen magnitudes to zero and applying the preceding smoothness and transversality proof with shifted \(\alpha\). For fixed \(t\), choices of the \(j\) Möbius maps permit arbitrary independent values and nonzero tangent components at \(t\). Having both divisors pass through those values is codimension at least two. Having one divisor pass through the values and be tangent is also codimension at least two: at a smooth divisor the differential imposes a nontrivial linear condition on the tangent components. Letting \(t\) vary raises the incidence dimension by only one, so a nonempty open of Möbius choices avoids all such coincidences and tangencies. The bad images are closed because the parameter \(t\) ranges over the projective line. Each divisor then cuts \(2j\) simple points (the multidegree is two in each moving coordinate), disjoint from the other divisor's cuts. Hence the genus is \(2j-1\). In particular a generic one-variable relaxation is genus one, and a generic rational path moving two or more magnitudes has genus at least three. A special path seeking a rational family must therefore have genuine branch cancellations or a constant squareclass; generic independent changes cannot furnish such a family.

One can obtain elementary nonsquare specializations in any finite set of other local opens along a nonzero-branch path. Choose a polynomial factor of \(\rho\) with odd exponent. Schur's theorem gives infinitely many primes at which it has a root over the finite field \(\mathbb F_\ell\); omit primes dividing its discriminant, the other relevant resultants, or the specified finite set. The root is simple and separate modulo \(\ell\), so one may choose a congruence class modulo \(\ell^2\) where that factor has valuation exactly one. The ratio then has odd valuation and is nonsquare in the p-adic field \(\mathbb Q_\ell\). Weak approximation imposes that open along with the given others. This is an optional elementary complement to Hilbert irreducibility, not an obstruction to special square-producing parameters. For completeness, Schur's result follows by translating an integer polynomial \(f\) to have nonzero \(f(0)=a\). If a finite set were all possible prime factors of its values, the nonconstant integer polynomial \(f(ax)/a\), with constant coefficient one, would take values prime to the whole set at all sufficiently large multiples of their product, a contradiction.

The conclusions isolate precisely which one-parameter reductions can be rationally parametrized. They do not settle the rational symmetric 17-site endpoint, an unrestricted endpoint, positivity, or RK stages. The proofs use source-level identities and standard algebraic geometry only; no held data, broad search, network, Lean or checkout edit was used.
