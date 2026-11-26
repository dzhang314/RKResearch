# Flat defect bands for lower-triangular Runge–Kutta tableaux

## Setting and valid conclusion

Let K be a field of characteristic zero, let the actual RK matrix A be lower triangular, let c=A1 and C=diag(c), and use the normalized rooted numerical vectors with nominal model X^(|t|−1). Write E_k for the span of the pairs through tree grade k=|t|−1, and Z_k for the vectors of zero-model pairs there, with f_k=dim Z_k. The requisite separation through H is: if deg P≤H and P(c) belongs to Z_H, then P=0. Independence of the literal powers of c alone is not enough. The pair operations give (A,J) and (C,X·) at degree cost one, where J integrates from zero; they also give Z_j coordinatewise times Z_j contained in Z_(2j).

Suppose j≥4, H≥2j, and f_(k+1)=f_k+1 for every j≤k<H. If H>2j, this is impossible over any characteristic-zero field. If H=2j, then Z_H is C-invariant for j≥5 over any characteristic-zero field, and for j=4 over fields in which −6 is not a square (in particular ordered fields). In the remaining j=4,H=8 case, a noninvariant endpoint would force the stated exceptional ratio, not a contradiction over arbitrary characteristic-zero fields. No existence of an RK tableau at the exceptional ratio follows.

## Invariant exit on the actual chronological prefixes

For a C-invariant U⊂Z_k with separation through k, invariant clock-fibre projectors split U. Call a clock fibre detectable if its indicator is not in U. There are at least k+1 detectable clocks: otherwise the polynomial vanishing exactly on these clocks with degree at most k would evaluate to a vector in U, contradicting separation. For each such clock ξ take the first physical prefix on which its indicator no longer agrees with any member of U. A detecting row λ_ξ supported on that prefix and in that fibre annihilates U and can be normalized by λ_ξ1=1. Its last nonzero coordinate occurs at this first prefix endpoint. The endpoints are distinct for distinct fibres, since failure of agreement at a new coordinate must be in that fibre.

Consider the first d=⌊k/2⌋ nonzero detectable clocks in this prefix order. If a nontrivial linear combination λ of their detecting rows annihilated Z_(k+1), then λA would annihilate U since AU⊂Z_(k+1). It is supported on the prefix ending at the latest clock u used in the combination, by lower triangularity. Any fibre whose indicator still agrees with U on that prefix gives (λA)1_ξ=0, and therefore cannot contribute to (λA)G'(c).

Take G₀ as X times the product of the squared factors for earlier nonzero detectable clocks; use X² in place of X if the zero fibre has already been detected. There are at most d−1 prior nonzero clocks. Multiply G₀ by the linear factor 1−(G₀'(u)/G₀(u))(X−u). The resulting G vanishes at 0 and all earlier nonzero detected clocks, has derivative zero at all previously detected clocks and at u, but has G(u)≠0. Its degree is at most 2+2(d−1)+1=2d+1≤k+1. Thus λA G'(c)=0 and λG(c)≠0. But A G'(c)−G(c) is in Z_(k+1) by the primitive pair rule, a contradiction. The detectors are independent on Z_(k+1)/U, giving f_(k+1)≥dim U+⌊k/2⌋. No strictness or assumption about a literal zero clock stage was used. In particular no Z_k for j≤k<H is C-invariant under the stipulated flatness.

## Exact single head, including the support bookkeeping

Since Z_j is not invariant and CZ_j⊂Z_(j+1), dim(Z_j+CZ_j)=f_j+1. For W=Z_j put W_i={v∈W:C^a v∈W for 0≤a≤i}. The map C induces an injection from W_i/W_(i+1) to W_(i−1)/W_i. The successive drops are therefore one to the first plateau, which is the maximal invariant part U. Choosing w just before that plateau gives exactly
\[
 Z_{j+a}=U\oplus\operatorname{span}(w,Cw,\dots,C^{r+a-1}w),
 \qquad r=\dim Z_j-\dim U\ge1,\quad 0\le a\le H-j.
\]
For a=0 this follows from the successive quotient pivots; for later grades, each noninvariant current span must gain its next C-power and has exactly one dimension to gain. The description reaches Z_H whether or not that endpoint is invariant.

For the multiplier argument, N≥r+j+1 effective clock labels is needed. It follows from noninvariance of Z_(2j): the next head power then survives modulo U in addition to the r+j current powers. Diagonal spectral decomposition modulo U reduces independence to ordinary polynomial evaluation at the N clocks with nonzero head class. If H>2j, noninvariance of Z_(2j) follows from the exit inequality at k=2j. If H=2j it must be assumed for contradiction; one cannot assert N≥r+j+1 just from the flat count at an invariant endpoint.

For v∈Z_j write D_v=diag(v). The product closure gives D_v Z_j⊂Z_(2j). For h∈U confined to one clock fibre, the possible head polynomial of D_v h modulo U vanishes at all but that effective clock, hence at ≥N−1>r+j−1 points. It is zero, so every D_v preserves U. Only now choose a complement to U respecting C and these multipliers jointly: use a finite basis of the multipliers, group coordinates by the tuple of their diagonal eigenvalues and C, and split each joint block. The joint projectors are polynomials in these diagonals, so U decomposes on the blocks. Projecting w into this complement leaves all head spans modulo U unchanged.

In the chosen complement, D_v C^i w is represented literally by a head polynomial of degree ≤r+j−1 for every 0≤i<r. To improve that bound for i=0, compare each polynomial with X times the one immediately before it. Both have degree ≤r+j<N, and agree at all effective clocks, so the equality is exact at each step. This proves that v agrees on the coordinate support S of w with a polynomial of degree ≤j. A fibre-local h∈U has its polynomial zero at N−1>j other effective clocks, so U vanishes coordinatewise on S. Taking v=w gives w=P(c) on S for nonzero P of degree ≤j. Taking v=C^(r−1)w sharpens this to deg P≤j−r+1, since X^(r−1)P can be compared with a degree-≤j polynomial at N distinct effective clocks.

## The marked pivot and its degree budget

For Q nonzero of degree d∈{1,2}, the actual vector z_Q=(QP)(c)−Q(C)w has model QP and grade at most j+d. Separation implies z_Q∉U. Choose the first physical prefix ending at row i where its restriction fails to agree with U, and choose h∈U matching on preceding rows. Neither U nor z_Q has any nonzero coordinate in S. Thus i∉S. Since U splits by clock, a row λ supported in the prefix and in the fibre ξ=c_i detects this mismatch while killing U. Delete any coefficients of λ in S; this changes neither property. This deletion matters because a single clock fibre may contain coordinates both inside and outside S. Now λ kills the entire head and hence Z_H, and λ z_Q=λ1·Q(ξ)P(ξ)≠0.

Let D=CA−AC−A². Its polynomial model is XJ−JX−J²=0, by formal integration by parts, and it raises tree grade by at most two. Thus D(z_Q−h)∈Z_(j+d+2)⊂Z_H, since H≥2j and j≥4. For the lower-triangular D its diagonal at i is exactly −a_ii². As z_Q−h starts at i and λ ends there,
\[
 0=\lambda D(z_Q-h)=-a_{ii}^{2}\lambda_i(z_Q-h)_i.
\]
The last product without a_ii² is nonzero, so the detecting physical diagonal a_ii is zero. Division by the mismatch and the implication a_ii²=0⇒a_ii=0 use the field assumptions.

Consequently for any R the contribution λ A R(C)(z_Q−h) is zero, because the first possible input is row i, whose diagonal is now zero. The h contribution is also killed whenever its resulting grade fits, since h has zero model. Comparing the primitive of the model with the actual A action gives
\[
 \int_0^\xi R(X)Q(X)P(X)\,dX=0\qquad
 \bigl(\deg R\le H-j-d-1\bigr).
\]
Here the grade for the marked primitive is j+d+deg R+1, not merely the degree of the polynomial P. Taking Q=X yields a nonzero u; subsequently Q=X(X−u) yields v distinct from 0,u, since the detecting scalar Q(ξ)P(ξ) is nonzero in each case. Put m=H−j−1. After rescaling by u, a=v/u is distinct from 0,1, and the two actual tests are
\[
 \int_0^1 X R P=0 \ (\deg R\le m-1),\qquad
 \int_0^a X(X-1)R P=0 \ (\deg R\le m-2),
\]
where the rescaled P is nonzero of degree ≤m+1 because r≥1 and H≥2j. No sign or ordering of u,v has been used.

## Scalar endpoint and sharp field qualification

Let F=J^m(XP). It is nonzero, has degree ≤2m+2, and is divisible by X^(m+1). At 1 its first m jets vanish: the relevant iterated primitives are integrals of XP against (1−X)^k/k! of degrees k≤m−1. Thus F=X^(m+1)(X−1)^m(αX+β). The second identities say that T(H)=∫_0^a HF^(m) is a scalar multiple of H(1) on degree ≤m−1, because it annihilates the exact kernel of that evaluation. Integrating by parts m times against H=(X−a)^k shows that the first m jets of F at a agree with those of λ(X−1)^(m−1)/(m−1)!. Since a≠1, division by (X−1)^(m−1) in the jet algebra is legitimate. The polynomial G=X^(m+1)(X−1)(αX+β) is consequently constant through jet order m−1 at a. Hence G' has multiplicity at least m−1 at a. Its nonzero factor after dividing by X^m is quadratic at most. For m≥4 this is impossible at a≠0.

For m=3, a double root gives G'=κX³(X−a)² with κ≠0. Because G(0)=G(1)=0, integrating produces 1/6−2a/5+a²/4=0, equivalently (15a−12)²=−6. This is not a contradiction in a field admitting such a square. It is a real scalar exception to unqualified field transfer: for either root in an extension containing sqrt(−6), start with G=J(X³(X−a)²), set F=(X−1)²G and P=F'''/X. The displayed factorization and a's double root give both sets of primitive conditions, and P is a nonzero quartic. This is only the isolated scalar system, not an RK tableau. If the head rank is independently at least two at j=4,H=8, then deg P≤m and the factor after X^m is at most linear, so the exception disappears even over that field.

If H>2j then m≥4 and the proof uses only noninvariance at 2j, so it contradicts any such longer flat band, even if its endpoint at H happened to be invariant. If H=2j then assume noninvariance of Z_H and apply the stated field cases. This yields the precise endpoint-invariance theorem above without extrapolating to unrestricted ring or full RK bounds.
