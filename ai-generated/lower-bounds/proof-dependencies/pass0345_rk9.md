# Order nine: one-prime six-on certificate by directional norms

The single six-on exclusion can be made self-contained over one prime, with no Hensel lift, irreducibility test, characteristic-zero conjugacy, exact degree-48 coefficient array, or factorization of a quartic over an extension field. The existing stage-placement derivation and the order-nine lower bound s ≥ 13 are unchanged. This is an exact finite certificate, not a computation-free proof.

## Setup and parameter reduction

Keep the six-on atlas equations and definitions from the One Norm Proof, including the endpoint and placement obstructions. Write W=F0 G1−F1 G0, B=(3/14)J3(v) h (u−v)(v−r)D(u−r), K=W/B as a polynomial, and T=p̂2 O5 O6 Hc. A candidate gives K=T=0. The ordered-root algebra of Q=J4+λJ3 is the monic tower of ranks 4,3,2. Write N for the composition of the three relative multiplication determinants (equivalently, the norm of the rank-24 tower). For divisibility W=BK, integrality at 523, and deg H≤48 for H=N(K), use the independent polynomial divisibility and infinity proof in pass0145_rk9.md. These steps require no exact coefficient expansion.

Evaluate N(W)/N(B) at λ=0,...,48 over F_523; N(B) is nonzero at all 49 samples. Interpolate. The degree is 48, with coefficient 55 at λ^48, and the ascending residue array is
    269,220,353,170,380,463,377,375,273,17,295,457,204,374,266,217,519,
    58,279,174,382,378,229,239,201,275,253,85,260,13,134,361,165,453,251,
    437,522,10,244,68,231,435,208,378,151,365,206,390,55.
This proves that the leading coefficient of the characteristic-zero H is a unit at 523, so H can be normalized monic over Z_(523). For any alleged candidate, λ is integral at 523 since H(λ)=0, and h,u,v,r are integral as roots of the monic Q. A maximal ideal over 523 in the ring obtained by adjoining these coordinates supplies a field k and a map from A=F_523[λ]/(H mod 523) to k. The ordered tuple is well defined in the reduced tower even if some entries coalesce: the three defining equations hold before reduction, and they are monic-polynomial identities. The equations W=T=0 also reduce into k.

## Coordinate compression, with three sizes of small determinant

Work in the same ordered-root tower over A[ε]/(ε²). Set α_d=[ε]N(W+εd), for d=1,h,u,v. The exact gcd check gcd(H,α_1)=1 implies α_1 is a unit in A. Therefore put (h*,u*,v*)=(α_h,α_u,α_v)/α_1 within A, and evaluate T* from the manuscript's ordinary formulas at that triple, with r*=2−λ−h*−u*−v*. A second check gives gcd(H,T*)=1. Thus the potentially expensive terminal polynomial is only evaluated in the degree-48 coefficient ring, not the order-24 tower.

Why the computed coordinates are the only relevant ones: after base change to k, let M_w be multiplication by W in the 24-dimensional algebra and φ the evaluation homomorphism of any candidate tuple. The image of M_w lies in ker φ, a subspace of dimension 23. By the determinant derivative formula, α_1=tr adj(M_w); since it is nonzero, some 23×23 minor is nonzero. Consequently im M_w=ker φ. For any d, M_d−φ(d)I maps to ker φ, and adj(M_w) kills that image since adj(M_w)M_w=0. Taking the trace of adj(M_w)M_d=φ(d)adj(M_w) gives α_d=φ(d)α_1. The tuple therefore reduces to the images of (h*,u*,v*), where T* is nonzero. This contradicts the required reduction T=0. No squarefree or irreducibility assumption on the parameter polynomial is needed.

Compact replay specification:
    H = interpolate( [(j, N(W_j)/N(B_j)) for j in 0..48] )
    A = F_523[λ]/H
    α_d = coefficient of ε in N(W+εd) over A[ε]/ε², for d=1,h,u,v
    assert gcd(H, lift(α_1)) == 1
    h*,u*,v* = α_h/α_1, α_u/α_1, α_v/α_1
    assert gcd(H, lift(T(h*,u*,v*,λ))) == 1
Each N uses the same relative determinant mechanics as the interpolation: the 2×2, 3×3, and 4×4 matrices have columns equal to the power-basis coordinates of f, xf, ..., x^(n−1)f. A repeat with no ring-matrix dependence on larger dimensions independently verified the numerical result: over the degree-48 finite field, splitting the quartic and directly checking all 24 permutations gives exactly one W-zero assignment and gives the same terminal polynomial T* coefficient for coefficient as the directional norm computation. Constant coefficients of h*,u*,v*,T* are respectively 21,519,511,464.

Standard-library replay: `replay.py` (historical replay reference). Independent split-and-enumerate cross-check: `one.py` (historical replay reference) (imports the prior modular arithmetic core). This pass did not repeat the fixed-Radau work.
## Shortest preferred closure: one coefficient and one gcd

The same modular interpolation and reduction argument also supports a shorter closure that avoids even the adjugate lemma and recovery of the tuple. In the ordered tower over A[ε]/(ε²), set β=[ε]N(W+εT). An alleged simultaneous zero of W and T induces evaluation to k[ε]/(ε²), a split surjection (split by constants). Multiplication by W+εT maps wholly into the kernel of evaluation. Its matrix in a basis adapted to the free rank-23 kernel has a zero last row; hence its determinant, and in particular the coefficient β, vanishes at the alleged tuple. The computed gcd(H, lift(β)) is 1, a contradiction. This version evaluates T in the modular tower but uses only a single ordinary 2×2/3×3/4×4 norm chain over a dual base and one Euclidean gcd. In particular, it needs no characteristic-zero conjugacy, no separate prime, and no irreducibility or even squarefreeness test.

Exact β residues in ascending order:
    237,433,15,189,256,483,211,216,346,207,442,461,163,485,464,330,
    426,241,142,249,368,277,458,144,71,489,443,352,105,329,17,113,
    416,217,317,5,517,83,271,450,60,455,462,176,288,346,153,357.
The standalone standard-library implementation `direct.py` (historical replay reference) passed in about seven seconds; `replay.py` (historical replay reference) passed in about six seconds for the coordinate compression. For readers who prefer scalar calculations, the final gcd can be verified directly from the H and β arrays above.
