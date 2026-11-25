# Complete characteristic classifier for the genuine nonzero-origin quartic pencil port

**Theorem.** Let K be a field of prime characteristic p>13. Use the original F,j,J=Xj and normalize a=1 in G=X(j+bF), with b(b+1)≠0. Consider distinct nonzero roots t,u, z=u/t, a quartic R nonzero at 0,t,u, and the true factorization G=R X(X−t)(X−u). Define Iₖ(x) as the zero-constant primitive of XᵏR evaluated at x. Require the three genuine scalar conditions I₁(t)=0, I₂(t)=κJ(t) and I₂(u)−tI₁(u)=κJ(u) with the same κ. Over an algebraic closure of K these have a solution **if and only if**

    p divides 40743825584966961425950943209234954914929956692140434167752418813578190817982950589.

There is no cutoff on p and no need to factor the displayed integer in order to test any given characteristic. This is the classification of the scalar pencil port, not a statement that a Runge–Kutta tableau with that branch exists.

There is also an exact test for the original K, not just its closure. Set

    U = 65637022433 = 64279·1021127,
    V = 107451025593855819651531329774816424560049512380020377454517620130829.

The displayed exceptional integer is 53·109·U·V, with these four factors pairwise coprime. For p dividing 53U there is exactly one normalized ordered solution, already over Fₚ. For p dividing 109V the solutions over K are parametrized by the roots in K of a monic separable quadratic:

* p=109: z²+75z+81;
* p dividing V: z²+22308708150660568534577735707715131317381807983010544121493288439542z+104589693048698079822014684935511662722383905613595108139641152049864, with its coefficients reduced in K.

Every root gives exactly one normalized solution. In particular every exceptional characteristic needs at most a quadratic extension of the prime field. The coefficients t,u,b,κ,R in each of the four universal component rings are in `quartic_global_accepted.json`. Quadratic ring entries [c,d] mean c+dz; R is listed from constant to leading coefficient. The nonzero scaling of R can be restored when one does not fix the monic complementary factor.

## Necessity: one additional projection keeps the same t-fiber

As in the original nonzero-origin calculation, the three physical equations imply the integer A(z,t)=M(z,t)=B(z,t)=0. Here R₀ is the **primitive degree-40 ratio polynomial**, not the quartic profile R. The integer Resₜ(A,M;9,10) is R₀ times a positive constant whose only prime factors are at most 13. Thus R₀(z)=0. No leading coefficient is assumed a unit at the chosen point. Set

    U₀(z)=Resₜ(A,B;9,14),      U₁(z)=Resₜ(M,B;10,14),
    D₀=Res_z(R₀,U₀),          D₁=Res_z(R₀,U₁).

A common finite root forces both ordered fixed Sylvester determinants to vanish even when degrees drop. Therefore p divides gcd(D₀,D₁). The exact U degrees are 84 and 100 and the signed indices have 27,020 and 24,040 bits. The first index and R₀ are independently verified in `verify_indices.py`. The second is independently recomputed at all 161 degree-bounded integer interpolation points by the original fraction-free determinant; `verify_quartic_global.py` checks its full signed value by 1590 exact prime-field remainders and a rigorous Hadamard/CRT bound. This is not numerical elimination.

Remove the small-prime factors 2^2854 · 3^1259 · 5^650 · 7^404 · 11^730 · 13^144 from gcd(D₀,D₁). The residual is a positive 740-bit integer. The following eight pairwise-coprime components have **exactly the same prime support** as this residual. Replicating the components’ prime powers is not needed: each divides the residual, and repeatedly removing their gcds leaves 1.

| Component | Necessary gcd on z | Result for all its prime divisors |
|---:|---:|---|
| 43 | 1 | Singular F/j pencil |
| 53 | 1 | Accepted over the prime field |
| 109 | 2 | Accepted in the quadratic component |
| V | 2 | Accepted in the quadratic component |
| 7109270134834058998139 | 1 | Zero or repeated knot |
| 104295260060968696963648183 | 1 | Singular F/j pencil |
| 2551619843329 | 1 | Terminal/zero-origin condition fails |
| U | 1 | Accepted over the prime field |

In the second column the number is the **degree** of the monic gcd, not its polynomial value.

## Why the component certificate decides all primes simultaneously

For every component m the verifier first proves a monic g(z) is gcd(R₀,U₀) over Z/mZ in the strong sense that g divides both inputs **and** is a polynomial Bézout combination of them, each identity checked coefficient-by-coefficient. Therefore the same g is the actual gcd after reduction to every Fₚ, p|m. All possible finite z are the roots of g, with no lifting assumption. The two degree-two components have discriminants coprime to m.

Form the free ring E=(Z/mZ)[z]/g. Its monic defining relation makes arithmetic unambiguous even if m is not prime or g splits. In E[t] the verifier proves a second set of two divisibilities and one Bézout equality: gcd(A,M)=t−t₀ is monic linear. This is a simultaneous ideal identity, so at any root z in any field of characteristic p|m, t must equal the specialization of t₀. Quotient-field inverses are never guessed. Every division uses an explicit inverse whose product is checked to be 1.

The four rejected components have an identically zero forbidden quantity at that candidate, or a unit obstruction, in E. On each accepted component t,u,b,b+1 and the relevant knot values are units in E; direct coefficient arithmetic verifies G=R X(X−t)(X−u), deg R=4, all three amplitudes are units, and the three original primitive equalities hold. A monic g always has a root after algebraic closure. Conversely any root already in the given K specializes these same polynomial identities and units and hence gives an actual solution. This proves the claimed necessity, sufficiency and degree-of-extension test without a primality assumption on U or V.

## Replay

From this directory:

    python3 verify_indices.py inputs .
    python3 verify_quartic_global.py inputs .

Both verifiers use only the Python standard library. The second returns the complete classification and regenerates all eight component decisions and the universal accepted witness file. The separate search/splitting code is not needed to establish or use the theorem.
