# All field characteristics for the bare cubic quotient-coprimality statement

Over any field K of characteristic zero, the nonzero cubic profile P of the original five physical primitive equations is coprime to the original pencil W=a j+b F. Over **every field** of characteristic p>13, the complete exception test is as follows. Normalize a=1 and normalize the nonzero cubic scale by P(tY)=P_z(Y), with the branch-free mask in CUBIC-ALL-FIELDS.md. Assume b,t,u and t−u nonzero, W(t)=W(u)=0, and all five literal primitives with the same κ. No hypotheses on P(t), P(u), P(0), κ or 1+b are imposed. This counts only solutions where W and P fail to be coprime.

There are four pairwise-coprime positive integers:
* m0=23.
* m1=59148809425984527898638696983 (=31729·294013·1980936907·3200755097).
* m2=1619055934325082180928905385249423969591945531.
* m3 is the 2,183-bit fourth entry of `cubic_global_components.json`, specified equivalently, as regards its prime support, by the exact resultant test below.

If p divides none, the bare coprimality assertion holds. If p divides the product, over K there is **exactly one normalized ordered exception**, already defined over the prime field. Its universal z,t,u,b,P,κ, monic gcd, and minimal numerator and cofactor are in `cubic_bare_accepted.json` under the component's modulus, in ascending powers. Each survives b+1≠0, P(0)≠0, κ≠0 and degree exactly three.

| Exceptional component | P(t) | P(u) | deg gcd(W,P) | minimal deg N for (XW)T=NP with N≠0 |
|---|---|---|---:|---:|
| m0 | nonzero | zero | 2 | 5 |
| m1 | zero | nonzero | 1 | 6 |
| m2 | nonzero | zero | 1 | 6 |
| m3 | nonzero | nonzero | 1 | 6 |

In particular the **bare two-amplitude** coprimality exception set is exactly p|m3. Zero shared leakage implies bare coprimality unconditionally. With deg N≤5, the sole unguarded exception is p=23; requiring the second amplitude nonzero rules it out. The distinguished p=23 configuration is t=14, u=15, b=1, P=15+8X+19X²+22X³, κ=5, already over the prime field. These are statements about the scalar port, not positive-characteristic RK stage lower bounds.

## Necessity and support check

Retain R,A,C,q from the original exact full-mesh calculation (equations and branch-free normalization in CUBIC-ALL-FIELDS.md). In particular R is the degree-50 primitive ratio polynomial, A,C are the two t-degree-five primitive gates, and q=Res_Y(H,P_z;6,3). If W and P have a common factor, the point z=u/t,t makes A,C,q and R all vanish over an algebraic closure. Define

    T(z)=Res_t(A,q;5,33),      U(z)=Res_t(C,q;5,33),
    Δa=Res_z(R,T),            Δc=Res_z(R,U).

Hence both integers vanish. There are no such bad points in characteristic zero. In prime characteristic >13, the single exact test is **p divides gcd(Δa,Δc)**; every prime left by this necessary test is realized. In particular m3 has exactly the prime support of this gcd after removing the prime supports of 2·3·5·7·11·13·m0·m1·m2. This is an alternative definition that does not require displaying a 658-digit modulus.

The U degree bound is 7·33+5·12=291. All 292 integer interpolation nodes of U were independently verified with fixed Sylvester determinants and the full inner degree-bounded q grid. Its actual degree is 283. The full signed Δc has 54,291 bits; separate finite-field Euclidean resultants at 4,310 sieve-proved primes and the squared Sylvester-Hadamard bound certify the exact integer by CRT. The independently checked old Δa has 45,887 bits. Divide the common gcd by 2^6033·3^4467·5^2590·7^333·11^836·13^165. Each mᵢ divides what remains, the four mᵢ are pairwise coprime, and repeatedly dividing away their gcds removes the entire remaining integer. Factoring the mᵢ is unnecessary.

## Sufficiency and uniqueness over every extension

Over ℤ/mᵢ verify, with actual Bézout identities and two polynomial quotient identities, gcd(R,T)=z−zᵢ. Evaluate A,C at zᵢ and verify the second polynomial gcd is t−tᵢ by the same three identities. These witnesses remain proofs after reduction to **every** prime divisor of mᵢ and after arbitrary field extension. Thus no further orderings or extension-field roots are possible. W(t)=0 gives the unique b=−j(t)/F(t) because the denominator, j(t), t,u and t−u are units modulo mᵢ. Branch-free cubic normalization gives the unique P, and I₃(t)=κt j(t) fixes κ.

The verifier checks W(t)=W(u)=0 and all five original primitive equations in ℤ/mᵢ; the promised nonzero quantities have explicit multiplicative inverses. It verifies monic gcd(W,P)=gcd(XW,P) by the same strong combination and divisibility equations, and checks the primitive quotients N=(XW)/g and T=P/g by their literal product identity. Every nonzero mesh numerator is divisible by this N, hence its recorded minimal degree is exact. The table is therefore both necessary and sufficient in every stated field.

From this directory run `python3 verify_indices.py inputs .`, then `python3 verify_cubic_bare_global.py inputs .`. Both are standard-library only. This single additional norm and complete component audit give an independent, shorter proof of the full-mesh characteristic-23 classification; the complementary-quartic derivative proof in CUBIC-ALL-FIELDS.md remains available separately.
