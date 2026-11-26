# Exact widths for strictly adjacent terminal-output SDIRK methods

This note combines the [negative-diagonal width theorem](NEGATIVE-MATCHED-MINIMUM.md) with the [positive-diagonal Chebyshev criterion](POSITIVE-CHEBYSHEV-THRESHOLD.md). The stage minimum below applies to the specified adjacency and output-support pattern, not to unrestricted SDIRK. This is a mathematical proof note, not a Lean certificate.

## Unified statement and separate diagonal hypotheses

Fix p>=2 and a prescribed real-algebraic common physical diagonal gamma. The strict part B=A-gamma I is strictly adjacent: each actual nonzero edge crosses precisely one level; weights are supported only on the terminal output level. Write d for the distance from terminal output, s=p-d, and
```
q=ceil(p/2),     R(s)=min(q,floor((2s+1)/3)).
```
In the two regimes below, literal order at least p forces at least R(s) distinct clock labels eligible for an actual strict route to the terminal support at each d=0,...,p-1. One actual tableau meets all R(s) physical widths simultaneously, with exact order p, exact strict depth p-1 and positive terminal quadrature weights, over a finite real algebraic extension of Q(gamma). It consequently minimizes the physical stage sum in this format, not in unrestricted SDIRK.

- **Negative branch:** every prescribed gamma<0 is allowed; there is no size threshold or excluded negative root. The negative lower proof is over the real reference field and its determinant remains nonzero after extension. Advertised algebraic attainment is at any prescribed negative real-algebraic gamma.
- **Sufficient positive branch:** gamma>0, the nonexceptional scalar lambda_(p-1)(1)!=0, and for p>=3 the singleton scalar lambda_(p-2)(1)!=0. Here J=I_0-gamma I, ell is uniform integration, and lambda_j(f)=ell J^j f. For p>=6 supply an audited sufficient Haar regime: gamma>=tau_(p-5) from the all-prefix theorem, or gamma>=(p-4)/3 from the closed corner bound. For p<=5 this additional gate is void. These are sufficient fixed-positive hypotheses, not a conclusion for every positive gamma or a necessary Haar threshold.

A simple positive root-free choice is **any gamma>=p/3**. In fact the associated Laguerre reciprocal squares sum to j(j+2)/12, so both applicable scalar root maxima are <=sqrt((p^2-1)/12)<p/3, and p/3 satisfies the closed Haar condition. This gives one convenient prescription at arbitrary p, not a necessary language for the diagonal. The exceptional positive construction with lambda_(p-1)(1)=0 is separate (depth p-2), and gamma=0 is separate (the word-span equality below loses its low-valuation terms).

The minimum sum is
```
sum_(s=1)^p R(s) = (p-N)q + 3u^2+u+a(2u+1),
N=floor((3q-2)/2)=3u+a, 0<=a<=2.
```
The unsaturated triples are (2j+1,2j+1,2j+2). This is a physical-layer count, not the dimension of a dense representation frame.

## Common proof steps

**1. Pay one actual layer word, then take adjoints.** At s=p-d take r=R(s) and lower budget b_0=s-r. Using c=A1, multiply by powers of 1-c at the actual levels, with d B edges and the last multiplication allowed at the bottom with the polynomial column. Degrees a<r and sum of multiplier degrees <=b_0 cost at most 1+d+a+b_0<=p. Thus scalar literal order pays the substitution A->I_0, c->X without assuming any intermediate model equality. Before expansion, the row is supported exactly at physical distance d. It factors through the eligible clock labels there; signs of entries, clocks and weights are irrelevant to this factorization.

In reflected coordinates y=1-X, write T=V-gamma I for the adjoint of J, M for multiplication by y. The factorial transform makes these multiplication by z-gamma and D_+=z+z^2 d/dz, respectively. The span of words with d T steps and at most b multiplications is
```
T^max(d-b,0) Poly_(<= b+min(d,b)).
```
For equality add one multiplication at a time: T^d M^b 1 gives the new highest degree, and for b<=d the word M^b T^d1 gives the newly possible valuation d-b at z=gamma. The latter's leading coefficients use nonzero gamma, not a sign. Beyond b=d only the top degree grows. In the lower application r<=dimension is equivalent to 3r<=2s+1 and 2r<=p+1. The word matrix thus asks for r-rank of an exact paired polynomial moment matrix, not a rank assertion about all local dense values.

**2. Substitute the sign-specific line only at the rank and hull gates.** At negative gamma, T has the nonnegative bidiagonal coefficient matrix (-gamma)I+shift; its powers and ordered generalized Vandermondes show every initial test prefix is strict Chebyshev. This is positivity of the formal reference test, not of B. The scalar gates are automatic since ell(I_0+|gamma|)^d 1>0. At positive gamma, ordinary tests and the audited rectangular contact lemma already handle the nonsquare cases. Beyond the tall singleton the only protected lower squares are s=3k+1, r=2k+1 with exponent p-4k-1 (k>=1), hence at most p-5. The upper multi-moment test spaces have dimension n=2b+1 and exponent m=d-b, with m+(n-3)/2=p-s-1<=p-6. This explains the stated sufficient Haar range; no theta/Delta optimization is needed.

At s=1, nonzero lambda_(p-1)(1) forces the oldest layer and its physical depth path. At s=2 there is a real extra singleton obstruction when p>=3: at one eligible clock the second paid row moment equals that clock times the first, whereas lambda_d(X)=lambda_(d+1)(1)+gamma lambda_d(1). If lambda_d(1)=0 the second is nonzero by the nonexceptional premise. If it is nonzero, the required one-node hull is X-lambda_d(X)/lambda_d(1). No assumption places that node inside the interval. At p=2 the s=2 stage is terminal and the extra gate is unnecessary.

**3. Use one actual upper mesh and the separate upper budget b=s-1-r.** Use p levels, initially one site gamma (only the leaf profile reaches it), and reuse the chosen terminal hull at q-capped levels. Below the cap, r>=2b+1 and b<=d. The quotient of a local interpolation error by the monic hull, plus all ancestor sibling degrees, is bounded by b. Its exact test space is contained in T^(d-b) Poly_(<=2b), and the adjoint receipt makes the error vanish. At b=0, use the singleton formula or the one-moment split hull with r-1 generic distinct rational trials and one last root determined by the moment. The two values lambda_d(1),lambda_d(X) cannot both vanish, by consecutive associated Laguerre degrees, so denominators and collisions can be avoided. For b>=1 use the admitted Haar test pairing. With all initial prefixes available, the monic degree-r orthogonal hull has r simple interior roots by the bordered determinant sign test. When using only the closed bound on the actual n-dimensional space, the same sign argument uses filler points tending to the endpoint, and one can add r-n rational outer roots by multiplying the test space by their product. These roots lie in a finite real algebraic extension; there is no assertion about the exact previous coefficient field.

Actual adjacent blocks apply J to predecessor cardinal basis functions and evaluate at the receiving sites. Their strict row sum is J1(X)=X-gamma, so restoring gamma makes c=A1 equal the assigned sites. In the ancestor-first telescope remove a projection only after those above it have been removed. Siblings may keep projections since they cannot increase degree. Each difference is killed by its own receipt, simultaneously over all levels. At order <=p every tree has height <=p-1. Expanding edges A=B+gamma I and I_0=J+gamma I contracts the identity edges and transfers all shifted scalar exactness to literal order. The paid nonzero shifted tall row yields depth exactly p-1.

**4. Use a common terminal witness if exact order is desired independently of the sign.** For even p=2q, take the q-node Gaussian hull P_q. Its square has degree p, vanishes at the nodes and has positive integral. For odd p=2q-1, take the monic hull P_q+epsilon P_(q-1) for a sufficiently small nonzero rational epsilon. Sign brackets retain distinct interior roots; orthogonality to degrees <=q-2 gives exact quadrature through p-1, and cardinal squares give positive weights. Multiplication by P_(q-1) yields a degree-p polynomial with zero quadrature and nonzero integral. In either parity the lower degrees agree, so the degree-p clock moment, i.e. the first unpaid bush, fails. This is valid for either sign: capped ancestors require only d+b=p-1-q, namely q-1 (even) or q-2 (odd), so the odd perturbation does not invalidate capped reuse. The original negative Gaussian rule can instead be retained with its already audited unpaid tall failure; there is no need to demand an unpaid tall test in the positive case.

## Estimate for the closed positive-diagonal gate


The closed sufficient bound reduces to positivity of the two odd-corner forms in the three-column case. Set M=p−5 ≥ 1 and consider the factors u^(3−k)(u−1)^k for k=1 and k=3.
For u≥1 they are at least (u−1)^3. If
Q(z)=S(1+γz) and N=∫₀∞ z^3 e^(−z)Q(z)^2 dz, the positive tail
is at least γ^4 exp(−1/γ) N. For 0≤u≤1 the same associated
Laguerre kernel estimate as in the all-m proof, keeping its
pointwise exponent, gives

    |S(u)|² ≤ N · binom(M+3,4)/6
                    · exp(2(M−1)(1−u)/(4γ)).

In fact expand Q in L_j^(3), j<M, with squared norms
(j+3)!/j!, and use
L_j^(3)(−t)≤binom(j+3,3) exp(jt/4) for t≥0, from their
nonnegative coefficient series. Cauchy–Schwarz and the
hockey-stick sum give the displayed inequality.
The possible negative mass divided by the positive tail
is therefore at most

    [binom(M+3,4)/(6γ^4)]
       ∫₀¹ v^k(1−v)^(3−k)
                  exp((M+1)v/(2γ)) dv.

For nonnegative tilt the integral is at most the same
integral with v^3: weighted AM–GM bounds its mixed monomial
by the appropriate convex combination of v^3 and (1−v)^3,
and reflection pairs the increasing tilt preferentially with
v^3. At γ=(M+1)/3 the prefactor is at most 27/32: for the
integer U=M+1≥2,
(1−1/U)(1+1/U)(1+2/U)≤3/2, since multiplying the difference
by 2U³ gives (U−2)(U²−2U−2)≥0, with U=2 handled by equality.
The remaining integral of v^3 exp(3v/2) is
(32−2 exp(3/2))/27 by direct integration. Hence the mass
ratio is strictly below 1 (at most 1−exp(3/2)/16). Both
corner forms are positive definite at this γ. For larger γ the same bound only decreases. This gives the sufficient gate γ≥(p−4)/3.
