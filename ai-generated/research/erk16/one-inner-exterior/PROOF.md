# A uniform six-node density exclusion of the one-inner-exterior quartic

**Scope.** This is a source-mathematics exclusion with an exact rational certificate, not a Lean replay or a stage-floor theorem. Use the actual `WeakFive16.Moments` packet (monic quartic after harmless scaling) and the already earned one-inner-exterior signs and chronology from [the paid chronology](CHRONOLOGY.md), §2:

    a < 0 < z < h < u < 1,   sign q(z) = sign q(u) = − sign q(h).

All these three q-values are nonzero. The true outside word is integral_a^0 x(x−u)q=0. The true right words are integral_z^1 (1−x)q=0 and integral_z^1 (1−x)^2q=0. The six global words are

    integral_0^1 W q D H = 0       for deg H ≤ 5,
    W = X(1−X)(X−a),               D = (X−z)(X−h)(X−u).

All integrals below mean the polynomial formal-moment functional, with the original exact normalization. The integral reparametrizations are affine polynomial substitutions only. We use no hypotheses on signs of RK output weights.

## 1. Actual roots and the exterior density parameter

Work, if necessary, in an order-preserving real closure of the original ordered field. The displayed polynomial identities, strict inequalities, formal-moment identities, and exact rational integration rule all persist by scalar extension; a contradiction there excludes the original packet. No Archimedean assumption, limit, continuity of real-valued parameter functions, or numerical approximation is used. The only root extraction is the ordinary intermediate-value property for polynomials over a real closed field.

Because W is strictly positive on the open unit interval, the global words force at least six interior sign-changing roots of qD. Indeed if there were at most five, multiply by the product of those roots. The resulting polynomial has fixed sign on the interval. Its weighted degree is at most 3+7+5=15; the 19 distinct interior nodes of the checked positive rule cannot all be its zeros, so its integral is strictly nonzero. Similarly the nonzero q must have a sign-changing root α in (a,0), because x(x−u)>0 there and the paid outside word is zero. The polynomial is quartic and D supplies just three interior roots, all simple and disjoint from q. Hence q has exactly the one simple exterior root and exactly three simple interior roots. Write

    q = (X−α) R,   R = ∏_{j=1}^3(X−ρ_j),   0<ρ_1<ρ_2<ρ_3<1.

Set A=−a>0 and λ=−α>0. The outside word is very restrictive for the **actual** root, unlike an arbitrary exterior atomic mass. Substitute x=−A t and cancel the nonzero scalar:

    0 = integral_0^1 t(At+u)∏_j(At+ρ_j)·(t−λ/A).

The first factor (including t) has strictly positive coefficients of powers 1 through 5. Its integral-weighted barycentre is therefore a strict convex combination of the rationals (k+1)/(k+2), k=1,…,5. Thus

    2/3 < C := λ/A < 6/7.

This uses only formal antiderivatives of monomials. Define the compact parameters

    s = A/(1+A),       r = λ/(1+λ) = C s/(1−s+C s),
    W_{s,r} = X(1−X)[s+(1−s)X][r+(1−r)X].

Both factors normalizing W(X−α) are positive constants, so the global words say that the monic degree-six polynomial RD is the actual monic orthogonal polynomial of degree six for W_{s,r}. Its six unit roots, in increasing order, will be denoted β_1,…,β_6.

Each of (z,h) and (h,u) contains an odd number of roots of q because the actual q-values alternate. There are just three unit roots of q, so each such gap contains exactly one; the last q-root lies before z or after u. The two possibilities are precisely:

    phase A: z=β_2, h=β_4, u=β_6,   roots R = β_1,β_3,β_5;
    phase B: z=β_1, h=β_3, u=β_5,   roots R = β_2,β_4,β_6.

## 2. Reusable coordinatewise monotonicity of the six positive-rule nodes

For every parameter pair in the whole closed square 0≤s,r≤1, W_{s,r}>0 on (0,1). The moment Gram matrix through degree five is nonsingular: for any nonzero degree≤5 polynomial f, the integral of W_{s,r} f² is strictly positive by the checked finite 19-point rule (integrand degree≤14). Hence there is a unique monic orthogonal polynomial of degree six. The sign-cut argument from §1 gives six distinct unit roots for it; now the maximal weighted degree is 4+6+5=15.

Division by this polynomial gives the six-node interpolation rule for W_{s,r} exact through degree eleven. Each node weight is strictly positive by testing the square of its degree-five cardinal polynomial: the integrand degree is ≤14, so the 19-point rule has a strict positive sample. In particular, for every nonzero f of degree≤5 the quotient

    R_{s,r}(f) = integral_0^1 X W_{s,r} f² / integral_0^1 W_{s,r} f²

is a positively weighted average of those nodes where f is nonzero. This use of a quotient is only an algebraic identity over the ordered real closure.

Hold r fixed and write μ_k=integral_0^1 X^k V f² with V=X(1−X)[r+(1−r)X]. For s_lo<s_hi, the numerator of R_{s_lo,r}(f)−R_{s_hi,r}(f) after multiplying the positive denominators is

    (s_hi−s_lo)(μ_0 μ_2−μ_1²) > 0.

The strict variance identity follows by integrating (X−μ_1/μ_0)^2 V f² with the same positive rule; its degree is ≤15. Thus every quotient decreases with s, and symmetrically with r. No derivative of a moving root is required.

To transfer this to the i-th ordered root, take the subspace of the degree≤5 polynomials whose values at the six low-parameter roots are supported on the first i of those roots. Take the subspace whose values at the six high-parameter roots are supported on the last 7−i of those roots. These subspaces have dimensions i and 7−i by uniqueness of ordinary interpolation. Their intersection has a nonzero polynomial f, for which the two averages satisfy

    β_i(low) ≥ R_low(f) > R_high(f) ≥ β_i(high).

Hence each β_i is strictly decreasing in each coordinate separately, or weakly decreasing when comparing corners with equality allowed. This finite-dimensional argument holds over any ordered real closure and depends only on paid positive polynomial moments.

## 3. The two true right tests as uniform multiaffine functions

For either phase put L=1−z>0, x=z+Lt, and

    γ=(1−r)(1−z),     δ=r+(1−r)z,
    x+λ=(1+λ)(δ+γ t).

In phase A set e=(z−β_1)/L, l=(β_3−z)/L, k=(β_5−z)/L. The actual right combination equal to zero by the two right words is

    integral_z^1 (1−x)(x−z)q(x)
      = (1−z) integral_z^1 (1−x)q − integral_z^1 (1−x)^2 q
      = (1+λ)L^6 A_test(γ,δ,e,l,k),

where

    A_test(γ,δ,e,l,k) = integral_0^1 t(1−t)(δ+γ t)(t+e)(t−l)(t−k).

In phase B set l=(β_2−z)/L, m=(β_4−z)/L, k=(β_6−z)/L. The actual right second word is

    integral_z^1 (1−x)^2 q(x) = (1+λ)L^6 B_test(γ,δ,l,m,k),

where

    B_test(γ,δ,l,m,k) = integral_0^1 (1−t)^2(δ+γ t)(t−l)(t−m)(t−k).

In both cases the prefactor is strictly positive and the five-variate normalized test is separately affine in every argument. Its bound on a closed rectangular box is thus the largest vertex value, by sequential convex linear interpolation. This observation is valid over the ordered field, including for degenerate interval bounds.

## 4. Entire continuous-sector rational certificate

Partition s into the intervals with endpoints

    (0,1,2,3,4,5,6,8,10,12,16,20,24,32,48,64)/64.

Every cell uses the **entire** ratio interval C∈[2/3,6/7]. Because C s/(1−s+C s) increases in both arguments, the lower (s,r) corner is at (s_lo,2/3) and the upper corner is at (s_hi,6/7) in the (s,C) chart. The theorem of §2 encloses each β_i of the actual unknown parameter between the β_i of these corners in reverse order. At each rational corner the six disjoint rational isolators are given in the checker table as [N/4096,(N+1)/4096]. The checker verifies them by opposite exact endpoint signs of the unique orthogonal monic polynomial; it solves only the rational linear equations for that polynomial, and verifies all six equations again. For a corner with W = x(1−x) Σ_{j=0}² v_j x^j, its k-th moment is exactly Σ_{j=0}² v_j/[(k+j+2)(k+j+3)]. Six disjoint alternating endpoint signs and degree six identify all the roots. There is no root approximation of the original parameters.

For each cell the γ and δ bounds use their monotonicity in r,z. The centered ratio (β−z)/(1−z) is increasing in β and decreasing in z on the open unit square (clearing positive denominators proves both); compute end bounds using opposite interval endpoints. Change signs for e. This gives the five parameter intervals for A_test and B_test. Each of the 32 vertices is evaluated by exact polynomial multiplication and integration via the monomial formula. The resulting signed upper bounds below have common denominator 1,000,000:

    s cell (numerators /64)      A cap     B cap
      0–1                       −744      −38
      1–2                       −740      −50
      2–3                       −741      −65
      3–4                       −746      −88
      4–5                       −758     −114
      5–6                       −750     −134
      6–8                       −673      −39
      8–10                      −692      −99
     10–12                      −704     −162
     12–16                      −609      −68
     16–20                      −650     −187
     20–24                      −692     −301
     24–32                      −594     −237
     32–48                      −490     −221
     48–64                      −713     −737

Both are uniformly strictly negative on all cells, contradicting the corresponding paid right zero. The few rational corner calculations merely bound the full continuous families; no input is restricted to a fixed fibre or a real numerical sample. The checker uses only integer/rational arithmetic, verifies the fixed interval table and signed caps, and performs no parameter search or resultant, algebraic norm, or Robin calculation. It ran successfully using the standard Python rational library, not Lean.

**Reflection.** For h>1 and the other three non-origin marks interior, set q′(x)=q(1−x) and (u′,a′,h′,z′)=(1−z,1−h,1−a,1−u). Both outer pairs exchange; the two inner words reflect exactly to their opposites, and the degree-four nodal mask and weight X(1−X) preserve the global tests under substitution. The non-origin q-values stay nonzero, and no reflected non-origin clock is 1 by the original distinctness from 0. To ensure the reflected packet is also active at its inserted origin, the outside-word and global variation argument in §1 applies before use of the chronology: the reflected W is positive, the three interior reflected marks are distinct and not q′-zeros, and the reflected exterior word forces a fourth root off [0,1]. Thus q′(0)≠0. The previously earned chronology and sign transfer can then be applied to q′, with a′<0.

**Handoff boundary.** This closes the one-inner-exterior sector, using the already established one-inner chronology and alternation in its suitable orientation. It does not analyze the strictly interior chart, any different weak-four chart, or the independent admission and stage-floor assembly. In particular no unconditional ERK16 bound is claimed.
