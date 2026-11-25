# Strict properness as an algebraic common-diagonal refinement

This is a source-only mathematical supplement to `PROOF.md`. **Strictly proper means exactly `deg P<deg Q`** for the normalized scalar tall fraction. No stability assertion, sufficient tableau subclass, small-order nonlinear test, or new unrestricted floor is used.

Let the finite tableau have strict nonzero rational common diagonal γ, over any characteristic-zero coefficient field. A reduced response has `Q=(1−γX)^r`, with `m=deg P<r`; `r=s−c₀` records canceled factors exactly. If its paid order is `p≥2`, then

    r ≥ p+1,          s ≥ p+1+c₀.                          (1)

This is stronger than just `s≥p+1` when the physical response loses a pole copy. Proof: one distinct pole gives `p≤m+1≤r`. If `r=p`, then `m=r−1` and the degree-r paid coefficient equation is

    0=E_r(γ)=Σ_(i=0)^r binom(r,i)(−γ)^i/(r−i)!
            =(−γ)^r L_r(1/γ),

where `L_r` is the ordinary Laguerre polynomial. For `r≥2` its rational-root exclusion is elementary. Multiply by `r!` with an overall sign to make it monic integral. A rational root a is a nonzero integer. If a prime ℓ divides a, then for `j≥1` the valuation of its j-th term is at least

    v_ℓ(r!) + j − v_ℓ(j!) > v_ℓ(r!).

The inequality `v_ℓ(j!)≤j−1` follows immediately by counting multiples of ℓ recursively (if `k=floor(j/ℓ)>0`, use `k+v_ℓ(k!)≤2k−1≤j−1`). This contradicts cancellation of the constant term. Thus a would be `±1`. Reducing at any prime dividing r kills every nonleading term because `r!/j!` contains r for `j<r`, whereas the leading term is a unit. This proves (1) over the stated field by injectivity of the rational embedding.

## The adjacent rational cap is excluded too

At `r=p+1` there could a priori be `m=p−1` or `m=p`. The first would use the extra slot `p=m+1` and would require

    E_p(γ; r=p+1) = (p+1) Σ_(k=0)^p binom(p,k)(−γ)^(p−k)/(k+1)! = 0,

by changing variables `k=p−i`. This is precisely the previously proved rational common-diagonal shifted scalar at degree p (equivalently `L_p^(1)`), known nonzero for `p≥2`. Consequently **`r=p+1` forces `m=p`**. At the minimum physical width `s=p+1` there is no cancellation and exactly one numerator-degree deficit; no generic assumption on the leading coefficient was necessary. More generally a strictly proper rational common diagonal paying `p=m+1≥2` must have `r≥p+2`. This does not exclude such a cap for every higher exponent.

If `ν=r−m≥1`, formula (1) together with the scalar capacity is `p+c₀+max(1,ν−1)≤s`. For ordered coefficients the signed condition replaces the second term under the max by `ν−1+η+σ` with the precise numerator repeat and sign-gap charges of `PROOF.md`. A negative retained pole also imposes `p≤m`. The arithmetic proof of (1) itself imposes no order or realness on the coefficient field.

## Signed root consequences and all-order scalar benchmark

Under a real embedding, the minimal rational strict-proper width `s=p+1` is in the **one-below-cap** case, `m=p` and `δ=1`. All nonreal numerator roots are simple. A repetition can only be one real double root. If γ>0, it must belong to one of the two allowed reciprocal bins (negative or above γ), and at most one simple real root can occur in the other bin; if γ<0, the negative-side rules apply, with all real roots negative in this exact-degree branch. There is also an exact possible double-root location, not a claim it occurs. Whenever `p=m`, compare the full finite recurrence of `F=(1−γX)^r exp(X)` with its degree-m prefix P to get

    (1−γX)P′ + (γX+rγ−1)P
      = X^m [ γ E_m X − (m+1)E_(m+1) ].

Thus a repeated ordinary numerator root x, necessarily nonzero, would have to be `x=(m+1)E_(m+1)/(γ E_m)`. At the minimum rational width this candidate is rational and nonzero by the two Laguerre exclusions. No further rational nonvanishing test is claimed.

The strictly proper rational bound is sharp **for scalar tall order at every p≥2**, not just at selected low orders. Fix any nonzero rational γ, put `s=p+1`, take `Q=(1−γX)^s`, and truncate `P=Σ_(j=0)^p E_j(γ; s)X^j`. The `L_p^(1)` exclusion gives exact numerator degree p, and the ordinary `L_(p+1)` exclusion gives a nonzero first unpaid coefficient. Any cancellation would lower r below p+1, contrary to (1). Thus it is a normalized reduced strictly proper pair with exact scalar paid order p. Realize it by `A=γI+L` with unit subdiagonal shift L; since `A^j 1`, `0≤j<s`, form a rational basis, choose `b` to match the first s tall coefficients of this particular fraction (including the chosen first unpaid coefficient of the target exp prefix). Equal denominator and numerator degree ≤s ensure the resulting fraction is exactly P/Q. This benchmark does not assert full rooted-tree order.

If the nonzero common diagonal is allowed to be algebraic, proper scalar width `s=p` instead forces `r=p,m=p−1,c₀=0`. Its `p` positive simple gamma branches are exactly the ordinary Laguerre ones; the numerator configuration alternates on increasing gamma as in the cap table of `PROOF.md` with `m=p−1`. Conversely every such branch admits a proper exact scalar realization by the same basis construction. The elementary proof establishes irrationality for p≥2. Invoking the classical Schur irreducibility of the ordinary Laguerre polynomial additionally gives exact field degree p; that known irreducibility result was not re-proved or network-verified in this pass. Then the individual branch configurations describe the different real embeddings of the **scalar** fraction, even if the whole tableau is not defined over `ℚ(γ)`.
