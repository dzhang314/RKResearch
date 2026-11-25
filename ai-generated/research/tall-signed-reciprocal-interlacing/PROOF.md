# Ordered signed reciprocal labels: exact variation, interlacing and common-diagonal cap

Source-only all-order analysis. No finite-case probe, Lean invocation, repository change, network access, or held input. The signed atom weights below are pole/zero multiplicities and are not RK weights, clock masses, or chronology flags. No new unrestricted stage minimum is claimed.

## 1. Exact finite log moments and the residual interlacing theorem

Let K be an ordered field and work in its real closure and algebraic closure as needed. For a reviewed order-p tableau set `R=P/Q`, normalized and reduced (`P(0)=Q(0)=1`). Let `m=deg P`, `r=deg Q`. Assume only in this ordered part that **Q splits over the real closure** (automatic for a lower triangular A over K); P need not split there. The nonzero reciprocal labels λ are the roots of the monic reciprocal polynomials of P and Q, counted as distinct locations. At a pole put `wλ=+` its multiplicity; at a numerator zero put `wλ=−` its multiplicity. No label is common to both. Put `d=#distinct pole labels`, `eP=#distinct numerator labels`, `u=#distinct nonreal numerator labels`. The u nonreal labels occur in conjugate pairs and do not count their multiplicities.

The finite paid response agrees with the reciprocal-factorial prefix through degree p. Setting `U=Σ_(j≤p) X^j/j!` gives `R′/R=1+O(X^p)` at zero, since `U′−U` vanishes to order p, a finite polynomial identity. Equally, from the product `(1−λX)^(−wλ)`, we have `R′/R=Σ wλ λ/(1−λX)`. The exact moment conditions are

    Σ wλ λ^k = 1_(k=1)         (1≤k≤p),
    Σ wλ = r−m.                (constant degree census)

In particular, for every polynomial f of degree at most p,

    Σ wλ f(λ) + (m−r) f(0) = f′(0).                        (1)

For the special tests `f=tg`, define atoms `ρλ=λ wλ` and `ρ0=−1`. These annihilate all g of degree ≤p−1. Sort the real reciprocal labels together with 0; let `v` be the number of adjacent sign changes of ρ on this sorted real list, and `σ` the number of adjacent equal-sign pairs. Thus `σ=d+eP−u−v`. In particular the signs on negative real labels are the opposite of the zero/pole types, and 0 is always a negative atom in this test. It is not ordinary unweighted pole-zero interlacing at the origin.

Here is an exact polynomial mechanism, stronger than just the degree inequality. Define

    H(t)=t ∏_(λ distinct nonzero)(t−λ),    N=deg H=d+eP+1;
    B(t)= H(t) Σ_(a in support including 0) ρ_a/(t−a).

Then `B` is a nonzero polynomial, `B(a)=ρ_a H′(a)` at every support point, and

    deg B ≤ N−p−1 = d+eP−p.                               (2)

This follows by expanding `(t−a)^−1` at infinity: the annihilated moments are precisely the first p Laurent coefficients. The conjugation-symmetric B has real coefficients. For sorted real locations `a_1<…<a_n`, `H′(a_i)` has sign `(-1)^(n−i)` because all nonreal quadratic factors are positive on the real line. Thus B changes sign in each consecutive real gap whose two atoms have **equal signs**, and its sign agrees at the two endpoints of each opposite-sign gap. Every equal-sign gap contains at least one real root of odd multiplicity; an opposite-sign gap can only contain even total real root multiplicity. This follows over a real closed field purely by factoring polynomials and comparing signs. It proves

    p ≤ d+eP−σ = u+v.                                      (3)

More strongly, at most `u+v−p` root-degree units of B can be used beyond one required per equal-sign gap. If `p=u+v`, B has exactly one simple real root in each equal-sign gap and nowhere else, and the scalar precision is exactly p by its nonzero top Laurent term. If also `σ=0`, then `B=−H′(0)` and `ρ_a H′(a)=−H′(0)` at every label; this is the unique barycentric equality, not just a sign constraint.

**Sharpness of the sign-only mechanism.** For a prescribed list of distinct labels (including conjugate pairs) and arbitrary real signs with a negative origin, choose a real linear factor with one root in each equal-sign gap, and scale the product to have `B(0)=−H′(0)`. Then `B(a)/H′(a)` gives exactly those real signs and nonzero conjugate weights at nonreal labels. Its partial fractions give exact vanishing through the order in (3). This is sharp for variable signed atom weights, not a claim that the resulting weights have the integer-multiplicity form of an actual response or that the resulting response has genuine nonlinear RK order.

## 2. Split-real DIRK: explicit gaps and the near-cap ledger

The exact variation `v` has an elementary gap census. On the negative side poles have sign −, numerator zeros sign +, and 0 has sign −. Let `a_−` be the indicator of a numerator zero to the left of the first negative pole (or anywhere in the negative half if there are no negative poles). Let `g_−` count occupied gaps between successive negative poles or between the last negative pole and 0; a gap is occupied if it contains at least one real numerator zero. The contribution is `v_−=a_−+2g_−`. On the positive side poles have sign +, numerator zeros sign −, and 0 has sign −. If there is any positive pole let `g_+` count its occupied interior gaps and `a_+` indicate a zero to the right of the last positive pole. The positive contribution is `v_+=1+2g_++a_+`, and is zero if there is no positive pole. Positive zeros before the first positive pole spend degree but add no variation. In both halves additional zeros in an already occupied gap add no variation. In particular

    v ≤ 2d+1,      p ≤ u+2d+1,

and if there is no negative real numerator root, already `v≤2d`. If every numerator root is real, the first bound yields `p≤2d+1` no matter how large r is. Statement (3) with the actual gaps can be stricter. With `σ=0` the signed list alternates: on either side the types alternate, the nearest negative label to 0, if any, is a numerator zero, and the nearest positive label, if any, is a pole.

Let `η=m−eP` be the numerator repeated-degree excess. For `p=m+1−δ`, the exact constraint is

    η+σ ≤ d−1+δ.                                          (4)

At the ordered degree cap `p=m+1`, repetitions and failures of signed alternation share only `d−1` degrees. A repeated nonreal conjugate pair costs at least two. Equivalently `m−u≤v−1+δ≤2d+δ`. If the budget in (4) is fully spent, (2) describes the residual interlacing exactly, and the precision is exactly p.

For physical DIRK stage bookkeeping let `c₀` be the canceled degree from the characteristic numerator/denominator and `ν=s−deg N_phys`, so `m=s−c₀−ν`. The older split-pole theorem permits at most one extra slot, and only if a retained pole is positive. Consequently the combined bound is precisely

    p+c₀+ν ≤ s + min( 1_(positive retained pole), d−η−σ ).   (5)

The signed result tightens that older bound for measured data when `η+σ>d−1_(positive retained pole)`. It is not an unconditional improvement after ignoring numerator and pole data. At `s=p−1` the old split-pole cap would force `c₀=ν=0,m=s` and a positive retained pole; (4) gives the additional necessary interlacing condition. A physical diagonal zero is not a retained pole, and no clock or weight failure enters (5).

### Extra moment strength beyond variation

The k=0 census in (1) retains information lost by the `f=tg` sign test. Let `J(t)=∏_(ζ nonreal distinct numerator labels)(t−ζ)`, real monic and strictly positive on the real line. For any real f of degree ≤p−u, (1) gives the **full** remaining real moment condition

    Σ_(real zeros ζ) mult(ζ) J(ζ) f(ζ)
      = Σ_(poles λ) mult(λ) J(λ) f(λ)
        + ((m−r)J(0)−J′(0))f(0) − J(0) f′(0).             (6)

This permits localized positivity tests and uses no unknown numerical RK weights. For one useful uniform test, put `C=J ∏_(poles distinct)(t−λ)^2`, a positive value on each real numerator zero and at 0. Define the real quantity

    T = m−r + 2 Σ_(poles distinct) 1/λ
                + Σ_(nonreal numerator distinct) 1/ζ.

If `p≥u+2d`, then testing C in (1) gives

    Σ_(real zeros ζ) mult(ζ) C(ζ) = C(0) T.                 (7)

Thus T≥0, and equality occurs exactly when there are no real numerator zeros. If `p≥u+2d+1`, testing `tC` gives `Σ mult(ζ) ζ C(ζ)=−C(0)`; thus T>0 and the C-weighted real-root centroid is `−1/T`, with the usual strict between-extremes inequalities when multiple real labels occur. If `p≥u+2d+2`, testing `t²C` contradicts the existence of those real zeros, giving an independent positivity proof of the coarse order ceiling. For nonsingular real split DIRK `m≤r`; if all retained poles are negative and the numerator is real-rooted, `T<0` for d≥1, strengthening the real-rooted ceiling to `p≤2d−1`. For d≥1, negative poles and `m≤r` also imply a nonreal right-half numerator pair when `p≥u+2d`, because the sum of the reciprocals of the distinct nonreal zeros must then be positive. The real-part sign of a reciprocal equals that of the original root. For arbitrary mixed DIRK the same T test applies, without presuming `m≤r`.

## 3. Strict common-diagonal SDIRK: exact near-cap cost and cap branches

Strict common diagonal means γ≠0 and every `A_ii=γ`. Then `Q=(1−γX)^r` after reduction and `0≤m≤r≤s`. For positive p one must have r≥1, since otherwise `m=0` and `R=1`. The distinct pole count is d=1. The following sign analysis also applies to any reduced one-pole scalar response, except clauses using `m≤r` are specific to strict nonsingular width (or another separately proved type bound).

### Positive common diagonal

Let `α=1_(a negative real numerator label exists)` and `β=1_(a real numerator label >γ exists)`. The sorted signs give `v=1+α+β`. Let `m_R` count the real zeros with multiplicity, and let `Δ_C` count nonreal excess degree (`total nonreal multiplicity − u`, always even). Then (3) becomes the exact charge

    δ := m+1−p ≥ Δ_C + m_R − α − β.                       (8)

Thus every real numerator zero in `0<ζ<γ` spends one unit, each extra real zero or extra multiplicity in either preferred bin spends one, and every nonreal repeated pair spends at least two. At `p=m` all nonreal roots are simple, and a repetition can only be one real double root in a preferred bin. If that double root occurs there can be no further extra root in either bin and no root in the forbidden middle bin. More generally (8) implies `m_R≤δ+2−Δ_C`; a completely real-rooted numerator therefore pays at most order 3, and already at most 2 unless both preferred bins occur.

At `p=m+1`, every numerator root is simple. There is at most one negative reciprocal zero and at most one above γ; there are none in `(0,γ)`. The exact signed configuration can be distinguished **without a root search**. Write `A_m=[X^m]P≠0`, `xγ=1/γ`. Dividing the cleared log derivative by `(1−γX)^(r−1)` gives a degree-`m+1` polynomial with vanishing through degree m; comparing its top coefficient gives

    (1−γX)P′ + (γX+rγ−1)P = γ A_m X^(m+1).                (9)

Hence `P(xγ)=A_m xγ^(m+1)/r` and for every real root x of P,

    sgn P′(x) = sgn[ A_m x^(m+1)/(1−γx) ].

The derivative signs of consecutive simple real roots alternate. The right-hand sign is constant on each of `(-∞,0)`, `(0,xγ)`, `(xγ,∞)`, so there is at most one root in each interval. The signs of `P(−∞),P(0),P(xγ),P(+∞)` (where the infinities mean eventual signs) are respectively `sgn(A_m)(−1)^m,+,sgn(A_m),sgn(A_m)`. They give the exact prescription, stated in reciprocal coordinates:

| m parity | sign of A_m | negative real reciprocal zeros | real reciprocal zeros >γ |
| --- | --- | --- | --- |
| even | positive | none | none |
| even | negative | one | one |
| odd | positive | one | none |
| odd | negative | none | one |

All remaining zeros are nonreal and simple. In the even negative-leading case, `p=u+3`; (7) with the `tC` refinement places the negative reciprocal root strictly below `−1/T`, and the positive reciprocal root strictly above this centroid.

**Which old Laguerre branch has which sign?** Let

    E_n(γ)=Σ_(0≤i≤min(r,n)) (−γ)^i binom(r,i)/(n−i)!.

The old scalar cap condition is `E_(m+1)=0` and `A_m=E_m`. The Laguerre reduction in the cited ordered tall budget shows `E_(m+1)` has `D=min(r,m+1)` positive simple gamma roots. Directly by coefficients, `γ E_n′=nE_n−E_(n−1)`. Thus at a cap root gamma, `A_m=−γ E_(m+1)′(γ)`. The leading coefficient of `E_(m+1)` has sign `(−1)^D`; at its j-th **increasing gamma root** the derivative has sign `(−1)^j`. Hence `sign A_m=(−1)^(j+1)`: the preceding exact configuration alternates with the old Laguerre branch. Ordering the reciprocal parameter `1/γ` instead would reverse that index.

### Negative common diagonal

The established ordered scalar budget already excludes the extra slot `p=m+1`. Put `α_−=1_(a real numerator label <γ)`, `β_−=1_(a real label in (γ,0))`. The exact variation is `v=α_−+2β_−`; positive numerator labels give no variation. Thus `(m_R+Δ_C)≤(m−p)+α_−+2β_−`. In particular `p=m` pays no repeated nonreal pair, permits at most one real double root by `m−eP≤1`, and all real roots are negative because `P_i=E_i(γ)>0` through m in this exact-degree branch. If there is no real root in `(γ,0)`, only a single simple real root left of γ can occur. Condition (7) is stronger in the entirely real-rooted strict branch: `T=m−r+2/γ<0` implies `p≤1`, not three. More generally for `p≥u+2` a right-half nonreal pair is forced even if all real zeros are negative. These are conditional zero-location constraints, not new nonlinear order assumptions.

## 4. Exactly what changes relative to the proved stage floors

* **Ordered strict common nonzero diagonal, without fixing gamma:** the older scalar bound is `p≤m+1≤r+1≤s+1`, with a positive common diagonal required for the extra slot. It is exact at the scalar level for arbitrary dimensions: take `m=r=s`, let gamma be any root of the established Laguerre cap polynomial, and set `P=Σ_(j≤s)E_j(γ)X^j`, `Q=(1−γX)^s`. No cancellation is possible (would reduce m and violate the old bound). For a triangular scalar realization choose `A=γI+L`, where L is the unit subdiagonal shift. The first s powers `A^j 1` form a basis, so b can prescribe the first s paid tall moments; the fixed denominator and numerator degree at most s determine exactly this fraction. This does **not** assert full RK order. Hence the new signed analysis cannot raise the unrestricted scalar lower bound `s≥p−1`; it classifies its gamma and numerator-root branches and strengthens particular measured cases. For negative gamma the old `s≥p` is likewise scalar sharp by prescribing the first s tall moments (or the truncated prefix with all E_j positive).
* **Rational common diagonal over any characteristic-zero field:** the existing proved scalar obstruction is `s≥p` for `p≥3`, even with algebraic/complex off-diagonal entries and weights, since the degree-s common-diagonal Laguerre scalar has no rational root once s≥2. The old one-stage order-two exception remains. Its `s=p` scalar ceiling is already witnessed by the same cyclic triangular construction with rational gamma. No unconditional rational stage-floor strengthening follows. The sign analysis is conditional over an ordered field (or a chosen real embedding of the response); it does not assume such an embedding in the published rational scalar theorem. In particular do not misread the published no-rational-root result as excluding all rational-gamma cap pairs with `m<r`.
* **Split-real general DIRK:** the previous scalar stage ceiling is `s+1` with a retained positive pole, `s` without one, plus the existing cancellation/degree charges. Width `s=p−1` is scalar-feasible, e.g. the ordinary `[p−1/1]` Padé response on a triangular realization with one positive diagonal and remaining zero diagonals; it also follows from the strict common scalar example above. Formula (5) and the real gap/positivity statements can exclude particular configurations, not all scalar methods at that width. The separate reviewed full-order nonsingular quadratic bound and the established nonlinear DIRK/SDIRK stage rows are unchanged.

This proof uses no inference from same-clock donor/receiver cancellation, no restricted time-order placement, and no claim of a new Lean verification.
