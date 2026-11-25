# Symmetric multiplicity budget for the genuine tall response

**Status:** source-only mathematical proof and an exact rational/finite-field audit. This result is not advertised as a Lean theorem; no Lean was run. The existing native denominator-only result and geometric interpretation cited below are independently reviewed, not a certificate of this new joint bound. The argument is about the actual scalar response of every reviewed-order tableau, not a new unrestricted stage minimum.

## Theorem

Let K be any field, let A be any finite s-stage Runge–Kutta matrix and b its weights (no triangularity or ordering required here), and let p be a nonnegative achieved literal rooted-tree order. Write its normalized scalar response as

    R(X) = 1 + X bᵀ(I−XA)⁻¹1 = P(X)/Q(X),     P(0)=Q(0)=1.

Equivalently use the reviewed finite `Fraction` cross-product relation and its denominator normalization; the derived `Fraction.num_zero` gives numerator normalization. Define `e(F)=deg F−deg gcd(F,F′)`. Then

    p ≤ e(P)+e(Q).                                            (1)

Coprimeness of P,Q is unnecessary for this inequality; use the reduced pair for the sharp invariant of R and to interpret its zeros and poles without overlap. In characteristic zero, e(F) counts the *distinct* geometric roots of F. Thus p is at most the number of distinct zeros plus the number of distinct poles, **counting neither multiplicity**. In characteristic q>0, e(F) counts exactly those distinct geometric roots whose multiplicity is nonzero modulo q; roots whose multiplicity is divisible by q are *not* charged. Since p! is a unit, q>p whenever p≥1. Even then, an actual physical numerator/denominator can have degree or multiplicity ≥q; order does not bound the number of physical stages from above.

### Direct proof

`HasOrder p A b` in the reviewed definition states a factorial times each tree output is one for every tree of order ≤p. The bushy conditions imply `1,…,p` are units (also for positive characteristic), hence `p!` is a unit. No reciprocal of `(p+1)!` is needed. Let

    U = Σ_(j=0)^p X^j/j!,   Z=P−QU,   W=QP′−PQ′−PQ.

The reviewed `paid_fraction_coeff` gives `X^(p+1) | Z`. Therefore `X^p | Z′` by the polynomial derivative rule and `X^p | Z`. Since `U′−U=−X^p/p!`, the exact product-rule identity

    W = Q²(U′−U) + Q Z′ − (Q′+Q)Z

implies `X^p | W`. This includes `p=0`. The two differentiated terms of W are zero or of strictly smaller degree than `PQ`, so `−PQ` is its unique leading term: `W≠0`, `deg W=deg P+deg Q`. This does not require derivatives to be nonzero.

Let `G_P=gcd(P,P′)` and `G_Q=gcd(Q,Q′)`. Their **product** divides W: each term has a separate factor from P or P′ and from Q or Q′. One must not infer product divisibility merely from separate divisor claims; it is this termwise factorization that justifies adding both savings. Since `P(0)=Q(0)=1` the product has nonzero constant coefficient, so is coprime to `X^p`. Hence `X^p G_P G_Q | W`, giving `p+deg G_P+deg G_Q≤deg P+deg Q`. This is (1). Equivalently, `W/(G_P G_Q)` is a nonzero polynomial of exact degree `e(P)+e(Q)` vanishing to order at least p at the origin. In characteristic zero the order of this residual at the origin is the paid precision when the first unpaid coefficient of R is nonzero; the lower-divisibility argument alone is used here, and no converse requiring a nonzero `(p+1)` is asserted in positive characteristic.

For the geometric counts, pass to an algebraic closure (gcd degrees agree on scalar extension). At a root α of a nonzero polynomial of multiplicity h, the derivative has valuation h−1 if the coefficient h is nonzero in K, and at least h otherwise. Thus the gcd removes h−1 or h copies respectively. This works over nonperfect fields after passing to the algebraic closure and includes `F′=0`. For characteristic zero the reviewed `TallDerivativeGcdAlgebraicClosure` already proves the needed one-polynomial equality; apply it to both P and Q.

### Strength and sharpness

Previous individual counts for the response and its reflected reciprocal only yield `min(m+e(Q), r+e(P))` with `m=deg P`, `r=deg Q`. Formula (1) subtracts **both** multiplicity losses: `p+(m−e(P))+(r−e(Q))≤m+r`. This is strictly stronger if both polynomials have repetitions. Do not count an arbitrary imaginary pole twice beyond counting its distinct conjugate pair when working in a real ordered field.

The bound is sharp even in the presence of simultaneous repeated zeros and poles. Fix positive integers a,b,k, put `p=a+b`, and take the ordinary rational `[a/b]` Padé pair of exp, normalized by

    Q_j=(−1)^j binom(b,j)(p−j)!/p!,  P_j=binom(a,j)(p−j)!/p!.

The identity for its paid coefficients is `[t^(p−n)] (1+t)^p(1−1/(1+t))^b = binom(a,n)`, valid for 0≤n≤p; with the common factor `(p−n)!/p!` this gives exactly `P_n`. The pair must be coprime by the weaker bound p≤deg P+deg Q after reduction. Formula (1) forces both polynomials squarefree at this degree equality. The powered response `R(X/k)^k` has precision p (at least p by multiplication/substitution of the paid prefix; (1) excludes p+1), and its degrees are ka,kb but its distinct-root credits are still exactly a,b. This is a scalar family over the rationals; arbitrary nonlinear order of these Padé powers is not claimed.

A concrete **actual** family is k consecutive implicit midpoint steps on substeps of size 1/k. Its lower triangular tableau has `A_ii=1/(2k)`, `A_ij=1/k` for j<i, `b_i=1/k`. Its clocks `(i−1/2)/k` (i=1,…,k) and weights satisfy `bᵀ1=1`, `bᵀc=1/2`, all rooted-tree conditions at order two. The scalar transfer is `(1+X/(2k))^k/(1−X/(2k))^k`. The distinct-root bound is exactly 2; neither individual unilateral count improves on k+1. A positive-characteristic actual example with a root invisible to e(F) is the F₇ order-two core described in the [companion physical-count proof](../volterra-tall-multiplicity/PROOF.md): `A=I+unit subdiagonal`, `b=(5,3,3,5,1,6,6)`, `R=(1+X+4X²)/(1−X⁷)`. Here e(P)=2,e(Q)=0, while the denominator has one geometric root. This is a check of hypotheses, not evidence that all field pairs of the specified type attain a high RK order.

### Splice with actual lower triangular physical zero rows

When A is lower triangular, its unnormalized characteristic denominator factors over K. Let `z=#(A_ii=0)`, `c₀` the degree canceled in reducing `N/H`, `ν=s−deg N`, `η=(m−e(P))+(r−e(Q))`. Thus `r+z+c₀=s`, `m=s−c₀−ν`. If (M_l=\lfloor l(p+1)/2\rfloor-\lfloor l^2/2\rfloor), `1≤l≤ceil(p/2)` as in the independently checked physical Volterra census, its `l s ≥ M_l+(l−1)(r+c₀)` together with (1) now gives

    (2l−1)s ≥ M_l + (l−1)(p+2c₀+ν+η).                        (2)

The added numerator loss is genuine, not a conditional clock/weight assumption. After forgetting all multiplicity/cancellation information the integer projection is unchanged: the unpowered degree-optimal Padé pairs are squarefree on both sides. In particular there is no change to existing uncontrolled DIRK, ERK, or SDIRK stage tables for p≤20.

### A separate ordered consequence (no dependency for (1) or for its native gate)

Over an ordered field, take the real closure and its algebraic closure. Factor the reduced R as `∏_(λ) (1−λX)^(−w_λ)` over nonzero distinct reciprocal geometric labels. A pole has positive signed multiplicity `w_λ`, a zero negative. Since `R′/R=1+O(X^p)` by the same residual, reading the finite geometric expansion gives

    Σ_λ w_λ λ f(λ)=f(0)     for every polynomial f of degree ≤p−1.

The `(w_λ λ)` here are signed atoms *not* physical RK output weights. Let `u` be the number of nonreal distinct labels, and sort the real labels together with 0; give a real nonzero label the sign of `w_λ λ`, and the label 0 the negative sign. If v is the number of adjacent sign changes in this sequence, then `p≤u+v`. Otherwise multiply the real monic quadratic for every nonreal conjugate pair (strictly positive on the real line) by one affine factor with root strictly between each adjacent pair of opposite signs, and choose its global sign so every atom after multiplication has positive value. This polynomial has degree `u+v≤p−1`; the signed measure including the origin atom then sums to a strictly positive number although it must annihilate the polynomial. Even if there are no real labels, the origin term remains. This is distinct from the earlier ordered variations of the *coefficients* of a numerator. No ordered refinement is needed to prove (1) or intended as a prerequisite to formalize it.

## Exact evidence

`check.py` is self-contained exact arithmetic. It tests 18,819 normalized polynomial pairs over F₂,F₃,F₅,F₇, including noncoprime and zero-derivative pairs; 3,743 have positive paid precision. It separately verifies the multiplicative gcd quotient, its exact degree, its paid zeros, 75 sharp Padé-power cases (50 strictly improve both old counts), nine actual midpoint tableaux's two order equations, and finite-characteristic Frobenius examples. These are bounded exact checks; the symbolic proof establishes the unrestricted claim.
