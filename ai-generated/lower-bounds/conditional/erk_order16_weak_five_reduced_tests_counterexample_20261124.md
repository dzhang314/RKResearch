# Exact negative control for reduced ERK16 weak-five scalar tests

This example satisfies **all six assigned local primitive identities**,
the mixed moment, and the finite sign-count necessities. Both assigned
extra clocks lie inside the numerical end overlap, yet neither is a
common primitive zero. It is **not** a tableau or a counterexample to the
native order-16 claim: it fails the full global mask equation already at
the constant test R=1.

Use the ordered field ℚ(a) inside ℝ. Set u=2/3, z=1/3, s=x(1−x), and

    q(x) = 2835 s² − 1020 s + 82,
    H(x) = 270 x³ − 480 x² + 258 x − 41.

Let a be the unique root of H in (9/16,37/64), and h=1−a in (27/64,7/16).
Indeed H(9/16)=623/2048>0 and H(37/64)=−13429/131072<0.  The derivative
is negative on both brackets: H''(x)=1620x−960<0 there, while
H'(9/16)=−3291/128 and H'(27/64)=−5811/2048.  In the h bracket
H(h)>H(7/16)=5345/2048>0. The permitted chronological labels are
(0,u,a,h,z), not their numerical sorting. They are distinct and all four
nonzero clocks are in (0,1); a,h are both in (z,u).

## Six identities and lack of common zeros

Define the same true anchored polynomials as in the weak-five statement:

    F(t)=∫₀ᵗ x(x−u) q(x) dx,     G(t)=∫ₜ¹ (1−x)(z−x) q(x) dx.

The polynomial identity F(t)=(3/2)t²(t−u)² H(t) follows by differentiation
and the zero constant term. The symmetry q(1−x)=q(x) gives G(t)=F(1−t).
Using q=82−1020x+3855x²−5670x³+2835x⁴, the first two integrals below
evaluate to zero by termwise integration, and reflection gives the next
two. The last two are the assigned interior zero each:

    ∫₀ᵘ x q(x) dx                 = 0
    ∫₀ᵘ x² q(x) dx                = 0
    ∫_z^1 (1−x) q(x) dx           = 0
    ∫_z^1 (1−x)² q(x) dx          = 0
    ∫₀ᵃ x(x−u) q(x) dx           = F(a) = 0
    ∫_h^1 (1−x)(z−x) q(x) dx      = G(h) = 0

But F(h)=G(a)>0 from H(h)>0, so neither a nor h is common. Both
assigned zeros are simple: F'(a)=(3/2)a²(a−u)²H'(a)<0, so q(a)>0 from
F'(a)=a(a−u)q(a); q(h)=q(a)>0. Also q(0)=82 and q(u)=q(z)=−14/3.

With Z₂=(X−a)(X−h), Z₂'=2X−1 and F(x)G(x) is invariant under
x↦1−x. Therefore ∫₀¹ Z₂' F G=0 exactly, because its integrand reverses
sign. The parity argument also gives the three odd-centered global
tests R=(x−1/2)^j for j=1,3,5, but not the even ones.

## Actual finite samples

Put N₄=(X−u)(X−z)Z₂. The following nine nodes are all present in the
[19-node positive rational rule](positive_rational_rule_degree19_20261124.json).
The non-rational factors' signs follow just from the two brackets;
the q signs are rational evaluations. Positive x(1−x) does not change
these signs.

    node numerator over 128     1   26  44  54  64  74  84  94  110
    sign q                     +    −   −   +   +   +   −   −    +
    sign N₄                    +    +   −   −   +   −   −   +    +
    sign q N₄                  +    −   +   −   +   −   +   −    +

Thus qN₄ reaches the degree-eight ceiling of eight sampled sign
alternations, exceeding the six necessary for the global tests. The
sign counts alone do not stand in for those moment equalities.

## Precisely omitted global equation

The original native mask also entails

    I(R) = ∫₀¹ x(1−x) q(x) N₄(x) R(x) dx = 0   for all deg R≤5.

This feature is **not** retained in the reduced mixed-moment/sign
test. For this example ν=u(1−u)=2/9, η=a(1−a)>0, and
N₄=(ν−s)(η−s). Using ∫₀¹ s^k=(k!)²/(2k+1)!, the three signed moments
∫ s q, ∫ s² q, ∫ s³ q are −1/12, −11/210, −7/660. Consequently,

    I(1) = (32/945) η + 43/41580 > 0.

This isolates the lost information: an overlap, maximal sign
variation, and the mixed identity can coexist with the assigned ports
without a common zero. At least one additional genuine global equality
or a new paid condition is needed; the example makes no assertion
about whether the full six global equations do force a stronger cut.

The [companion verifier](erk_order16_weak_five_reduced_tests_counterexample_20261124.py) uses only Python standard-library
rational arithmetic to check the displayed coefficients, brackets,
witness signs, and I(1). With the audited certificate path it checks
that those sample nodes are present by file hash and metadata only.
It does not regenerate or replay the positive quadrature weights.
