# One additional all-tree width reduction at shallow exceptional depth

Let p=4k with k≥5,
q=p/2=2k, D=p−2. Choose a positive γ which is the reciprocal
of a zero of L_(p−1)^(1) and satisfies γ≥3. Such a γ exists
without any search (take the largest reciprocal). The [exceptional one-degree adjacent construction](PAID-WIDTH-REDUCTION.md) of width sum U(p,q)−q,
where U=pq−q(q−1)/2, admits **one additional stage deletion** over
a finite real-algebraic coefficient extension. It has exact order
p, exact strict depth p−2, and unchanged q positive Gaussian
terminal clocks and weights. At p=20 this gives 144 instead of 145.
This is an upper construction at selected positive exceptional
diagonals, not a minimum, an arbitrary-positive or unrestricted
claim, or a fixed-small-field result.

## 1. Exceptional selection by a uniform reciprocal sum inequality

The published tall witness is

    λ_j(1)=ℓ((I_0−γ id)^j1)=(-γ)^j L_j^(1)(1/γ)/(j+1).

Here ℓ is uniform unit-interval integration, I_0 the zero-origin
primitive. Write n=p−1. The n zeros of L_n^(1) are simple and
positive by the ordinary Laguerre orthogonality argument: a polynomial
of degree n orthogonal to lower degrees for the strictly positive
weight x exp(−x) on (0,∞) must change sign n times there. Write the
factorization normalized by its value at zero as
`L_n^(1)(z)/(n+1)=∏ (1−γ_i z)`. The first two coefficients in the
standard Laguerre formula are −n/2 and n(n−1)/12. Hence

    Σ γ_i = n/2,     Σ γ_i² = n(n+2)/12,
    max_i γ_i ≥ (Σ γ_i²)/(Σ γ_i) = (n+2)/6 = (p+1)/6.

As p≥20, this exceeds 3. This argument selects an admissible exact
real-algebraic diagonal and performs no approximate root test.
At this γ the only omitted paid height is the p-vertex tall tree:
its value λ_(p−1)(1) is zero. Consecutive-index Laguerre recurrence
excludes a common zero and gives λ_(p−2)(1),λ_p(1) nonzero.
These are the existing sharp-depth and first-unpaid tall witnesses.

## 2. A uniform real-split theorem for the two-adjoint test family

Use the coordinate y=1−x. In this variable the adjoint of J=I_0−γ id
is T=V−γ id, with V integrating from 0 to y. For every γ≥3 and
every k_0≥1, the first k_0 polynomials `T²(y^j/j!)`, 0≤j<k_0,
form a strict Chebyshev system on (0,1): no nonzero element of their
span vanishes at k_0 distinct interior points.

To prove it, use the factorial coefficient bijection B sending
`y^j/j!` to `z^j`. It sends T to multiplication by z−γ. Therefore a
polynomial of degree ≤k_0+1 is in `T² R[y]_<k_0` exactly when its
factorial transform has value and derivative both zero at z=γ.
For hypothetical k_0 distinct zeros in (0,1), take their monic
root polynomial R(y) of degree k_0. Any nonzero member of the span
with those zeros would have to be R(y)(a+b y). It suffices to prove
that the jets at z=γ of B(R) and B(yR) are independent.

Keep R fixed when differentiating in z. Put f(z)=B(R)(z) and
`g(z)=B(yR)(z)=z f(z)+z² f'(z)`. For e_j the elementary symmetric
functions of R's positive roots, and t=1/z, write

    f(z)=k_0! z^k_0 S(t),
    S(t)=Σ_(j=0)^k_0 (-1)^j a_j t^j,
    a_j=(k_0−j)! e_j/k_0!.

Here a_0=1, `0≤a_j≤1/j!` and `a_(j+1)≤a_j/(j+1)`. The last
inequality follows by expanding `(j+1)e_(j+1)` as the sum over
j-subsets of their product times the sum of remaining roots,
which is ≤(k_0−j)e_j since every root is <1. For `0<t≤1/3` the
alternating terms therefore give `S≥1−t≥2/3`. The coefficient
bound gives `|S'|, |S''| ≤ Σ_(u≥0) t^u/u! ≤ 3/2`.

Now

    g/f=(k_0+1)z−S'(t)/S(t),
    (g/f)'=k_0+1+t² (S''S−(S')²)/S².

The magnitude of the last term is at most
`(1/9) ((9/4)+(9/4)²) = 13/16`. Thus (g/f)' > 0 for z≥3,
where f(z)>0. The two-jet determinant is `f g'−f'g=f²(g/f)'`,
nonzero at z=γ. This excludes any such R(a+b y) and proves the
Chebyshev assertion. It gives a constant threshold independent of
k_0; it is not a statement for all positive γ or higher powers T^m.

As a consequence, for any r≥1 the r moments against
`T²(y^j/j!)`, j=0,...,r−1, define an invertible pairing on
polynomials of degree <r, and their unique monic degree-r
orthogonal polynomial has r simple roots in (0,1). Here is the
sign argument, requiring no positivity formula for the jet matrix:
a nonzero polynomial with a<r interior sign changes pairs nontrivially
with a linear combination of the first a+1 tests, formed by bordering
the evaluations at the sign-change points with the row at y. The
ordered evaluation determinant is continuous and nonzero on its
connected chamber, so that combination alternates sign exactly at
those points. Their product has constant nonzero sign away from
finitely many zeros, giving a nonzero integral. This proves invertibility
on degree <r and forces r sign changes for the monic orthogonal solution.
Its coefficients lie in Q(γ) by the nonsingular rational-coefficient
moment system; its simple roots are real algebraic whenever γ is.
Reflect y to x and adjust the leading sign to get the corresponding
monic split hull in the original coordinate.

## 3. The exact one-layer replacement, retaining all paid trees

In the existing depth-D construction write d=D−h, s=p−d.
Take the single frontier layer

    s₀=3k−1,   d=k+1,   h=3k−3.

Since s₀≥q+1 and h is positive and nonterminal, the published
one-degree profile keeps this layer at the full q-node Gaussian hull.
Replace only this layer by r=q−1=2k−1 nodes. The published exact
ancestor test budget for this replacement is

    b=s₀−1−r=k−1,    m=d−b=2,    ν=b+min(d,b)=2k−2=r−1.

Thus the actual sufficient local condition to erase the hull error
is precisely orthogonality to the r tests `T² K[y]_<r`. The monic
split hull just constructed satisfies it. Note that b here is the
**local error budget** s−1−r, not the b₀=s−r used for rank probes.
This removes one stage from the existing q-wide mesh, despite the
fact that the loss from the full uncapped local polynomial cutoff
is larger than one. Everything else, including the terminal rule,
is unchanged.

Apply the published all-tree ancestor-first telescoping proof. At
this new layer the error quotient and all ancestor siblings together
cost at most b; its weighted moment is zero by the exact test span
T² K[y]_<r. At other layers use their already valid independent
one-degree, exact, or original paid terminal hull receipts. These
local receipts hold simultaneously, irrespective of which of the
sibling projections remain. With the same actual adjacent cardinal
rows and terminal-only weights, every paid literal tree of height
≤D is preserved. Taller paid trees are excluded only by the stated
Laguerre zero; the depth and exact-order witnesses from §1 are
unchanged after restoring γ to the diagonal. The count is
`U(p,q)−q−1`. In this one frontier layer the new width matches the
separate characteristic-zero Hilbert floor `floor((3p+1)/4)−d`
with q cap; this says nothing about attaining that floor everywhere.

At p=20 the replacement is h=12, d=6, s₀=14, r=9, b=4, m=2,
ν=8. This identification is a consequence of the displayed general
frontier, not any finite special-case scan or numeric test.

## 4. Field and remaining compression scope

The old construction may use the field K₀ generated by the same
γ and Gaussian terminal nodes. Its earlier one-degree meshes can
be chosen in Q(γ). The new hull polynomial also has coefficients
in Q(γ), but its nine roots at p=20 need not lie in K₀. The new
construction is in K₀ adjoined the split roots; it is a finite real
extension (in general the extension degree is at most r!). In
particular this does **not** assert the new count in the exact
72,960-degree field of the published 145-stage order-20 endpoint,
or any actual strict enlargement/minimum beyond this bound.

The useful next direction is to certify split hulls for the next
few powers of the shifted adjoint, keeping actual terminal moments
and depth fixed. In the factorial basis this is a higher jet
interpolation test, not terminal quadrature optimization. More
formally, a monic degree-r hull solving the local gate corresponds
to `J^m H` in the span of the monic shifted Legendre polynomials
of degrees ν+1,...,m+r, with leading coefficient r!/(m+r)!,
and factorial transform divisible by (z−γ)^m. This gives m exact
linear jet conditions plus a separate real splitting requirement.
The m=2 proof above resolves one uniform frontier; it makes no claim
about those higher powers. For the negative-diagonal matched minimum,
a different topology such as skipped edges or nonterminal output
must instead break the actual one-level factorization.
