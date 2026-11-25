# Finite tall-tree order and retained poles

These are constraints on the **scalar tall-tree response** of a
Runge–Kutta tableau. They are not new unrestricted stage bounds. The
examples show sharpness for tall trees alone, not full rooted-tree order
or stability.

For an `s`-stage matrix `A` and weights `b`, let

```text
R(X) = 1 + X bᵀ(I−XA)⁻¹1 = P(X)/Q(X),     P(0)=Q(0)=1,
```

where the last pair is reduced. Write `m=deg P`, `r=deg Q`. The tall
tree of order `n≥1` has weight `bᵀA^(n−1)1`. Thus literal rooted-tree
order `p` makes `R` match the reciprocal-factorial coefficients
through degree `p`, by the finite geometric identity modulo `X^(p+1)`.
Equivalently,

```text
E_n(Q) := Σ_(i≤n) Q_i/(n−i)! = P_n,       0≤n≤p.             (1)
```

## 1. Partial real poles over any ordered field

In an ordered real closure, count the negative real, positive real,
and nonreal roots of `Q` with multiplicity as `h₋`, `h₊`, and `u`.
These are the retained poles: Bézout preserves coprimality on field
extension. There is no zero root, and `u` is even.
Every consecutive block of zeros in `E_n(Q)` has length at most
`u+1_(h₊>0)`. Hence

```text
p ≤ m + u + 1_(h₊>0).                                     (2)
```

There is also a separate additive bound on any finite prefix of the
sequence: the number of zeros, plus the number of **adjacent nonzero**
pairs of opposite signs, is at most `u+h₊`. A sign change across a zero
is not counted again.

**Proof.** Put `F_j=(1+∂)^j Q` for the formal derivative `∂`. The finite
binomial formula gives `F_j(0)=j!E_j(Q)`. Starting at any index `n`,
the values `F_(n+i)(0)` are unit-triangular combinations of
`F_n(0),F_n′(0),…,F_n^(i)(0)`. Thus `L` successive zeros starting at
`n` are equivalent to a root at zero of multiplicity at least `L` in
`F_n`.

For the local step `F → F+F′`, write
`F=a B∏_(i=1)^d(X−x_i)^{m_i}` in the real closure, with `x₁<⋯<x_d`
and `B` a product of monic irreducible quadratics, positive everywhere.
After division by `∏(X−x_i)^{m_i−1}`, the residual value at `x_i` is
`a B(x_i)m_i∏_(j≠i)(x_i−x_j)`, of sign `sgn(a)(−1)^(d−i)`.
The residual leading coefficient is `a`, and its degree is
`d+deg B`. If `d>0`, its sign sufficiently far to the left is therefore
opposite to the sign at `x₁`. A left point is obtained by coefficient
dominance: take its negative magnitude larger than
`1+|x₁|+Σ|H_k/a|`, summed over the lower coefficients of the residual
`H`. No unbounded natural sequence is needed. A sign change in a
real closed field supplies a root: a product of real linear factors
and sign-definite quadratics cannot change sign in a root-free
interval. Thus select one new root in each strict gap before each
`x_i`. Every old real multiplicity loses exactly one, by the nonzero
residual values. The total real root count cannot decrease.

In particular, the negative root count never decreases: all gaps
preceding negative roots are negative. If `F(0)=0`, the gap preceding
zero gives one additional negative root. If consecutive nonzero
values at zero have opposite signs, the negative root count changes
parity, since the leading coefficient stays fixed and nonreal counts
are even. It must increase by at least one. A zero is charged on its
outgoing step, disjoint from any adjacent nonzero flip. Summing over
the steps, including one after the last index, proves the additive
bound by the initial allowance `r−h₋=u+h₊`. That last step requires
no paid order condition.

A newly acquired zero root can occupy at most one of the selected
real-gap units. There are at least `h₋+h₊−1` guaranteed real root
units elsewhere, so the new zero multiplicity is at most `u+1`.
An inherited zero root loses exactly one unit, and initially
`Q(0)=1`. Also at least the initial `h₋` negative roots persist in
count, bounding zero multiplicity by `u+h₊`. Taking the minimum proves
(2) using the trailing paid zeros from (1). The argument works over
non-Archimedean ordered fields. It does not say that all allowances
are eventually spent: for positive infinitesimal `t` in `ℚ((t))`,
`Q=1−tX` has a positive pole but `E_n=(1−nt)/n!>0` at every natural
index.

### Physical bookkeeping and comparison

Let `D=det(I−XA)`, `N=DR`, `D=CQ`, `N=CP` with `C(0)=1`.
The adjugate gives `deg N≤s` (the zero-stage case is constant).
Let `ν=s−deg N`, and let `κ_real` and `κ_nr` be the real and
nonreal root counts of `C`. If `u_D` counts nonreal roots of `D`,
then `m=s−ν−κ_real−κ_nr` and `u=u_D−κ_nr`. Consequently

```text
p + ν + κ_real + 2κ_nr ≤ s + u_D + 1_(h₊(Q)>0).            (3)
```

In the additive sign budget, write `κ₊` for positive roots of `C`,
`t=min(p,m)`, and `B_t` for zeros plus adjacent nonzero flips in
`P₀,…,P_t`. The paid tail is all zero, so

```text
κ₊ + κ_nr + B_t + max(p−m,0) ≤ h₊(D) + u_D.                (4)
```

A nonreal cancellation consumes two degree slots in (3); a real
cancellation consumes one. The bonus depends on what is **retained**.
These counts are pole multiplicities, not zeros of weights or clock
fibre counts.

For comparison, over arbitrary characteristic zero the ordinary
finite Padé bound is `p≤m+r`: the degree-`≤r` polynomial
`Σ_i Q_i∏_(j<i)(T−j)` takes the value `n!E_n(Q)` at every natural
`n` and equals `1` at `0`, so it cannot vanish at `r+1` distinct
indices. The ordered bound (2) saves `h₋+max(h₊−1,0)` degrees from
that bound. It ties it with no real retained poles, or with just one
positive and no negative retained pole. Internal zeros and flips can
make (4) stricter still.

For ERK, `D=Q=1` and both arguments give `p≤m≤s`. For ordered
diagonal DIRK, `u_D=0`: one gets `p+deg C+ν≤s+1_(h₊(Q)>0)` and
no extra slot if all retained diagonal values are nonpositive. A
physical zero diagonal contributes the factor `1`, not a canceled
pole: for lower triangular `A`, writing `z` for the zero diagonal
count gives `m=r+z−ν`. These ordered conclusions depend on the pole
coefficients alone; ordered diagonal scalars in an embedded ordered
subfield also suffice when the rest of the tableau is not in it.

## 2. A single retained pole over arbitrary characteristic zero

Suppose `Q=(1−γX)^r`, `γ≠0`, `r≥1`, **without an order assumption on
the coefficient field**. Then `p≤m+1`. Using the extra slot forces the
parameter `γ` to be algebraic with all rational conjugates positive
real. Thus there is no extra slot with genuinely complex or
transcendental `γ`. A pole-free response still has `p≤m`.

To see this, for integers `d,α≥0` define

```text
L_d^(α)(x) = Σ_(j=0)^d (−1)^j binom(d+α,d−j) x^j/j!.
```

Reversing the finite sum for `E_n`, for `n≥1`, gives

```text
n≤r: E_n = (−γ)^n L_n^(r−n)(1/γ),
n≥r: E_n = (−γ)^r (r!/n!) L_r^(n−r)(1/γ).
```

For completeness, all roots of `L_d^(α)` are simple positive real
algebraic numbers. The functional `I_α(x^j)=(α+j)!` is real integration
against `x^αe^(−x)` on `(0,∞)`, by integration by parts. For `k<d`,

```text
I_α(x^k L_d^(α))
   = ((d+α)!/d!) Σ_j (−1)^j binom(d,j) ∏_(l=1)^k(α+j+l) = 0,
```

by finite differences of a degree-`k` polynomial. If fewer than `d`
distinct positive roots change sign, multiply by their linear factors.
The resulting polynomial has a constant nonzero sign off finitely
many points of `(0,∞)`, contradicting orthogonality. The integration
is only a proof of this rational polynomial root fact, not an
operation in the original coefficient field.

Now if `p>m`, then `E_(m+1)=0`, and the finite equation above places
`1/γ` at a root of a polynomial all of whose roots are positive real.
The field `ℚ(γ)` embeds in the real algebraic numbers with positive
`γ`; all `E_j(Q)` lie in that field. Two successive zero tests would
transfer across this embedding and contradict (2) for a split
polynomial. This proves the claim in the original field. For strict
SDIRK, `m≤r`. At `m=r≥2`, the separate [rational scalar obstruction](../strict-sdirk-rational-common-diagonal/PROOF.md)
excludes the extra slot for rational `γ`, since its scalar sum is
exactly `E_(r+1)`. Hence rational common-diagonal strict SDIRK at
`p≥3` needs `r≥p`; `r≤1` already gives `p≤2`. This does not exclude
every extra-slot case at `m<r`. The one-pole theorem also applies
to mixed explicit rows when all nonzero retained diagonals are equal.

## Exact families and replay

The bounds are sharp at the scalar level. For arbitrary `m,h≥0`,
`k≥1`, put `n=m+1`, `r=h+k`, and

```text
W_M=X^k∏_(j=1)^h(X+jM),     U_M=(1+∂)^(−n)W_M,     Q=U_M/U_M(0).
```

The inverse is the finite sum
`Σ_(j≤r)(−1)^j binom(n+j−1,j)∂^j`, since the derivative is nilpotent
on this degree range. For sufficiently large rational `M`,
`U_M(0)` and `((1+∂)⁻¹W_M)(0)` are nonzero: as polynomials in `M`
they have respective top coefficients
`h!(−1)^k binom(n+k−1,k)k!` and `h!(−1)^k k!` at `M^h`.
The scaled correction `M^(−r)U_M(MY)−W_1(Y)` is exactly
`Σ_(j≥1)(−1)^j binom(n+j−1,j) W_1^(j)(Y)/M^j`. At each rational
endpoint `−j±1/4` of a negative-root gap, take
`M` greater than twice the sum of the absolute correction numerators
divided by `|W_1|` at that endpoint. Also take `M≥1` and larger
than `1+Σ|g_i/g_h|` for the lower coefficients of each of the two
degree-`h` polynomials in `M`. This preserves the `h` strict negative sign
gaps. Since `(1+∂)^nQ=W_M/U_M(0)`, it has zero multiplicity exactly
`k` at zero. The bound (2) therefore forces the remaining `k` poles to
be nonreal when `k` is even, or `k−1` nonreal and one positive when
`k` is odd. Take `P=Σ_(i≤m) E_i X^i`. Then `deg P=m`, exact tall order
is `m+k`, and there can be no common factor: reduction would lower
`m` without increasing the allowance in (2). The `k` tail zeros
also exhaust the additive budget. Negative-only split examples
saturate the zero-slot bound by truncation, since all `E_i>0`.
For any `m≥0,r≥1`, choosing a positive algebraic root of the Laguerre
polynomial at `n=m+1` gives a single-pole example of exact tall order
`m+1`; neither neighbor of the zero coefficient is zero, and the pair
is reduced by the same argument.

These scalar pairs have finite square realizations of width
`ρ=max(m,r)` (width zero is the constant response `1`). Otherwise
use a companion matrix with characteristic polynomial
`T^ρ Q(1/T)` and first cyclic vector `e₀`. Fit the first `ρ` coefficients
of `(R−1)/X` by choosing the output on the cyclic basis. Its subsequent
moments obey the same characteristic recurrence, since
`Q(R−1)/X=(P−Q)/X` has degree `<ρ`. For split poles, use instead a lower
bidiagonal matrix with reciprocal pole roots on its diagonal, `ρ−r`
zeros, and unit subdiagonal. The change of basis with first column `1`
and other columns the usual basis vectors makes `1` the input and
preserves lower triangularity. When `m≤r` in the one-pole case all
diagonals equal `γ`. This realizes only the tall responses.

Run `python -B check_exact.py` here. The [recorded output](expected-audit.txt)
replays exact rational coefficient identities and Sturm counts: 80
inverse-transform families, 78 derivative iterations, and 81
single-pole coefficient and orthogonality checks. The general claims
are proved above; the finite checks are not an enumeration proof.
