# Distinct retained poles and finite tall-tree order

Let `K` be any characteristic-zero field. For a Runge–Kutta matrix `A`
and output weights `b`, put its scalar response in normalized reduced form

```text
1 + X bᵀ(I−XA)⁻¹1 = P(X)/Q(X),     P(0)=Q(0)=1.
```

Write `m=deg P`, `r=deg Q`, and let `d` count the distinct roots of `Q`
in an algebraic closure. Then

```text
p ≤ m+d
```

for every paid rooted-tree order `p`. This is a **tall-only** condition,
not an unrestricted stage bound. It saves `r−d` degrees relative to
the ordinary Padé degree sum. No order or splitting assumption on `K`
is needed.

## Finite recurrence over the base field

The order-`j` tall tree has weight `bᵀA^(j−1)1` for `j≥1`. By the
finite geometric identity, paid order `p` implies

```text
E_j := Σ_(i≤j) Q_i/(j−i)! = P_j,      0≤j≤p.
```

Take a gcd `G=gcd(Q,Q′)` in `K[X]` and put `V=Q/G`, `B=Q′/G`. Then
`VQ′=BQ`, `V₀≠0`, `deg V=d`, and `deg B<d` (for `Q=1`, use `V=1`,
`B=0`). To see the root count, if `Q=c f^a H` with `f` irreducible and
`f∤H`, then `Q′/f^(a−1)` reduces modulo `f` to `ca f′H≠0`.
Here characteristic zero makes `a` nonzero and `f′` nonzero of lower
degree. Thus the gcd removes exactly `a−1` copies, and the retained
irreducible contributes its degree to the distinct geometric count.
The computation does not require adjoining any root.

At a coefficient index `k≥0` use the ordinary polynomial
`U=Σ_(j≤k+1) X^j/j!` and set `F=QU`. Since
`U′−U=−X^(k+1)/(k+1)!`, the polynomial identity

```text
V F′ − (V+B)F = VQ(U′−U)
```

has zero coefficient at `k`. Every needed coefficient of `F` is at
index at most `k+1` and equals its finite convolution `E_j`. Hence

```text
Σ_(i=0)^min(d,k) V_i (k−i+1) E_(k−i+1)
  = Σ_(i=0)^min(d,k) (V_i+B_i) E_(k−i).                      (1)
```

There is no negative index. A prefix one term shorter would give the
nonzero residual `−V₀/k!` at the required coefficient.

If `E_(j+1),…,E_(j+d+1)=0`, read (1) at `k=j+d`. The derivative side
vanishes, and the only surviving term on the other side is
`(V_d+B_d)E_j=V_d E_j`. Thus `E_j=0`. A zero block of length `d+1`
therefore propagates back to `E₀=1`, a contradiction. Paid coefficients
past degree `m` are zero, proving `p≤m+d`. This argument applies even
to an unreduced normalized fraction; reduction makes the budget sharper.
The zeros must be consecutive: `Q=(1−X/2)^2` has `d=1` but
`n!E_n=(n−1)(n−4)/4`, with two separated zeros.

## Cancellation and the complementary ordered bound

Let `D=det(I−XA)`, `N=DR`. The adjugate gives `deg N≤s` for `s` physical
stages (with a constant response at width zero). Write `D=CQ`, `N=CP`, and define

```text
c=deg C,   ν=s−deg N,   z_D=s−deg D,
d_D=# distinct roots of D,   δ=d_D−d.
```

Here `δ` counts pole locations removed completely, not all canceled
copies. Since `m=s−c−ν` and `r=s−z_D−c`, the same inequality is

```text
p + c + ν + δ ≤ s+d_D,
p + 2c + z_D + ν + (r−d) ≤ 2s.
```

A cancellation costs one numerator slot, and removing the last copy of
a pole costs an additional distinct-location slot. For lower triangular
`A`, `z_D` counts its zero diagonals, while `d_D` counts its distinct
nonzero diagonals. A zero diagonal contributes no pole. None of these
counts concerns the output-weight signs or repeated stage clocks.
Pole-free ERK gives `p≤m`; a single repeated nonzero pole gives
`p≤m+1`, including for unordered characteristic-zero fields.

The [ordered pole refinement](../tall-ordered-pole-budget/README.md)
is complementary. With `u` nonreal retained poles **counted with
multiplicity** and `h₊` positive real retained poles in an ordered real
closure, the combined ceiling is `p≤m+min(d,u+1_(h₊>0))`. The ordered
bound is at least as strong when every retained pole is real; the
distinct-pole bound can be strictly stronger when nonreal poles repeat.
The earlier ordered sign budget and the positive algebraic branch
condition for a single pole are not consequences of (1).

## Sharpness with repeated poles

For an explicit rational family, fix `d,e≥1` and take `P=1`,

```text
W=Σ_(i≤d)(−X/e)^i/i!,      Q=W^e.
```

Finite multiplication of exponential prefixes gives `E₀=1` and
`E₁=…=E_d=0`. Indeed `W` agrees with the reciprocal-factorial prefix
of parameter `−1/e` through `d`, and the binomial formula adds the
parameters under multiplication. The first error is exactly
`−e(−1/e)^(d+1)/(d+1)!`. Hence the bound forces `W` to have `d`
distinct roots, each retained with multiplicity `e` in `Q`, and the
exact tall precision is `d`. For `d≥2`, the ordered split bound
precludes all its roots being real. If also `e≥d`, at least `2e>d`
nonreal root units are retained, so the distinct-pole bound is both
sharp and strictly stronger than the earlier multiplicity bound.

There is also exact algebraic existence at every numerator degree.
Fix `m≥0,d≥1` and any prescribed exponents `e_i>m`. In `d+1` variables
`Γ₁,…,Γ_d,t`, set the following `d` homogeneous polynomials to zero,
for `j=1,…,d`:

```text
[X^(m+j)] { ∏_i(1−Γ_i X)^e_i · Σ_(k≤m+d) t^k X^k/k! } = 0.     (2)
```

They have degrees `m+j`. Over an algebraic closure of the rationals,
there is a nonzero common solution: otherwise Nullstellensatz would
make the radical the origin ideal of height `d+1`, contrary to the
Krull height bound for `d` generators.

A nonzero solution cannot be at `t=0`. Indeed there the ordinary
polynomial `H=∏_i(1−Γ_i X)^e_i` has zero coefficients at
`m+1,…,m+d`. If a parameter is nonzero, `deg H>m` since its exponent
exceeds `m`. But with `1≤a≤d` actual distinct roots, the identity
`V H′=B H` has `deg V=a`, `deg B<a`, `V₀≠0`. Reading it at `k`
determines `H_(k+1)` from only its preceding `a` coefficients: the
leading coefficient is `(k+1)V₀`, and the right-hand side goes back
only to `H_(k−a+1)`. At `k=m+d`, these preceding indices are all
in the given block, which therefore propagates forward, forcing
`deg H≤m`, a contradiction. With all parameters zero and
`t=0` the point would be the origin.

Scale a nonzero solution to `t=1`. Set `Q=∏_i(1−γ_i X)^e_i` and
`P=Σ_(j≤m) E_j(Q)X^j`. Equations (2) pay through `m+d`. Since the
actual numerator degree and actual distinct count are at most `m`
and `d`, the bound already proved forces both equalities, and hence
all `γ_i` are nonzero and distinct. A common factor would lower
`deg P` without increasing the number of distinct poles. The common
factor is a unit modulo `X^(m+d+1)` because its constant term is nonzero;
canceling it preserves the same paid prefix. This contradicts the bound, so the pair is reduced. Its next
coefficient fails by the contiguous-zero obstruction. These families
attain `m+d` with arbitrarily large repeated excess. They establish
existence over an algebraic coefficient field, not over every field
or for untested smaller multiplicity profiles.

These scalar responses can be realized with actual square tableaux:
use a cyclic companion for `T^ρQ(1/T)`, where `ρ=max(m,r)`, and fit
the first `ρ` moments of `(P/Q−1)/X` by the output on its cyclic basis.
The later moments obey the same recurrence since
`Q(P/Q−1)/X=(P−Q)/X` has degree `<ρ`. A change of basis makes the
constant-one vector the input. Nonsplit examples do not thereby
become lower triangular, and none establishes full nonlinear order.

Run `python -B check_exact.py` from this directory. The [recorded output](expected-audit.txt)
contains independent exact rational gcd and prefix checks, the
explicit repeated-pole families, and both cancellation identities.
The proofs above are uniform, not enumerations of those checks.
