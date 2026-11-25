# Rational common-diagonal tall-tree obstruction

**Stage consequence.** Let `K` be any field of characteristic zero. Let `A`
be an `s × s` lower triangular Runge–Kutta matrix over `K`, with output vector
`b` over `K`. Suppose that all the entries on the diagonal of `A` are the
image of a single `γ ∈ ℚ`. If the tableau has order at least `p` and `p ≥ 3`,
then **`s ≥ p`**. The off-diagonal entries and `b` need not be rational. This
includes nonzero rational strict SDIRK diagonals, as well as `γ = 0`. No
positivity, nonzero-weight, abscissa, or stability assumptions are used.

## Reusable shifted-moment theorem

Let `V` be a vector space over `K`, `T : V → V` linear, `e ∈ V`, and `λ` a
linear functional on `V`. Fix `s ≥ 2`. Suppose

$$
\lambda(T^j e)=\frac{1}{(j+1)!}\quad(0\le j\le s).
$$

Then `λ((T − γ I)^s e) ≠ 0` for every rational `γ` (embedded in `K`). In
particular `(T − γ I)^s e = 0` is impossible. Only these `s+1` scalar moments
are used; no nilpotency, matrix size, or other rooted-tree condition is an
assumption of this abstract version.

### 1. Scalar reduction and normalization

The binomial formula applies because `T` commutes with scalar operators. Write

$$
S_s(g)=\sum_{j=0}^s {s\choose j}\frac{(-g)^{s-j}}{(j+1)!}.
$$

Then `λ((T − γ I)^s e)` is the image of `S_s(γ) ∈ ℚ`. The embedding is
injective, so it suffices to exclude a rational zero of `S_s`. At zero its
value is `1/(s+1)!`, which is nonzero. For `g ≠ 0`, use the ordinary
coefficient convention for generalized Laguerre polynomials:

$$
L_s^{(1)}(x)=\sum_{j=0}^s {s+1\choose s-j}\frac{(-x)^j}{j!},\qquad
S_s(g)=\frac{(-g)^s}{s+1}L_s^{(1)}(1/g).
$$

Indeed `binom(s+1,s−j)/j! = (s+1) binom(s,j)/(j+1)!` for every `j`.
Equivalently, put

$$
F_s(x)=(-1)^s s! L_s^{(1)}(x)
      =\sum_{j=0}^s c_j x^j,\qquad
c_j=(-1)^{s-j}{s\choose j}\frac{(s+1)!}{(j+1)!}.
$$

This is a monic integral polynomial with constant term
`(-1)^s (s+1)!`, and `(s+1)! S_s(g) = g^s F_s(1/g)` for `g ≠ 0`.

### 2. Elementary no-rational-root proof, all degrees `s ≥ 2`

A rational root `r` of the monic integer polynomial `F_s` is integral: write
`r = u/v` in lowest terms with `v > 0`, multiply by `v^s`, and reduce modulo
`v` to get `v | u^s`, hence `v = 1`. The constant term rules out `r = 0`.

Every coefficient except the leading one is divisible by `s(s+1)`: for
`j ≤ s−2` both factors occur in `(s+1)!/(j+1)!`; for `j = s−1` the
coefficient is exactly `−s(s+1)`. One of the consecutive positive integers
`s,s+1` is odd and at least 3. Take any prime `ℓ` dividing that odd integer.
The congruence `F_s(r) ≡ r^s (mod ℓ)` forces `ℓ | r`.

Write `v_ℓ` for the prime exponent on nonzero integers. For `n ≥ 1`,

$$
(\ell-1)\,v_\ell(n!)\le n-1.
$$

For completeness, let `m = ⌊n/ℓ⌋`; counting the multiples of `ℓ` in `n!`
with their extra prime powers gives `v_ℓ(n!) = m + v_ℓ(m!)`. For `m = 0`
the desired bound is immediate. Otherwise the induction bound at `m`
gives `(ℓ−1)(m + v_ℓ(m!)) ≤ ℓm−1 ≤ n−1`. Thus for `j ≥ 1` and `ℓ ≥ 3`,
`v_ℓ((j+1)!) ≤ j/(ℓ−1) < j`.

Put `V₀ = v_ℓ((s+1)!)`. Since `v_ℓ(r) ≥ 1`, for every `1 ≤ j ≤ s`,

$$
v_\ell(c_j r^j)=V_0-v_\ell((j+1)!)+v_\ell\!\binom{s}{j}+j\,v_\ell(r)
\;\ge V_0+1.
$$

All the nonconstant terms are therefore divisible by `ℓ^(V₀+1)`, but
`c₀` has valuation exactly `V₀`. They cannot sum to zero. This proves the
all-degree scalar obstruction without using an irreducibility theorem.
It asserts no rational roots, not a new claim of polynomial irreducibility
or literature priority.

## Application to the reviewed rooted-tree order predicate

The reviewed `RKResearch.HasOrder p A b` requires
`(t.factorial : K) * (b ⬝ᵥ Φ t A) = 1` for every tree of order at most `p`.
For `t = tallTree (j+1)`, the reviewed `FiniteRootedTree.order_tallTree`,
`FiniteRootedTree.factorial_tallTree` and `RKResearch.Φ_tallTree` give,
respectively, `j+1`, `(j+1)!`, and `A^j *ᵥ 1`. In characteristic zero the
factorial is invertible, giving exactly the moment in the abstract theorem
with `T(v)=A v`, `e=1` and `λ(v)=b·v`. The core source versions are pinned in
`reviewed-inputs.sha256`; no replacement definition of order is used.

For `s ≥ 2`, `N = A − γ I` is strictly lower triangular. Each term of an
entry of `N^s` would require a strictly decreasing chain of `s+1` stage
indices among `s` indices, so `N^s = 0`. If `p ≥ s+1`, all the displayed
moments are paid, and the shifted-moment theorem contradicts this zero.

For `s = 0`, there is no weight and the one-vertex order condition fails.
For `s = 1` and `p ≥ 3`, the three moments are `b = 1`, `bγ = 1/2`, and
`bγ² = 1/6`. The first two imply `bγ² = 1/4`, a contradiction. The
restriction `p ≥ 3` cannot be discarded: at `s = 1`, `A = (1/2)` and
`b = (1)` give order two (there is just one rooted-tree shape at each of
orders one and two). Equivalently `F₁(x) = x−2`.

This is a necessary bound for common rational diagonals, not for general
DIRK matrices with distinct diagonals or for arbitrary algebraic common
diagonals. It proves neither full-order existence at `s=p` nor a bound in
positive characteristic. The proof does not use trimming or padding.

**Tall-only sharpness.** In every width `s ≥ 1`, for any chosen rational
`γ`, the down-shift matrix `N` with ones just below the diagonal has
`N^j 1` equal to the vector with the first `j` entries zero and the rest
one, for `j=0,…,s−1`. These form a rational basis. For `A=γ I+N`, the
vectors `A^j 1` form a basis too, by a triangular change with coefficient
one on its diagonal. Thus a unique rational `b` prescribes the tall
moments through order `s`. This says nothing about non-tall trees; it
identifies the exact ceiling of this particular moment budget at `s ≥ 2`.

## Independent finite arithmetic replay

`check_tall_laguerre.py` supplies a separate certificate for all critical
widths `2 ≤ s ≤ 19` (threshold orders `3` through `20`). It independently
forms the integer coefficient family from both expansions. Because `F_s`
is monic with nonzero constant term, any rational root must be a signed
integer divisor of `(s+1)!`. The script factors the integers in that
factorial, generates all such divisors with both signs, and evaluates by
integer Horner arithmetic without any congruence or valuation pruning.
The finite replay does not depend on the all-degree argument in §2 after
the rational-root reduction. Compare its output to `expected-check.txt`:

```sh
sha256sum -c files.sha256
python3 check_tall_laguerre.py | diff -u expected-check.txt -
```

`reviewed-inputs.sha256` is for comparison from the root of the reviewed
repository, not for running the standalone arithmetic checker. The result
here is an all-order mathematical proof plus exact finite replay, not a
claim of a newly Lean-checked lower-bound theorem.
