# How invariant defects count toward tall-pole cancellation

An invariant subspace invisible to the output uses up part of the
physical tall-response budget. It does not consume that budget a
second time after the cancellation has already been counted. The
identity below separates those two statements. It holds over every
characteristic-zero field, without sign or distinct-clock assumptions.

## Exact accounting on an invariant quotient

Let `A,b` be a physical `s`-stage Runge–Kutta tableau, with `e=1`,
`ℓ=bᵀ`, and literal rooted-tree order at least `p`. Write

```text
R = 1 + X ℓ(I−XA)⁻¹e = N/D = P/Q,
D = det(I−XA),  N = DR,  D = CQ,  N = CP,
D(0)=N(0)=C(0)=P(0)=Q(0)=1,  gcd(P,Q)=1.
```

Let `d_D,d` count the distinct geometric roots of `D,Q`, respectively,
and put `c=deg C`, `ν=s−deg N`, `δ=d_D−d`. Here `δ` counts fully
lost pole locations, not multiplicities; `ν≥0` by the adjugate formula.
The [distinct-pole budget](../tall-distinct-pole-recurrence/README.md)
gives `p≤deg P+d`, equivalently `p+c+ν+δ≤s+d_D`.

Suppose `W` is `A`-invariant and `ℓ(W)=0`. Let `w=dim W`, let `w₀`
be the algebraic multiplicity of eigenvalue zero on `W`, and let
`L(W)` count the distinct nonzero geometric eigenvalues of `A` whose
entire algebraic multiplicity lies on `W`. Use primes for the same
quantities on the quotient state space `K^s/W`. Then

```text
c = (w−w₀)+c′,     ν = w₀+ν′,     δ = L(W)+δ′,
p + w + L(W) + c′ + ν′ + δ′ ≤ s+d_D.                         (1)
```

Indeed, the projection intertwines resolvents and `ℓ` factors through
it, so the quotient has exactly the same scalar response `R`. The
invariant block determinant gives `D=G D′`, where
`G=det(I−X A|_W)` has degree `w−w₀`. Thus `N=G N′` and `C=G C′`.
Subtracting dimensions and degrees gives the first two identities.
The same block determinant gives `d_D−d_(D′)=L(W)`, proving the
third. Over a nonsplitting field, each completely removed nonzero
irreducible factor of the characteristic polynomial contributes its
degree to `L(W)`, since characteristic zero makes it separable. For
lower triangular `A`, the labels are simply the nonzero physical
diagonals. Eigenvalue zero is not a pole location.

**Only residual losses add to the charge for `W`.** Formula (1) is
the original physical inequality, not a stronger one. If a direct
physical receipt and an invariant-subspace receipt both bound the
canceled multiplicity at a label, take the larger lower bound there
unless an extra loss has been proved on the quotient. Two invisible
subspaces charge their sum, not the sum of their dimensions. If an
invariant subspace `U` containing `e` is also used to restrict the
response, the remaining state is `U/(U∩W)`; the removed dimension is
`codim U + dim(U∩W)`, not `codim U + dim W`.

This reasoning preserves the scalar response only. It does not
preserve the coordinatewise products used in full rooted-tree order.

## Earning an invariant witness from tree order

Let `Z_g` be the span of normalized equal-grade stage-weight
differences through grade `g` (tree order minus one). The normalization
multiplies a tree's stage weight by the product of the factorials of
its root children. Attaching a unary root therefore multiplies the
normalization for both trees in a difference by the same old tree
order. Literal order gives `ℓ A^j Z_g=0` for `0≤j<p−g`.
If `Y⊆Z_g` has actual support in an invariant tail with a monic
annihilator of degree at most `p−g`, its recurrence extends these
zeros to every unary probe. The `A`-span of `Y` is then a valid
`W`. A projection onto a mask does not establish actual support.

## A tight counterfamily with actual order at every `p≥3`

There is a rational lower-triangular method of exact order `p`, with
`A c_vec=c_vec²/2` at every row (here `c_vec=Ae` is the clock vector), whose
reduced scalar denominator is `Q=1−X/p` and whose numerator has degree
`p−1`. Thus the distinct-pole budget is tight before any extension.

**Seed.** Put `γ=1/p`. Start with a zero row and a row `(γ,γ)`, with
clocks `0,2γ`. Add `p−2` explicit layers on the same `p` distinct
rational nodes `x_i`, for instance `2,…,p+1`. The first layer uses
taps `x−x²/(4γ), x²/(4γ)` to the first two rows. Every later row at
`x` has taps `∫₀ˣ L_j(t)dt` only to the immediately preceding layer,
where `L_j` is the Lagrange basis on those `p` nodes. Output weights
are `∫₀¹ L_j(t)dt` on the final layer and zero elsewhere. All integrals
here are finite polynomial primitives over the rationals.

The constant and linear primitive equations give the stated clocks
and `A c_vec=c_vec²/2` in every row. More generally, in explicit layer
`ell`, the stage weight for any tree `t` of grade at most `ell+1` is
`x^(|t|−1) / ∏_(u child of t) u!`, with the usual rooted factorial
`t!=|t|∏_(u child of t)u!`. Layer one follows from the two primitive
equations. For each later layer, every child is in the preceding
profile; one primitive supplies the factor `1/|u|`, and joining
multiplies the child factors. The final layer has grade `p−1`, so
its quadrature gives `1/t!` for **every** tree through order `p`.

The first two coordinates of `Q(I−XA)⁻¹e` have degree at most one.
Each explicit layer adds at most one, as does the final `X` in the
response. Hence `deg N≤p`. Paid tall order then gives

```text
N=P=Σ_(j=0)^(p−1) (1−j/p) X^j/j!,    Q=1−X/p.
```

The coefficient at `p` vanishes, and `P(p)>0` over the rationals, so
there is no cancellation in the seed. The first unpaid tall
coefficient exceeds `1/(p+1)!` by `1/(p(p+1)!)`. The method has exact
order `p`, and these rational identities extend to any
characteristic-zero field.

**Live affine extension.** Fix a rational `λ`. Add `p+1` rows with
diagonal `λ`, a sole strict tap `t_j` into the original zero row,
and output weights `w_j=1/∏_(k≠j)(t_j−t_k)`. Choose the rational
`t_j` distinct, avoiding `±λ` and any clock collision. Their
weighted sum on polynomials of degree at most `p` reads the
coefficient of degree `p`, by interpolation. A tree of grade `g`
has stage weight polynomial in `t_j` of degree at most `g`:
unary rooting combines `λ` times the child polynomial and the tap
times the old child value; joining multiplies. The new rows leave
all paid rooted conditions unchanged. They also leave **all** tall
coefficients unchanged, since their stages in the scalar test are
`(1+Xt_j)/(1−λX)` and the weights annihilate `1,t_j`.

The actual grade-two defect `q=2A c_vec−c_vec²∈Z₂` now vanishes on
the seed and takes values `λ²−t_j²` on the new rows. Thus
`Aq=λq`, `ℓq=0`, and `W=span(q)` is a supported invisible line.
Every weight on its support is nonzero. For `p≥5` the local weighted
square `Σ_j w_j q_j²` is zero, since its polynomial has degree four.
Nevertheless `ℓ(c_vec^(p−2)q)=−1`: the highest-degree term of the
polynomial in the tap is `−t_j^p`. The line is not invisible to
all tree contexts.

| Fan diagonal | Actual physical loss from the added rows |
| --- | --- |
| `λ=0` | `p+1` more numerator-deficit units, no pole |
| `λ=γ` | `p+1` canceled copies of the retained pole, no lost location |
| `λ≠0,γ` | `p+1` canceled copies and one lost location |

Since `P,Q` do not change, in every case `p+c+ν+δ=s+d_D`.
Adding one more unit for this genuine paid defect line would be
false, including in the locally isotropic examples. On the other
hand, appending just one such row with `λ≠0,γ` and output weight
zero gives `L(W)=1`: deleting the full primary block really costs
one state and one location, both already recorded in (1).

This is an exact tall constraint and a boundary on double counting,
not an unrestricted stage minimum. The counterfamily is DIRK with
an explicit first row, not strict SDIRK.

## Exact cross-check

Run `python3 check_exact.py` and compare
[`expected-audit.txt`](expected-audit.txt). The checker uses rational
arithmetic, enumerates all rooted trees through each tested order
3–8, verifies the first unpaid tall condition, and constructs each
one-dimensional quotient directly before comparing its polynomial
ledger. The arguments above are for every indicated order.
