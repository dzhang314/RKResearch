# Full tall width does not force a third low-order defect direction

For every integer `p ≥ 3` there is a rational strict SDIRK tableau with
common diagonal `1`, exact rooted-tree order `p`, and
`s = 4 + p·max(1,p−3)` physical stages, satisfying all of the following:

- Every successive subdiagonal entry and the final weight are nonzero.
  The reduced scalar tall-tree response has denominator `(1−X)^s`.
- Exactly `p` clock fibres carry nonzero output weight. Their clocks
  are `−1,…,−p`, with one contributing row per fibre.
- The actual defect space **through tree order four has dimension two**.

Thus full tall-response width, arbitrary paid order, and many live clocks
alone do not supply a third or fourth defect direction. The result
applies to the lower-triangular class containing strict SDIRK, not to
zero-diagonal ERK. The early weights here are zero and the terminal
weights are signed. No assertion is made about all-active or
near-minimal methods, stability, or any unrestricted stage bound.
The same rational identities and nonzero minors survive extension to
any characteristic-zero field.

## The actual four-tree defect space

Write `c=A1`, `q=2Ac−c²`, `r=3Ac²−c³`, and `N=A−I`; vector powers and
products are pointwise. If `t` has children `u`, the normalized stage
column `W_t = (t!/|t|) Φ_t` is the product of the child factors
`|u| A W_u`, where `t!` is the rooted-tree factorial and `|t|` is the
tree order. The leaf column is `1`. The order condition is therefore
`bᵀ W_t = 1/|t|`.

Let `D₄` be the span of normalized column differences at the same tree
order at most four. This is the [reviewed `zeroSpace A 3`](../../lean/RKCert/ReviewedNative/GradedDefects.lean),
not `zeroSpace A 4` (which includes tree order five). At tree orders
one and two there is nothing to subtract. At three the difference is
`q`. At four the root-child size patterns are `1+1+1`, `1+2`, or `3`,
with two order-three trees available in the last pattern. The four
columns are `c³`, `c³+cq`, `c³+r`, and `c³+r+3Aq`. Consequently

```
D₄ = span(q, cq, r, Aq) = span(q, cq, r, Nq).
```

This is an exact shape computation, not a chosen upper estimate for
the defect space. For `p=3` the space is still defined even though
its order-four members are not all paid; the counterexample also holds
at every `p≥4` when the whole space is paid.

## Four-row seed and the base block

Start with the four rows below, every omitted entry zero:

```
(1)
(1, 1)
(1, 1, 1)
(7/3, −5/3, 1/3, 1)
```

These give `c=(1,2,3,2)`, `q=(1,2,3,0)`, `Nq=(0,1,3,0)` and
`r=(2,7,15,0)`. In all four rows,

```
(c−1)q = 2 Nq,       r = (c+1)q + Nq.                 (1)
```

The evaluation columns `1,c,c²,q` are independent on the seed:
subtract the two clock-2 rows to isolate the `q` coefficient, then
use the three distinct clocks for the remaining Vandermonde test.
The first two rows already show `q,Nq` independent.

Append an initial block of `p` rows at the prescribed clocks
`−1,−2,…,−p`, in that order. For a new row at `x`, assign diagonal
`1` and solve for the four strict coefficients on the seed so that

```
(A1)_row=x,    (Ac)_row=x²/2,    (Ac²)_row=x³/3,    (Aq)_row=0.
```

Use the planned self value `q=0`; the first three equations indeed
give actual `c=x`, `q=0`, and `r=0`, so the last uses the actual
column. On the first new row, subtract the strict `q` moment from
the strict `c` moment. The seed values of `c−q` are `(0,0,0,2)`;
thus the coefficient on its immediate predecessor is
`(x²/2−x)/2 = 3/4` at `x=−1`. On every remaining row of this block,
first prescribe coefficient `1` on the immediately preceding new
row and subtract its known contribution in the same four-by-four
seed solve. The predecessor is not one of the four seed donors.
All other strict entries are zero. This block has `q=r=Aq=0`;
by the exact low-tree columns it is stage-exact through grade three,
meaning `W_t = c^(|t|−1)` at those rows for `|t|≤4`.

## Raising exactness and reading the output

For `g=4,…,p−1`, append a block of `p` rows at the same clocks
`−1,…,−p`. Place `1` on each diagonal and on the edge from the
immediate physical predecessor. For each row at `x`, choose the
first `g` rows of the preceding block as donors and solve

```
(A c^j)_row = x^(j+1)/(j+1),    j=0,…,g−1.
```

After subtracting the diagonal and predecessor terms, these are `g`
linear equations in `g` strict coefficients at distinct donor clocks.
The prescribed predecessor never overlaps the donors: at the first
row it is the last row of the preceding block and `g≤p−1`; thereafter
it is in the new block. All other strict coefficients are zero.
All solves are rational Vandermonde solves, not searches.

Every used earlier row is stage-exact through grade `g−1` by induction
on blocks and chronology. At the receiving row, prove exactness up
to grade `g` by induction on tree order. A child of order `j+1` uses
only its already known normalized `c^j` values at the donors, predecessor,
and self. The primitive equation gives its branch factor as `x^(j+1)`.
Multiplying branches gives `W_t=x^(|t|−1)`. This also verifies the
implicit self contribution, which uses strictly lower tree order.
In particular `q=r=Aq=0` in every appended row, including the base
block. Thus (1) holds on the full tableau, implying `D₄=span(q,Nq)`.
The seed pivots prove dimension two. All defect columns here restrict
to zero on the final weighted block; the stated rank uses all physical
coordinates, including zero-weight rows.

The last block is stage-exact through grade at least `p−1`. Give
only its `p` rows weights, using Lagrange quadrature on `−1,…,−p`
for the rational polynomial functional `I(x^j)=1/(j+1)`. It pays all
clock moments through degree `p−1`, so terminal stage exactness proves
all literal rooted-tree order conditions through `p`. Every weight is
nonzero: each Lagrange numerator is a product of factors `x+j` with
positive `j`, so it has strictly positive `I`, and its denominator
is a nonzero constant. In fact the signs alternate in the stated
node order. To see that order is exactly `p`, the polynomial
`∏_(j=1)^p (x+j)` vanishes on the output nodes but has strictly
positive `I`. Since all lower moments are exact, the degree-`p`
clock moment (the next bush) fails.

## Full tall width and exact replay

Strict triangularity makes `N^s=0`. Therefore the scalar response is

```
R(X) = 1 + sum_(k=0)^(s−1) (bᵀ N^k 1) X^(k+1)/(1−X)^(k+1).
```

After multiplication by `(1−X)^s`, its value at `X=1` is
`bᵀ N^(s−1)1 = b_last ∏_(i=1)^(s−1) A_(i,i−1)`, since the only strict
path with `s` vertices is the chronological path. It is nonzero by
construction. Thus no denominator factor cancels, even though the
seed and intermediate blocks carry no final weight.

Run the [exact rational checker](check_boundary.py) with Python 3:

```sh
python -B check_boundary.py $(seq 3 20)
```

It accepts any integer orders at least three as arguments. It instantiates
the constructive rows and weights, checks the low-order identities and
pivots, exact primitive moments and dependency grades, and verifies the
pure next-order failure. The parameterized proof above covers every
`p≥3`; the finite run is an audit, not an all-order enumeration and
not a Lean kernel claim.
