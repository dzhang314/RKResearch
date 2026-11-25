# A prime cut for the support of rational quadrature

Let `p` denote quadrature order: all monomials of degrees `0,…,p−1`
have exact uniform probability moments on `[0,1]`. Let `n` count the
distinct abscissae carrying **nonzero aggregate weight**. Repetitions
are grouped first. Only these `n` abscissae are required to be rational;
zero-aggregate sites may be arbitrary. Weights may be signed or lie
in any characteristic-zero field. For a Runge–Kutta rule the reviewed
bushy trees provide exactly this law at the actual nodes `A *ᵥ 1`.
There is no triangularity, diagonal, or positivity hypothesis.

## The reusable prime projection

**Theorem.** Suppose `n < p ≤ 2n`, write `t=p−n`, and let `q` be a
prime with `n < q ≤ p`. Put `B=q−t−1`. Existence of the rule implies
that for some `0 ≤ r ≤ B` there is a nonzero degree-`r` polynomial
`R ∈ F_q[X]` splitting into linear factors, with multiplicities
allowed, satisfying
```
Σ_{j=0}^r R_j/(j+k+1) = 0 over F_q    (0 ≤ k < m),
m = t       if r < B,
m = t−1     if r = B.
```
All displayed denominators are units. In the second case the lone
possibly unpaid row determines a specific next digit, as below.

**Proof.** Write the distinct active sites as `u_i/v_i`, where
`gcd(u_i,v_i)=1` and `v_i>0`, and use the integral nodal polynomial
`P(X)=∏_i(v_iX−u_i)=Σ_{j=0}^n a_j X^j`. Multiplying its zero at each
active site by the monomial of degree `k<t` gives the rational equations
```
Σ_{j=0}^n a_j/(j+k+1) = 0.                                   (1)
```
Indeed the stage sum is zero irrespective of the weights, and the
formal moment scalar is rational; its zero descends through the
injective rational map into the coefficient field. No reduction of
the rule or its weights is needed.

Each factor of `P mod q` is a nonzero constant or a nonconstant
linear factor. If `r` denominators `v_i` are units at `q`, the
reduction is nonzero of degree exactly `r`. Choosing the coefficient
of degree `j` uses at least `j−r` q-divisible denominators if
`j>r`; therefore
```
q^max(0,j−r) divides a_j.                                   (2)
```
This applies even when the reduced finite roots collide.

Since `q>n` and `p≤2n`, all denominators in (1) are below `2q`,
and the only possible nonunit is exactly `q` in column
`j*=q−1−k`. Multiplying (1) by `q` and reducing forces
`q | a_j*` whenever the column exists. The union of these columns
is `q−t,…,n`, hence `r≤B`. Now reduce (1) itself in the local
integers. The exceptional column is always strictly above `r`,
and by (2) it reduces to zero even after dividing by `q` unless
`j*=r+1`. This exception occurs only at `r=B,k=t−1`. All ordinary
columns above `r` vanish modulo `q`. The remaining rows are
exactly those stated for `R=P mod q`. At the exception, (1) gives
`(a_{r+1}/q) mod q = −Σ_{j=0}^r R_j/(j+t)`. □

This proof uses only one prime digit beyond the reduced support.
It does not require an explicit Legendre basis, ordered field
machinery, or assumptions on other primes, and it applies at any
order. One can normalize `R` to be monic for the finite tests.

### Strict consequence and the critical pencil

A degree-`r` polynomial satisfying the first `r+1` displayed
rows under unit denominators must be zero: the square Hilbert
matrix is a Cauchy matrix. For a direct proof, multiply
`Σ_j R_j/(Z+j+1)` by `∏_j(Z+j+1)`. The numerator has degree
at most `r`, vanishes at `0,…,r`, and hence is zero. At
`Z=−j−1` the remaining product of differences is nonzero,
forcing `R_j=0`. In the applications of this argument here
`2r+1<q`, so all the required differences and denominators are units.

* **Strict gap.** If `n < q < 2t`, then `B≤t−2`. At least
  `t−1≥r+1` rows survive, a contradiction. Thus for every prime
  `q>n`, necessarily `2(p−n)≤q` (the interesting primes are
  `q≤p`; the ordinary Gaussian bound handles `p>2n` independently).
* **Critical odd prime.** If `n<q=2t+1≤p`, then `B=t`. Any
  `r<t` gives at least `r+1` rows and is impossible. For
  `r=t`, the residual space is exactly the two-dimensional pencil
  `L_t + λ L_{t−1}` up to a nonzero scalar, with `λ∈F_q`.
  Here `L_j` is the shifted Legendre polynomial with the convention
  `L_j(1)=1`:
  ```
  L_j(X) = Σ_{i=0}^j (−1)^(j−i) binom(j,i) binom(j+i,i) X^i.
  ```
  Rodrigues' formula `L_j=(d/dX)^j[X^j(X−1)^j]/j!` gives
  orthogonality against lower tests by integrating by parts.
  Reduction preserves these moments here. The leading coefficients
  of `L_t,L_{t−1}` are units since `2t=q−1`, and the lower
  `t−1` columns of the `t−1` surviving rows give the invertible
  Cauchy block. Therefore they span the residual space, and
  the degree-`t` coefficient in front of `L_t` must be nonzero.

The exact pencil certificate below counts the number of finite
field roots **with multiplicity**. The entries are in order
`λ=0,…,q−1`; none reaches the degree.

| q | t | Root multiplicity sums for `L_t+λL_{t−1}` | Max |
|---:|---:|---|---:|
| 11 | 5 | 3, 1, 0, 0, 2, 1, 1, 2, 0, 0, 1 | 3 |
| 13 | 6 | 0, 2, 0, 1, 1, 0, 2, 2, 0, 1, 1, 0, 2 | 2 |
| 17 | 8 | 0, 2, 0, 0, 0, 1, 3, 2, 1, 1, 2, 3, 1, 0, 0, 0, 2 | 3 |
| 19 | 9 | 3, 3, 0, 2, 2, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 2, 2, 0, 3 | 3 |

The companion verifier builds the four pencils from the displayed
binomial formula and removes each linear factor by exact synthetic
division. It checks exact finite algebra, not any real/rational
quadrature or tableau candidates. No all-prime nonsplitting
assertion for the pencil is being made.

### A separate stronger cut from the same theorem

For `(q,t)=(17,7)`, `B=9`. Degrees below seven are impossible
by the Cauchy test. For `r=7,8,9`, the surviving row counts are
respectively `7,7,6`. The leftmost square Hilbert block is invertible.
Normalizing the leading coefficient to one leaves exactly
`17^(r−m)` monic possibilities in each affine finite-field slice.
The following independently reproducible exact finite-algebra
certificate uses modular elimination and the same linear-factor test:

| Degree | Paid residual rows | Number in affine slice | Greatest total linear factor degree |
|---:|---:|---:|---:|
| 7 | 7 | 1 | 1 |
| 8 | 7 | 17 | 3 |
| 9 | 6 | 4913 | 7 |

This excludes every width `n<17` with `p−n=7` and
`17≤p≤2n`. In particular it rules out `n=13,p=20`
without using an order-20 tableau or any held input.

## Consequences at orders 6–20

Equivalently, these tests give the closed lower floor
```
n ≥ max_{q≤p prime} min(q, p−floor(q/2)+ε_q).
```
The strict-only floor has `ε_q=0`. The four pencils allow
`ε_q=1` at `q∈{11,13,17,19}`; the additional slice replaces
`ε_17=1` by `ε_17=2`. For example, if `n<17`, the
strict, critical, and separate slice exclusions at `q=17`
leave only `p−n≤6`. If `n≥q` the corresponding minimum
is already satisfied. This formula is an all-order lower
bound from the stated fixed-prime certificates, not a fit
to the table. Combine it with the independent support baseline.

The prior rational-support baseline is
`max(4,ceil(p/2))`: four for order at least five by the checked
order-five rational theorem, and the ordinary Gaussian support
bound. The latter follows by applying the exact law to the square
of the monic nodal polynomial when `2n≤p−1`; its moment is a
strictly positive rational number (evaluate the real integral),
independent of any ordering on the field of the weights.

| p | Prior rational support floor | Strict prime gap | Strict plus four critical pencils | Also the (17,7) slice |
|---:|---:|---:|---:|---:|
| 6 | 4 | 4 | 4 | 4 |
| 7 | 4 | 5 | 5 | 5 |
| 8 | 4 | 5 | 5 | 5 |
| 9 | 5 | 6 | 6 | 6 |
| 10 | 5 | 7 | 7 | 7 |
| 11 | 6 | 7 | 7 | 7 |
| 12 | 6 | 7 | 8 | 8 |
| 13 | 7 | 8 | 9 | 9 |
| 14 | 7 | 9 | 10 | 10 |
| 15 | 8 | 10 | 11 | 11 |
| 16 | 8 | 11 | 11 | 11 |
| 17 | 9 | 11 | 12 | 12 |
| 18 | 9 | 12 | 13 | 13 |
| 19 | 10 | 13 | 13 | 13 |
| 20 | 10 | 13 | 13 | 14 |

These are lower bounds for the **number of distinct contributing
sites**, not stage minima, and the first unexcluded count is not an
existence assertion. For example, the new obstruction at order 15
excludes ten rational support sites by `q=11,t=5`; at order 18 it
excludes twelve by `q=13,t=6`.

## Exact limitation of one local prime test

For `n≥2`, an admissible **squarefree split** residual `R` cannot be excluded
by purely local splitting at its prime. In fact it admits a lift
with rational polynomial coefficients whose degree-`n` nodal
polynomial splits over `Q_q` and obeys (1). This is not a lift of
the sites to rational numbers.

Normalize `R` to be monic. Here `q≥2t+1`: for `n≥2` the
prime is odd, and smaller primes are excluded by the strict cut.
In either projection case `r≥t`, by the Cauchy test if `r<B`
and by `B=q−t−1≥t` if `r=B`. Put `d=n−r`, so
`1≤d<q` because `q≤p` and `q>n`. Choose a monic degree-`d`
polynomial `I(Y)∈F_q[Y]` with distinct roots and, if `r=B`,
with the coefficient of `Y^(d−1)` prescribed by the exceptional
row above. Translation of any `d` distinct roots can set their
sum arbitrarily since `d` is a unit. Set `a_{r+h}=q^h b_h`
for integer lifts `b_h` of the coefficient of `Y^(d−h)` in
`I`, choosing `b_d≠0` even if its residue vanishes. Choose
integer lifts of `R_j` for `t≤j≤r`. Solve (1) for
`a_0,…,a_{t−1}` over the rationals. The left block has unit
determinant at `q` by the Cauchy test, and all right sides are
integral at `q`. The reduced system is exactly satisfied,
including the deliberately prescribed digit in the exceptional
row. Thus the low coefficients reduce to `R`.

Hensel's lemma lifts its `r` distinct finite roots. For the other
`d`, the reciprocal polynomial
`q^(−d) Σ_{j=0}^n a_j(qY)^(n−j)` is integral and reduces to
`I`. Its `d` simple roots also lift; none is exactly zero
because `b_d≠0`. They give distinct nonintegral roots of `P`
via `X=1/(qY)`. As a concrete limitation, `q=5,t=2` allows
`R=L_2+L_1 ≡ X(X+1)`, so this prime's local splitting test
alone cannot refute four rational sites at order six. No actual
four-site rational rule is claimed.
