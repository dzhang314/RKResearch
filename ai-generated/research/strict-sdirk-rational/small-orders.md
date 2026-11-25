# Minimum stage counts over the rationals at orders three and four

For a strict singly diagonally implicit Runge–Kutta method over the
rationals, the minimum is three stages at order three and four stages at
order four. Here “strict” means that the matrix is lower triangular and its
diagonal entries are all the same nonzero rational number.

## Lower bounds

Let `s` be the number of stages and let `g` be the common diagonal entry.
The matrix `A - g I` is strictly lower triangular, so its `s`th power is zero.
If the method has order at least `s+1`, the tall tree with `k+1` vertices
gives `b · A^k 1 = 1/(k+1)!`, for each `k` from zero to `s`. Applying
`b` and the constant stage vector to the binomial expansion of
`(A - g I)^s` therefore gives
$$
  0=\sum_{k=0}^s \binom{s}{k}(-g)^{s-k}\frac{1}{(k+1)!}.
$$
At two stages this is `6g² - 6g + 1 = 0`; at three stages it is
`24g³ - 36g² + 12g - 1 = 0`. Neither polynomial has a rational root.
Indeed, the denominator of a rational root in lowest terms divides the
leading coefficient, so in both cases it is invertible modulo five. But
the respective lists of values at the five residues are `(1,1,3,2,3)`
and `(4,4,1,4,2)`. Appending a stage with diagonal `g`, zero coupling
to all other stages, and zero output weight leaves every order condition
unchanged. Thus the exclusions also apply to smaller widths.

## Rational constructions

At order three use
$$
18A=\begin{pmatrix}3&0&0\\6&3&0\\8&4&3\end{pmatrix},\qquad
8\mathbf b=(3,2,3).
$$
At order four use
$$
18A=\begin{pmatrix}3&0&0&0\\6&3&0&0\\12&-6&3&0\\6&4&2&3\end{pmatrix},\qquad
8\mathbf b=(3,1,1,3).
$$
In both tableaux the diagonal is `1/6`. The accompanying exact checker
enumerates the unordered rooted trees and verifies each equation
`t! (b · Phi_t(A)) = 1` through the claimed order. To make the
arithmetic reproducible, the right column below lists the values of
`(8b) · Phi_t(18A)` for all trees at each order; trees of the same order
are listed as a multiset.

| Order | Integer values |
| --- | --- |
| 1 | 8 |
| 2 | 72 |
| 3 | 432, 864 |
| 4 | 1944, 3888, 5832, 11664 |

The next tall-tree values are `5/108` for the first method and
`11/1296` for the second, against `1/24` and `1/120` respectively.
Thus the displayed methods have exactly the stated orders. These
certificates use only rational coefficients; no priority claim is made
for the tableaux.
