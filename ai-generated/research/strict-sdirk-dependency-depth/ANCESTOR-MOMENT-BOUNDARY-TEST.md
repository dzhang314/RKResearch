# One transferable simplification: the exact m=1 boundary test

In the moment system with T=V−γ and V integration from y=0,
let r≥1 and write P_r for the monic degree-r orthogonal
polynomial under the base uniform moment form. On polynomials
of degree at most r define the finite jet functional

    L_γ(P) = Σ_{j=0}^r γ^j P^(j)(0).

For any Q of degree <r, `(VQ)(0)=0` and its j-th derivative
at 0 is Q^(j−1)(0) for j≥1. Thus L_γ(VQ)=γ L_γ(Q), so
`(V−γ)Q` lies in ker L_γ. Conversely V−γ is injective
on degree<r by its nonzero leading primitive coefficient, and
L_γ(1)=1. Both spaces have dimension r, hence

    (V−γ) K[y]_<r = ker L_γ in K[y]_≤r.           (*)

This does not divide by γ, holds for γ=0 as well, and only
uses characteristic-zero polynomial arithmetic.

Projecting the left side to its ordinary r moments fails to
be invertible exactly when its image meets the orthogonal
line `K P_r` nontrivially. By (*) this is exactly
`L_γ(P_r)=0`. In fact this polynomial equals the m=1 square
moment determinant up to a fixed nonzero rational factor:
in the factorial basis e_j=y^j/j! the columns
`[1, e_1−γe_0, …, e_r−γe_(r−1)]` have determinant 1;
replacing the first column by P_r multiplies it by L_γ(P_r).
Apply the fixed invertible full moment matrix (all moments
0,…,r) to these columns. In its first column the first r
entries vanish and the last is `ℓ(y^r P_r)=ℓ(P_r²)≠0`.
Expansion along that column gives the determinant claim.
The same argument works for another nonsingular base moment
form with its corresponding monic P_r and nonzero norm.

For odd r the ordinary monic P_r has all roots in (0,1), so
P_r(0)<0; the coefficient of γ^r in L_γ(P_r) is r!>0.
Continuity gives a positive real root, algebraic over Q because
the coefficients are rational. At such a root choose Q with
`(V−γ)Q=P_r` using (*). The original tests include all
`(V−γ)Q` with `deg Q<r`. For every monic H of degree r,
`ℓ(H P_r)=ℓ(P_r²)≠0`, so no such H meets them, even after
coefficient extension. This reproduces the positive-diagonal
counterexample without computing a compression or using its
spectrum; it is the same m=1 obstruction, not a new stage case.
