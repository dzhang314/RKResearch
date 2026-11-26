# A uniform later-layer rank floor for a nonzero diagonal in characteristic zero

This is a separate consequence of the paid physical word construction
in the [paid ancestor-word proof](NEGATIVE-MATCHED-MINIMUM.md) (§§1–2). It uses neither the negative
sign nor the Chebyshev step of that note. Scope is a characteristic-zero
field, arbitrary nonzero common diagonal γ in that field, actual strict
B=A−γI whose nonzero entry Bᵢⱼ requires receiver level i to be exactly
one higher than donor level j, and output
weights supported in the terminal level. It is not a minimum or an
unrestricted lower bound. The zero diagonal and arbitrary rings are not
included in this separate extension.

Let d be the strict distance below the terminal level, let p be the paid
order, and put q=ceil(p/2). For every positive integer r with

    r ≤ q,               d+r ≤ floor((3p+1)/4),

that level must exist and have at least r distinct effective clock
labels (in particular r stages). Combine this with the already proved
common-diagonal staircase to get the stronger pointwise maximum of the
two bounds. No condition on real sign, coefficient-field degree, or
existence of split support is used.

## Uniform injective pairing

Take b_0=p−d−r, which is nonnegative under the bounds. Each actual
word

    b · (Y^{k_0} B ... B Y^{k_d} Y^a 1),
       0≤a<r,   Σk_i≤b_0,   Y=diag(1−A1)

is paid at order ≤1+d+a+Σk_i≤p. The physical rows factor only through
indices at distance d from b's support; equal clock labels have equal
right rows. In the ideal polynomial model, the full word span is
T^m K[y]_{≤ν}, with m=(d−b_0)_+, ν=b_0+min(d,b_0) and y=1−x,
T the adjoint of J=I_0−γ (I_0 the zero-origin primitive). The span
argument requires γ≠0 but not its sign.

If a column combination with polynomial P(y) of degree <r is killed
by those rows, then moving the adjoint back yields

    ℓ((J^m P) Q) = 0 for every Q of degree ≤ν.

Here J is expressed in the original x-coordinate; reflecting P and Q
does not change their degree bounds or the uniform pairing. If
ν≥m+r−1, this forces J^m P=0: its degree is at most m+r−1, and the
uniform polynomial moment pairing is nonsingular on degrees up to
m+r−1. Its rational Hilbert determinant is nonzero since the pairing
is positive definite over the reals; the nonzero rational determinant
stays nonzero in every characteristic-zero field. Also J raises the
degree of any nonzero polynomial by one (its primitive top coefficient
cannot be canceled by the scalar shift), so J^m is injective and P=0.
This proves rank r of the fully paid physical matrix.

If d≤b_0 then m=0, ν=p−r≥r−1. Otherwise

    ν−(m+r−1) = 3b_0−d−r+1 = 3p−4(d+r)+1 ≥ 0.

Both cases give the asserted rank. This is a one-way sufficient
certificate for nondegenerate rank at arbitrary γ≠0, not a claim that
some larger minor must vanish when the arithmetic test fails.

## Order 20 comparison

At p=20, q=10 and floor((3p+1)/4)=15. Combining the two valid layer
floors gives, at terminal distances d=0,...,18,

    10,10,10,10,10,10, 9,8,7,6, 5,4,4,3,3,2,2,1,1.

The first six must maintain ten clock labels each: a ten-site
terminal Gaussian rule is not the only ten-wide layer forced. The
count is 60+(9+8+7+6)+(5+4+4+3+3+2+2+1+1)=115. The baseline
100-stage staircase is still correct; these paid additional row
decorations certify 15 more stages in the stated nonzero-diagonal
field scope.

At shallow depth 18 the published 145-stage one-degree construction
has width 10 at d=0,...,9, widths 9,...,2 at d=10,...,17, and 1
at d=18. Of the 30 stages not explained by this new floor, 10 are
in d=6,...,9 (surpluses 1,2,3,4), and 20 are in d=10,...,17
(surpluses 4,4,3,3,2,2,1,1). These are not proved removable; no
uniform positive-diagonal sharpness or coefficient-field claim is
made. In particular changing only the final quadrature cannot save
any stages in this shape without violating its terminal rank floor.
