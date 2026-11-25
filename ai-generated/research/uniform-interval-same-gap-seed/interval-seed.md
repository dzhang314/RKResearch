# A genuine uniform same-gap seed with all sites in the integration interval

There is an exact signed rational quadrature rule for
\(\int_0^1 f(X)\,dX\) with **12 distinct contributing sites in
\([0,1]\)** and **exact order 14**, and its two-shift elliptic
pencil on the endpoint pair has a nontorsion infinity difference.
Three of its weights are negative. This is a second uniform
seed, stronger in site location than the
[ten-site order-12 seed](../uniform-same-gap-seed/uniform-seed.md),
not a claim that the ladder keeps later nodes in the interval.

## A symmetric confluent start

Write \(Y=2X-1\) and \(L_Y(Y^j)=1/(j+1)\) for even \(j\),
\(0\) for odd \(j\). The symmetric Jacobi weight
\((1-Y^2)^3\) has second-moment/zeroth-moment ratio \(1/9\).
Thus for
\[
          P=(Y^2-1)^3(Y^2-1/9)
\]
one has \(L_Y(P)=L_Y(YP)=0\) by the ratio and parity.
Expanding the factors gives
\[
 \begin{split}
 h&=L_Y(Y^2P)=-256/31185,\\
 (C_{-1},C_{-1/3},C_{1/3},C_1)
    &=(-16/945,16/105,-16/105,16/945),
 \qquad C_i=L_Y(P/(Y-i)).
 \end{split}
\]
The endpoints have multiplicity three. There is no ordinary
quadrature rule asserted at this confluent stage.

## Four prescribed moves, no grid

Apply the [same exact multiset move](../uniform-same-gap-seed/uniform-seed.md)
successively to the following pairs, in centered coordinates:
\[
       (1/3,1),\qquad (55/87,1),\qquad
       (-1,5/44),\qquad (-1,5142230101/23576082933).
\]
For an old pair \(u,v\) use \(a=h/(C_u(v-u)^3)\),
\(b=-h/(C_v(v-u)^3)\) and the earlier
[rank-free triple](../two-shift-elliptic-transfer/elliptic-transfer.md);
recompute \(h,C\) from the current nodal polynomial at every
step. In particular the first triple is
\((5/44,-19/39,55/87)\), and the second is
\[
  (3927397/16686208,\ 5142230101/23576082933,\
             40354847243/50117037387).
\]
These formulas plus the four literal pairs specify all final
nodes exactly without long integer literals for the last two
triples.

The [exact checker](verify-interval-seed.py) proves for this
fixed program that all newly introduced nodes are in
\((-1,1)\), avoid the retained roots, and multiply to the
literal paid cubic at each step. The endpoint multiplicities
\((m_{-1},m_1)\) are successively
\[
             (3,3),(3,2),(3,1),(2,1),(1,1).
\]
It checks the paid shifts, next defect, and every distinct
cofactor throughout. The final degree-12 polynomial is
squarefree. Its centered Lagrange weights
\(L_Y(P/(Y-y))/P'(y)\) are rational and nonzero.

Map each site \(y\) to \(x=(1+y)/2\) and keep its weight.
The binomial formula preserves paid order and scales the
first defect by \(2^{-14}\), so the transformed rule is exact
order 14 for the uniform functional on \([0,1]\). The checker
also directly evaluates all 14 required moments and the
nonzero failure at degree 14 of the transformed rule.
All sites are interior except \(0,1\).

## Nontorsion at the endpoint pair

The marked pair in centered coordinates is \((-1,1)\), hence
\((0,1)\) on \([0,1]\). The normalized \(a,b\) are unchanged by
the affine map: the degree-12 monic nodal polynomial scales
by \(2^{-12}\), its cofactor integrals by \(2^{-11}\), the
unpaid \(h\) by \(2^{-14}\) since lower shifts vanish, and
the pair gap by \(1/2\). The exact \(\chi(a,b)\ne0\) check
succeeds on the final pair.

The explicit Weierstrass model is integral at 31 and reduces
to
\[
          Y_E^2=X_E^3+12X_E^2+16X_E+14,\quad
          D=(0,18),\qquad \operatorname{disc}=5\pmod {31}.
\]
All denominators of the successive affine additions through
\([12]D\) are units at 31, so the rational points are affine
and their reductions include
\[
 [6]D=(26,27),\quad [9]D=(27,27),\quad [12]D=(0,13)
                         \qquad\bmod31 .
\]
As before the rational 3-torsion and Mazur's theorem show
that \(D\) is nontorsion.

This provides an independent, bona fide interval-contained
start for the [fixed-functional ladder](../same-gap-seed-ladder/seed-ladder.md);
that theorem gives arbitrary exact orders allowing unrestricted
rational sites, not an interval-constrained sequence or a positive
rule. This exact computation stops at order 14. There is no
new RK stage bound, Lean certificate, or coefficient table at
order 20.

Run `python3 verify-interval-seed.py` for the exact standard-library
replay ([expected output](exact-check.txt)).
