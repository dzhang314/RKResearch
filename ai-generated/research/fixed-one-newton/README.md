# Rational strict SDIRK: 18 stages at order nine and 26 at order eleven

Both literal tableaux have rational coefficients, are lower triangular, and have common nonzero diagonal **1**. The rational upper bounds in the earlier two-order family were 19 and 28, respectively. This does not change the smaller unrestricted real-algebraic upper bounds (14 and 20), settle either minimum, or assert stability.

| Order | Stages | Old stages | Scalar sites | Physical merges | Full unordered rooted-tree tests | Cleared next-bush defect |
|---:|---:|---:|---:|---:|---:|---:|
| 7 (new seed) | 11 | 5 | 6 | 0 | 85 | −313679/23275 |
| 9 | **18** | 11 | 8 | 1 | 486 | −476370191016701677/251256338027100 |
| 11 | **26** | 18 | 10 | 2 | 3,047 | −6024707639071705614354709058029075/15580360964832483881697516342 |

Here the last column is ((p+1)\sum_i b_ic_i^p-1), with (c=A\mathbf1). Thus these are *exact* orders over the rationals. In any nonzero commutative ring in which both common integer scales of the chosen tableau are units, the same cleared integer equalities give order **at least** (p), and the common diagonal remains 1; exactness additionally follows when the displayed defect remains nonzero. This is not a construction over every characteristic-zero ring.

## The change in the construction

Use the existing five-stage rational order-five common-diagonal-one seed, and retain that diagonal. Rebuild the order-seven **head**, rather than treating the pre-existing eleven-stage order-seven witness (diagonal 1/7) as immutable. In each two-order Newton lift for odd target (p=2q+1), use (2q) scalar sites and (q) distinct prescribed trailing clocks (1-(2i-1)\gamma), in reverse index order. There are (q) ordinary quadrature head slots. Certain head rows can be more locally accurate than the construction requires. Those *physical* rows become donors for the next lift.

| Target | Head sites in chronological order | Pure through tree sizes | Trailing clock list |
|---:|---|---|---|
| 7 | −1, −3, (z_7=2462/3325) | 4, 4, **5** | −4, −2, 0 |
| 9 | (z_7), −5, −7, (z_9=-504145702/299864349) | merged local 5, local 5, **6**, **6** | −6, −4, −2, 0 |
| 11 | −7, (z_9), −9, −11, (z_{11}=251647454237400205/337389807870474227) | two merged local 6, **7**, **7**, **7** | −8, −6, −4, −2, 0 |

In each row (H) is the monic product over the sites other than (z_p), and (z_p = \int_0^1 xH/\int_0^1 H); the interpolatory rule then also integrates the full hull of degree (p-1). The site table is not an assumption that the gates or stage rows work: the supplied literals pass the direct exact rooted tests. The generator independently checks the signed quadrature moments, the nonzero defect, all required local stage equations, and the Newton row identities.

The normalized elementary derivative column (N_t) has ideal value (x^{|t|-1}), and a child (u) contributes (|u| A N_u) multiplicatively. For a new row at (x) with old strict feed (v), previous (old and already assigned) stages (B), and own diagonal 1, local size (h) is guaranteed by the finite linear system
[
 v N_u(B)=x^{|u|}/|u| - x^{|u|-1},qquad |u|\le h-1.
]
The generator solves this rational linear system using independent pivot columns and verifies it on *every* such tree. This directly proves local purity by induction. A merge copies the old strict row (without its own diagonal) onto the old-prefix coordinates, with zero taps to earlier virtual head slots. The generator checks literal row equality after removing the two separate diagonals and moves every dependency and the output weight before deleting the duplicate. No donor is appended outside the counted quadrature head.

The rest of the Newton tail uses the earlier reverse Newton proof. In brief, let (P_j) be the monic product over the last (j) sites, (L_f=(w_i f(x_i))_i), (S) the strictly lower part of the new block, and (I) integration on ([0,1]). Complete the free columns of (S) by the (q) row identities (L_{P_j}S=-L_{P_{j+1}}/(j+1)), (0\le j<q). They are triangular Vandermonde solves with nonzero weights. For the old-to-new feed (U) keep all prescribed head rows; the last (q) rows are uniquely determined by
[
 L_{P_j}U=(b_i^0 h_j(c_i^0))_i,qquad h_j=\int_X^1 P_j(t)\,dt-P_j(X)+P_{j+1}(X)/(j+1).
]
The prescribed trailing ladder makes (h_0=0), (\deg h_j\le j-1). This is precisely the archived two-order lift. No new stage order at an implicit pivot is assumed.

## Independent replay

From this directory:

```sh
python3 check.py tableau-7.json tableau-9.json tableau-11.json
```

The checker uses only the Python standard library. It reads neither the generator nor its seed or moment calculations. A rooted tree is uniquely a root over a multiset of unlabelled child trees. At size (n), enumerate every nondecreasing multiset of already numbered children with total size (n-1). Distinct child orders have the same elementary vector and factorial by commutativity of componentwise multiplication; the resulting nonplane enumeration therefore covers the ordered-constructor convention as well. The counts by size are 1, 1, 2, 4, 9, 20, 48, 115, 286, 719, 1842. With (M=dA), (w=eb), compute integer stage vectors by multiplying (M\Phi_M(u)) over every child; compare (t!\,w^T\Phi_M(t)) against (e d^{n-1}). The largest check uses 3,047 trees and then independently tests the 12-vertex bush. Positivity, order conditions beyond the first unpaid bush, and minimality are not required.

Reconstruct the tables independently with Python and SymPy:
```sh
python3 generate.py ../../research/strict-sdirk-rational/five-stage-repeated-clock-numerators.json --out .
```
Supply the actual path to the existing five-stage seed if this packet is moved.

## Higher odd orders: constructive deduction, not a full-table replay

The improved seed lowers the rational counts at orders 13, 15, 17, 19 from 37, 48, 60, 74 to **35, 46, 58, 72**, respectively. These follow from the established Newton lift and exact finite scalar gates; this packet does not claim a Lean or exhaustive higher-table replay for these four entries.

For target (p=2q+1), suppose the old tableau has order (2q-1), and an existing bank of (r) head rows exact through size (q+1), including two distinct negative clocks. Old order gives, for every old zero relation among normalized columns through size (q+1), vanishing moments of the associated polynomial (P) of degree at most (q) up to degree (q-2) (attach leaves). Purity also gives (P(a)=P(b)=0) at the two negative samples. Write (P=(X-a)(X-b)Q), (deg Q\le q-2); the zero moment against (Q) is now the integral of a positive factor times (Q^2) on ([0,1]). Thus (P=0), so linear interpolation on the old column span gives a rational decoder through size (q+1). There is no field extension.

All (r) bank rows meet the normal purity requirement for head-slot merges. Make the other (q-r) head rows locally exact through size (q+2) using that decoder with strict feed ((J-1)D) evaluated at their respective clocks, where (J) takes the formal primitive. These rows use no other new stage; the Newton repair is confined to the (q) trailing pivot rows. The new physical stage count is (s+(p-1)-r). The (q-r) newly protected rows are the next bank, and include at least two new strictly negative sites. The initial bank is the three actual rows of the 26-stage tableau at −9, −11, and (z_{11}), exact through size seven by its construction.

At each step choose (q-r-1) exterior sites (-100p-2j-1) for (j=0,\dots,q-r-2) and one solved (z), plus the usual (q) prescribed ladder sites. The standard-library file `continue_odd.py` checks every quadrature moment, noncollision and activity of every site, and nonzero degree-(p) error for each of the four explicit steps. It is a scalar check, intentionally separate from `check.py`. The merge counts are (3,3,4,4); the returned banks have (3,4,4,5) rows. The argument uses the known two-order lift for all rooted conditions rather than inferring ordinary order from quadrature alone.
