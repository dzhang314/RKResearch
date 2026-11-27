# Forcing one early clock in the regular reflected quartic-pole chart

This is an exact reduction and a family of rational exclusions, **not** a lower bound for arbitrary nine-stage SDIRK7 tableaux. Use the notation from [the quartic-pole chart](../strict-sdirk7-quartic-pole/README.md): the integration interval is ([0,2m]), (P_j) is its monic shifted Legendre polynomial, (g=P_4+delta P_3), and the affine denominator is (W(Y)=Y-h). The fixed fourth early clock is (c); the reflected suffix is (1,u,4-u) with (M=(u-2)^2-2). Work on the finite affine-pole, seven-distinct-clock, nonvanishing regular branch. In particular this does not treat constant (W), vanishing (V=g/W), or degenerate suffix or chronology branches.

The quartic-pole fourth-read equation (Q_g(c)=0) is independent of (M). Here (Q) is the linear map taking quartic coefficients (a_0,ldots,a_4) to the polynomial with coefficients
[
(11a_0+6a_1+6a_2+12a_3+36a_4,
 -8a_0-7a_1-12a_2-30a_3-96a_4,
 a_0+a_1+2a_2+6a_3+24a_4).
]
Thus (g) is fixed once ((m,c)) is fixed, provided (Q_{P_3}(c)
e0).

## Deliberately forcing a rational port

Set (q=Y^2-4Y+2-M), (R_3=(Y-1)q). The quadratic interpolant multiplied by (M/2) is
[
T_{mathrm{sc}}=operatorname{rem}_{R_3}(g)+g(1)q=T_0+M T_1.
]
This identity follows by monic division; the two quadratics are given literally in `recovery.py`. The nodal polynomial splits as (Omega=R_3 S_4) with (S_4(c)=0). Writing (J_I) for the second-kind operator (J_I f(Y)=I_X((f(Y)-f(X))/(Y-X))), the Gram chart gives (J_I(g)S_4equivlambda,WT_{mathrm{sc}}/R_3pmod g) for some scalar (lambda). The Legendre Wronskian gives (J_I(g)^{-1}propto P_3mod g), and monic division gives
[
T_{mathrm{sc}}/R_3equiv g(1)/(Y-1)-(Y+g_3+5)
              equiv -igl((g(Y)-g(1))/(Y-1)+Y+g_3+5igr)pmod g.
]
The quotients used here are defined on this chart: (g) and (R_3) are coprime, as are (g) and (Y-1). Define
[
B=operatorname{rem}_g!left(P_3igl((g(Y)-g(1))/(Y-1)+Y+g_3+5igr)ight),
qquad A=operatorname{rem}_g(YB).
]
Then (S_4=g-g(c)(A-hB)/(A(c)-hB(c))). This follows since (S_4-g) has degree below four and the normalization is forced by (S_4(c)=0).

With (P_0=(A(c)g-g(c)A)/(Y-c)) and (P_1=(B(c)g-g(c)B)/(Y-c)), requiring another early rational clock (a) forces
[
h=P_0(a)/P_1(a),qquad M=-T_0(h)/T_1(h).
]
The remaining two early clocks split precisely when the discriminant of the quadratic
[
rac{P_0(Y)P_1(a)-P_1(Y)P_0(a)}{Y-a}
]
is square, with nonzero leading coefficient. Its unnormalized discriminant is a quartic (D_{m early}(a)). The suffix splits only if (M+2=N(a)/D(a)) is square. With (N,D) coprime of degree six on the tested fibers, this is the degree-twelve square-class test (N(a)D(a)). Distinctness, nonzero leading coefficients, (Wmid T_{mathrm{sc}}), and all the unsolved chronology/rooted-order conditions are not automatic from square splitting.

One can also force two mirrored early clocks (a_pm=mpm t). Writing (P_j(m+T)=sum_k p_{jk}T^k), elimination of (h) gives
[
P_0(m+t)P_1(m-t)-P_1(m+t)P_0(m-t)=2t(E_0+E_1t^2+E_2t^4).
]
The literal (E_i) are in the native theorem `mirrored_ports`. Thus selecting a mirrored early pair reduces to at most a quadratic in (t^2), before the remaining square and chronology tests.

## Whole rational fiber exclusions

In each row (g) exists on the specified chart, the two pivot pairs ((P_0,P_1)), ((T_0,T_1)) are coprime, and **no rational (a)** passes both square tests:

| (m) | (c) | Obstruction modulus |
|---:|---:|---:|
| 3 | 4 | 256 |
| 1 | 3 | 19 |
| 3 | 3/4 | 64 |
| 3 | -3/2 | 64 |
| 1/2 | 1/2 | 81 |
| 3/2 | 5/2 | 23 |
| 3/2 | 3/4 | 13 |
| -1/2 | 3/2 | 47 |
| 1 | 1942/1399 | 19 |
| 2 | 0 | 256 |
| 1 | 2 | 9 |

The missing pivots cannot conceal a finite (h,M) because of the coprime tests. The check extracts the odd-multiplicity polynomial factors, retaining the signed scalar, and multiplies by a square to get integral representatives. Any scalar normalization at the testing prime also removes only an even valuation. At a regular point the removed factors are nonzero: the two quadratic discriminands and suffix denominator are nonzero by distinctness and the chart guards. For a modulus (ell^k), if (ainmathbb Z_{(ell)}) use the ordinary polynomial; otherwise put (s=1/ainellmathbb Z_{(ell)}) and use the reversed polynomial, multiplied by the appropriate even power of (s). If either representative is square over (mathbb{Q}), its value is now (ell)-integral, so its square root is also (ell)-integral. Both charts are reduced modulo (ell^k); each row has an empty intersection. This is a finite proof for an entire rational fiber, not a height cutoff. For instance ((m,c,a)=(3,4,3)) yields four distinct rational early clocks (4,3,6,27/7), but (M+2=6604/1945) is nonsquare.

## Verification

Run `PYTHONDONTWRITEBYTECODE=1 python check-fibers.py` with Python-flint 0.8 and SymPy installed. The exact replay reconstructs all coefficients, checks coprimality, and verifies both primitive homogeneous charts. For the two main rows ((3,4)) and ((1,1942/1399)), it also checks that the coefficients exactly match both native receipts, and tests all residues even in the inverse chart.

`RKCert.Research.SDIRKSevenQuarticPort` formalizes the ring-level forced port and mirrored port identities, square-class transfer (N D=((u-2)D)^2), and the two explicit finite no-simultaneous-square obstructions, using kernel `decide`. The relation of those scalar data to the regular chart and the passage from rational to local projective coordinates are proved in this note and replayed exactly, not asserted as native `HasOrder`-level theorems. This module was typechecked on stock Lean 4.36.0 with the repository's pinned Mathlib. No real or ordered-field exclusion is claimed.
