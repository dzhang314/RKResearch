# A universal thirteen-stage explicit method of exact order eight

Let $R$ be a nonzero commutative unital ring. A factorial-cleared
explicit Runge–Kutta method of exact order eight exists over $R$
if and only if $8!$ is a unit. The eight-vertex tall-tree equation
forces this condition for any stage count. The tableau here
proves sufficiency in **thirteen stages**. If $41$ is also a unit,
the original twelve-stage method works. The construction does
not prove a stage minimum or change the established real upper bound.

## Tableau

Each row lists the numerators of its strict predecessor coefficients,
divided by the indicated denominator.

| Stage | Numerators | Denominator |
|:---|:---|---:|
| 1 | none | 1 |
| 2 | 1 | 9 |
| 3 | 1, 3 | 24 |
| 4 | 1, 0, 3 | 16 |
| 5 | 29, 0, 33, −12 | 500 |
| 6 | 33, 0, 0, 4, 125 | 972 |
| 7 | −21, 0, 0, 76, 125, −162 | 36 |
| 8 | −30, 0, 0, −32, 125, 0, 99 | 243 |
| 9 | 1175, 0, 0, −3456, −6250, 8424, 242, −27 | 324 |
| 10 | 293, 0, 0, −852, −1375, 1836, −118, 162, 324 | 324 |
| 11 | 1303, 0, 0, −4260, −6875, 9990, 1030, 0, 0, 162 | 1620 |
| 12 | 0, 0, 0, 0, 0, 3, 2, 0, 0, 3, 0 | 8 |
| 13 | −8595, 0, 0, 30720, 48750, −67716, −702, −729, −1944, −2916, 3240, 0 | 108 |

$$
 \mathbf b\coloneqq \frac{1}{840}(41,0,0,0,0,216,272,27,27,36,180,40,1).
$$

## The row split

The first eleven stages are from E. Baylis Shanks,
[*Solutions of Differential Equations by Evaluations of Functions*](https://doi.org/10.1090/S0025-5718-1966-0187406-1),
*Mathematics of Computation* 20 (1966), 21–38. The original final
row $\mathbf a$ has denominator $4428=108\cdot41$ and its output
weight is $41/840$. All other coefficients already belong to
$\mathbb Z[1/210]$.

The new parallel baseline row $\mathbf r$ taps stages 6, 7, and 10
with weights $3/8,1/4,3/8$ at their clocks $1/6,1/2,5/6$.
Their stage weights for every tree $u$ of size at most four are
the exact polynomial values $|u|c^{|u|-1}/u!$. The three new row
weights integrate each polynomial of degree at most three over
$[0,1]$. Thus $\mathbf r$ reads $1/u!$ on each of the eight
child trees of size at most four. Direct evaluation shows that
$\mathbf a$ has those same reads.

Let $P_t(z)$ be the stage weight of tree $t$ with row
$\mathbf r+z(\mathbf a-\mathbf r)$ acting on the unchanged first
eleven stages. Only children of size at least five can give a
factor that depends on $z$. Through size nine there is room for
at most one such child, so $P_t$ is affine and
$$
  \frac{41}{840}P_t(1)
  =\frac{40}{840}P_t(0)+\frac{1}{840}P_t(41).
$$
The two weights on the right go to stages 12 and 13, whose rows
are $\mathbf r$ and $41\mathbf a-40\mathbf r$. Neither row
depends on the other. The new tableau preserves every tree
output through order nine while eliminating the denominator
prime $41$.

## Exact order and base change

The [exact checker](check.py) verifies the two rows' low tree
reads, all 200 rooted equations through order eight, and equality
of all 486 old and new outputs through order nine. For the
nine-vertex bush the weighted output is $4321/38880$ and the
tree factorial is $9$, giving the cleared defect $1/4320$.
This is a unit of $\mathbb Z[1/210]$.

The verified cleared identities over $\mathbb Q$ hold in
$\mathbb Z[1/210]$, where every new coefficient lies. If $8!$
is a unit in $R$, that coefficient ring maps into $R$ and sends
the unit defect to a nonzero element. This proves exact order
eight without any extra required prime. The check is exact
arithmetic; no Lean upper certificate is claimed.
