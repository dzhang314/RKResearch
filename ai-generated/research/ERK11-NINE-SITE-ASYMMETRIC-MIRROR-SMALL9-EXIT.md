# Mirrored variable edge: exclude the bidegree-(9,12) width component

**Scope.** In the [mirrored finite chart](ERK11-NINE-SITE-ASYMMETRIC-MIRRORED-FINITE.md)
take left extras $\{t,s\}$, right extras $\{h,t\}$ and literal
$c_8=z$ dormant, $c_9=e,c_{10}=s$. Its affine slope is known
live. The singular mixed determinant is already excluded by the
[A0=0](ERK11-NINE-SITE-ASYMMETRIC-MIRROR-RANK-A0-EXIT.md) and
[A0-live](ERK11-NINE-SITE-ASYMMETRIC-MIRROR-RANK-LIVE-A-EXIT.md)
proofs. The new two-factor width split excludes its smaller
component over characteristic zero. The larger component and
the asymmetric opposite central order are separate.

## Two compatibility polynomials without a new scalar pivot

Write $(L_0,L_1)$ and $(R_0,R_1)$ for the actual scaled derivative
rows of the preceding atlas. Put $T_a=T_4(a)$, $T_b=T_4(b)$,
$U=U_{4,4}(a,b)$, and $k_j=K_j(z)$. The first actual mixed
contact and the dormant left physical-8 port give
$$
 (L_0+T_aL_1)R_0+(T_bL_0+UL_1)R_1=0,\qquad
 k_0R_0+k_1R_1=0.
$$
Multiply the first by $k_0$ and use the second. As $R_1$ is
a live product of actual clock differences, this gives
$$D=k_0(T_bL_0+UL_1)-k_1(L_0+T_aL_1)=0.$$
No particular kernel coefficient is required to be nonzero.

Let $x_0,x_1$ be the actual weighted right half-at-9 mark
coefficients, so $x_0L_0+x_1L_1=0$. They are exactly the rowe
coefficients in the finite chart's regular data: their two terms
come from $b(C_1-sH)K_j^R(e)$ and
$30(1-e)(e-d)(e-s)J_0\langle D_L^j,r_d\rangle_N$,
homogenized in the already-live affine slope.
Combining these with the first contact and dormant port gives
$$
 K=x_1k_1-T_a x_0k_1-T_b x_1k_0+U x_0k_0=0 .
$$
Indeed multiply by $L_1R_1$, substitute the two homogeneous
port equations, and the answer is the first contact times $x_0k_0$.
Only the actual live $L_1R_1$ is canceled.

After removing listed live factors, the $z$-resultant of $D,K$
has bidegree $(88,94)$ in $(b,a)$. Its factors from $J_0,R_{33}$
are already live by the excluded mixed determinant drop.
The remaining factorization is precisely one component each of
bidegrees $(9,12)$ and $(51,54)$, both simple. Thus the present
polynomial $C_9$ of bidegree $(9,12)$ is an actual width
alternative, not an extra assumption about a generic width.

## Exact smaller-component exit

Let $W_{DQ},W_{DE}$ be the normalized $z$-resultants with the
free quadratic and right weighted half mark respectively, with
the known live factors $J_0,R_{33}$ also removed. At an actual
width on $C_9=0$,
$$
 r_Q=\operatorname{Res}_b(C_9,W_{DQ}),\qquad
 r_E=\operatorname{Res}_b(C_9,W_{DE})
$$
both vanish. Use primitive integral representatives. At 103
the generic $b$-degrees in both constructions are retained.
The residue $a$-degrees are 1518 and 1200, and their gcd is
the unit. This is sufficient over characteristic zero after
checking **one** leading degree: the first scaled Sylvester
matrix has exact upper degree 1524, and two successive
nullities 3, 3 at infinity. Thus $r_Q$ has exact degree 1518
and its lead is a 103-adic unit. Any actual $a$ would be
algebraic and integral at a place over 103 by that leading
term, but its residue would be a common root of the two
residue projections. This is impossible; no hypothesis on
the integrality or even the specialized degree of the other
width is needed.

Run the standalone Python replay with SymPy, python-flint,
NumPy and SciPy. SciPy proposes integer Sylvester scalings,
which the receipt checks in exact arithmetic. The actual
tableau and finite-place proof are not claimed native Lean.

The [standalone exact source and independent replay log](erk11-nine-site-asymmetric-mirror-small9-exit/) are included.
