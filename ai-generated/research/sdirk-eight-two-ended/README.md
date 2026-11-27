# Two-ended inverse design at the nowhere-zero SDIRK8 floor

This note develops a nonsymmetric route to a ten-stage strict SDIRK8 construction. It gives a finite obstruction, **not** a real or real-algebraic upper improvement:

> Over each of $\mathbb F_{11},\mathbb F_{13},\mathbb F_{17},\mathbb F_{19},\mathbb F_{23}$, no ten-stage strict SDIRK method of order at least eight has every quadratic residual nonzero.

Both ends can be either stars or cross-fed, with different shapes. Repeated clock values are allowed, provided the two-coordinate pairs are distinct as required by saturation. The result does not exclude a ten-stage tableau with a quadratic zero over these fields. It makes no general restriction on characteristic-zero tableaux: reduction may introduce zeros or land in an extension of a residue field.

## The two physical ends

The [tied-floor two-coordinate flags](../clock-localized-tail/tied-stage-floor/README.md) give
$$
(\dim E_j)_{j=0}^6=(1,2,4,6,8,9,10),\qquad F_{j+2}=G E_j,\quad G=\operatorname{diag}(\mathbf g),
$$
when the ten-stage tableau is nonsingular and all its quadratic residuals are nonzero. After dividing $A,c,g$ by $\gamma,\gamma,\gamma^2$, respectively, the common diagonal is 1 and the formal scalar moment is the average on $[0,2m]$, with $2m=1/\gamma$. The moment and complete-intersection arguments extend to any characteristic greater than seven: the normalizing factorials through order eight are units; the scalar Hilbert minors needed have size at most four, with nonzero determinants whose numerators/denominators have only primes at most seven. The monic shifted $L_4,L_3$ are coprime from the three-term recurrence and the norm of $L_3$ is $(2m)^6/2800\ne0$. The substitution $g=t^2$ gives two distinct points for each nonzero $g$ over the algebraic closure; the same degree-four by degree-five Bézout equality shows all ten pairs are distinct and the two-coordinate points simple. Each weight is therefore nonzero by $b_i g_iJ_i=-\|L_3\|^2$. This uses no ordered-field positivity.

Let $A^\dagger=\operatorname{diag}(b)^{-1}A^{\mathsf T}\operatorname{diag}(b)$, with pairing $\langle f,h\rangle_b=\sum_i b_i f_i h_i$. For $f\in E_j$ and $h\in E_{6-j}$, the true scalar primitives and integration by parts in the normalized moments show
$$
 \langle A^\dagger f-J^* f,h\rangle_b=0,
 \qquad J^*f(x)=\int_x^{2m} f(t,0)\,dt.
$$
Indeed $A h-Jh$ is a pure error of grade at most $7-j$ and is killed in pairing against $f$, and scalar trace products through grade seven are paid. The space orthogonal to $E_{6-j}$ is exactly $G E_{j-1}$ by the dimensions and the paid pure products. Thus the reverse chronological weighted adjoint, after reflecting clocks, also has true primitive lifting through grade six. At grade zero its clock is $2m-c$. At grade one its quadratic residual is a constant multiple of $g$ by $A^\dagger f-J^*f\in G E_0$. The actual first reversed row has unit diagonal and residual $1/2$, so the reflected residual is $g/(2G_*)$, where $G_*=g_{10}$ is the literal terminal residual. The mixed moments and extension step then give ordinary order eight for the reverse method. Equivalently, only the two low-grade flags and the fourth-row gate of the reverse method are needed here.

Write the first three normalized pairs as $(1,1/2),(1+u,k/2),(1+w,q/2)$, with $k=1+2u-u^2$ and $q=1+2w-w^2+2ru$, where $r=a_{32}$ in normalized coordinates. The same [paid first-three gates](../clock-localized-tail/tied-stage-floor/FIRST-THREE-ROWS-AND-PHYSICAL-LEVEL-OBSTRUCTIONS.md) hold in these characteristics:
$$
 r u(2u-w)=0,\qquad wq=k[w+r(k-1)].
$$
In the star case $r=0$, distinct pairs force $w=2-u$ and $u\notin\{0,1,2\}$. Otherwise $w=2u$ and
$$
r=\frac{2u(3u-2)}{-2+u+4u^2-u^3}.
$$
The denominator cannot be zero in the mixed case: if it were then $u=2/3$, where the denominator is $4/27\ne0$. The six end pairs are defined from independent forward/reflected choices of these opener data and the nonzero parameter $G_*$. In actual chronological order the three reflected pairs are taken in reverse order, with $x\mapsto2m-x$ and $g\mapsto2G_* g$.

## Recovering all remaining pairs and checking chronology

In normalized centered coordinate $t=x-m$, the complete intersection has equations
$$
  U=L_4(t)-g[A(t)+B g],\qquad V=L_3(t)-g[D(t)+F(t)g],
$$
where $A,D,F$ have degrees at most $2,3,1$. Its leading forms must be coprime: at infinity this is checked by $B\ne0$, the nonvanishing of the degree-five part of $V$, and that no root of $D_3+F_1q=0$ also has $1-A_2 q-Bq^2=0$. At $t=0$ at infinity, $B\ne0$ already separates; at $g=0$ the quartic leading form is nonzero. The six end pairs impose linear constraints on the four coefficients of $U$ and the six of $V$.

The actual forward fourth pair obeys a local gate. If $T(x)=a+bx+cx^2$ matches the first three residuals, put $J_T=ax+bx^2/2+cx^3/3$, $\Lambda=1+(x-1)/k$ and $\Delta=4/3+2(k+1)(x-1)/(3k)$. The genuine relations $Ag=g\Lambda$, $Ax^2-x^3/3=g\Delta$ follow from $F_3=G E_1$, using the first two actual rows. Since $g-T$ vanishes at the first three rows, the diagonal requires
$$
 g-T(x)+J_T(x)-g[\Lambda(x)-b-c\Delta(x)]=0
$$
at row four. Apply the identical gate at the actual fourth reflected pair (row 7 in the original ordering). These tests do not assume the other residuals have the same level or an imposed sign.

For positive search, given both fourth pairs, if the decic projection is regular an explicit shortcut for the two middle clocks is
$$
 P(t)=B D(t)-F(t)A(t),\quad Q(t)=B L_3(t)-F(t)L_4(t),\qquad
 U_{\rm proj}=L_4 P^2-AQP-BQ^2.
$$
When $P$ is nonzero at each pair, $g=Q/P$ and the eight known clocks divide the decic, leaving a quadratic if all clocks are distinct. This is an inverse-design shortcut, not assumed in the finite exclusion. Over the finite fields the replay instead enumerates all common pairs with any clock, including repeated clock values and zero projection pivots. If the six end pairs do not already determine both polynomials, it enumerates both fourth pairs satisfying their affine gates, solves all eight-pair linear constraints, and enumerates every remaining affine coefficient choice. Thus rank-deficient end fits are included. The last two sites have two possible assignments; for a unique six-pair fit, every permutation of its four other pairs is tested.

For each remaining placement, use the [exact prefix reconstruction criterion](../clock-localized-tail/tied-stage-floor/EXACT-PREFIX-DIAGONAL-RECONSTRUCTION.md). At stage $i$ choose the least $j$ and a polynomial $f\in E_j$ with prefix values $(0,\ldots,0,1)$. Solve the linear membership problem requiring $(\delta_{ik}-Jf(x_k))/g_k$ on the prefix to belong to the restricted $E_{j-1}$. A true triangular diagonal-one tableau must pass, for every choice of $f$. The code takes a deterministic choice by exact modular elimination. The arithmetic excludes all remaining placements.

## Exact replay

Compile `c++ -std=c++17 -O3 exact_finite.cpp -o /tmp/sdirk8-two-ended` and call the binary with one of the primes below. The counts, including the two rank-deficient fit stages, are:

| Prime | Six-pair parameters | Unique consistent fits | Rank-deficient fits | Affine eight-pair completions | Unique-fit ten-pair sets | Placements passing both fourth tests |
|---:|---:|---:|---:|---:|---:|---:|
| 11 | 20714 | 406 | 0 | 0 | 39 | 0 |
| 13 | 54324 | 644 | 31 | 4 | 42 | 14 |
| 17 | 142606 | 1118 | 0 | 0 | 78 | 8 |
| 19 | 343617 | 1788 | 18 | 0 | 144 | 18 |
| 23 | 650891 | 3086 | 25 | 4 | 172 | 38 |

All listed fields give zero accepted full chronologies. No probabilistic tests or parameter-height cutoffs enter the result. The C++ search distinguishes unique consistent linear fits before checking leading forms, and the eight-pair count includes all affine completions before those checks.

For $\mathbb F_{11}$, run `PYTHONDONTWRITEBYTECODE=1 python check_f11.py` (no third-party packages). It independently enumerates literal third-row taps rather than their rational branch formulas, finds all 39 ten-pair cases, verifies both causal gates by direct quadratic interpolation, and matches the data in `RKCert.Research.SDIRKEightTwoEndedF11`. Its Lean kernel receipt certifies that no two distinct outside pairs in these literal supplied cases can pass both physical fourth gates. The exhaustive generation of those cases and the bridge to `HasOrder` are algebraic arguments and exact external replays, **not** native Lean theorems.
