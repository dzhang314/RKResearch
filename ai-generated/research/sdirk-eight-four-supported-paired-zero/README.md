# Four physical quadratic zeros exclude every genuine supported graph

Let a strict ten-stage SDIRK tableau with common nonzero diagonal $\gamma$ satisfy ordinary order at least eight over a characteristic-zero field or a field of characteristic greater than seven. Define $\mathbf c=A\mathbf 1$, $\mathbf g=A\mathbf c-\mathbf c^{\odot2}/2$, $C=\operatorname{diag}(\mathbf c)$, $G=\operatorname{diag}(\mathbf g)$, and $U=\ker G$. Suppose exactly four physical entries of $\mathbf g$ vanish. Then **there is no actual supported grade-two vector**
$$\mathbf v=r(\mathbf c)+\alpha\mathbf g\in E_2\cap U,\qquad \deg r\le2,\quad \alpha\ne0.$$
The exclusion does not assume nonzero output weights, real ordering, or prior distinctness of either clock set. It closes a supported graph, not all four-zero tableaux: a supported vector with $\alpha=0$, or a trivial supported space, still requires a separate proof.

## 1. Sharp rank forces three live off-zero pairs

The [both-off-zero-third packet](../sdirk-eight-four-supported-both-off/README.md) gives four facts that do not assume any third-row phase: all four zero clocks are distinct fourth Gaussian nodes with nonzero output weights; off-zero residuals obey the common graph $g=-r(c)/\alpha$; each live off-zero clock has zero aggregate ordinary weight; and there are at least two live off-zero clocks. Use its genuine paid flag spaces and the restriction identity
$$\dim(W_j\cap U_{\rm row})=4-\dim(E_{5-j}\cap U).$$
Here $U_{\rm row}$ consists of rows supported on the four literal zero coordinates. The proof of this identity by the unit diagonal of $M$ and the inclusion $W_j G\subset Z_{j+2}$ works at **both** $j=2$ and $j=3$.

There is a stronger universal silent-row obstruction in this projected graph. Since two distinct live off-zero clocks exist, $F_3=GE_1=\langle\mathbf g,C\mathbf g\rangle$. Weighting $E_3\longrightarrow W_3$ is injective: the first four scalar probes detect the cubic trace if its weighted row vanishes, and the two distinct live off-zero clocks detect its remaining pure correction $\mathbf g$ times an affine polynomial. Both spaces have dimension six, so this is an isomorphism. In particular the restriction of $W_3$ to live off-zero coordinates has rank exactly $n$, the number of distinct such clocks: $n\le3$ since each live site needs at least two live rows, and on the graph the entire six-dimensional degree-three feature set depends only on its clock, with ordinary scalar polynomials already achieving rank $n$ there.

If $n=2$, then $\dim(W_3\cap U_{\rm row})=6-2=4$. The restriction identity at $j=3$ forces $E_2\cap U=0$, contradicting $\mathbf v$. Thus $n=3$. The six off-zero rows are all live, partitioned into three clock pairs each with equal graph residual and opposite weights. In particular **all ten weights are nonzero**. This rules out every silent profile in the present four-zero graph, even in a chronology with a zero third stage. It is separate from the two-ended phase analysis.

The [previous two-ended proof](../sdirk-eight-four-supported-both-off/README.md) now excludes both third stages off-zero. The genuine weighted mirror exists; a zero third is always the arithmetic zero phase with normalized second gap a root of
$$Q(u)=4u^3-12u^2+3u+2.$$
The forward and reflected first two stages are off-zero, at distinct clocks. If just one actual third is zero, reflect as necessary to put the off-zero third forward.

## 2. Just one zero third has no geometric characteristic support

Use normalized forward off-zero gaps $x=(c-\gamma)/\gamma$. Put $\lambda=1/\gamma-2$, so physical $c=1-\gamma$ has gap $\lambda$. Write $u,w$ for the actual forward second and third gaps and $v$ for the reflected second gap. The latter pays $Q(v)=0$, and physical $c_9$ has forward gap $\rho=\lambda-v$. The reflected third zero has centered clock $(4v-\lambda)/(\lambda+2)$ in reflected orientation. Thus its Gaussian gate, before dividing by $\lambda+2$, is
$$L_h(4v-\lambda,\lambda+2)=0,\qquad
L_h(Y,D)=35Y^4-30Y^2D^2+3D^4.$$

Let $\chi(x)$ be the actual ratio $g(x)/g_1$ at a physical off-zero graph site written in gap coordinates, so $\chi(0)=1$, $\chi(u)=\kappa(u)=1+2u-u^2$. If the forward third is star then $w=2-u$, $\chi(w)=\kappa(u)$. If arithmetic then $w=2u$ and
$$H(u)\chi(w)=H(u)\kappa(2u)+4u^2(3u-2),\qquad H(u)=-2+u+4u^2-u^3.$$
The true backward second ratio requires
$$\chi(\rho)=\kappa(v)\chi(\lambda).$$
This is a literal equality of graph residuals, not an equality of quadrature aggregates.

When $\gamma=1/2$, forward and backward first clocks coincide. Their physical second clocks cannot coincide: one would otherwise need $\kappa(u)=\kappa(-u)$. The reflected second physical clock is then the other forward off-zero clock (its third), so $\rho=w=-v$. A star gives $u=2+v$, arithmetic gives $u=-v/2$. Here $\lambda=0$. These are the first two exact cases below.

When $\gamma\ne1/2$, write $z$ for the normalized forward gap to the third graph clock other than $\gamma,1-\gamma$. The forward pair $\{u,w\}$ is $\{\lambda,z\}$ and the reflected second gap is one of $\lambda,\lambda-z$. The literal phase relation gives the following eight cases:

| Forward phase | $(u,w)$ | $z$ | $\lambda$ if $v=\lambda$ | $\lambda$ if $v=\lambda-z$ |
|:--|:--|:--|:--|:--|
| Star 1 | $(\lambda,z)$ | $2-\lambda$ | $v$ | $(v+2)/2$ |
| Star 2 | $(z,\lambda)$ | $2-\lambda$ | $v$ | $(v+2)/2$ |
| Arithmetic 1 | $(\lambda,z)$ | $2\lambda$ | $v$ | $-v$ |
| Arithmetic 2 | $(z,\lambda)$ | $\lambda/2$ | $v$ | $2v$ |

In the first column choice $\rho=0$, in the second $\rho=z$. After inserting these expressions, the graph ratio and Gaussian gate are both polynomials in $v$ after clearing $H(u)$ in the arithmetic cases; the only constant denominators in them are paid. In all ten cases the gcd of the exact resultant numerators of the two gates against $Q(v)$, after stripping only primes $2,3,5,7$, is **1**. This means no algebraic $v$ in any paid characteristic can satisfy them simultaneously. There is no finite-prime list or square-root assumption in this case.

## 3. Both zero thirds: exact scalar support

Now $Q(u)=Q(v)=0$ for the two actual second gaps. In the mid-diagonal case $\gamma=1/2$ again the two physical second clocks differ. The three centered off-zero sites are $0,u,-v$ and the endpoint zero clocks are $2u,-2v$ in original orientation.

For $\gamma\ne1/2$, keep the normalized gaps $\lambda,z$ as above. The forward second is $\lambda$ or $z$; the reverse second is $\lambda$ or $\lambda-z$. If both second gaps equal $\lambda$, then $u=v=\lambda$ and the reciprocal endpoint graph ratios force $\kappa(u)^2=1$, which contradicts $Q(u)=0$ by the native Bézout scalar receipt in the [both-off packet](../sdirk-eight-four-supported-both-off/README.md). The remaining three choices give:
$$
(\lambda,z)=(u,u-v),\quad (v,u),\quad (u+v,u).
$$
Distinctness excludes $u=v$ in the first two, but not the third. The two physical Gaussian zero pins are
$$ L_h(4u-\lambda,\lambda+2)=L_h(4v-\lambda,\lambda+2)=0 .$$

For unequal $(u,v)$ the primitive coordinate $\theta=u+2v$ represents all six ordered pairs: its two-variable equations are $Q(u)=0$ and the literal quadratic quotient $(Q(v)-Q(u))/(v-u)=0$. The code verifies these coordinate relations in the original quotient and guards every coefficient in the reductions. All denominators are paid. The equal-gap case can use the same model through its $u$ coordinate, which covers all three cubic roots. The gcd of the two Gaussian norm numerators has the following stripped support, with every exponent included:

| Actual choice | $u\ne v$ | $u=v$ |
|:--|--:|--:|
| $\lambda=0$ for $\gamma=1/2$ | $267613^2$ | $267613^2$ |
| $\lambda=u,\ z=u-v$ | 1 | impossible by distinctness |
| $\lambda=v,\ z=u$ | 1 | impossible by distinctness |
| $\lambda=u+v,\ z=u$ | $4271\cdot8150279\cdot16397761$ | $3517^2$ |

No field requires ordering or prime-field gaps. The nesting is via ordinary resultants with guarded leading coefficients and all algebraic gap pairs are represented.

## 4. Only two finite anchored controls, both rejected by the same odd block

In each listed characteristic, the code tests the exact Gaussian pins in a full splitting field of **both** $Q$ and $35y^4-30y^2+3$ (least common multiple of factor degrees), with literal clock distinctness and actual nonzero gap ratios. It also reconstructs the common quadratic graph by interpolation at its three off-zero clocks. At $\gamma=1/2$ the centered site values, normalized by $g_1$, are $(1,\kappa(u),\kappa(v))$ on $(0,u,-v)$. In the $\lambda=u+v$ case they are $(1,\kappa(u)/\kappa(v),\kappa(u))$ on $(-\lambda/(\lambda+2),\lambda/(\lambda+2),(u-v)/(\lambda+2))$. The ordinary paid anchors are $Jr_c(a)=\gamma r_c(a)$ and $J^*r_c(b)=\gamma r_c(b)$ at the first and last physical zero. Here $J$ is the centered half-density primitive and $r_c$ is the interpolated graph, proportional to the supported trace.

Only two anchored controls remain:
* Characteristic 267613: $\gamma=1/2$, $u=v=168562$, outer zeros $69511,198102$.
* Characteristic 3517: $\gamma=1800$, $u=v=338$, outer zeros $3435,82$.

In both controls the centered outer clocks are opposite; the interior Gauss clocks are therefore another opposite pair $\pm y$. The graph is even, $r_c(y)=R_0+R_2 y^2$, with three centered off-zero clocks $0,\pm s$, $s\ne0$. The precise value of $s$ need not equal $2\gamma-1$ in the mid-diagonal case. The degree-three supported odd traces $y r_c(y)$ and $y(y^2-s^2)$ furnish the two actual odd coordinate pair indicators as in Section 4 of the [both-off proof](../sdirk-eight-four-supported-both-off/README.md). The same calculation uses the *principal ordered four-zero submatrix* even when off-zero stages intervene. Their support is literal, so the extra stages contribute nothing to the paid bilinear reads. The actual constant-diagonal read and inner/outer odd contractions thus force
$$
y^2(R_0+R_2y^2/3)^2-(2\gamma)^2(R_0+R_2 y^2)^2=0.
$$
It has exact nonzero residues **241314** and **2937** at the two controls. This excludes either order of the inner clocks.

## Domain and replay

The three phase cases above and in the previous proof exhaust the three-live-pair chart; the rank argument in Section 1 excludes all its silent alternatives independently of chronology. Neither $\alpha=0$ nor $E_2\cap U=0$ is claimed impossible here. In a nonzero commutative coefficient ring with $8!$, $\gamma$, $\alpha$ and all six off-zero residuals units, maximal-ideal reduction preserves this exact supported graph and zero count, so gives the same exclusion. This is a conditional ring corollary, not a result for arbitrary nonunit support.

Run `python check_one_zero.py`, `python check_both_norms.py` and `python check_both_fibers.py` with SymPy 1.14 and Python-flint 0.8. The latter checks exact primality and all splitting-field constraints. `RKCert.Research.SDIRKEightFourSupportedPairedZero` contains the reflected scalar ratio and homogeneous clock identities and the native nonzero pin residues. The full support-rank, causal reduction, and algebraic-closure arithmetic are the exact source proof and replays, not a single native `HasOrder` theorem. Stock Lean/Mathlib 4.36.0 audit attached.
