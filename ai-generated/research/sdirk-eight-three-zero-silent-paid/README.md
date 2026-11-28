# No silent quadratic-zero row in the paid three-distinct supported graph

Consider a strict ten-stage SDIRK tableau of ordinary order at least eight over a field of characteristic zero or greater than seven, with nonzero common diagonal $\gamma$. Write $c=A1$, $g=Ac-c^{\odot2}/2$, $C=\operatorname{diag}(c)$, $G=\operatorname{diag}(g)$ and $M=CA-AC-A^2$. Suppose precisely three entries of $g$ vanish, at three different clocks, and a nonzero grade-two vector is supported on those physical coordinates. By the [constant-trace](../sdirk-eight-constant-zero-trace/README.md) and [affine/null](../sdirk-eight-affine-null-trace/README.md) exclusions, it must be $v=r(c)+\alpha g$ with a monic quadratic $r$ and $\alpha\ne0$.

**Result.** All ten output weights are nonzero in this stratum. In particular the quadratic signed moment Hankel on the three zero clocks is nonsingular. This eliminates the silent or singular branch, not the all-active quadratic graph, the zero-free case, or any larger physical zero set.

## 1. There could only be one silent zero and it would have to be first among the zeros

The seven off-zero rows are all live and at distinct clocks. Otherwise the ordinary paid moments $b^{\mathsf T}C^j g=0$, $0\le j\le5$, on at most six live off-zero clock groups would make every off-zero group have zero ordinary aggregate (since $g$ is a nonzero function of its clock). The ordinary scalar quadrature has rank four, impossible on only three other clocks.

Let $U=\ker G$, $B=\operatorname{diag}(b)$, and use the [saturated flags](../../lower-bounds/characteristic-zero/sdirk_saturated_weighted_mirror_duality_20261123.md) and their paid algebraic versions. The supported row $v^{\mathsf T}B\in W_2$ has trace $r$ and is nonzero at at least two of the three zero coordinates. Otherwise the product of the single supported clock's linear nodal factor and $r$ would be a nonzero cubic killed by the degree-three Hilbert form. The same argument applies if that row is zero.

In fact $v$ itself is nonzero at all three zero coordinates: if it had exactly two nonzero coordinates, both would have nonzero weights by the preceding argument. Then the weighted grade-three vectors $v^{\mathsf T}B$ and $v^{\mathsf T}CB$ separate those two coordinates. Since $Mv\in F_4=\operatorname{Ann}(W_3)$, it would vanish there. This is impossible at the first nonzero coordinate of $v$, since $M$ is lower triangular with diagonal $-\gamma^2$. Thus all three values $r(c_i)$ on $U$ are nonzero.

If a silent stage remains, then it is one of the three zeros and exactly two zero weights are nonzero. At the latter two coordinates $F_4=\operatorname{Ann}(W_3)$ is clean, by the identical weighted separation argument. At the earliest physical zero $Mv$ has nonzero entry $-\gamma^2r(c_i)$, so that row must be the silent one. Call its clock $s$; let $a,b$ be the two live zero clocks in chronological order. The trace $r$ of the supported weighted row, multiplied by $(X-a)(X-b)$, is orthogonal to all degrees at most three. Therefore $a,b$ are simple fourth Gauss clocks and $r=L_4/[(X-a)(X-b)]$.

## 2. The literal silent read and the two local ends

There are at least two distinct active off-zero clocks, so $E_1\cap U=W_1\cap U_{\rm row}=0$ and $F_3=GE_1$, $Z_3=W_1G$ are clean at all zeros. Applying $A$ to the supported column at the earliest physical zero, and right multiplication by $A$ to the supported row at the latest live zero, gives
$$ (Jr)(s)=\gamma r(s),\qquad \gamma=(J^*r)(b)/r(b).$$
Here $J$ is the primitive from zero and $J^*r=I(r)-Jr$. The first live zero $a$ is clean in $F_4$. The degree-three and degree-four reads of $Av$ and $A(Cv)$ there have only one earlier supported input, from the actual silent zero at $s$. This gives
$$
A_{a,s}r(s)=D,\quad s A_{a,s}r(s)=N,\quad
D=(Jr)(a)-\gamma r(a),\quad
N=(J(Xr))(a)-\gamma a r(a),
$$
where the subscript denotes the actual chronological positions, not a clock-indexed tableau. Thus $D=0$ requires $N=0$; otherwise $s=N/D$. This is *not* the earlier exactly-two-physical-zero chart, whose silent row was off-zero and did not have to satisfy the $Jr(s)$ anchor.

Both first and last physical pairs are off-zero. At the first pair, $g_1=\gamma^2/2$, and $g_2=0$ would give $\kappa=0$ in the actual front equation $(C-\gamma I)g=\kappa(A-\gamma I)g$, localizing all off-zero clocks to $\gamma$. At the rear, the last weight is nonzero, $b^{\mathsf T}G$ spans $Z_2$, and the last residual is nonzero (otherwise all live clocks would be zero clocks). The second-to-last weight is nonzero and clock distinct by the actual grade-one reverse read and full reverse rank. The literal column-nine read of $(b^{\mathsf T}G)A\in Z_3$ then forbids it from being a quadratic zero, since the last-to-penultimate tap is nonzero. The latest live zero is therefore at most row eight and the earlier silent zero at most row six. In particular the last three weights are all nonzero; their weighted reflected block is legitimate regardless of any omitted normalization at $s$.

At either end, use $r_e=r(X)$ or $r(1-X)$ respectively, $R_e=r_e(\gamma)\ne0$, and $k_e$ its linear coefficient. The normalized second gap $u$ is given by the linear read
$$ (R_e+\gamma^2)u=2R_e-\gamma(2\gamma+k_e).$$
The live reflected end and the actual front end both obey the [literal first-three identities](../clock-localized-tail/tied-stage-floor/FIRST-THREE-ROWS-AND-PHYSICAL-LEVEL-OBSTRUCTIONS.md), with no restriction on the front weight. An off-zero third can only be a star or arithmetic graph read. A zero third is arithmetic with gap $2u$ and $4u^3-12u^2+3u+2=0$; at the front its clock must be $s$, at the rear its original clock must be $b$. All such alternatives, including both second-gap denominator/numerator zero, are retained.

## 3. Homogeneous norms and complete exceptional check

Use the same nonmirror ordered-pair algebra as the [two-clock packet](../sdirk-eight-two-clock-triple-paid/README.md), with primitive generator $\theta=a+2b$. The replay checks that the original two-variable Gauss equations imply the coordinate-polynomial identities in $\theta$; it also guards every denominator in the reduction quotients, in the gates, and in the inverse $1/r(b)$. The only nonpaid coordinate prime is 13, which is tested directly. A mirror pair can use the same $\theta$ algebra after first picking a nonmirror partner of $a$ in the algebraic closure.

For the nonmirror pair with $D\ne0$, multiply the chronological silent-anchor equation by $D^3$ to give the polynomial
$$D^3[(Jr)(N/D)-\gamma r(N/D)]=0.$$
The star and arithmetic graph polynomials at both ends are homogenized in the second-gap numerator and denominator before taking norms. For a zero third the cubic and the corresponding position pin must both vanish, so take the gcd of their norm numerators. At the front that pin is $N d_f-\gamma D(d_f+2n_f)$, where $d_f,n_f$ are the actual second-gap denominator/numerator. At the rear use $(1-b)d_r-\gamma(d_r+2n_r)$. Both ends also retain the gcd of their second-gap denominator and numerator norms. The gcd of the nonmirror homogeneous silent-anchor norm and both chronological products has no prime support beyond $2,3,5,7,13$. The separate nonmirror gcd of norms of $D,N$ has the same property.

For mirror pairs $D$ is identically zero, so $N=0$ is necessary. The joint gcd of the norm of $N$ and the rear chronological product, after stripping $2,3,5,7,13$, is exactly $19^2$. For p13 and p19 the direct geometric census is performed in the finite field splitting all four distinct Gauss roots and tests all twelve oriented pairs. For p13 no anchors remain. In p19 the single anchor candidate is $(a,b,\gamma)=(3,17,4)$, with $D=N=0$ and no restriction on the silent clock from this quotient; it already fails the actual rear graph and zero-third gates. The code additionally checks the old possible mirror-$N$ prime 137 directly, with no rear survivor. No extension with an extra root for $s$ can revive a candidate rejected at the rear. The census includes any nonsplit ambient field because the normalized pair lies in its algebraic closure and the gates there specialize through the complete finite splitting field.

Thus no silent branch survives. All three signed coefficients $b_i r(c_i)$ on $U$ are nonzero. The $3\times3$ moment matrix of $I(r\,\cdot)$ through degree four factors as their diagonal between a three-site Vandermonde and its transpose, so is nonsingular.

## Reproducibility and verification scope

Run `python check_norms.py` and `python check_primes.py` with SymPy 1.14 and Python-flint 0.8. `RKCert.Research.SDIRKEightSilentQuadratic` proves the two-site clean-read linear inference, its anchor homogenization, and the literal characteristic-19 rear scalar rejection. The full support and chronology reduction and the norm replay remain the source proof above, not one end-to-end native `HasOrder` theorem. See `proof-audit.lean` for the Lean/Mathlib 4.36.0 check.
