# No two uniform midpoint end triples at the nowhere-zero SDIRK8 floor

Suppose all ten quadratic residuals are nonzero, the common diagonal is nonzero, and the method has ordinary order at least eight over a characteristic-zero field. Normalize that diagonal to one as in the [two-ended inverse design](../sdirk-eight-two-ended/README.md), with moment interval $[0,2m]$. The chart considered here asks for a literal uniform midpoint chain as the first three rows of the method and also of the chronological weighted adjoint. The opener parameter $u$ in both directions is $2$. There is **no** a priori reflection symmetry or distinct-clock assumption. This chart is impossible.

The six end pairs in actual normalized coordinates are $(1,1/2),(3,1/2),(5,1/2)$ and $(2m-1,G),(2m-3,G),(2m-5,G)$. They follow from the paid first-three-row identities. The last group uses the ordinary weighted adjoint, whose actual residuals are the original reversed residuals divided by $2G$. In particular $G$ cannot equal $1/2$: the quartic defining the saturated pair set would have all six distinct pairs on a single fixed residual level despite being monic of degree four in the clock. Distinct physical pairs are guaranteed by saturation, not assumed for clocks.

Let $t=x-m$ and $\beta=3-m$. The quartic defining equation $U=L_4(t)-g(A_0+A_1t+A_2t^2+Bg)$ has no cubic clock term. Thus at residual $1/2$ its roots are $\beta-2,\beta,\beta+2,-3\beta$ counted with multiplicity, and at residual $G$ they are negatives of the same multiset. The shared quadratic coefficient is $-6\beta^2-4$, so $A_2=0$ and
$$
 6m^2/7=6(3-m)^2+4,\qquad 18m^2-126m+203=0 .
$$
The opposite linear coefficients are $8\beta^3-8\beta$ and its negative. They are nonzero under the quadratic, so $G=-1/2$. The constant coefficients agree, which gives $A_0=0$. The remaining coefficients are
$$
 A_1=-16\beta(\beta^2-1),\qquad
 B=4(3m^4/35+3\beta^4-12\beta^2).
$$

Likewise at residual $1/2$ the quintic weighted equation specializes to a multiple of the monic cubic $(t-\beta)((t-\beta)^2-4)$, and at $-1/2$ it specializes to the negative reflection of that cubic, with potentially different leading multiplier. The quadratic coefficient is nonzero for the monic cubic because $\beta\ne0$. Comparing the quadratic coefficients at the two residuals forces the leading multipliers to agree, hence both are 1 because they have form $1\mp d_3/2$. The linear and constant coefficients then force the $gt$ and $g^2$ terms to vanish. So the equation is
$$
 V=t(t^2-3m^2/5)-g(D+Et^2+Ftg),
 \quad (D,E,F)=(2\beta(\beta^2-4),6\beta,-4(3m^2/5+3\beta^2-4)).
$$
No symmetry of order or times of the four intermediate rows was used.

Eliminate $g^2$ between $U$ and $V$ to obtain
$$
 [B(D+Ew)-FA_1 w]\,g=t[B(w-3m^2/5)-F L_4(t)],\qquad w=t^2.
$$
At the first clock $x=1$, the $g$ coefficient is $(2274704m-5703824)/405$ under the quadratic in $m$. The nonzero exact difference is checked both by `check_pivot.py` and by `RKCert.Research.SDIRKEightDoubleMidpoint.pivot_ne_zero`. Thus any stage at clock 1 must have residual $1/2$.

But the normalized forward relation $Ag=g x$ holds by the first two stage values (the general relation is $Ag=g[1+(x-1)/k]$ with $k=1$). Subtracting $A(1/2)=x/2$, at the first stage where $g_i$ differs from $1/2$, the strict lower entries only read earlier zeros of $g-1/2$. The unit diagonal gives $g_i-1/2=x_i(g_i-1/2)$, so $x_i=1$. At least one such departure exists by the ordinary conditions $\sum b_i=1,\ \sum b_i g_i=0$. The pivot contradiction proves the exclusion.

The coefficient and final pivot proofs are algebraic and apply in all characteristic-zero fields. This does not exclude either a single uniform end or a zero-containing tableau and does not change the unconditional 10–11 interval. Run `python check_pivot.py` with SymPy 1.14 to verify the arithmetic. The native module formalizes scalar trace comparison and the pivot nonvanishing, not the full rooted-order flag bridge.
