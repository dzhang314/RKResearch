# The graph with no active off-zero clock cannot have a long off-zero prefix

Let $A,\mathbf b$ be a strict ten-stage SDIRK tableau of ordinary order at least eight with common nonzero diagonal $\gamma$ over a field of characteristic zero or greater than seven. Set $\mathbf c=A\mathbf1$, $\mathbf g=A\mathbf c-\mathbf c^{\odot2}/2$, $C=\operatorname{diag}(\mathbf c)$ and $U=\ker\operatorname{diag}(\mathbf g)$. Assume exactly five physical zeros, genuine graph support, and no active off-zero stage.

**Result.** The first five positions cannot all be off-zero over any paid field. If the first four positions are off-zero, the graph and chronology are forced into one of two monomial forms over every paid field. Both monomial forms are impossible over every characteristic-zero field. Thus in characteristic zero the first physical zero in this chart must be literal row 3 or 4. No exclusion of those remaining two positions or general ten-stage exclusion is claimed.

## 1. Structural monomial reduction over paid fields

By [four-ordinary-site exclusion](../sdirk-eight-five-zero-graph-four-ordinary-duplicate/README.md), all five physical zero rows are live at five distinct clocks. By the [off-clock rank exclusion](../sdirk-eight-five-zero-graph-distinct-off/README.md), the five off-zero clocks also are distinct. Use $A'=A/\gamma$, $\mathbf x=\mathbf c/\gamma$, $C'=\operatorname{diag}(\mathbf x)$, $\boldsymbol\eta=\mathbf g/\gamma^2$, and $D=1/\gamma$. Write $\mathbf q=P(\mathbf x)-\boldsymbol\eta$ for the actual supported graph column, where $P$ is a nonzero polynomial of degree at most two and $P(1)=1/2$. On every off-zero row $\eta_i=P(x_i)\ne0$.

The normalized commutator $M'=C'A'-A'C'-A'^2$ takes $E_2$ into $F_4$. Its diagonal is $-1$, so $(M'\mathbf q)|_U$ is nonzero at the earliest nonzero coordinate of $\mathbf q$ in $U$. The normalized fourth Legendre polynomial is
$$L(T)=70T^4-140DT^3+90D^2T^2-20D^3T+D^4.$$
Its clock vector belongs to $F_4$ by the paid pairing and ordinary Legendre orthogonality. Its value on $U$ is nonzero because five distinct clocks cannot all be roots of a quartic. Since $GE_2$ vanishes on $U$ and has codimension one in $F_4$, the two nonzero restrictions of $M'\mathbf q$ and $L(\mathbf x)$ span the same line. Hence for one fixed polynomial $H_2$ of degree at most two,
$$ L(x_i)=P(x_i)H_2(x_i)\quad\text{at any off-zero position where }(M'\mathbf q)_i=0.$$
Indeed the difference of the two pure vectors is in $GE_2$, where the graph makes every off-zero value $P$ times a polynomial of degree at most two.

Also $A'\mathbf q$ has scalar primitive $JP$ and some pure grade-three part in $F_3=GE_1$. On any off-zero row its value is therefore $JP(x_i)+P(x_i)H_1(x_i)$ for a fixed affine $H_1$. Before the first zero, $\mathbf q$ is zero on the actual prefix, so both $A'\mathbf q$ and $M'\mathbf q$ vanish there.

If all five off-zero rows are at the front, their five distinct clocks force both polynomial identities
$$ L=P H_2,\qquad JP=-P H_1.$$
The first identity forces $\deg P=2$ and $P(0)\ne0$. Write $JP=P(\alpha T+\beta)$. Since $JP(0)=0$ we get $\beta=0$; the leading cubic coefficient gives $\alpha=1/3$ while the linear coefficient gives $\alpha=1$. This is impossible in a paid field. Thus the first zero is at index at most five.

If the first four rows are off-zero, their distinct clocks already force $JP=-P H_1$ identically (degree at most three). Comparing coefficients for degrees one and two shows that $P$ must be a monomial $T^d/2$, $d=0,1,2$. The native file checks these coefficient implications over their stated domains. At the first two physical rows the normalized residual ratio is
$$1+2u-u^2=\frac{P(1+u)}{P(1)}=(1+u)^d,\qquad u=x_2-1\ne0.$$
The quadratic monomial $d=2$ would imply $2u^2=0$, impossible. For $d=0$ one gets $u=2$; for $d=1$ one gets $u=1$.

The first zero now is physical row 5, of normalized clock $a$. The diagonal grade-three clean read gives $JP(a)=P(a)$. For $d=0$ it yields $a=1$. For $d=1$ it gives $a=2$ or $a=0$, but at $a=0$ one would have $(M'\mathbf q)_5=-P(0)=0$ while $L(0)=D^4\ne0$, impossible because their restrictions span the same nonzero line. Thus $a=d+1$, $P(a)\ne0$, and as a full column identity
$$ A'\mathbf q=\frac{1}{d+1}C'\mathbf q.$$
This follows on $U$ by the clean $JP$ read, and on every off-zero row from the identically zero polynomial $JP+P H_1$ and the vanishing of $\mathbf q$ there.

The sole later off-zero stage cannot be row 6. There its $A'\mathbf q$ read would see only the earlier zero 5, so its actual strict tap into row 5 would be zero. Then $(A'C'\mathbf q)_6=0$, and the full identity above implies $(M'\mathbf q)_6=0$. Thus $M'\mathbf q$ would be zero on all five off-zero rows, forcing $L=P H_2$ identically, now contradicted by $\deg(PH_2)\le3$. The final two rows are live zeros, so the only possibilities are later off-zero row 7 with live row 8, or later off-zero row 8 silent.

## 2. Exact characteristic-zero live-eighth elimination

In the live-eighth case the first zero is $a=d+1$ and the rear three live zeros have normalized clocks $D-1-w,D-1-v,D-1$, where $w=2-v$ in the literal star and $w=2v$ in the literal arithmetic phase. Use the same moment pin and second-zero line gate as the [pure live-eighth proof](../sdirk-eight-five-zero-pure-live-eighth/README.md) but with $r(T)=T^d$ (nonzero rescaling of the actual graph). Specifically the other zero $b$ is pinned by $b=D M_1/M_0$, where $M_i=I_D(T^iP_4(T))/D^i$, $I_D(T^j)=D^j/(j+1)$, and $P_4$ is the product at the four known zero clocks. $M_0$ is the literal weight at $b$ times $P_4(b)$ and so is nonzero. The two equations are $M_0M_2-M_1^2=M_0M_3-M_1M_2=0$.

The same grade-four discrepancy line gives the necessary scalar polynomial at $b$,
$$ g(T)=L(a)[a(Jr)(T)-(J(Tr))(T)+(T-a)r(T)]
       -L(T)[a r(a)-(J(Tr))(a)].$$
At first zero $a$, $L(a)\ne0$ because the $M'\mathbf q$ diagonal component there is $-P(a)\ne0$. Insert the pinned $b$ into $g$, clearing $M_0^4$. In the star use $V=(v-1)^2$; in arithmetic use $V=v$. This is a three-polynomial problem in $D,V$ over the rationals. The exact script computes all pairwise resultants eliminating $V$, then their common factor in $D$, and verifies its exact factorization for all four charts. Each nonzero $D$-factor either gives $L(a)=0$ directly or, after the full univariate gcd in $V$ in its exact quotient field, has no common root or forces $M_0=0$. Thus this is not an inference from pairwise resultants alone. It applies to all algebraic roots over a characteristic-zero field, with no real embedding assumption.

## 3. Exact characteristic-zero silent-eighth elimination

In the silent-eighth case the reverse cubic is $v^3-4v^2-v+2=0$, and the three known zero clocks are $a,D-1-v,D-1$. Form $P_3$ at these clocks and the moment sequence $m_i=I_D(T^iP_3)$ through index four. The two interior live nodes are a monic quadratic, so the Hankel determinant $H_m$ and the cleared Cramer polynomial $F_2$ are exactly those in the [pure silent-eighth proof](../sdirk-eight-five-zero-pure-silent-eighth/README.md). Keep the zero Cramer pivot $\Delta=m_0m_2-m_1^2$ separate. The same second-zero line test is $g(b)=0$ at one root of the interior quadratic.

Over the irreducible reverse cubic field $\mathbb Q(v)$, take the two univariate common factors in $D$: $H_m$ with $\operatorname{Res}_T(F_2,g)$ for the regular chart, and $H_m$ with $\Delta$ for the singular chart. The exact monic gcds are $D^6 L(1)$ (constant graph) or $D^6$ (linear graph) for the regular chart, and $D^2$ in both singular charts. The only zeros in either chart violate the physical $D\ne0$ or $L(a)\ne0$ guard. This handles every algebraic gap and every rank drop in characteristic zero.

Run `python check_live.py` and `python check_silent.py` with SymPy 1.14. The native `RKCert.Research.SDIRKEightFiveZeroGraphFourOff` checks the affine and quadratic primitive-divisibility coefficient gates over integral domains; the actual rooted flag reduction and exact arithmetic projections remain the source proof and exact replay, not one native `HasOrder` theorem. The structural monomial reduction holds in paid positive characteristics, but the final exclusions here do not make that extrapolation. Stock Lean/Mathlib 4.36.0 audit attached.
