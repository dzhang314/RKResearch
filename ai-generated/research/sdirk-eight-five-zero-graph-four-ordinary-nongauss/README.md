# The four-ordinary-site graph must have five Gaussian physical zero clocks

Consider a strict ten-stage SDIRK tableau with ordinary order at least eight, common nonzero diagonal $\gamma$, and exactly five physical quadratic zeros over a field of characteristic zero or greater than seven. Write $\mathbf c=A\mathbf1$, $\mathbf g=A\mathbf c-\mathbf c^{\odot2}/2$, $C=\operatorname{diag}(\mathbf c)$, $G=\operatorname{diag}(\mathbf g)$, and $U=\ker G$. Assume genuine graph support, all five off-zero stages silent, and exactly four distinct nonzero ordinary clock masses, as in the [five-zero support census](../sdirk-eight-five-zero-support-rank/README.md).

**Result.** Every physical zero clock must be Gaussian, over every paid field. The surviving case has a Gaussian duplicate among the five zero rows. No conclusion about that duplicate, five distinct ordinary sites, or activity at an off-zero clock is claimed here.

## 1. A non-Gaussian zero must be the first physical zero

The ordinary four sites are the four distinct roots of the fourth shifted Legendre polynomial. All live zero rows are Gaussian: a non-Gaussian live site would need two live rows to cancel its mass, which would leave too few physical rows for four Gaussian sites. Thus a non-Gaussian physical zero would be the unique silent zero, and the other four zeros would have distinct Gaussian clocks and nonzero weights.

Use $A'=A/\gamma$, $\mathbf x=\mathbf c/\gamma$, $\boldsymbol\eta=\mathbf g/\gamma^2$, $D=1/\gamma$, and let $\mathbf q=P(\mathbf x)-\boldsymbol\eta$ be the actual supported graph vector (the scalar $P$ is a polynomial of degree at most two). Let $a$ be the normalized silent non-Gaussian clock and
$$L(T)=70T^4-140DT^3+90D^2T^2-20D^3T+D^4.$$
The line $F_4|_U$ is spanned by $L(\mathbf x)|_U$: it has dimension at most one since $GE_2$ has codimension one in $F_4$ and vanishes on $U$, and $L$ is a pure scalar polynomial nonzero at $a$. Another generator is $(M\mathbf q)|_U$, since its first nonzero supported action is the diagonal of $M=CA-AC-A^2$, namely $-\gamma^2$ times the first nonzero entry of $\mathbf q$. This line is supported only at $a$, so all actual $\mathbf q$ entries before the silent zero are zero, and $P(a)\ne0$.

If any live zero occurs earlier, denote its normalized Gaussian clock by $s\ne0$. The literal value $P(s)=0$, and both $A'\mathbf q$ and $A'(\mathbf x\odot \mathbf q)$ vanish there by chronology. Their primitive reads are clean (respectively $F_3=GE_1$ at every zero, and $F_4$ at this Gaussian zero). With $J$ the polynomial primitive from zero, this forces
$$P(s)=(JP)(s)=J(TP)(s)=0.$$
If $P=p_0+p_1T+p_2T^2$, clear 6 and 12 in the two primitive equations and cancel $s$ and $s^2$ respectively. The two resulting equations are
$$6p_0+3p_1s+2p_2s^2=0,\qquad 6p_0+4p_1s+3p_2s^2=0.$$
Together with $P(s)=0$ they force $p_0=p_1=p_2=0$. This contradicts $P(1)=1/2$ at the first physical stage. Thus the silent non-Gaussian zero must be the first physical zero.

## 2. Exact projection from the literal first three off-zero rows

If physical stage 3 is zero, the [literal-third graph exclusion](../sdirk-eight-five-zero-graph-four-ordinary-third/README.md) already applies. The first two stages are off-zero by the first-three pure transition (a zero second residual would localize every off-zero to one clock). We therefore have all first three physical stages off-zero and their clocks distinct.

As in the [literal-third proof](../sdirk-eight-five-zero-graph-four-ordinary-third/README.md), the actual Gaussian rear permits only characteristics $37,269,379$ (live star third) or $397,487,69877$ (silent third), with all controls in the complete Gauss splitting field. If physical stage 8 is silent it is off-zero, since the unique silent zero is earliest among five zeros and hence has index at most six. Its graph value must therefore be nonzero. Let $b,c$ be the first two live Gaussian zero clocks in normalized time; the exact rear chronology determines them up to the two possible orders of the unused Gaussian roots where appropriate.

Let $u=x_2-1$ and $\kappa=1+2u-u^2$, nonzero here. All three initial residuals determine $P$. With arithmetic tap denominator $H=-2+u+4u^2-u^3$ and $j=3u-2$ in the arithmetic phase, and $H=1,j=0$ in the star, the corrected actual three-row interpolant is
$$
P(T)=\widetilde P(T)/H,\qquad
\widetilde P(T)=H(2T-1-T^2/2)+j(T-1)(T-1-u).
$$
The exact replay checks all three residual values, including the arithmetic adjacent tap correction. It removes only literal forbidden factors: $u=0$, $\kappa=0$, the star exclusions $u=1,2$, or the arithmetic exclusions $H=0$, $3u-2=0$, or zero third residual. If stage 8 is silent it additionally requires the graph at its actual clock to be nonzero.

At the first live Gaussian zero $b$, the supported cubic $(T-a)P$ has a diagonal-only actual read. Use the line $F_4|_U$ above to make its read clean. After multiplying by $H$, set
$$\Delta=(J\widetilde P)(b)-\widetilde P(b),\quad
N=J(T\widetilde P)(b)-b\widetilde P(b),\quad N=a\Delta.$$
In every finite rear/forward chart the gcd of $\Delta,N$ has no admissible factor. The replay treats both identically zero and rank-drop cases before division. Thus $\Delta$ is nonzero and $a=N/\Delta$.

The silent first zero gives $(J\widetilde P)(a)=\widetilde P(a)$. At the first two live Gaussian zero rows, the [three-zero supported primitive test](../sdirk-eight-five-zero-graph-four-ordinary-third/README.md) applies verbatim: $F_5|_U$ is spanned by $L$ and the scaled third Legendre $\ell_3$, so both grade-five discrepancies are one common multiple of $\ell_3$. Substitute $a=N/\Delta$ into that cross-gate and the silent first primitive. Clearing $\Delta^2$ and $\Delta^3$ respectively gives two polynomials in the front gap $u$. In each of the 24 complete charts their gcd is constant after removing only forbidden factors from the literal guards, $\Delta$, $L(a)\ne0$ and $\widetilde P(a)\ne0$. This proves incompatibility in every extension of the Gaussian control field, including a front gap not lying in that field. In particular the conclusion is not based on testing a prime-field grid.

Run `python check_fibers.py` with Python-flint 0.8 to reproduce the geometric rear and guarded front gcds. `RKCert.Research.SDIRKEightFiveZeroGraphFourOrdinaryNongauss` checks the exact two-primitive contradiction at a nonzero earlier clock over integral domains; the source proof and finite replays supply the actual rooted support reduction, not one native `HasOrder` theorem. Stock Lean/Mathlib 4.36.0 audit attached.
