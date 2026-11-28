# Pure support with five ordinary sites: characteristic-zero closure

Let a strict ten-stage SDIRK tableau $A,\mathbf b$ of ordinary order at least eight over a characteristic-zero field have exactly five physical quadratic zeros. Write $\mathbf c=A\mathbf1$, $\mathbf g=A\mathbf c-\mathbf c^{\odot2}/2$, $G=\operatorname{diag}(\mathbf g)$, $U=\ker G$, and $\gamma\ne0$ for the common diagonal. Assume the unique supported grade-two column is purely polynomial in the clock and **all off-zero stages are silent**.

**Result.** This entire pure, zero-active-off-clock case is impossible in characteristic zero, with no ordering or real-embedding requirement. The [four-ordinary-site](../sdirk-eight-five-zero-pure-four-ordinary/README.md) and [silent-eighth](../sdirk-eight-five-zero-pure-silent-eighth/README.md) cases had all-paid-field exclusions. This final live-eighth calculation is currently characteristic zero only. The other support and weight strata from the [support census](../sdirk-eight-five-zero-support-rank/README.md) are not decided here.

## 1. Normalized actual nodes and a nonzero moment pivot

Only the five-distinct-ordinary-site case with a live stage 8 needs consideration. All five physical zero weights are therefore live, and the five zero clocks are distinct. There are two distinct physical off-zero clocks. The first and second literal forward rows are off-zero, at $\gamma,\gamma(1+u)$, and the third is zero with $c_3=\gamma(1+2u)$, $Q(u)=4u^3-12u^2+3u+2=0$. These are the same literal front identities as in the [pure four-site proof](../sdirk-eight-five-zero-pure-four-ordinary/README.md).

Use $T=X/\gamma$, $D=1/\gamma$, and $a=1+2u$. The last three weighted stages, namely physical rows 10, 9, 8 in reverse order, are all live zeros. Write $v=(c_{10}-c_9)/\gamma$ and $w=(c_{10}-c_8)/\gamma$. Their literal weighted reverse suffix has the star or arithmetic third phase, $w=2-v$ or $w=2v$. This uses the actual three-row pure identities, not an assumption that reversing the whole tableau preserves order. Thus the four known normalized zero clocks are
$$a,\quad D-1-w,\quad D-1-v,\quad D-1,$$
and the remaining normalized zero clock $b$ is the **second** chronological zero: it lies between physical row 3 and the last three rows.

Let $P_4(T)$ be the monic polynomial with the four known roots, $I_D(T^i)=D^i/(i+1)$, and $m_i=I_D(T^i P_4(T))$. Because the ordinary quadrature is supported exactly on the five live zeros,
$$m_0=b_{\text{second zero}}\,P_4(b)\ne0.$$
The two factors are nonzero separately by activity and distinctness. In particular the rank-drop possibility $m_0=0$ is **not** a regular chart. Quadrature at degrees five through seven gives
$$m_1=bm_0,\qquad m_2=bm_1,\qquad m_3=bm_2.$$
Use $M_i=m_i/D^i$, which is valid since $D\ne0$. The pinned clock is $b=D M_1/M_0$. The two moment equations without the pinned variable are
$$F_1=M_0M_2-M_1^2=0,\qquad F_2=M_0M_3-M_1M_2=0.$$

## 2. The actual supported grade-four read

Let $r(T)=(T-1)(T-1-u)$ and $L(T)=70T^4-140DT^3+90D^2T^2-20D^3T+D^4$. The first and second zero-row calculation is exactly [the supported grade-four line argument](../sdirk-eight-five-zero-pure-silent-eighth/README.md), which used no silence assumption at row 8. Namely $A'_U r$ reads $Jr$ exactly because $F_3=GE_1$ is clean on $U$. The pure grade-four restriction to $U$ is the line spanned by $L(\mathbf c_U/\gamma)$. The restriction is nonzero at $a$ because $M r_{\rm phys}(\mathbf c)$ has literal first zero component $-\gamma^2r_{\rm phys}(c_3)\ne0$. Therefore the difference between $A'_U(Tr)$ and the primitive $J(Tr)$ has a common single scalar coefficient multiplying $L$. Here $J$ is the normalized polynomial primitive from zero.

The two actual zero rows read only their diagonals and, in the second row, the tap from the first zero. Eliminating that tap and the line coefficient gives $g(b)=0$, where
$$
g(T)=L(a)[a(Jr)(T)-(J(Tr))(T)+(T-a)r(T)]
       -L(T)[a r(a)-(J(Tr))(a)].
$$
Write $g(T)=\sum_{i=0}^4 g_i T^i$. Its polynomial equation after inserting the guarded moment pin is
$F_{\!p}=\sum_{i=0}^4 g_i(DM_1)^i M_0^{4-i}=0.$$
In forming these three projection polynomials the exact replay divides out only powers of $D$, a guarded nonzero factor.

## 3. Both complete characteristic-zero towers

Work first over $K=\mathbb Q(u)$, with $u$ a root of the irreducible cubic $Q/4$. The source checks its irreducibility over the rationals. A proposed characteristic-zero tableau embeds this abstract cubic field in its coefficient field. It need not admit an order or a real embedding. In the arithmetic chart keep $V=v$. In the star chart set $V=(v-1)^2$: then
$$P_4(T)=(T-a)(T-D+1)[(T-D+2)^2-V],$$
so the three equations depend only on $V,D$. This substitution is a necessary identity for every actual star, even over an arbitrary extension.

Take the three pairwise resultants of $F_1,F_2,F_{\!p}$ eliminating $V$. An actual root makes all three vanish. Their monic gcd in $K[D]$ factors as follows:

| Phase | Degree of the three projections | Common factor structure |
| --- | --- | --- |
| Star | 24, 64, 64 | $D^4 P_5(D)$, with one degree-five factor |
| Arithmetic | 48, 128, 128 | $D^8(D^2-10D+10)P_8(D)$, with one degree-eight factor |

The script prints the exact common polynomials and checks the factor product coefficient by coefficient. This projection alone does **not** show that there is a common rear parameter. For each non-$D$ factor $q(D)$ it reconstructs all three polynomials in $V$ in the exact quotient $K[D]/(q)$. Univariate Euclidean elimination there gives a **monic linear gcd** in $V$ for each of the three factors (degrees 5, 2, 8 respectively). Every pivot inverse is verified by a Bézout identity in $K[D]$, so each step is valid at every actual root of the factor in any extension. The remaining linear divides $M_0$ in that quotient; its exact remainder on $M_0$ is zero. Thus any proposed geometric solution in any of these factors has $M_0=0$, contradicting the nonzero literal fifth weight and distinct known clocks. The $D=0$ factor is directly unphysical. No positive-dimensional leftover or unexamined root of an irreducible projection is suppressed.

## 4. Scope and verification

The conclusion only claims characteristic zero for the live-eighth case. Arbitrary paid positive-characteristic reduction is not justified by a characteristic-zero Euclidean computation, whose pivots can become zero after reduction. The earlier four-site and silent-eighth charts remain all-paid-field exclusions. Combined, these results give complete characteristic-zero nonexistence of **exactly five zeros, pure support, and no active off-zero stages**.

Run `python check_towers.py` with SymPy 1.14; the exact trace takes tens of seconds. `RKCert.Research.SDIRKEightFiveZeroPureLiveEighth` kernel-checks the nonzero fifth-node moment, the two paired moment eliminations, and the star rear clock factorization over their stated structures. The full rooted ingress and exact characteristic-zero quotient computations are the source proof and replay, not a single native `HasOrder` theorem. Stock Lean/Mathlib 4.36.0 axiom audit attached. No overall stage interval changes.
