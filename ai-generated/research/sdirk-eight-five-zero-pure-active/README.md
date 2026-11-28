# Pure supported quadratics with active off-zero rows are impossible at five zeros

Consider a strict ten-stage SDIRK tableau \(A,\mathbf b\) of ordinary order at least eight over a characteristic-zero field. Write \(\mathbf c=A\mathbf1\), \(\mathbf g=A\mathbf c-\mathbf c^{\odot2}/2\), \(G=\operatorname{diag}\mathbf g\), \(U=\ker G\), and \(\gamma\ne0\) for the common diagonal. Suppose exactly five physical quadratic zeros, the unique supported grade-two direction is a pure scalar quadratic, and there is at least one live off-zero row.

**Result.** Every such chart is impossible in characteristic zero. Both canceled and nonzero aggregate off-zero masses are covered, including coincident or silent zero rows. The proof uses no field ordering and makes no all-prime assertion.

## 1. The two physical off clocks and the reflected phases

The [support census](../sdirk-eight-five-zero-support-rank/README.md) gives exactly two distinct physical off-zero clocks, and one or two clock groups with a live off-zero weight. A nonzero \(\mathbf b^\mathsf T G\) spans \(Z_2\); thus it is proportional to \(\mathbf z^\mathsf T=-\mathbf b^\mathsf T(CA-AC-A^2)/2\), and physical row 10 is off-zero. The [literal terminal stages](../sdirk-eight-four-zero-gaussian-rear/README.md) have \(c_{10}=1-\gamma\) and stages 9 and 10 live. Physical 8 cannot be silent, because the reverse ghost condition would give \(z_8\ne0\) at a silent weight.

Normalize by \(A'=A/\gamma,\ \mathbf x=\mathbf c/\gamma,\ D=1/\gamma\). The first two rows are off-zero: the literal forward ratio cannot be zero when the nonzero-residual clocks include two distinct values. The first three literal forward clocks are distinct, so row 3 is zero. By the arithmetic third-zero gate, with forward gap \(u=x_2-1\),
\[
 x_1=1,\quad x_2=1+u,\quad a=x_3=1+2u,\qquad Q(u)=4u^3-12u^2+3u+2=0 .
\]
The supported scalar trace is \(P(T)=(T-1)(T-1-u)\). Its full vector \(P(\mathbf x)\) vanishes on the two off-zero groups.

If both off clocks are active, their weights form two canceled live pairs, with one additional silent off stage at one of those clocks. The reflected ratio \(\kappa_R\) is nonzero because \(\mathbf z^\mathsf T\) is nonzero at both distinct off clocks, and the reflected first and second stages must be those two clocks. The third reflected stage (physical 8) is zero and the reflected arithmetic gap \(v\) again satisfies \(Q(v)=0\). Since \(\{x_9,x_{10}\}=\{1,1+u\}\), we get \(u=\pm v\). The coprime cubics \(Q(T),Q(-T)\) exclude the minus sign, leaving \(u=v,\ D=2+v,\ x_8=1-v\).

If only one clock is active, call it \(d=x_{10}=D-1\). Then stages 8 and 9 are live zeros, the reflected quadratic ratio is zero, and
\[
 v^2-2v-1=0,\qquad x_9=D-1-v,\quad x_8=D-1-w
\]
with \(w=2v\) or \(2-v\). Also \(D=2\) or \(2+u\), since \(d\) is one of the two first clock values. These are the four exact candidate frames. In either active case the pure scalar column has clean grade-three primitive on \(U\) by \(F_3=GE_1\). The grade-four pure space restricted to \(U\) has dimension at most one since \(GE_2\) has dimension three, vanishes on \(U\), and lies in \(F_4\) of dimension four. The full vector \(L_4(\mathbf x)\), scaled to \(D\), belongs to \(F_4\): it is orthogonal to the ordinary degree-three clock rows by order-eight moments and to \(Z_3=\operatorname{Ann}(E_4)\) because it is a scalar quartic. Thus whenever its zero-row restriction is nonzero, that line is exactly \(\langle L_4|_U\rangle\), even with nonzero ordinary mass at the active off clock.

## 2. Two active clocks, or one with a canceled ordinary mass

With two active clocks, ordinary mass is on the five zero rows. Four distinct ordinary labels would all have to be Gaussian, including live row 8; its literal clock \(1-v\) has nonzero \(L_4(1-v)\) in the cubic field, so this is impossible. If a zero-output grouping canceled, five physical zeros could not leave four other live sites. Thus there are exactly five distinct live ordinary clocks. Mask \(a=1+2v\) and \(s=1-v\), and use the nonsingular masked ordinary recurrence for the monic cubic whose roots are the three remaining zero clocks. The [second forward supported read](../sdirk-eight-five-zero-graph-arithmetic-silent/README.md#2-three-supported-equations-in-the-same-arithmetic-pencil) with the fixed pure trace \(P\) has constant gcd with this cubic, so no second chronological zero can satisfy it.

With one active clock and **zero** net ordinary weight there, irrespective of variation among its live residuals, ordinary mass is again on the five zeros. Four live ordinary labels would force both \(x_8,x_9\) Gaussian, which is impossible in characteristic zero by the [one-active Gaussian pair projection](../sdirk-eight-five-zero-graph-one-active/README.md#2-four-ordinary-sites-are-impossible). With five distinct live ordinary sites, mask the three known distinct zeros at rows 3, 8, 9. Only two unknown sites remain, so the exact \(3\)-by-\(3\) masked Hankel determinant must vanish. It is nonzero in each of the four literal frames over \(\mathbb Q(u,v)\). No combination of residual classes is assumed to cancel individually in this argument.

## 3. A nonzero ordinary off aggregate forces five distinct literal zero clocks

The only remaining case has one active off clock \(d\) with nonzero aggregate \(B_{\mathrm{off}}\). The support census forces four live off stages at that clock with varying nonzero residual and one silent off stage at the other clock. Set \(N=A-\gamma I\) and \(\boldsymbol\eta^{\mathsf T}=\mathbf z^\mathsf T N\in Z_3\). The off projection of \(W_3\) has dimension two by \(d_2=1\) and the [support restriction theorem](../sdirk-eight-two-zero-line/README.md). Its two independent directions are \(\mathbf b^\mathsf T\) and \(\mathbf b^\mathsf T G\), restricted to the off rows; independence uses the differing live residuals at \(d\). In particular \(\eta\) vanishes at the silent off stage. At a live off stage,
\[
 \eta_i=\beta b_i(g_i-g_{10})
\]
for one scalar \(\beta\), since the last coordinate of \(\mathbf z^\mathsf T N\) is zero. Testing the first five scalar clock powers, using \(\boldsymbol\eta^{\mathsf T}\in\operatorname{Ann}(E_4)\) and \(\sum_{\mathrm{off}} b_i g_i=0\), gives
\[
 \sum_{i\in U}\eta_i x_i^j=\lambda d^j,\quad 0\le j\le4,\qquad
 \lambda=\beta g_{10}B_{\mathrm{off}} .
\]

Both physical \(\eta_8,\eta_9\) are nonzero. Since \(z_8=z_9=0\), these are the single taps from row 10, times \(z_{10}\). The normalized reflected row-2 tap is \(v\ne0\). For row 3 of the reflected live suffix, the normalized first and second strict taps \(p,q\) satisfy \(p+q=w\). The zero reflected defect of this row is \(1+2w-w^2+2qv=0\). Hence \(2pv=2wv+1+2w-w^2\), equal to \(1+4v\) in the arithmetic phase and \(-2\) in the star, since \(v^2=2v+1\). Both are nonzero. The weighted reflection has the same zero/nonzero status for these actual taps because the three weights are live.

If \(\lambda=0\), the moments force each aggregate of \(\eta_i\) at an individual zero clock to vanish (Vandermonde in at most five distinct clocks). Then each of the two distinct clocks at rows 8 and 9 requires a second physical zero row at the same clock. Only one zero row remains, so there are at most three zero labels, hence at most four ordinary labels including \(d\). Ordinary moment rank forces exactly four nonzero labels, and both rear zero clocks are Gaussian. The previously excluded two-Gaussian reflected phase gives a contradiction.

If \(d\) occurs among the literal zero clocks, the moments give zero \(\eta\)-aggregate at every other zero clock by uniqueness in that same Vandermonde. Again rows 8 and 9 need duplicate mates at their two distinct clocks, neither equal to \(d\); with \(d\) as the fifth zero their ordinary mass has at most three labels in total, contradicting rank. Thus \(d\) is not any literal zero clock. Finally, if at most four distinct labels occurred among the five zero rows, their monic nodal polynomial of degree at most four would annihilate the entire left side and give the nonzero right side \(\lambda\prod(d-x_i)\). This is impossible. We have proved five distinct **literal** zero clocks, without assuming they all carry weight.

## 4. Exact last four frames

Mask \(d\) and the three fixed zero clocks \(x_3,x_8,x_9\). This remains a valid ordinary mask even if one of these zero rows is silent. The only remaining literal zero clocks are the second and third chronological zeros, both before row 8. In all four fixed \((D,w)\) frames the exact \(2\)-by-\(2\) masked Hankel pivot for the two unknown clocks is nonzero. Thus their unordered pair is uniquely the root set of the recovered monic quadratic; no weight assumption beyond the moment identity is needed to apply the recurrence. It uses ordinary degrees at most seven.

The supported polynomial \(P\) is already fixed. Its grade-four discrepancy line is \(\langle L_4\rangle\) on the five distinct zero labels, as above. The first zero is \(a\), and \(L_4(a)\ne0\) in all four fields. The second forward gate has constant gcd with the recovered quadratic in every frame. Since both possible orders are covered, this excludes the nonzero off-aggregate case.

Run `python check_two_active.py`, `python check_one_canceled.py` and `python check_one_noncanceled.py` with SymPy 1.14. They use only rational algebra and verified exact quotient fields. The supported flag and literal tap ingresses are the cited mathematical proofs; these files are not a single native `HasOrder` formalization. All conclusions are restricted to characteristic zero.
