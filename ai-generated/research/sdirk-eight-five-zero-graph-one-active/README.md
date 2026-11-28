# One active off-zero clock is impossible for a five-zero graph in characteristic zero

Consider a strict ten-stage SDIRK tableau \(A,\mathbf b\) of order at least eight over a characteristic-zero field, with common nonzero diagonal \(\gamma\), clocks \(\mathbf c=A\mathbf1\), and quadratic residual \(\mathbf g=A\mathbf c-\mathbf c^{\odot2}/2\). Suppose exactly five physical quadratic zeros, a genuine degree-two supported graph, and exactly one physical off-zero clock with an active output weight.

**Result.** This chart is impossible over every characteristic-zero field. The two-active-off-clock graph, and the pure-polynomial supported chart with active off-zero weight, are independent strata. No general stage interval is changed.

## 1. Actual terminal and pair chronologies

The [support census](../sdirk-eight-five-zero-support-rank/README.md) gives four distinct physical off-zero clocks. Exactly one has two live rows with equal nonzero residual and opposite nonzero weights. The other three off-zero stages are individually silent at three other clocks.

Put \(G=\operatorname{diag}\mathbf g\) and \(M=CA-AC-A^2\). Because some \(b_i g_i\ne0\), the pure row \(\mathbf b^\mathsf T G\) spans \(Z_2\). The actual pure row \(\mathbf z^\mathsf T=-\mathbf b^\mathsf T M/2\) spans the same line. Its last value is \(\gamma^2 b_{10}/2\ne0\), hence physical stage 10 is one member of the active off pair. Its other member has index less than 10. The two indices agree on all values of \(E_5\): their row difference is proportional to \(\mathbf z^\mathsf T\in Z_2=\operatorname{Ann}(E_5)\). Thus the pair cancels any weighted scalar read of grade through five. With a clock polynomial multiplier the cancellation persists, since their clocks coincide.

As in the [literal Gaussian rear work](../sdirk-eight-four-zero-gaussian-rear/README.md), the last two rows are live with distinct clocks and \(c_{10}=1-\gamma\). Since the only live off-zero clock is \(c_{10}\), row 9 is zero, whence its normalized reflected residual \(\kappa_R\) is zero. A silent row 8 is impossible: the reverse ghost gate would give \(z_8\ne0\), whereas \(\mathbf z^\mathsf T\) is proportional to \(\mathbf b^\mathsf T G\). Thus row 8 is live, at a distinct clock, and is also zero. Write the earlier two terminal clocks in normalized coordinates as
\[
 c_9/\gamma=D-1-v,\qquad c_8/\gamma=D-1-w,\qquad D=1/\gamma,
\]
where \(v^2-2v-1=0\) and \(w=2v\) (arithmetic) or \(w=2-v\) (star). These are the literal reflected phases, not a mirror method assumption.

## 2. Four ordinary sites are impossible

Ordinary mass is carried by the five zero rows. The ordinary Hilbert \(4\)-by-\(4\) moment rank shows that at least four scalar labels have nonzero aggregate weight. If exactly four do, all four are roots of \(L_4(X)=70X^4-140X^3+90X^2-20X+1\) by its four ordinary orthogonality tests. In this case any live zero row must have a clock with nonzero aggregate: a canceled live group would consume at least two of the five zero rows and leave at most three sites. In particular the distinct clocks \(c_9,c_8\) are both Gaussian nodes.

In reflected physical coordinates \(x=1-c_9\) and \(y=1-c_8\) we have
\[
 y/x=(1+2v)/(1+v)\quad\text{or}\quad(3-v)/(1+v),
\]
respectively. The guards \(x\ne0\) and \(1+v\ne0\) follow from \(\gamma\ne0\) and the quadratic on \(v\). The exact divided-difference resultants of \(L_4(x)\), \([L_4(y)-L_4(x)]/(y-x)\) and the quadratic in \(v\) are nonzero in both phases. This excludes every algebraic pair of Gaussian nodes in characteristic zero. Accordingly all five zero clocks are live and distinct. None is Gaussian by the [five-site Gauss guard](../sdirk-eight-five-zero-graph-arithmetic-silent/README.md#1-literal-clock-data-and-the-ordinary-cubic).

## 3. Five ordinary sites and all first-zero positions

The first two physical rows are off-zero, since the forward quadratic ratio cannot vanish with multiple distinct off-zero clocks. Row 10 is off-zero, and the other four off-zero rows have distinct clocks before it. Thus the first zero is physical row 3, 4 or 5. In normalization \(A'=A/\gamma\), the supported column is \(\mathbf q=P(\mathbf c/\gamma)-\mathbf g/\gamma^2\), a scalar quadratic graph \(P\). The same supported reads used in the no-active branch remain valid: \(F_3=GE_1\); \(GE_2\) and \(GE_3\) have ranks three and four on the off-zone; and the literal canceled pair agrees in \(E_5\). Therefore on the five zero rows the grade-four and grade-five discrepancies lie in the shifted Legendre spaces \(\langle L_4\rangle\) and \(\langle L_3,L_4\rangle\), respectively. No assertion of cancellation for grade six or seven is needed.

**First zero at row 5.** Four distinct off clocks precede the first zero. The grade-three clean-prefix identity at those four clocks forces \(JP=P H_1\) as polynomials for an affine \(H_1\), as in the [four-off prefix proof](../sdirk-eight-five-zero-graph-four-off/README.md). Thus \(P=T^d/2\), \(d=0,1,2\). The first two literal residuals exclude \(d=2\) and pin the forward gap for each other monomial. A clean diagonal read at the first zero gives \(a=d+1\), with the additional apparent root \(a=0\) for \(d=1\) excluded by the nonzero \(L_4(a)\) and the first nonzero component of \(M\mathbf q\).

**First zero at row 3.** The literal forward quadratic ratio is nonzero. The star phase would leave the third residual nonzero, so the front is arithmetic with \(a=1+2u\) and \(4u^3-12u^2+3u+2=0\). The graph is \(P=P_0+\lambda(T-1)(T-1-u)\) for \(P_0=2T-1-T^2/2\). The two gap extensions are represented by a verified primitive element \(u+2v\), of degree six; it covers all pairs of roots.

In both of these known-first cases, mask the first known zero and the two live reflected zero clocks from rows 8 and 9. The two remaining ordinary clocks solve the monic quadratic from the masked \(2\)-by-\(2\) Cramer equations; their order is retained by a signed quadratic variable. The third masked Hankel condition is a polynomial of degree 15 in \(D\), with degree nine after exact structural guard removal. The inversion of the \(2\)-by-\(2\) pivot in that quotient is checked, together with all its moment recurrences. With a fixed monomial use the second-zero gate and the third-zero determinant directly. With the free graph parameter use their common-parameter elimination. In each of the six combinations (row 3 or \(d=0,1\), each rear phase), the final exact norm gcd is constant.

**First zero at row 4.** Both initial zero candidates follow the same [scaled three-early-zeros tower](../sdirk-eight-five-zero-graph-arithmetic-silent/README.md) with the two known clocks now at actual rows 8 and 9. If the initial three off rows are a star their graph is fixed \(P_0\), so the first two supported-gate norms alone suffice. If they are arithmetic, the same cleared regular and singular pencil applies. The computed degrees are:

| Literal front | Exact guarded common divisor degree |
| --- | --- |
| Star | \(\deg\Delta^{12}=72\) |
| Arithmetic, regular | \(\deg(\Delta^{48}D_1^3 L^3)=504\) |
| Arithmetic, singular | \(\deg(\Delta^{30}D_1 L)=252\) |

Here \(\Delta\) is the exact ordinary Cramer pivot, \(D_1=\operatorname{Disc}(Q_A)/\Delta^2\), and \(L=N(L_4(a))/\Delta^{16}\). They are structurally nonzero at the actual five distinct ordinary clocks. For **each** of the two rear phases, the replay checks exact divisibility in \(\mathbb Q(v)[\gamma]\) by those polynomials and degree-preserving reduction of the fixed witness pair to a gcd of precisely that degree over \(\mathbb F_{19^2}\). The characteristic-zero Sylvester rank then proves there are no additional factors. This is not a characteristic-19 enumeration.

Run `python check_four_ordinary.py`; then, for each rear `star` and `arith`, run `python check_known_first.py REAR MODE` for `MODE=0,1,third` and `python check_first4.py REAR FRONT` for `FRONT=star,arith`. The known-first and Gaussian replays use SymPy 1.14; the first-four replay uses Python-flint 0.8. Rooted ingress and exact polynomial calculations are the mathematical proof, with the supported scalar identities shared with the no-active-off packet.
