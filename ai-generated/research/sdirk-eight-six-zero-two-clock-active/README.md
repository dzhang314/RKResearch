# Two off-zero clocks with activity are impossible at six zeros

Consider a strict ten-stage SDIRK tableau \(A,\mathbf b\) of ordinary order at least eight with common nonzero diagonal \(\gamma\), exactly six physical zeros of \(\mathbf g=A\mathbf c-\mathbf c^{\odot2}/2\), two distinct physical off-zero clocks, and some active off-zero weight.

**Result.** Every such chart is impossible over a characteristic-zero field. The case where the residual is constant within each of the two physical off groups is impossible over every paid field (characteristic zero or greater than seven). All statements are about exactly this physical census, not a global stage bound.

## 1. Rank and two constant off groups

For \(U=\ker G\), use the [saturated support identity](../sdirk-eight-two-zero-line/README.md). Let \(\nu\) count the physical off groups at which the residual varies. The \(E_2\) off rank is \(2+\mathbf1_{\nu>0}\); the \(E_3\) off rank is \(2+\nu\) because affine multiples of \(\mathbf g\) separately detect variation in the two groups. Thus the \(W_2\) off rank is \(2-\nu\). With an active off-zero row weighting \(E_2\) identifies it with \(W_2\) (ordinary moments detect its scalar part and a nonzero weighted residual detects its pure part). In particular \(\nu=2\) is impossible with any off activity.

If \(\nu=0\), both off groups must be active to give rank two. The first two residual moments separate the groups and show ordinary cancellation in each; hence there are exactly two live stages in each group, with equal residual and opposite weights. The canonical pure row \(\mathbf z^\mathsf T=-\mathbf b^\mathsf T(CA-AC-A^2)/2\) is proportional to \(\mathbf b^\mathsf T G\). The first and second actual forward clocks are the two off clocks, the third is distinct and zero. In the reflected direction the [literal terminal gates](../sdirk-eight-four-zero-gaussian-rear/README.md) give the same census: rows 10 and 9 are the two off clocks, both active, and row 8 is a live zero. The reflected ratio cannot vanish because both off clocks support \(\mathbf z^\mathsf T\), and a silent row 8 would require a nonzero \(z_8\). The two literal third-zero phases are arithmetic, with gaps \(u,v\) satisfying \(Q(T)=4T^3-12T^2+3T+2=0\). Normalize by \(\mathbf x=\mathbf c/\gamma\), \(D=1/\gamma\). The two equal off-clock assignments give \(u=v,\ D=2+v\), or \(u=-v,\ D=2\).

On those two forward clocks the quadratic \(P_0(X)=2X-1-X^2/2\) matches the normalized residual in both **entire** groups. Thus \(P_0(\mathbf x)-\mathbf g/\gamma^2\) is a supported grade-two column, and after weighting by \(\mathbf b\) gives a supported grade-two row with scalar profile \(P_0\). The pure reverse \(Z_3\) is off-supported: it is spanned by \(\mathbf z^\mathsf T,\mathbf z^\mathsf T(A/\gamma-I)\), and the nonzero reflected ratio makes the latter an affine clock multiple of the former. At row 8 the right primitive of the supported row is therefore clean and diagonal, with \(s=x_8=D-1-2v\):
\[
 JP_0(D)-JP_0(s)=P_0(s),\qquad JP_0(X)=X^2-X-X^3/6 .
\]
Multiplying by 12 gives \(-4v^3+30v+4=0\) in the equal-gap assignment and \(-16v^3+36v+4=0\) in the opposite assignment. In the former, the two equations force \(4v^2-11v-2=0\), then \(3v+2=0\) and \(64=0\). In the latter, the sum and difference of \(Q(v),Q(-v)\) give \(1-6v^2=0,\ 4v^2+3=0\); the read further gives \(12v+1=0\). These imply both \(11=0\) and \(23=0\). No characteristic-11 gap is silently discarded.

The native `RKCert.Research.SDIRKEightSixZeroPairScalar` module proves these scalar contradictions over integral domains with the displayed paid numeral guards, and the first-strict-tap identity used next. The actual rank/phase ingress above is a mathematical source proof.

## 2. One varying off group with a canceled live pair

For \(\nu=1\) the \(W_2\) off rank is one. Thus there is exactly one active off clock, at which all live residuals are the same. The aggregate cancels; counting the four off physical rows and the physical variation leaves exactly two live rows at that clock with opposite weights. The terminal row 10 is one of them and the reflected ratio is zero. Rows 8 and 9 are distinct live zeros. The forward first two clocks are again the two physical off clocks and the third is zero. Thus \(Q(u)=0,\ a=x_3=1+2u,\ x_1=1,\ x_2=1+u\); the supported direction is the pure polynomial \(P(X)=(X-1)(X-1-u)\). The active off clock is \(D-1\), giving \(D=2\) or \(2+u\). Let the reflected gap \(v\) satisfy \(v^2-2v-1=0\), and put \(s=x_8=D-1-w,\ t=x_9=D-1-v\), with \(w=2v\) or \(2-v\). These are all four possible exact frames.

In this case \(\boldsymbol\eta^\mathsf T=\mathbf z^\mathsf T(A/\gamma-I)\) is supported entirely on \(U\): \(W_3\) off rank is \(d_2=1\), and its nonzero off direction is the live pair, whereas \(\eta_{10}=0\). The ordinary measure is entirely on the six zero rows. Mask the known three distinct zero labels \(a,s,t\). The ordinary \(3\)-by-\(3\) masked Hankel determinant through degree seven is nonzero in every fixed frame. This forces at least three other distinct live zero labels outside the mask, and there are only three free physical zero rows. Thus all six literal zero clocks are distinct; a masked known row may be silent without disrupting the argument.

Let \(P_6\) be the monic polynomial whose roots are the six zero clocks. Since \(\boldsymbol\eta\) annihilates scalar clock powers through degree four, its six values are a nonzero common multiple of \(1/P_6'(x_i)\). Its rear ratio is the literal tap ratio \(b_8p_R/(b_9v)\), where \(2p_Rv=2wv+1+2w-w^2\). Therefore
\[
 p_R I_D(P_6/(X-s))=v I_D(P_6/(X-t)).
\]
Write \(P_6=(X-a)(X-s)(X-t)Q_3(X)\) with \(Q_3\) monic cubic. This ratio is one linear equation in its three unknown coefficients. The two ordinary equations \(I_D(P_6)=I_D(XP_6)=0\) supply the other two. The full three-by-three pivot is nonzero in all four exact fields and all coefficients are recovered without assuming the three roots lie in the base field.

Finally \(F_3=GE_1\) is clean on the zero rows, and the \(F_4\) discrepancy there is the line of \(L_4\) since \(GE_2\) has rank three and the six literal zero clocks are distinct. At first zero \(a\), \(L_4(a)\ne0\) by the nonzero diagonal read of \(M P(\mathbf x)\). The [second physical zero read](../sdirk-eight-five-zero-graph-arithmetic-silent/README.md#2-three-supported-equations-in-the-same-arithmetic-pencil) gives a scalar polynomial in the second zero's clock, which must be a root of \(Q_3\). Its exact gcd with \(Q_3\) is constant in all four fields.

Run `python check_one_active.py` with SymPy 1.14 for the complete characteristic-zero algebra in section 2. The native scalar module and its axiom audit are separate from the symbolic coefficient fields and rooted ingresses.
