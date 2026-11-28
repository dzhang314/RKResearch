# DIRK12/15: the two-repeat variable eight-site face is impossible

Consider ordinary real order-twelve DIRK in fifteen physical stages with \(C(2), f_5=3\), and invisible weighted forward cubic \(\mathbf b\odot\mathbf h=0\). Suppose there are exactly four zero-weight physical rows, all truly dirty in \(\mathbf h=A\mathbf c^2-\mathbf c^3/3\), at four distinct ghost clocks. Suppose the live scalar grid has eight sites, seven of them appearing among the ten nonterminal live physical stages. If at most two live numerical labels are repeated, the tableau is impossible. In this chart the only remaining eight-site multiplicity is three repeated pairs. The real order-twelve interval remains **15–16**.

Use the [variable-grid quotient](../dirk12-fifteen-rank3-invisible-four-ghost-variable-grid/README.md). All four ghost axes are in actual pure \(F_6\). The actual terminal is the unique live row at its numerical label. The genuine \(T_6\) is the span of the four ghost axes, the terminal axis and the degree-at-most-six scalar evaluations. In true reverse physical order let \(N=A^{\mathsf T}\), \(\mathbf y=\mathbf1-\mathbf c\), \(Y=\operatorname{diag}(\mathbf y)\), \(\mathbf W(P)=\mathbf b\odot P(\mathbf y)\), and \(JP(X)=\int_0^X P\). The actual weighted flag \(\mathcal B_5=\operatorname{Ann}T_6\) vanishes on ghosts, on the terminal (reflected origin), and at every live singleton, and has zero aggregate at each live label. Its lower flags \(\mathcal B_3,\mathcal B_4\) have dimensions one and two. All references to rows and diagonals below are to actual physical stages, not a normalized transposed rooted method.

## First live debuts and the necessary early split

The genuine reverse cubic \(\mathbf G=N\mathbf W(X^2)-\mathbf W(X^3)/3\) is nonzero, supported within repeated live labels. It cannot have exactly two support labels by the invariant grade-four obstruction. Thus it is local at the first nonzero live reflected clock \(d\), where the first normalized amplitude is \(g_1=G_{i_d}/b_{i_d}=d^3/6\). Its actual grade-four head \(\mathbf H=N\mathbf G-(d/2)\mathbf G\) is zero at that first \(d\)-row and nonzero at the next distinct nonzero live debut \(v\), by the two leading weighted moments and \(\mathbf G\) locality. See the [literal first head](../dirk12-fifteen-rank3-one-active-cubic-head/README.md). Consequently \(v\) is a second repeated label, so a single repeat is already impossible. The total of three extra live rows forces repeated multiplicities \(3,2\). Every other live nonzero label is a singleton.

Let \(u,w\) be the first two nonzero singleton live debuts in actual chronology. They are the third and fourth distinct nonzero live labels. For \(P=X(X-d)(X-v)\), the weighted scalar input is zero before \(u\), and nonzero at \(u\). Its genuine grade-five commutator \(YN-NY-N^2\) is pure and zero there. The literal diagonal of the commutator is \(-N_{ii}^2\), so the physical diagonal at \(u\) is zero. The exact reads for \(P,XP\) then give \(JP(u)=J(XP)(u)=0\). Expanding and simplifying gives the two true Radau relations
\[
                    d+v=6u/5,\qquad dv=3u^2/10 .
\]
Thus \(d/u,v/u\) are the two roots of \(10X^2-12X+3\), equivalently \(5(v/d)^2-14(v/d)+5=0\).

At least two earlier \(d\)-rows must have different normalized \(\mathbf G\)-amplitudes. If their amplitudes were all \(g_1\), the fact \(N\mathbf G=0\) at the singleton \(u\) would kill the aggregate tap to \(d\). With the physical diagonal at \(u\) zero, the remaining live labels are just \(0,v\), impossible by the exact degree-three integral of \(X(X-v)^2\) to \(u\ne0\). This argument tests every physical earlier live \(d\)-row, regardless of its weight sign.

## No repeat can complete before the second singleton

First address a repeated label \(s=d\) or \(s=v\) with zero total output mass. There are at least seven occupied nonzero-mass scalar labels including the reflected terminal \(0\), by the positive polynomial \(X\) times the square of the hull of the other occupied labels. Thus there is at most one zero-mass label among the eight live numerical labels. If such a repeat \(s\) differs from the reflected label \(1\), removing it leaves seven scalar quadrature labels including both endpoints \(0,1\): the literal ordinary origin is live because all four ghosts are cubic-dirty. They must be the fixed Lobatto grid. The remaining repeat and \(u\) would then be two different nonzero fixed nodes satisfying \(10v^2-12uv+3u^2=0\) (or the identical equation with \(d\) in place of \(v\)), contrary to the [fixed arithmetic](../dirk12-fifteen-rank3-invisible-five-ghost-exclusion/README.md). If the zero-mass repeat is label \(1\), it contains the literal ordinary origin, last in reverse physical order. It cannot complete before \(u\) or \(w\).

For either nonzero-mass repeated label \(s\), its live scalar cardinal on the seven nonterminal labels has degree at most six. Subtract its actual ghost coordinates and its actual terminal entry to obtain the whole live block indicator in genuine \(T_6\). If the block has already completed at a proposed early cut, this indicator is supported on earlier rows. Any true grade-four weighted scalar input \(\mathbf W(R)\) zero through that cut has \(N\mathbf W(R)\) zero there by causality. Pair the indicator with its actual grade-five discrepancy to obtain
\[
                         0=m_s JR(s)
\]
where \(m_s\ne0\) is the physical aggregate weight at the label. This is the actual \(6+5=11\) cut; no ordinary scalar profile for the corrected indicator is needed.

Before \(u\), choose \(R=X(X-s)(X-t)^2\), where \(t\) is the other repeated label. It vanishes on the entire preceding weighted prefix. The integral \(JR(s)\ne0\) by a definite-sign integrand on the segment from \(0\) to \(s\), also when \(s<0\). Hence neither repeat is completed before \(u\). In particular \(d\) must be the triple, and exactly two of its physical rows have occurred; \(v\) is the pair and exactly one of its rows has occurred. The second \(d\)-row comes after \(v\), since every \(d\)-row before \(v\) reads only the two earlier scalar labels \(0,d\) for which the true leading moments force the same normalized cubic \(d^3/6\).

Now apply the cut before \(w\) with \(R=X(X-d)(X-v)(X-u)\), zero on all possible earlier weighted source labels. The Radau relations factor its primitive exactly:
\[
                   JR(X)=X^2(X-u)^2(4X-3u)/20 .
\]
It is nonzero at \(d,v\), because their distinct nonzero ratios to \(u\) are roots of \(10X^2-12X+3\), neither of which is \(3/4\). Thus no repeat completes before \(w\) either, including the separate zero-mass endpoint case above. All earlier nonzero live rows through \(u\) are exactly the first \(d\)-row, first \(v\)-row, second \(d\)-row and the singleton \(u\), in this order, and there is no other live row before \(w\) except the unique terminal origin.

## A two-moment paid mask contradicts the second singleton

The two rows at \(d\) before \(u\) have independent readings of \(\mathbf G,\mathbf H\). At the first one, \(\mathbf G\ne0,\mathbf H=0\). At the second, \(\mathbf H\ne0\) by the [literal same-clock return identity](../dirk12-fifteen-rank3-one-active-third-debut/README.md):
\[
        \lambda H_i/b_i=(v-d/2)\,(G_i/b_i-d^3/6),
                \qquad \lambda=3(v-d)(v-2d)/d^2.
\]
The amplitude difference is nonzero from the necessary split. Also \(v-d/2\ne0\) by \(5(v/d)^2-14(v/d)+5=0\). The first two weighted moments and the vanished cubic discrepancy at the clean \(u\) give a nonzero normalized tap from its only earlier \(v\)-row:
\[
                       T_v(u)=\frac{u^2(2u-3d)}{6v(v-d)}\ne0 .
\]
Indeed quadrature on \(0,d,v\) has first moments \(u^2/2,u^3/3\), and \(d/u\) cannot equal \(2/3\) by its exact quadratic.

Take any \(S\in P_4\) with \(S(0)=S(u)=JS(u)=0\). Select real \(\alpha,\beta\) so that the true grade-four input
\[
                         \mathbf V=\mathbf W(S)-\alpha\mathbf G-\beta\mathbf H
\]
is zero on both earlier \(d\)-rows, using their independent readings. It is automatically zero on every ghost, the origin and \(u\). Its actual primitive error \(N\mathbf V-\mathbf W(JS)\) is in \(\mathcal B_5\), so at \(u\), \(N\mathbf V=0\) as \(JS(u)=0\). Its only other possible earlier nonzero input is the first \(v\)-row. The tap \(T_v(u)\ne0\) forces \(\mathbf V\) zero there as well. Thus the entire physical input vanishes before \(w\).

At \(w\), the true grade-five error vanishes by singleton, and its input coordinate is \(b_w S(w)\). Actual geometric lower triangularity then gives
\[
                           JS(w)=N_{ww} S(w)
\]
for every such \(S\). But their degree-at-most-five primitives are exactly the span \(X^2(X-u)^2P_1\), by the two double roots and the converse via differentiation. Put \(B=X^2(X-u)^2\). The primitive \((X-w)B\) has value zero and derivative \(B(w)\ne0\), forcing \(N_{ww}=0\). The primitive \(B\) then gives \(B(w)=0\), contradiction. No sixth-grade reverse projection or ordered assumptions on the variable clock positions are used beyond the definite real integrals and scalar quadrature.

## Verification scope

Only the possible *zero-mass interior repeat* reduction invokes the fixed-grid coefficient gate, already checked independently in Python and in the four-version core Lean receipt. All Radau equations, the polynomial primitive factor and the two-singleton argument concern actual unknown real coefficients and are analytic. This proves an exact exclusion of the two-repeat variable grid, not a full native stage-lower theorem. The [three-pair eight-site case](../dirk12-fifteen-rank3-invisible-four-ghost-variable-three-pairs/README.md) is excluded separately. The nine- and ten-label nonterminal cases remain open.
