# The two-active-off-clock five-zero graph is impossible in characteristic zero

Consider a strict ten-stage SDIRK tableau \(A,\mathbf b\) of ordinary order at least eight over a characteristic-zero field, with common nonzero diagonal \(\gamma\), \(\mathbf c=A\mathbf1\), and quadratic defect \(\mathbf g=A\mathbf c-\mathbf c^{\odot2}/2\). Assume exactly five physical quadratic zeros and a genuine graph as the unique supported quadratic direction. This packet treats the case of **two** distinct off-zero clocks with live output weights.

**Result.** The two-active graph is impossible over every characteristic-zero field. Combined with the [no-active graph proof](../sdirk-eight-five-zero-graph-arithmetic-live/README.md) and [one-active graph proof](../sdirk-eight-five-zero-graph-one-active/README.md), **every exactly-five-zero characteristic-zero candidate must have pure-polynomial support and at least one active off-zero clock**. This is a restricted structural result, not a 10-stage exclusion.

## 1. Actual reflected pure rows and front phase

By the [support census](../sdirk-eight-five-zero-support-rank/README.md), the five off-zero rows are two live pairs at two distinct clocks (each pair has equal nonzero residual and opposite nonzero weights), plus one individually silent off-zero at a third clock. Write \(N=A-\gamma I\), \(C=\operatorname{diag}\mathbf c\), \(G=\operatorname{diag}\mathbf g\), \(M=CA-AC-A^2\), and \(\mathbf z^\mathsf T=-\mathbf b^\mathsf T M/2\).

The pure row \(\mathbf b^\mathsf T G\) is nonzero and spans \(Z_2\), so it is proportional to \(\mathbf z^\mathsf T\). In particular physical stage 10 (whose last pure value is \(\gamma^2 b_{10}/2\ne0\)) lies in an active pair. Its common reflected relation is
\[
 \kappa_R \mathbf z^\mathsf T N
 =\mathbf z^\mathsf T((1-\gamma)I-C),\qquad
 \kappa_R=1+2v-v^2,\qquad v=(c_{10}-c_9)/\gamma .
\]
Because the pure row is nonzero at two distinct clocks, \(\kappa_R\ne0\). The literal penultimate row is live and its normalized reflected residual is \(\kappa_R\), so row 9 is off-zero at the other pair's clock. The [literal reverse ghost gate](../sdirk-eight-four-zero-gaussian-rear/README.md) forbids a silent row 8 here: it would require a nonzero \(z_8\). Thus row 8 is live at a distinct clock and has zero quadratic residual. Its reflected phase cannot be a star, which would have third reflected residual \(\kappa_R\ne0\). In the arithmetic phase the division-free third-zero gate gives
\[
 Q(v)=4v^3-12v^2+3v+2=0 .
\]
Equivalently, the literal arithmetic residual after multiplication by its cubic denominator is \(-\kappa_R Q(v)/2\). This scalar gate and the absence of a zero \(\kappa_R\) are used before any recovered clock division.

The same reflected relation shows that \(\mathbf z^\mathsf T,\mathbf z^\mathsf T N\) span exactly the **two literal pair differences**. They are independent since the two pair clocks are distinct, and span \(Z_3=\operatorname{Ann}(E_4)\). Thus each off pair agrees on all elementary columns through grade four, although we do not assume separate agreement through grade five.

There are three earlier off-zero rows, all at different clocks (one mate of each rear pair, plus the silent off row). The first two stages are off-zero because the literal forward ratio is nonzero with multiple distinct off clocks. Hence the first physical zero is at row 3 or 4. Normalize throughout by \(A'=A/\gamma,\;\mathbf x=\mathbf c/\gamma,\;D=1/\gamma\). The last zero at row 8 is
\[
 s=D-1-2v,\qquad x_{10}=D-1,\qquad x_9=D-1-v .
\]

## 2. Two ordinary possibilities and forward gates

Ordinary mass from the two equal-clock active pairs cancels. There are at least four nonzero scalar labels among the zero rows. If there are only four, every live zero clock is Gaussian by ordinary orthogonality and the four-site Vandermonde; a canceled group cannot consume two of the five physical zeros and still leave four live sites. Row 8 is a live zero, so this branch requires \(L_4(s)=0\), with \(L_4(T)=70T^4-140DT^3+90D^2T^2-20D^3T+D^4\). **Every literal frame below has \(L_4(s)\ne0\)** by exact field arithmetic, excluding this branch even for a repeated or silent fifth zero.

In the remaining branch all five ordinary sites are live and have distinct clocks; none is Gaussian. The supported graph column is \(\mathbf q=P(\mathbf x)-\mathbf g/\gamma^2\). Its order-three discrepancy is clean on the zeros because \(F_3=GE_1\). The order-four \(T P\) discrepancy on the five zeros is in the line of \(L_4\): the two live pairs cancel each grade-four read, and four ordinary clock-power tests give this line. Thus the first zero \(a\) satisfies \(JP(a)=P(a)\). At the second zero \(b\) the [literal one-tap discrepancy](../sdirk-eight-five-zero-graph-arithmetic-silent/README.md#2-three-supported-equations-in-the-same-arithmetic-pencil) gives
\[
 L_4(a)[a(JP(b)-P(b))+bP(b)-J(TP)(b)]-
 L_4(b)[aP(a)-J(TP)(a)]=0 .
\]
The first zero value \(P(a)\) is nonzero: \(M\mathbf q\) has a nonzero restriction to the zeros by triangularity, and spans the same \(L_4\) line on the zeros. Its first zero value is a nonzero diagonal factor times \(P(a)\). In particular \(a\ne0\) by the first diagonal read.

In each frame the first and last zero clocks \(a,s\) determine a monic cubic on the remaining ordinary clocks via the masked \(3\)-by-\(3\) Hankel recurrence. The pivot is nonzero by the [five-site Hankel factorization](../sdirk-eight-ordinary-hankel-pivot/README.md). The second chronological zero may be **any** of that cubic's three roots; the exact check never fixes its order by sorting.

## 3. First zero at physical row 4

All three early off-zero rows now precede the first zero. In the two literal forward phases their clocks are \((1,1+u,3-u)\) (star) or \((1,1+u,1+2u)\) (arithmetic). Choose an ordered pair of these three to be the mates of rows 10 and 9. Their difference is \(v\), so this pins \(u\) affinely in \(v\), and \(D\) is one plus the mate's clock for row 10. These are six directed assignments for each forward phase; there are no implicit Vandermonde-order assumptions.

The graph \(P\) is known: \(P_0=2T-1-T^2/2\) in the star; in arithmetic it is \(P_0+\lambda (T-1)(T-1-u)\) with \(\lambda=(-2+3u)/(-2+u+4u^2-u^3)\) from the [actual forward interpolation](../sdirk-eight-five-zero-graph-four-ordinary-duplicate/README.md). The first normalized zero \(a\) is a root of the exact cubic \(JP(a)-P(a)\). Mask \(a,s\) and use the ordinary cubic on \(b\), clearing the ordinary pivot by scaling the clock. Norm the second-zero gate over this monic cubic and take its gcd with the guarded first polynomial over the irreducible cubic field of \(v\). All twelve gcds are constant. The only two nonempty structural removals are linear factors with \(P(a)=0\), in the arithmetic ordered mate assignments \((2,1)\) and \((3,2)\). No other root is lost.

## 4. First zero at physical row 3

The phase is arithmetic and the first zero is \(a=1+2u\) with \(Q(u)=0\). The graph pencil is \(P=P_0+\lambda(T-1)(T-1-u)\). Since only one early off row is silent, at least one of the first two physical off rows is a mate of row 9 or 10. For each of the four choices this pins \(D\) from \(u,v\).

Now use an **additional supported reverse read**. Weight \(\mathbf q\) by \(\mathbf b\) to obtain a grade-two row supported on the physical zeros, with scalar trace \(P\) in the normalized coordinates. Its right primitive under \(A'\) has scalar profile \(J_D^*P(T)=JP(D)-JP(T)\). Its grade-three pure difference lies in \(Z_3\), already shown off-supported. At row 8, there are no later supported entries and the row is live, so the primitive is a clean diagonal:
\[
 JP(D)-JP(s)=P(s).
\]
The argument uses chronological support on the actual tableau, not a reversed method assumption.

The exact coefficient tensor of \(Q(u),Q(v)\) has a verified primitive element \(u+2v\) and splits into field factors of degrees \(3\) (equal gaps) and \(6\) (different gaps). In the resulting eight mate frames, the reverse diagonal is inconsistent in two. In the other six it pins \(\lambda\) uniquely. Then the second forward gate has constant gcd with the full ordinary cubic in \(b\) in each frame. This covers every algebraic arrow for the selected mate, whether or not the other first off stage is also a mate.

Run `python check_zero4.py` and `python check_zero3.py` with SymPy 1.14. Both are exact complete field checks. The underlying supported primitive identities are shared with earlier scalar proofs; the two-sided rooted ingress and coefficient extensions are mathematical source proofs and exact replays, not a standalone native `HasOrder` theorem.
