# Zero residuals force a lower-degree clock relation and a late clean pivot

Assume the [same orders and nonsingular quadratic floor](SIMPLE-LEGENDRE-COMPLETE-INTERSECTION-AND-WEIGHTS.md), but allow actual zero entries of the quadratic residual \(\mathbf g\). The basic argument uses an ordered field for its positive Gram conclusions and characteristic zero for the rank statements. Let
\[
 Z\coloneqq\{i:g_i=0\},\qquad L\coloneqq\{i:g_i\ne0\}.
\]
Projection to a leading prefix always means restriction of the actual unchanged stage rows. It does not recompute a suffix or forget any incoming stage.

## A forced low-degree relation on the nonzero-residual pairs

Let \(N_j\) be the dimension of weight-at-most-\(j\) polynomials in \((x,z)\) of weights \((1,2)\), and let \(T_j\) be the saturated dimension of \(E_j\). Both are zero at negative grades. The difference in passing from grade \(j-2\) to \(j\) is exactly
\[
 (N_j-T_j)-(N_{j-2}-T_{j-2})=\dim\mathcal O_j,
 \qquad \mathcal O_j=\operatorname{span}\{L_{p-j},\ldots,L_j\}.
\]
The latter span is zero if its lower index exceeds its upper index. Every such weighted polynomial is a genuine rooted profile with scalar trace its restriction to \(z=0\), but the evaluation need not fill \(E_j\) in this branch. Let \(I_j\) be the polynomials of weight at most \(j\) vanishing at all pairs. Then \(\dim I_j\ge N_j-T_j\). The trace of \(I_j\) lies in \(\mathcal O_j\) by paid scalar pairing, and it vanishes at every actual zero-residual clock. Define
\[
            r_j\coloneqq
        \operatorname{rank}\bigl(\mathcal O_j\longrightarrow
                            \mathbb K^{\{c_i:i\in Z\}}\bigr)
\]
by ordinary evaluation at the distinct named zero-residual clocks. The zero-trace part of \(I_j\) consists exactly of \(z R(x,z)\) with \(R\) of weight at most \(j-2\) vanishing at all nonzero-residual pairs. Hence
\[
 \dim\{R:\deg_{\rm w}R\le j-2,\ R(c_i,g_i)=0\ (i\in L)\}
                      \ \ge\ N_{j-2}-T_{j-2}+r_j.                 \tag{5}
\]
This is a concrete relation/rank penalty on the complementary pairs, not a count of hypothetical geometric sheets.

For odd \(p=2m-1\) with \(m\) even, \(j=m\) gives a nonzero relation of weight at most \(m-2\) whenever \(Z\) is nonempty, since the two consecutive Legendre values cannot both vanish. If the two-value evaluations at zero clocks have rank two, there are at least two independent such low-degree relations. With only one low-degree relation all zero clocks must lie in the zeros of one common polynomial in \(\operatorname{span}(L_m,L_{m-1})\). For even \(p=2m\), using \(j=m+1\) always gives a relation of weight at most \(m-1\); using \(j=m\) gives weight at most \(m-2\) if even one zero clock is not a root of \(L_m\).

## Zero residuals necessarily carry positive ordinary quadrature mass

Assume \(Z\ne\varnothing\). Choose a nonzero minimum-weight polynomial \(R\) vanishing on all nonzero-residual pairs, and write \(d\) for its weight and \(r(x)\coloneqq R(x,0)\) for its scalar trace, of degree \(a\le d\). The trace is nonzero: if \(R\) were divisible by \(z\), dividing by \(z\) would still give a nonzero relation on those same nonzero sites at strictly lower weight. The numerical vector \(R(\mathbf c,\mathbf g)\) is supported on the literal zero-residual stages. In particular the ordinary order supplies the exact low-degree read
\[
 \sum_{i\in Z} b_i r(c_i)P(c_i)=\int_0^1 r(x)P(x)\,dx
                                  \qquad(\deg P\le p-1-d).          \tag{6}
\]
On the vectors \(R(\mathbf c,\mathbf g)P(\mathbf c)\) with \(\deg P\le\lfloor(p-1)/2\rfloor-d\), the \(B=\operatorname{diag}(\mathbf b)\) quadratic form is the positive definite Gram \(\int_0^1 r(x)^2P(x)^2\,dx\). Thus there are at least
\[
                \lfloor(p-1)/2\rfloor-d+1
\]
**distinct zero-residual clocks with strictly positive aggregate weight and \(r(c_i)\ne0\)**. To justify this with repeated clocks, collapse only the **zero-residual** rows at each clock in this calculation. Their actual signed coefficients are \(\sum_{i\in Z:c_i=\theta}b_i\,r(\theta)^2\), and positive slots of a diagonal Gram realizing a positive definite subspace are at least that subspace's dimension. The full ordinary clock aggregate including nonzero residuals at the same clock is not the one being used. An independent nonzero-aggregate count using (6) and the square of the polynomial vanishing on its effective zero clocks is \(\lfloor(p-1-d-a)/2\rfloor+1\), but does not impose a sign unless the Gram budget is paid.

In particular any zero in the odd branch forces at least two distinct positively weighted zero-residual clocks; likewise in the even branch if a zero clock is off the \(L_m\) roots. In the even branch only one positively weighted zero clock is possible under this test only when all zeros are at \(L_m\) roots and the minimum-weight relation has \(d=m-1\). If there is only one *effective* zero clock in (6), rather than merely one positive coefficient, then additionally \(a=m-1\); (6) makes its trace a scalar multiple of the ordinary degree-\((m-1)\) reproducing kernel at that Gauss root. This last assertion concerns the single-effective-node hypothesis, not all signed cases with one positive weight. All positivity proofs here use rational moments and are valid over ordered fields.

## The first literal zero is a paid clean interpolation pivot

Let \(i_0\) be the first chronological zero-residual index. It is a proper prefix endpoint. Indeed at the floor a zero terminal output weight could be trimmed. If the only zero were \(g_s=0\), the genuine row \(\mathbf b^{\rm row}G\) would lie in the one-dimensional annihilator spanned by \(\mathbf b^{\rm row}M\); its terminal zero and the nonzero terminal coefficient of \(\mathbf b^{\rm row}M\) would force every weighted residual to vanish. Two or more weighted stages are required by the ordinary moment Gram, contradicting an isolated terminal zero.

Restrict now to the leading prefix through \(i_0\). Write \(E_j^{\rm lead},F_j^{\rm lead}\) for its actual spaces and \(M_{\rm lead},G_{\rm lead}\) for the restricted matrices. Saturation restricts literally to \(F_{j+2}^{\rm lead}=M_{\rm lead}E_j^{\rm lead}\). The map \(M_{\rm lead}^{-1}G_{\rm lead}\) preserves \(E_j^{\rm lead}\) through degree \(p-3\) and has one-dimensional kernel spanned by the coordinate at \(i_0\). Zero is semisimple: here the operator is lower triangular with exactly one zero diagonal entry, or one may identify the projection from the earlier coordinate-zero proof. Its image is the kernel of the last row of \(M_{\rm lead}\). Let \(d_0\) be the first genuine degree with a vector zero before \(i_0\) and nonzero at \(i_0\), so \(1\le d_0\le p-2\). For \(j<d_0\) within the budget, \(E_j^{\rm lead}\) misses that kernel and is contained in that image. Consequently \(F_{j+2}^{\rm lead}\) vanishes at \(i_0\); also \(G_{\rm lead}E_j^{\rm lead}=M_{\rm lead}E_j^{\rm lead}\) by dimension and pure inclusion. Induction now gives equality of the actual leading and literal two-coordinate polynomial spaces through grade \(\min(d_0+1,p-1)\). In particular \(d_0\) is the first weighted-polynomial interpolation pivot degree of \((c_{i_0},0)\) relative to all preceding literal pairs, rather than an unmeasured rooted rank.

Let \(f(x,z)\) be any weight-at-most-\(d_0\) polynomial with zero evaluations at the earlier pairs and value \(1\) at \((c_{i_0},0)\). The pivot and the budgeted clean stage actual primitive give the mandatory diagonal relation
\[
             a_{i_0 i_0}
                =\int_0^{c_{i_0}} f(x,0)\,dx.                     \tag{7}
\]
Indeed at \(i_0\) the input vector has earlier zeros and value \(1\), so the actual primitive \(A\) reads its own nonzero diagonal. At that stage all pure residuals through degree \(d_0+1\) are zero, so the scalar primitive must be the same. In particular the first zero residual cannot have clock zero. With common diagonal, the right side is forced to equal \(\gamma\), a relation using the earlier pairs, not just \(g_{i_0}=0\).

An exact point read at nonzero clock through degree \(a=d_0+1\) on the literal leading tableau yields the clean-point lower width \(i_0\ge Q(a+1)=Q(d_0+2)\). One may prove this by right powers of the leading \(A\) from that read: on degree \(j\) their scalar jet rank is \(\min(j+1,a-j+1)\), since \(J^{a-j}P\) already has the forced origin factors and a root at the point of prescribed multiplicity uses independent further factors. The same earlier commutator parity sum applies to this true nonsingular prefix. Since \(i_0<s=Q(p)\), necessarily \(d_0\le p-3\). The vector realizing the stage pivot then belongs to \(E_{d_0}^{\rm lead}\); its image under \(M_{\rm lead}\) has nonzero \(i_0\)-th entry (the diagonal times the nonzero pivot). It follows that the **first nonzero rooted defect at the first zero-residual stage has degree exactly \(d_0+2\)**, which is thus within the paid horizon. Before \(i_0\), every literal prefix has invertible \(G\) and the full two-coordinate flags; the diagonal reconstruction of the companion note applies there as a necessary test without any assumption on subsequent zeros.

This is not a claim that every zero-residual tableau is impossible, or that all later zero rows enjoy the first-zero cutoff without a separate physical rank check. For multiple zeros in a prefix the relevant kernel has several coordinates; its restrictions and the corresponding principal block of \(M\) can mix the old zero pivots.
