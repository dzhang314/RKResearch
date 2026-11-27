# Any quadratic zeros at the ten-stage strict SDIRK8 floor need three distinct clocks

Let \(A,\boldsymbol b\) be a characteristic-zero ten-stage strict SDIRK tableau of order at least eight. Write \(\boldsymbol c=A\boldsymbol1\), \(\boldsymbol g=A\boldsymbol c-\boldsymbol c^{\odot2}/2\), \(G=\operatorname{diag}(\boldsymbol g)\), and \(C=\operatorname{diag}(\boldsymbol c)\). Let \(U=\ker G\) be the physical coordinate space on its zero-residual rows. Use genuine forward spaces \(E_j,F_j\) and reverse \(W_j,Z_j\) with the same grading as the [saturated flag proof](../../lower-bounds/characteristic-zero/sdirk_saturated_weighted_mirror_duality_20261123.md).

**Result.** If \(\boldsymbol g\) has any zero, at least three *distinct physical clocks* occur among its zero rows. The [singleton](../sdirk-eight-singleton-exclusion/README.md) and [exactly-two](../sdirk-eight-two-zero-line/README.md) results already exclude both row counts and any number of zeros sharing just one clock. The proof below excludes all remaining multiplicities on exactly two distinct clocks. It does not rule out three or more distinct zero clocks, or the zero-free case; the overall stage interval stays **10–11**.

## Only one shape could have more than two zeros at two clocks

Assume the zero clocks are \(a,b\), with \(a\ne b\), and let \(m\ge3\) be the number of physical zero rows. As in the earlier packet, \(F_2=\langle\boldsymbol g\rangle\) and \(Z_2=\langle\boldsymbol b^{\mathsf T}G\rangle\), both vanishing on the zero rows. For the reverse statement, the last output weight is nonzero by trimming against the stage floor; if the last residual vanished, proportionality with the nonzero last coefficient of \(\boldsymbol b^{\mathsf T}M\) would force all active weights onto two clocks, contradicting ordinary quadrature.

A supported degree-one column has zero scalar trace: multiply its at-most-linear trace by \(N(X)=(X-a)(X-b)\), and test with all degrees at most three using the paid ordinary moments. The resulting polynomial has degree at most three, so the Hilbert matrix detects it. Thus \(E_1\cap U=0\), \(F_3=GE_1\), and \(F_3\) vanishes at the zero rows. Every degree-three column supported on \(U\) therefore has equal values on all zero rows at a common clock. Its dimension is at most two.

Similarly, for each supported degree-two row of \(W_2\), its scalar trace \(r\) has \(Nr\) orthogonal to every degree at most three, hence \(Nr\) is proportional to \(L_4\). If the trace is zero, its pure part (a multiple of \(\boldsymbol b^{\mathsf T}G\)) is also zero by its support. Thus \(\dim(W_2\cap U_{\rm row})\le1\). The [two-sided support identity](../sdirk-eight-two-zero-line/README.md) says
\[
 m=\dim(E_3\cap U)+\dim(W_2\cap U_{\rm row}).
\]
Therefore \(m=3\), and both bounds are equalities. In particular \(a,b\) must be distinct fourth Gauss clocks, and the trace of the supported reverse line is proportional to
\[
                          r(X)=L_4(X)/[(X-a)(X-b)] .
\]

In fact \(E_2\cap U\ne0\). Suppose the contrary. Then \(E_3\cap U\) consists exactly of the two independent indicators of the physical zero groups. The single-group probe of degree three gives normalized scalar traces proportional to \((X-b)r(X)\) and \((X-a)r(X)\), respectively; neither trace can vanish because \(F_3\) is clean on the zero rows. Since the genuine \(F_3\) is \(\langle\boldsymbol g,C\boldsymbol g\rangle\), the two group columns have affine corrections \(H_a,H_b\):
\[
 (c_q-b)r(c_q)+g_q H_a(c_q)=0,\qquad
 (c_q-a)r(c_q)+g_q H_b(c_q)=0\qquad(g_q\ne0).
\]
If there are at least three distinct clocks with \(g_q\ne0\), the quadratic \((X-a)H_a-(X-b)H_b\) vanishes identically by eliminating \(r\) at those clocks. It follows that \(H_a=\lambda(X-b)\), \(H_b=\lambda(X-a)\), whence \(r(\boldsymbol c)+\lambda\boldsymbol g\) is a nonzero degree-two column supported on \(U\). At least one linear factor is nonzero at each physical row because \(a\ne b\), and \(r(a),r(b)\ne0\) by simplicity of \(L_4\). This contradicts the premise. If there are at most two distinct nonzero-residual clocks, four distinct active clocks are still needed by the Hilbert rank. Thus there are exactly two others, disjoint from \(a,b\), and the four-node order-eight scalar quadrature has monic nodal polynomial \(L_4\), by orthogonality. Now \(r(\boldsymbol c)\) itself is the nonzero supported degree-two vector, also a contradiction.

Consequently a genuine supported degree-two column exists, and its nonzero scalar trace is proportional to \(r\) by the same four \(N(X)X^k\) probes. Normalize it to be
\[
           \boldsymbol v=r(\boldsymbol c)+\alpha\boldsymbol g \in E_2\cap U .
\]
In particular its literal value at every zero row at clock \(a\) or \(b\) is exactly \(r(a)\) or \(r(b)\).

## A forward anchored graph excludes even this shape

Take \(a\) to be the *first chronological zero clock*. Its row index is at least three. To see this, the prefix scalar columns \(\boldsymbol1,\boldsymbol c\) are independent by the two paid reads \(\boldsymbol e_i^{\mathsf T},\boldsymbol e_i^{\mathsf T}A\) at this clean stage; their determinant is \(-a^2/2\ne0\). Both are annihilated by the actual prefix row \(\boldsymbol e_i^{\mathsf T}M\), nonzero at \(i\), because the grade-three pure space vanishes here. The prefix must have width at least three.

Forward application of \(A\) to the supported \(\boldsymbol v\) at this earliest zero sees only the common diagonal. Grade three is clean there, so
\[
                           \gamma=(Jr)(a)/r(a).
\]
No reflected anchor or normalization by any output weight is used. By the exact replay below, \(R=r(\gamma)\ne0\). Since the first stage has nonzero residual \(g_1=\gamma^2/2\), it is off the support of \(\boldsymbol v\), so \(\alpha=-R/g_1\). This forces the actual graph \(g_q/g_1=r(c_q)/R\) on **every** nonzero-residual row (even a silent one).

Write \(r(X)=X^2+kX+q\). The second row is nonzero-residual, and its normalized gap \(u=(c_2-\gamma)/\gamma\ne0\). Its usual literal residual ratio \(1+2u-u^2\) and the graph give
\[
                 u=\frac{2R-\gamma(2\gamma+k)}{R+\gamma^2},
\]
where the denominator is checked below. Use the [actual first three row identities](../clock-localized-tail/tied-stage-floor/FIRST-THREE-ROWS-AND-PHYSICAL-LEVEL-OBSTRUCTIONS.md), which do not require special weights, support, or signs. If row three is itself the first zero, the star case would give \(g_3=g_2\ne0\), so the arithmetic case would force \(a=\gamma(1+2u)\). Otherwise row three obeys the quadratic graph and the star or arithmetic case forces respectively
\[
\begin{aligned}
 S &=R\kappa(u)-r(\gamma(3-u))=0,\\
 T &=\left(R\kappa(2u)-r(\gamma(1+2u))\right)(-2+u+4u^2-u^3)
                  +4Ru^2(3u-2)=0,\qquad\kappa(t)=1+2t-t^2 .
\end{aligned}
\]
As in the earlier packet, this \(T\) is cleared; there is no denominator from the possible neighboring tap.

The [exact rational replay](check_two_clocks.py) checks the six nonvanishings \((\gamma,R,R+\gamma^2,a-\gamma(1+2u),S,T)\) in all twelve directed pairs of distinct fourth Gauss clocks. In increasing scalar-root box indices, the signs are:

| Directed pair | Signs |
|---|---|
| \(1,2\) | +++--+ |
| \(1,3\) | +++--+ |
| \(1,4\) | +++--+ |
| \(2,1\) | +++--+ |
| \(2,3\) | +--+++ |
| \(2,4\) | +---+- |
| \(3,1\) | -++++- |
| \(3,2\) | +-++-- |
| \(3,4\) | +-++-+ |
| \(4,1\) | +++-+- |
| \(4,2\) | -++++- |
| \(4,3\) | +-++-+ |

All possibilities are therefore excluded. The script replays the previously verified root brackets and rational interval arithmetic before applying the different, **forward** diagonal anchor. It uses no floating point or root search. The interval certificate is real, but an embedding of the finite field \(\mathbb Q(a,b)\) into \(\mathbb C\) sends both clocks to real roots, so nonvanishing transfers to any ambient characteristic-zero coefficient field. No ordering on the entire field is used. This additional multiple-zero classification is a source-level argument with an exact replay, not a new Lean theorem.
