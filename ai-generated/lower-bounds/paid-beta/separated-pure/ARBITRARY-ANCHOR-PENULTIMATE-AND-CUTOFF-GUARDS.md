# Exact arbitrary-anchor penultimate input and the stage-cut guard

Use the first file for the separated pure-rank inputs. This note checks the other two dependencies of the zero/one-spare detector cutoff 6c60c6ae…: the literal penultimate row at an arbitrary anchor, and the separate strict size inequality needed to turn a tail reweighting into a contradiction.

## 1. Which proof gives the arbitrary-anchor result?

The primary source is [the penultimate paid tap](../../../research/clock-localized-tail/PENULTIMATE-PAID-TAP.md), content SHA-256 48505b2eb317dc0be0aaa1bffafac43cc67c2efac419d578a03b1b1dae84c9fa, manifest f5986589910aec4c195f441b39f6020755b1c3fc9a46aea78579f1f8dd6fa339. Its definition and theorem are at lines 14–27, before the separate midpoint application. It fixes an arbitrary \(g\ge0\), not \(g=d\). Let \(r\) be the effective weighted rooted size, \(m\) its shift, \(t\) the last actual index of the output row \(\boldsymbol\beta\), and \(L=r-1-g\). Its actual late subspace consists of the numerical vectors in \(E_g\) vanishing before row \(t-L\), equivalently through row \(t-L-1\).

The original source writes this weighted output as a tap of an ordinary tableau. The arbitrary weighted interpretation is justified in [the weighted detector stage bound](../07-WEIGHTED-DETECTOR-STAGE-BOUND.md), lines 11–21, content 9ae0a6cc26f3df84cdefc6315066c666ec6e54c3288c1d6a19d0fef02896ea3d, manifest be02d3f65574827f2f272948a566d4936b08a9893a39fd6660335124faa270b8. In fact the dependency can be checked directly. For an actual exact weighted row \(\boldsymbol\beta\),
\[
 \ell_m(JP)=\ell_{m+1}(P),\qquad
 \ell_m((1-X)^j P)=\frac{(m+j)!}{m!}\ell_{m+j}(P).
\]
Here \(\ell_m(P)=\int_0^1(1-X)^mP(X)\,dX/m!\) and \(J\) is the formal primitive from zero. Thus if \(a+b+j\le L\), the actual rooted tests imply
\[
 \boldsymbol\beta A^aY^jA^b\cdot\mathbf v
     =\frac{(m+a+j)!}{(m+a)!}\,\boldsymbol\beta A^{a+b+j}\cdot\mathbf v.
                                                                    \tag{1}
\]
No model separation is needed: make the calculation on any formal representation of the genuine numerical input, and both sides are the same resulting numerical reads. Similarly \(D E_i\subseteq F_{i+2}\) for \(D=CA-AC-A^2\), from the formal identity \(XJ-JX=J^2\). Consequently the exact weighted output and any paid adjoint words annihilate the actual numerical \(D A^{i-1}\mathbf v\) when their total budget satisfies \(i+a+j+1\le L\). These are all the scalar premises of the penultimate source. The field payment is \((m+r)!\), so every number and factorial in these operations is paid.

If the auxiliary final coordinate \(\mathbf e_t\) at clock 1 is adjoined, work with \(H_g=E_g+K\mathbf e_t\), in every grade of the same argument. Strictness and \(c_t=1\) give \(A\mathbf e_t=Y\mathbf e_t=D\mathbf e_t=0\). Every positive word in (1) kills it on both sides; at cost zero the identity is tautological. Thus the proof, including its next-grade comparison, uses \(H_g\) directly without requiring the auxiliary direction to be independent at that anchor.

The source establishes the needed properties in the following places.
* **Complete physical suffix and reciprocal coefficients:** lines 37–71. For \(\mu_j=\boldsymbol\beta A^j\cdot\mathbf v\) and \(\mu_L\ne0\), the suffix has exactly \(L+1\) relevant rows and its \(L\) adjacent edges are nonzero. In the actual basis \(\boldsymbol\eta_i=A^i\mathbf v\), the first subdiagonal coefficient of \(Y\) is \(m+L-i-y_i\mu_{L-1}/\mu_L\), where \(y_i=1-c_{t-L+i}\). Equal neighboring actual clocks force this entry zero by the two-dimensional diagonalizable quotient. Let \(\mathbf u_i\) be the leading-one suffix vector with the first \(L-i\) taps zero; its coefficients are the reciprocal series of \(\mu_{L-j}/\mu_L\).
* **Rooted purity gives the top geometric relation:** lines 72–101. The exact physical equality \(D\boldsymbol\eta_{i-1}=(y_{i-1}-y_i)\mathbf u_i\) holds by the chronological pivot and paid pure taps. The one- and two-\(Y\) tests at a clock jump force two adjacent endpoint clocks if the tested reciprocal coefficient is nonzero. Thus for \(L\ge5\) the relevant coefficients \(r_2,\ldots,r_{L-3}\) are zero, giving the reverse-geometric law beginning with \(\mu_{L-2}=(\mu_{L-1}/\mu_L)^2\mu_L\). The exact index allowing a specific \(r_j\ne0\) to force initial clock equalities is \(1\le i\le L-j-1\) in its equation (6); this is independent of \(g\).
* **Penultimate zero when the top is visible:** lines 102–115 for \(L\ge6\). The two actual vectors \(A\mathbf v\) and \((Y-y_0I)\mathbf v\) lie in the next genuine \(H_{g+1}\), vanishing through one additional physical row. Its budget is precisely \(L-1\); its penultimate-to-top ratio is uniform by the already proved quadratic relation and the actual vector \(A\mathbf v\) fixes that ratio. Inserting \((Y-y_0I)\mathbf v\) and using (1) forces the original ratio to be zero. With that ratio zero, equal consecutive actual clocks are forbidden, so the reciprocal equation also kills \(r_{L-2}\). This proves \(\mu_2,\ldots,\mu_{L-1}=0\) on top-visible vectors, and by linearity on the whole late subspace when the top row is not identically zero.
* **Penultimate zero when the top path is unavailable:** lines 116–end for \(L\ge6\). If \(\mu_L=0,\ \mu_{L-1}\ne0\), at most two actual \((L-1)\)-edge paths can contribute on the \(L+1\) available suffix rows. If there are two then their omitted rows are adjacent endpoints of a missing adjacent edge. Paid one-\(Y\) words of length \(L\) make every common row's reflected clock zero. Among the \(L-1\) shorter insertion ordinals, at most four can see either remaining adjacent position. A zero actual response conflicts with the nonzero exact \(\mu_{L-1}\) multiple. This counts literal suffix positions, not formal trees or an order midpoint.

Budget \(L=5\) uses the separately sealed order-eleven extension [the order-eleven threshold](../08-ORDER-ELEVEN-THRESHOLD.md), lines 11–35, content 9604e44d2956ae2eacb1f650e9925f7e1c84cd8f6e48236a66f5c78f7ff43de6, manifest 172152e6d53e7c327243f50d9a6d856ab2bb51aeb62f625d0d1aad3efa71cfee. Its arguments are similarly independent of the anchor:
* In the top-visible next-grade space, the budget is 4. If its first two physical reflected clocks differ, equation (6) of the primary proof at \(j=2,i=1\) still forces \(r_2=0\), hence proportionality of the top and penultimate rows. If those clocks coincide at \(y\), diagonalizability in the same two-dimensional quotient forces \(m+4-y\,\mu'_3/\mu'_4=0\) for every top-visible vector, which again gives one fixed ratio. The general two-level comparison then forces the original budget-five penultimate to zero. With the ratio zero, the same adjacent-clock calculation forces \(r_3=0\), so the other intermediate zeros used in the top-visible subcase also hold.
* In the missing-top-path case there are six physical positions and four insertion ordinals. Only the central adjacent pair 2 and 3 could be seen by all four ordinals. At insertion ordinal 0, the only possible active starting site is physical 2, and a three-edge path from there has to be \(2\to3\to4\to5\). The edge \(2\to3\) is the already missing edge, so the response is again zero, contrary to the paid nonzero multiple of \(\mu_4\).

Finally the localized issue requires no additional theorem: take \(a=b=0,j=\ell\) in (1) for a genuine vector supported at one clock \(x\). It gives
\[
 \boldsymbol\beta A^\ell\cdot\mathbf v
    =\frac{m!}{(m+\ell)!}(1-x)^\ell\boldsymbol\beta\cdot\mathbf v
    \quad(1\le\ell\le L).
\]
At \(\ell=L\) this is the bare physical last-path cutoff. At \(\ell=L-1\) on the literal late kernel, the penultimate theorem implies zero nonendpoint output. Both remain valid in the augmented spaces by the preceding word argument. This is the exact anchor input in the detector-tail filling. No inference from a merely formal residual or from a missing model at an arbitrary grade is made.

## 2. The strict short-prefix threshold at each application

The arbitrary-anchor detector theorem does not say that rank saturation alone contradicts a full-order tableau. It gives an early factor only when the **separate literal cut**
\[
                         k+1<N_*,\qquad k=s-L-1
\]
is satisfied. Here \(N_*\) is a valid common lower bound for each weighted reweight/next-tap read of effective size \(r-1\) or \(r-2\), at its actual shift. The older paid baseline gives the common choice \(N_*=\lceil3(r-2)/2\rceil-2\), requiring retained size at least five. If the new weighted order-eleven floor is independently admitted and \(r-2\ge11\), then the stronger common choice is \(N_*=\lceil3(r-2)/2\rceil\).

For \(r=2d+1\), these are \(3d-3\) and \(3d-1\), respectively. They give the following distinct guards:

| Application | Last permitted support of the reweighted row, \(k+1\) | Old common floor \(3d-3\) | New floor \(3d-1\), if admitted and \(d\ge6\) |
|:--|:--|:--|:--|
| Equality transfer at \(s=3d+1+h,\ g=d\) | \(2d+h+1\) | \(d>h+4\) | \(d>h+2\) |
| One surplus at \(s=3d+2+h,\ g=d\) | \(2d+h+2\) | \(d>h+5\) | \(d>h+3\) |
| Re-anchor \(g=d+j\) at a measured spike, \(s=3d+2+h\) | \(2d+h+j+2\) | \(d>h+j+5\) | \(d>h+j+3\) |

In the last row independently require the new budget \(d-j\ge5\) (or \(\ge6\) without the budget-five extension). In particular the one-surplus prose in SURPLUS-TRANSFER-AND-SPIKE-OUTPUT-CUT.md inherits this guard; the equality-transfer condition \(d>h+4\) by itself is not enough. At \(d=5\) the smallest retained weighted size is nine, below the new order-eleven theorem. The old common floor is 12 there. No general increase to that retained weighted floor is asserted, and equality with the cut \(k+1\) does not yield a contradiction.

This separates the pure-dimension inputs, paid penultimate inputs, and literal stage inequalities. A special verified weighted size-nine or other stronger retained-size theorem could be inserted only if it covers **every** shifted or reweighted output used in the appropriate branch; it cannot be inferred from a floor for only one final residual profile.
