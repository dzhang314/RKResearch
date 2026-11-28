# Seven quadratic zeros at three silent off clocks: zero reflected ratio excluded

Let \(A,\mathbf b\) be a ten-stage strict SDIRK tableau of ordinary order at least eight over a characteristic-zero field, with common nonzero diagonal \(\gamma\). Set \(\mathbf c=A\mathbf1,\ \mathbf g=A\mathbf c-\mathbf c^{\odot2}/2\). Assume exactly seven physical zeros of \(\mathbf g\), and that the three physical off-zero clocks are pairwise distinct.

**Result.** The reflected second defect ratio cannot be zero. Together with the [separate low-label nonzero-ratio exclusion](../sdirk-eight-seven-zero-three-clock-five-label/README.md), this leaves only **seven distinct literal zero labels and nonzero reflected ratio** in the three-off-clock chart. There is no change to the unrestricted stage interval.

## 1. Literal terminal duplicate and ordinary cubic

By the [rank census](../sdirk-eight-seven-eight-zero-census/README.md), all off weights are silent and the pure rows \(\mathbf z^\mathsf T=-\mathbf b^\mathsf T(CA-AC-A^2)/2\) and \(\boldsymbol\eta^\mathsf T=\mathbf z^\mathsf T(A'-I)\) are supported on the seven zero rows \(U=\ker\operatorname{diag}(\mathbf g)\), where
\[
 A'=A/\gamma,\quad \mathbf x=\mathbf c/\gamma,\quad
 D=1/\gamma,\quad s=x_{10}=D-1,\quad t=x_9=s-v .
\]
Here \(C=\operatorname{diag}(\mathbf c)\). The two pure rows span \(Z_3\), and have nonsingular restriction at rows 9 and 10. If \(\kappa=1+2v-v^2=0\), then \(\mathbf z^\mathsf T(\operatorname{diag}(\mathbf x)-sI)=0\) by checking those two physical coordinates. Thus \(\mathbf z^\mathsf T\) is supported at \(s\), and \(z_{10}\ne0\) and \(\sum_i z_i=0\) force a second literal zero at \(s\).

The [literal ghost gate](../sdirk-eight-four-zero-gaussian-rear/README.md) excludes a silent row 8, which would have nonzero \(z_8\) at a different clock. The last three physical rows are live zeros at distinct clocks. Put \(r=x_8=s-w\), where \(w=2v\) or \(2-v\) in the two phases. The actual first two strict rear taps give
\[
 \eta_8/\eta_9=b_8p_R/(b_9v),\qquad
 2vp_R=2wv+1+2w-w^2,\qquad v^2-2v-1=0 .
\]
Both coordinates are nonzero. If there were at most five zero labels, the pure moments of \(\boldsymbol\eta\) through degree four would force zero aggregates at \(r,t\) and hence a duplicate at each, in addition to the terminal duplicate. This leaves at most four labels, which by ordinary rank would all be Gaussian; the actual Gaussian rear triple is already excluded by the two exact resultants in the [five-label packet](../sdirk-eight-seven-zero-three-clock-five-label/README.md#1-clock-multiplicities-force-a-five-label-arithmetic-rear). There are therefore exactly six distinct zero labels, one of which is doubled at \(s\) and all five others are singletons. In particular \(r,t\) are unique and live.

Write \(P_3=(T-s)(T-t)(T-r)\) and \(P_6=P_3 Q_3\), where \(Q_3\) is the monic cubic on the other zero labels. Let \(I_D(T^j)=D^j/(j+1)\). As ordinary mass is on \(U\), the cardinal numerators
\[
 B(T)=I_{D,X}\bigl((P_6(X)-P_6(T))/(X-T)\bigr)
\]
satisfy \(B(x)=P'_6(x)\sum_{i:x_i=x,\ i\in U} b_i\). This equation uses the actual aggregate at \(s\). The six distinct aggregates of \(\boldsymbol\eta^\mathsf T\) form a nonzero barycentric row by its five pure moments. Since \(r,t\) are singletons, the literal tap ratio implies \(p_R B(r)=v B(t)\). Thus the coefficients of \(Q_3\) satisfy three linear moment equations: \(I_D(P_6)=I_D(T P_6)=0\) and the ratio at \(r,t\).

## 2. A fourth reverse read survives the duplicate

Let \(e\) be the latest of the four zero rows before physical row 8, also writing \(e\) for its clock. It may be the early occurrence of \(s\), or one of the three roots of \(Q_3\). Set \(R=(T-r)(T-t)\) and start with the literal weighted quadratic row \(\mathbf b^\mathsf T R(\operatorname{diag}(\mathbf x))\). Subtract a multiple of \(\mathbf z^\mathsf T\) to kill its physical terminal coordinate; its scalar profile stays \(R\). Because \(\mathbf z^\mathsf T\) has support exactly on the two copies of \(s\), with opposite entries, the corrected input at the early copy is the full ordinary aggregate at \(s\) times \(R(s)\). The other entries are unaffected.

The corrected input vanishes on all four later categories: physical stages 8, 9, 10 and every silent off row. Its right \(A'\) reads are zero at \(t\) and at the terminal coordinate, and diagonal at the physical row of \(e\). The pure error from the right primitive \(J_D^*R(T)=JR(D)-JR(T)\) lies in \(Z_3\). When \(e\ne s\), its input and read involve a singleton. When \(e=s\), take the aggregate of the physical error at \(e\) and at row 10; the \(\mathbf z^\mathsf T\) component cancels and the diagonal still uses the entire aggregate. At \(t\), the same pure \(\boldsymbol\eta\) multiplier is seen. Multiplying each by its ordinary nodal derivative and using the barycentric aggregate row gives
\[
             [R(e)-J_D^*R(e)]\,B(e)+J_D^*R(t)\,B(t)=0. \tag{1}
\]
This is valid whether the latest early zero is the duplicate or a singleton. In particular it never equates a physical terminal weight to the total weight at its clock.

## 3. Exact diagonal projections, including singular guards

The three ordinary coefficient rows above give a Cramer pivot \(\Delta_{\rm raw}\) of degree 12 in \(D\), with three numerators of degrees 15, 14 and 13. Their joint gcd in \(\mathbb Q(v)[D]\) is \(D^6\) up to a unit, in each rear phase. If the pivot vanished at a solution, the numerators would also vanish, impossible at \(D\ne0\). After removing the common \(D^6\), write the cleared cubic as \(\widehat Q_3=\Delta Q_3\) and use the corresponding \(\widehat{B}=\Delta B\) in (1).

There are two independent necessary diagonal projections:

* If \(e=s\), substitute \(s\) in (1).
* If \(e\ne s\), the cubic \(\widehat Q_3\) and the cleared left side of (1) must have a common root, so take their resultant in \(e\).

The raw degrees in \(D\) are 10 and 90. The only factors removed are exact divisors of the guards \(D,\ \Delta,\ \widehat Q_3(s),\ \widehat Q_3(t),\ \widehat Q_3(r)\); all are nonzero at a solution. The guarded degrees are 4 and 18, with one irreducible factor each over the quadratic \(v\) field. Whether \(e\) has any further properties is not assumed at this stage; on each diagonal fiber the replay reconstructs the cubic and tests every possible \(e\) satisfying the corresponding version of (1).

## 4. Geometric forward checks in all four cells

As in the [five-label forward reductions](../sdirk-eight-seven-zero-three-clock-five-label/README.md#2-ordinary-projection-and-actual-supported-forward-reads), the first two physical off clocks are \(1,1+u\), and the first zero follows either two off rows (physical row 3) or three (physical row 4). In the four early zeros, all clocks are distinct; let \(a,b\) be the first two, so both differ from the latest early clock \(e\). The residual graph is \(P=P_0+\lambda R_0\), with \(P_0=2T-1-T^2/2\), \(R_0=(T-1)(T-1-u)\). Its necessary literal first and second reads are
\[
 \begin{split}
 JP(a)-P(a)&=0,\\
 \mathcal G(P;a,b)
 &=L_D(a)[(b-a)P(b)+aJP(b)-J(TP)(b)]\\
 &\phantom{={}}-L_D(b)[aP(a)-J(TP)(a)]=0 ,
 \end{split}
\]
where \(L_D(T)=70T^4-140DT^3+90D^2T^2-20D^3T+D^4\).

For a **physical row-3 zero**, \(a=1+2u,\ Q(u)=4u^3-12u^2+3u+2=0\). Then \(JP_0(a)-P_0(a)=-Q(u)/3=0\) just as for a **physical row-4 zero after a star front**, where the graph is exactly \(P_0\). The replay finds \(JP_0(a)-P_0(a)\ne0\) at every possible early pair in all cells, rejecting both placements directly.

For a **row-4 zero after an arithmetic front**, use the exact cleared graph \(P_\sharp=H(u)P_0+(3u-2)R_0\), \(H(u)=-2+u+4u^2-u^3\ne0\) from the literal front tap. Substitution into the two linear graph gates gives polynomials of degree at most three in \(u\). At least one has unit leading degree three, and their residue gcd is constant for every directed early pair. This rejects every \(u\), not just the base-field rational residues.

The fixed checks are:

| Rear phase | Latest early clock | Exact guarded degree | \(p\) | Simple \(v\) residue | Degrees of residue factors |
|---|---|---:|---:|---:|---|
| Star | Duplicate \(s\) | 4 | 17 | 12 | 1, 3 |
| Arithmetic | Duplicate \(s\) | 4 | 17 | 12 | 1, 3 |
| Star | New clock | 18 | 23 | 6 | 1, 1, 2, 4, 5, 5 |
| Arithmetic | New clock | 18 | 239 | 100 | 2, 4, 5, 7 |

The simple root of \(v^2-2v-1\) embeds the coefficient field into \(\mathbb Q_p\); the exact projection leading coefficient is a unit. Every algebraic \(D\) candidate is thus integral and reduces to a checked root. For a residue factor of degree \(h\), the proof checks **all** its roots in \(\mathbb F_{p^{6h}}\), large enough to contain every root of the reconstructed cubic. Pivots and distinctness are verified in each fiber, together with all admissible choices of \(e\). The unit-degree front polynomial makes any actual \(u\) integral there, so the gcd contradiction transfers to characteristic zero. No claim about arbitrary paid characteristic follows.

## 5. Replay and scope

Run `python check_zero_ratio.py REAR PLACEMENT` with `REAR=star,arith` and `PLACEMENT=s,new`, SymPy 1.14 and python-flint 0.8. The four checks use fixed primes and complete geometric roots, not a numerical or bounded integer search. The saturated flag, literal ingress, and finite projection are mathematical plus exact replay. They are not an end-to-end Lean tableau theorem.

The [Lean scalar companion](../../lean/RKCert/Research/SDIRKEightSevenZeroThreeClockZeroRatio.lean) and local proof audit pass on Lean/Mathlib 4.36.0. The full tableau argument remains mathematical.
