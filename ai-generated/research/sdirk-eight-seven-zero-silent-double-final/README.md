# Last two-off-clock branches with seven physical quadratic zeros

Let \(A,\mathbf b\) be a strict ten-stage SDIRK tableau of ordinary order at least eight over a characteristic-zero field. The common diagonal is \(\gamma\ne0\), and \(\mathbf c=A\mathbf1,\ \mathbf g=A\mathbf c-\mathbf c^{\odot2}/2\). Suppose exactly seven physical entries of \(\mathbf g\) vanish. There are two distinct clocks among its other three rows.

**Result.** This is impossible over every characteristic-zero field. The new part below excludes the last silent equal-residual double branch, with nonzero reflected ratio and physical row 8 a zero. The [varying double](../sdirk-eight-seven-zero-pure-distinct/README.md), [active equal double](../sdirk-eight-seven-zero-two-clock-active/README.md), and [zero-ratio and off-eighth silent equal double](../sdirk-eight-seven-zero-silent-double-ghost/README.md) cover the other subcases. This is not a global ten-stage exclusion.

## 1. Setup and the exact five-label branch

In the remaining branch all three off weights are silent and the doubled off clock has equal residuals. Normalize \(A'=A/\gamma,\ \mathbf x=\mathbf c/\gamma,\ D=1/\gamma\), and use \(U=\ker\operatorname{diag}(\mathbf g)\). By the [off pure support analysis](../sdirk-eight-seven-zero-silent-double-ghost/README.md#1-the-off-pure-support-cancels-but-is-not-pointwise-zero), the pure row \(\mathbf z^\mathsf T=-\mathbf b^\mathsf TM/2\), \(M=CA-AC-A^2\), \(C=\operatorname{diag}(\mathbf c)\), has an off restriction of opposite entries on the doubled clock. Therefore \(\mathbf z^\mathsf T|_U\) annihilates powers through degree five. We do not assume the full \(\mathbf z^\mathsf T\) is supported on \(U\).

The normalized first two off clocks are \(1,1+u\), and the first zero is \(a=1+2u\), where \(Q(u)=4u^3-12u^2+3u+2=0\). The first new literal zero clock \(b\) and the next new literal zero clock \(c\) satisfy the [constant-double forward gates](../sdirk-eight-seven-zero-two-clock-active/README.md#2-the-third-new-clock-satisfies-a-quadratic):
\[
 b^2-(2u+4)b+1+2u=0,\qquad C_3(c;D)=0 .
\]
These use the actual grade-two supported profiles \(2T-1-T^2/2\) and \((T-1)(T-1-u)\); the taps do not depend on the off output weights. The coefficients of \(C_3\) are polynomial in \(D\), with degree at most four, because the two forward primitive pivots depend only on \(a,b\).

Let \(s=x_{10}=D-1,\ t=x_9=s-v,\ r=x_8\), and \(\kappa=1+2v-v^2\ne0\). Physical rows 9,10 have nonzero weights and \(z_9,z_{10}\ne0\). If at most six literal zero labels exist, Vandermonde makes each aggregate of \(\mathbf z^\mathsf T|_U\) zero. Thus both \(s,t\) require duplicate mates, leaving at most five labels. If \(z_8\ne0\), then \(r\) is a third distinct label requiring a duplicate, leaving at most four. Ordinary moment rank forces exactly four live Gauss labels in that case. The literal rear third makes the three reflected Gaussian clocks \(x,y,2y-x\) in arithmetic (also the silent ghost), or \(x,y,4x-y\) in star. Neither triple occurs: the replay takes the resultant in \(y\) of the divided difference of the fourth shifted Legendre polynomial and its evaluation at the prospective third clock, and checks constant gcd with the same Legendre polynomial in \(x\).

Thus row 8 must be live with \(z_8=0\), because a silent row 8 has nonzero \(z_8\). The literal star keeps the reflected residual ratio \(\kappa\ne0\), so the row must be arithmetic, \(r=s-2v\), and its zero residual forces \(Q(v)=0\). Even without \(z_8\ne0\), four or fewer labels would make the same Gaussian rear triple, impossible. Thus the only possible low count is five labels with two physical duplicates, at \(s,t\).

Exact base algebras for the possible \(v\) are the degree-six field for \(v=u\) and the degree-twelve field for \(v\ne u\). The degrees and inverse primitive-element maps are checked in the replay. The two forward clocks cannot *both* coincide with one of the three rear labels, because \(b-a\notin\{\pm v,\pm2v\}\) in both fields. When neither overlaps, the five labels \(a,b,s,t,r\) are known as functions of \(D\). The three ordinary means of their degree-five nodal polynomial times \(1,T,T^2\) have constant gcd in \(D\). When one overlaps, \(D=1+f+jv\) with \(f=a\) or \(b\) and \(j=0,1,2\). With the known four-label mask \(P_4\), the existence of the remaining unknown label would force
\[
 I_D(P_4)I_D(T^2P_4)-I_D(TP_4)^2=0,
 \qquad I_D(T^n)=D^n/(n+1).
\]
The exact calculation gives a nonzero determinant in all admissible fixed frames. Hence every low-label chart is excluded.

## 2. Seven distinct labels: exact cardinal and forward gates

Now \(\mathbf z^\mathsf T|_U\), by its six zero moments, is a nonzero barycentric row on precisely seven nodes. All its zero-row coordinates are nonzero. Let \(P_7\) be their monic nodal polynomial. For
\[
 B(T)=I_{D,X}\bigl((P_7(X)-P_7(T))/(X-T)\bigr)
\]
ordinary quadrature gives \(B(x_i)=b_iP_7'(x_i)\), including any silent zero. The literal rear ratio gives \(\kappa B(t)=B(s)\). The labels \(a,b,c\) occur before the three rear zeros, so \(P_7=(T-a)(T-b)(T-s)(T-t)(T-r)Q_2(T)\), where \(Q_2\) is monic quadratic and \(Q_2(c)=0\).

If row 8 is **silent**, the literal ghost gives \(r=s-2v,\ H(v)=v^3-4v^2-v+2=0\), and \(B(r)=0\).

If row 8 is live **arithmetic**, \(r=s-2v\) and \(H(v)\kappa_3=-\kappa Q(v)\). The [arithmetic sextic](../sdirk-eight-seven-zero-pure-distinct/README.md#2-rear-cardinal-rows-and-the-arithmetic-compatibility-sextic) applies here as well:
\[
 8v^6-44v^5+22v^4+97v^3-55v^2-13v+6=0 .
\]
In that proof the corrected weighted quadratic only needs to vanish at the last three physical rows. Subtracting a pure multiple can give nonzero earlier off entries in the present chart, but such entries do not enter any of those last three right reads. Also \(Z_3=\langle\mathbf z^\mathsf T,\mathbf z^\mathsf TC'\rangle\), \(C'=\operatorname{diag}(\mathbf x)\): independence follows at the two distinct rear sites with nonzero \(z\). Thus the same affine pure comparison in the suffix is legitimate, and the sextic holds unchanged. The third ratio, cleared as \(-\kappa Q(v)B(r)-H(v)B(s)=0\), does not divide by \(H(v)\).

For either of these modes write \(F=(T-a)(T-b)(T-s)(T-t)(T-r)\) and \(F_j=F/(T-j)\) for \(j=s,t,r\). Three exact moments on \(Q_2\) use masks
\[
 (F,\ \kappa F_t-F_s,\ F_r)
 \quad\text{or}\quad
 (F,\ \kappa F_t-F_s,\ -\kappa Q(v)F_r-H(v)F_s)
\]
for ghost or arithmetic respectively. Each mask times \(Q_2\) is of degree at most seven. Thus no unavailable higher ordinary moment is used.

## 3. The star cancels its gap

For the live reflected **star**, write \(m=D-2,\ \delta=v-1\). Then \(s=m+1,t=m-\delta,r=m+\delta,\ \kappa=2-\delta^2\), and the third ratio is \(\kappa_3=\kappa\), giving \(B(t)=B(r)\). For \(P=(T-a)(T-b)\) set \(H_j=I_D(PQ_2(T-m)^j)\). The equal cardinal values give \(2\delta(H_1-H_0)=0\); since the two sites differ, \(H_1=H_0\). The ordinary nodal equation now gives \(H_3=H_2\). Finally
\[
 \kappa B(t)=B(s)
 \quad\Longrightarrow\quad
 (2-\delta^2)(H_2-H_0)=H_2-\delta^2 H_0
 \quad\Longrightarrow\quad
 (1-\delta^2)(H_2-2H_0)=0 .
\]
The factor \(1-\delta^2=v(2-v)\) is nonzero, because either zero would collide one of the last two zero clock labels with \(s\). Thus \(H_2=2H_0\). All three linear moment masks on \(Q_2\) are now independent of the rear gap:
\[
 P(T-s),\qquad P(T-s)(T-m)^2,\qquad P\bigl((T-m)^2-2\bigr).
\]
This eliminates the gap without projecting along a singular pivot or bounding its possible degree.

## 4. Division-free projection and exact good reductions

For each of the three modes, multiply its moment masks by \(1,T,T^2\) and evaluate \(I_D\) to obtain rows \(m_\bullet,\ell_\bullet,n_\bullet\) of a three-by-three matrix. It annihilates \((q_0,q_1,1)^\mathsf T\) for \(Q_2=T^2+q_1T+q_0\). In particular the determinant vanishes. Let \((C_0,B_0,A_0)\) be the cross product of the first two rows, so \(C_0=A_0q_0,\ B_0=A_0q_1\) by their equations, even at \(A_0=0\). The cleared quadratic \(A_0T^2+B_0T+C_0\) therefore vanishes at the actual \(c\). Write \(C_3(T;D)=d_0T^2+e_0T+f_0\). The following scalar resultant must vanish too:
\[
 (A_0 f_0-C_0 d_0)^2-(A_0 e_0-B_0 d_0)(B_0 f_0-C_0 e_0).
\]
There is no nonzero-ordinary-pivot hypothesis: if \(A_0=0\) on a solution, the other two numerators also vanish, which is already covered by the cleared resultant condition.

The replay constructs exact primitive fields and verifies the following fixed simple residue roots. The determinant has degree 15, and only the exact factor \(D^6\) is removed because \(\gamma\ne0\) gives \(D\ne0\). Both the remaining determinant degree and the entire cleared resultant degree are preserved at the selected reductions, where their gcd is constant.

| Mode | Exact primitive field | \(p\) | Primitive residue | Recovered \((u,b,v)\) or \((u,b)\) | Guarded determinant / resultant degrees |
|---|---|---:|---:|---|---|
| Silent zero | \(u+b+2v\), degree 18 | 17 | 1 | (16, 7, 6) | 9 / 32 |
| Live arithmetic | \(u+b+2v\), degree 36 | 59 | 12 | (10, 4, 58) | 9 / 32 |
| Live star | \(u+b\), degree 6 | 13 | 11 | (4, 7) | 9 / 30 |

Each simple field root lifts to a \(p\)-adic embedding of the indicated exact number field. Unit denominators and the verified leading degrees make the corresponding resultant in \(D\) nonzero already over the exact field. Thus there is no common root in any extension of that field, even if \(D\) was not assumed algebraic at the start. This is not a positive-characteristic classification.

## 5. Replay and scope

Run `python check_low_labels.py` and `python check_distinct.py ghost`, `python check_distinct.py arith`, `python check_distinct.py star` with SymPy 1.14 and python-flint 0.8. The exact receipts do not perform a prime search. The native `RKCert.Research.SDIRKEightSevenZeroSilentDoubleFinal` verifies the star collision factor, gap-free moment implication and division-free common quadratic root projection, with stock Lean/Mathlib 4.36.0 axiom receipts in `proof-audit.lean`. Rooted tableau ingress and exact field certificates are separate from these native scalar statements.

Combined with the other two-clock packets, precisely seven physical zeros in a characteristic-zero ten-stage tableau require the three off rows to have **one or three distinct clocks**. The [one-clock closure](../sdirk-eight-silent-three-closure/README.md) independently rules out three silent off rows at one clock, and the [silence theorem](../sdirk-eight-seven-eight-off-silent/README.md) makes all three off weights individually zero. Thus three pairwise distinct off clocks, all with zero weights, are necessary in the exactly-seven case. This does not change the unrestricted stage interval.

For three distinct off clocks and a nonzero second reflected defect ratio, the [low-label exclusion](../sdirk-eight-seven-zero-three-clock-five-label/README.md) additionally forces all seven quadratic-zero clocks to be distinct.

The [zero second reflected ratio](../sdirk-eight-seven-zero-three-clock-zero-ratio/README.md) is also impossible. Together these results force seven distinct quadratic-zero clocks and a nonzero second reflected defect ratio in the exactly-seven case.
