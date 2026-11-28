# Seven zeros with two silent constant off clocks: zero ratio and off-eighth exclusion

Let \(A,\mathbf b\) be a strict ten-stage SDIRK tableau of ordinary order at least eight over a characteristic-zero field, with common diagonal \(\gamma\ne0\). Write \(\mathbf c=A\mathbf1,\ \mathbf g=A\mathbf c-\mathbf c^{\odot2}/2\). There are exactly seven physical quadratic zeros, and three silent off-zero rows at two distinct clocks. Assume the doubled off clock has equal residuals at its two rows.

**Result.** Neither zero reflected second ratio nor a silent **off-zero physical eighth row** is possible in this chart. A silent eighth row that is itself a quadratic zero is not excluded by this packet. The result does not exclude all silent constant-double tableaux, nor change the global stage interval.

## 1. The off pure support cancels, but is not pointwise zero

Use the [saturated two-clock census](../sdirk-eight-seven-eight-zero-census/README.md): \(r_2=r_3=2,\ w_2=w_3=1\). Put \(U=\ker\operatorname{diag}(\mathbf g)\), \(A'=A/\gamma,\ \mathbf x=\mathbf c/\gamma,\ D=1/\gamma\), and \(C'=\operatorname{diag}(\mathbf x)\). Let \(\mathbf z^\mathsf T=-\mathbf b^\mathsf T(CA-AC-A^2)/2\), with \(C=\operatorname{diag}(\mathbf c)\), and \(\boldsymbol\eta^\mathsf T=\mathbf z^\mathsf T(A'-I)\). The off restrictions of all weighted scalar profiles vanish. Hence \(\mathbf z^\mathsf T\) has nonzero off restriction (it is the only possible contribution to the rank-one \(W_2\) off restriction). Since \(\mathbf z^\mathsf T C'\in W_3\), its off restriction is proportional to that of \(\mathbf z^\mathsf T\). All nonzero off coordinates of \(\mathbf z^\mathsf T\) therefore share one clock.

The pure row annihilates \(\mathbf g\). It follows, by the equal nonzero residual at each group, that its off-coordinate sum at this clock is zero. Thus the support must be precisely the two coordinates of the doubled group, with opposite entries. Write \(d\) for that normalized clock. The off restriction of \(\boldsymbol\eta^\mathsf T\) is also proportional to that of \(\mathbf z^\mathsf T\). Consequently their restrictions to \(U\) still annihilate ordinary powers through degrees five and four, respectively: the off contribution cancels at \(d\) for each power. This does not assert that \(\mathbf z^\mathsf T\) itself is supported on \(U\). This reduction uses only paid field structure.

The first two physical rows are off by the [multi-clock clean row-two argument](../sdirk-eight-seven-eight-off-silent/README.md), and their clocks \(1,1+u\) differ by saturation. The first three physical clocks are distinct by the literal first-three gate, so row 3 is zero, and has the arithmetic phase \(a=x_3=1+2u\), with \(4u^3-12u^2+3u+2=0\). Here \(d=1\) or \(1+u\). On \(U\), the [constant-double supported profile arguments](../sdirk-eight-seven-zero-two-clock-active/README.md#1-actual-chronology-and-two-supported-quadratic-profiles) apply without any hypothesis of active off weights: \(P_0=2T-1-T^2/2\) is represented by \(P_0(\mathbf x)-\mathbf g/\gamma^2\), and \(P_{\rm off}=(T-1)(T-1-u)\) is supported. Their quadratic and cubic span forces the exact first-new zero equation \(b^2-(2u+4)b+1+2u=0\) and the [third-new zero equation \(C_3(c)=0\)](../sdirk-eight-seven-zero-two-clock-active/README.md#2-the-third-new-clock-satisfies-a-quadratic). The ordinary moments are supported on \(U\).

## 2. The zero reflected ratio is impossible

Let \(S=x_{10}=D-1\) be the terminal clock and \(T=x_9=S-v\) the penultimate one (temporary scalar site names). If the reflected second ratio \(\kappa_R=1+2v-v^2\) vanishes, then the pure row \(\mathbf z^\mathsf T(C'-SI)\) vanishes identically. Indeed it belongs to \(Z_3\) and vanishes at physical 10 and 9. The basis \(\mathbf z^\mathsf T,\boldsymbol\eta^\mathsf T\) has nonsingular restriction at these two physical coordinates by \(z_{10}\ne0,\eta_{10}=0,\eta_9=z_{10}A'_{10,9}\ne0\). So every nonzero \(\mathbf z^\mathsf T\) entry lies at \(S\). By the off support calculation, this pins \(S=d\), hence \(D=2\) or \(2+u\). The off sum cancels, and \(z_{10}\ne0\) on the zero rows, so the scalar zeroth pure moment forces a second physical zero at \(S\). There are at most six distinct literal zero labels.

The physical eighth row cannot be silent: the literal ghost would give a nonzero \(z_8\) at \(S-2v\ne S\). Thus both rows 8 and 9 are live zeros, with the two fixed zero-ratio phases and exactly the same \(s,t\) labels as in the [active-pair low-label certificate](../sdirk-eight-seven-zero-two-clock-active/README.md#3-six-or-fewer-literal-zero-labels). That certificate only uses \(u,b,v,D\), the clock pegs \(a,s,t\), forward grade-four restrictions, and ordinary mass on \(U\). It does not use \(\mathbf z^\mathsf T\) being off-only or the terminal being off. Its nonzero ordinary Hankel and exact quadratic exclusions contradict every configuration of at most six literal zero labels, as required. The earlier replay `check_six_or_fewer.py` is used unmodified.

## 3. Silent physical eighth row off-zero

Now let \(\kappa_R\ne0\). If physical row 8 is off, the [literal silent ghost](../sdirk-eight-four-zero-gaussian-rear/README.md) applied to its zero output weight requires \(z_8\ne0\). By section 1 its clock is \(d\), and the ghost pins
\[
 H(v)=v^3-4v^2-v+2=0,\qquad D=1+d+2v,\qquad
 s=x_{10}=d+2v,\quad t=x_9=d+v .
\]
The physical off rows are now exactly \(1,2,8\). Both \(s,t\) are live zeros and \(v,\kappa_R\ne0\).

The exact replay verifies the irreducible degree-18 primitive base \(\theta=u+b+2v\) and explicit recovered clocks. In each \(d\) frame, \((a,b,s,t)\) are distinct, the \(I_D(T^{i+j}(T-a)(T-s)(T-t))\), \(0\le i,j\le2\), Hankel determinant is nonzero, and six or fewer zero labels are excluded by the same two-coefficient nodal reconstruction and \(C_3\) tests (computed at these new values of \(D\)). This argument uses no literal ratio on repeated clock aggregates.

If all seven labels are distinct, the chronology on \(U\) is \(a,b,c,e,r,t,s\), with \(r=x_7\), and \(\mathbf z^\mathsf T|_U\) is a nonzero barycentric row. For the monic \(P_7\) on those seven labels define the ordinary cardinal polynomial \(B(T)=I_{D,X}((P_7(X)-P_7(T))/(X-T))\), with \(I_D(T^j)=D^j/(j+1)\). Then \(B(x_i)=b_iP_7'(x_i)\), and \(\kappa_R B(t)=B(s)\) by the literal reflected ratio. The latter equation and \(I_D(P_7)=0\) give two ordinary linear conditions on the two unknown coefficients of the monic \(Q_2=(T-e)(T-r)\) in \(P_7=(T-a)(T-b)(T-c)(T-s)(T-t)Q_2\).

For a third reverse read take the weighted degree-two row of \(R=(T-s)(T-t)\). Its primitive discrepancy lies in \(Z_3\) and vanishes at **physical row 8**: the row is silent there, and the only possible later weighted donors have zero \(R\) value. Since \(z_8\ne0\) and the off restriction has rank one, the discrepancy is in \(Z_3\cap U_{\rm row}\), the line of \(\mathbf z^\mathsf T(C'-dI)\). This row is nonzero at \(t\) since \(t-d=v\) and \(z_9\ne0\). The reads at \(t\) and at \(r\) are purely diagonal; the silent row 8 contributes nothing. Multiplying by the nodal derivatives and eliminating the common pure multiplier gives
\[
  (t-d)[R(r)-J_D^*R(r)]B(r)+(r-d)J_D^*R(t)B(t)=0. \tag{1}
\]
Thus the polynomial in the prospective \(r\) in (1) and the recovered \(Q_2\) must have a common root. No \(b_7\) or other prospective ordinary weight has been inverted.

At \(p=59\), the simple residue of \(\theta\) is \(1\), giving \((u,b,v)=(10,4,23)\). The \(C_3\) leading coefficients are units and their full reductions split into the two simple roots in each row below. The ordinary pivot and constant gcd are checked in every fiber. Write \(Q_2=T^2+q_1 T+q_0\); the final column gives the degree-at-most-one remainder in ascending coefficient order.

| \(d\) | \(D\) | \(c\) | \((q_1,q_0)\) | Pivot | Remainder of the left side of (1) |
|---:|---:|---:|---:|---:|---:|
| 1 | 48 | 13 | (19,58) | 38 | (0,31) |
| 1 | 48 | 37 | (34,0) | 53 | (46,42) |
| 11 | 58 | 5 | (8,50) | 18 | (9,46) |
| 11 | 58 | 41 | (34,18) | 56 | (27,21) |

A simple base root embeds the exact number field into \(\mathbb Q_{59}\); either \(C_3\) root lies in a simple lifted fiber. Unit pivots justify the coefficient recovery there. Since \(Q_2\) is monic, any common algebraic root with (1) would remain integral and would reduce to a common root, contradicted by the residue gcds. This is a characteristic-zero proof, not a classification in arbitrary positive characteristic.

## 4. Replay and native scope

Run `python check_ghost8.py` with SymPy 1.14 and python-flint 0.8, plus `check_six_or_fewer.py` in the active-pair packet for section 2. The new script uses the fixed residue table, not a prime search. The native `RKCert.Research.SDIRKEightSevenZeroSilentDoubleGhost` and `proof-audit.lean` verify the scalar off-level collinearity and cleared rear gate (1) under stock Lean/Mathlib 4.36.0. The rooted ingress, exact number-field projection, and characteristic-zero branch conclusion are given separately above.
