# Seven quadratic zeros and two constant off clocks: active pair excluded

Let \(A,\mathbf b\) be an actual ten-stage strict SDIRK tableau of ordinary order at least eight over a characteristic-zero field. The common diagonal is \(\gamma\ne0\), \(\mathbf c=A\mathbf1\), and \(\mathbf g=A\mathbf c-\mathbf c^{\odot2}/2\). Assume exactly seven physical entries of \(\mathbf g\) vanish. The other three coordinates have two distinct clocks; at the doubled clock their equal residuals are nonzero. Assume at least one of the three off-zero coordinates has a nonzero output weight.

**Result.** This chart is impossible over every characteristic-zero field. It includes all repeated zero clocks, silent zeros, and both directed rear phases. This result does not cover the corresponding all-silent off rows or the one-off-clock branches, and it does not change the global stage interval.

## 1. Actual chronology and two supported quadratic profiles

Use the [paid support census](../sdirk-eight-seven-eight-zero-census/README.md). At the doubled clock the two off weights must cancel, and the off singleton is silent. The pure row \(\mathbf z^\mathsf T=-\mathbf b^\mathsf T M/2\), \(M=CA-AC-A^2\), spans the difference of that pair and has a nonzero terminal coordinate. The \(W_3\) off restriction has rank one; \(\boldsymbol\eta^\mathsf T=\mathbf z^\mathsf T(A'-I)\) has zero terminal coordinate, so it is supported entirely on the seven zero rows. Here and below
\[
 A'=A/\gamma,\qquad \mathbf x=\mathbf c/\gamma,\qquad D=1/\gamma,
 \qquad U=\ker\operatorname{diag}(\mathbf g).
\]
The first row is off. The second cannot be zero: if its normalized residual were zero, the clean grade-three read \(A'(\mathbf g/\gamma^2)\) there would force \(x_2=1\), giving residual \(1/2\). The off rows are therefore exactly \(1,2,10\), and \(x_1=1,\ x_2=1+u\) are distinct since the terminal is a same-clock mate of one of them. The literal first zero is row 3, and its forward arithmetic phase gives
\[
 a=x_3=1+2u,\qquad 4u^3-12u^2+3u+2=0,\qquad D=2\ \text{or}\ 2+u.
\]
The last alternatives use the actual terminal clock \(x_{10}=D-1\). The reflected residual ratio is zero. By the [literal rear and ghost gates](../sdirk-eight-four-zero-gaussian-rear/README.md), both rows 8 and 9 are live zeros at distinct clocks, and with \(s=x_8,\ t=x_9\),
\[
 v^2-2v-1=0,\qquad w=2v\ \text{or}\ 2-v,\qquad
 s=D-1-w,\quad t=D-1-v,\qquad
 \frac{\eta_8}{\eta_9}=\frac{b_8p_R}{b_9v},
 \quad 2vp_R=2wv+1+2w-w^2 .
\]
All taps and weights entering this last ratio are nonzero. The two phases are arithmetic and star in that order. The canceled off pair has zero aggregate, so ordinary polynomial integration is entirely on the physical zero rows: \(I_D(T^j)=D^j/(j+1)\) through \(j=7\).

Put \(P_0(T)=2T-1-T^2/2\) and \(P_{\rm off}(T)=(T-1)(T-1-u)\). Both are actual supported grade-two traces, the first represented by \(P_0(\mathbf x)-\mathbf g/\gamma^2\), and the second by its scalar vector. Indeed the first two normalized residuals are \(P_0(1),P_0(1+u)\), and the terminal has an equal residual at its matching clock. These values are nonzero. Thus the two quadratics are coprime, and together with their \(T\)-multiples span **all** degree-at-most-three supported scalar profiles on \(U\). The actual representatives are zero on the individual off rows, including the live pair.

Let \(b\) be the first zero clock **different from** \(a\) in forward order, and \(c\) the first zero clock different from both \(a,b\). Such clocks exist by ordinary moment rank. No claim that these are physical rows 4 and 5 is needed until all seven labels are distinct. Let \(J\) be the scalar primitive from zero. The supported quadratic \(S=P_0(a)P_{\rm off}-P_{\rm off}(a)P_0\) vanishes on every zero donor before the first \(b\). Its clean grade-three read is diagonal there, so \(JS(b)=S(b)\). Over the cubic field of \(u\) the exact factorization is
\[
 JS(T)-S(T)
 =(-u^2/3+2u/3+1/6)(T-a)\bigl(T^2-(2u+4)T+1+2u\bigr).
\]
The cofactor is nonzero and at each root of the quadratic, \(S(b)\ne0\). Consequently \(b\) satisfies that quadratic. The replay checks that \(\theta=u+b+2v\) has one irreducible polynomial of degree 12, with exact inverse coordinates in the two successive quotient algebras, so this represents all choices of the three algebraic clocks and gap, not only rational choices.

## 2. The third new clock satisfies a quadratic

The grade-four pure restriction \(F_4|_U\) has dimension at most two: \(F_4\) has dimension four, and \(GE_2\) contributes a rank-two subspace vanishing on \(U\), where \(G=\operatorname{diag}(\mathbf g)\). At the first occurrences of \(a,b\), apply the normalized \(M\) to the two actual supported quadratics. Its diagonal is \(-1\); every earlier donor for the first \(b\) is at \(a\). The two evaluation columns have determinant \(S(b)\ne0\) after eliminating the common donor contribution. Thus \(F_4|_U\) has dimension two and evaluation at those two physical occurrences is injective.

Let \(Z_2(T)=(T-a)(T-b)\), \(Z_3(T)=TZ_2(T)\), and
\[
 L_D(T)=70T^4-140DT^3+90D^2T^2-20D^3T+D^4.
\]
The ordinary moments put \(L_D(\mathbf x)\) in \(F_4\). Find \(\alpha,\beta\) such that \(J(\alpha Z_2+\beta Z_3)\) takes values \(-L_D(a),-L_D(b)\) at \(a,b\); its pivot is \(a^2b^2(a-b)^3/24\ne0\). The supported input \(\alpha Z_2+\beta Z_3\) vanishes through the first \(b\), so its actual grade-four discrepancy agrees with \(L_D\) there, hence on all of \(U\). Its first \(c\) read is also diagonal. Therefore
\[
 C_3(c)=0,\qquad
 C_3(T)=\frac{\alpha(Z_2-JZ_2)+\beta(Z_3-JZ_3)-L_D}{(T-a)(T-b)}.
\]
The numerator is exactly divisible and the quotient has degree two in both exact \(D\) fields. This derivation allows any repeated earlier clocks: it uses first new labels, not first distinct rows by assumption.

## 3. Six or fewer literal zero labels

In each of the four base frames \((D,w)\), the fixed mask \(P_3=(T-a)(T-s)(T-t)\) has a nonzero ordinary three-by-three Hankel determinant from \(I_D(T^{i+j}P_3)\), \(0\le i,j\le2\). Therefore at least three live ordinary labels outside \(a,s,t\) are necessary, and at least six literal zero labels. The code verifies that \(a,b,s,t\) are distinct. If there are exactly six, write the remaining two as roots of a monic \(P_2\). With \(P_4=(T-b)P_3\), \(I_D(P_4P_2)=I_D(TP_4P_2)=0\) determines \(P_2\) at a nonzero exact two-by-two pivot. But \(C_3(s)\) and \(C_3(t)\) are both nonzero and \(\gcd(C_3,P_2)=1\). These are all candidates for the first \(c\). This proof does **not** apply the literal rear tap ratio to repeated clock aggregates; the duplicated label can be \(s\), \(t\), or any other zero.

## 4. Seven distinct literal labels: two chronological reverse reads

Now the physical zero labels \(a,b,c,e,r,s,t\) occur in that order. Let \(P_7=\prod(T-x_i)\) over these labels, and use the polynomial
\[
 B(T)=I_{D,X}\bigl((P_7(X)-P_7(T))/(X-T)\bigr).
\]
Thus \(B(x_i)=b_iP_7'(x_i)\), even if \(b_i=0\). The moment-null row \(\boldsymbol\eta^\mathsf T\) annihilates through degree four, so \(\eta_iP_7'(x_i)\) is an affine function of \(x_i\) by ordinary interpolation. On \(U\), \(Z_3\) is the line of \(\boldsymbol\eta^\mathsf T\), since \(\mathbf z^\mathsf T\) is off-only. For \(R=(T-s)(T-t)\), take the weighted \(W_2\) row of profile \(R\) and subtract a multiple of \(\mathbf z^\mathsf T\) so it is supported on \(U\). At \(t,r\) its right reads under \(A'\) are diagonal since \(R(s)=R(t)=0\). The primitive profile is \(J_D^*R(T)=JR(D)-JR(T)\). Clear the affine pure row and the literal tap ratio, using \(B(t)\ne0\) because row 9 is live. The result is
\[
 v(s-t)[R(r)-J_D^*R(r)]B(r)
 +J_D^*R(t)\left[v(s-t)B(t)+(r-t)(p_RB(s)-vB(t))\right]=0. \tag{1}
\]
No weight other than the proved nonzero \(b_9\) is canceled.

Let \(P_5=(T-a)(T-b)(T-c)(T-s)(T-t)\) and \(m_i=I_D(T^iP_5)\). The ordinary nodal equation is \(m_2-(r+e)m_1+re m_0=0\). Put \(k=r m_0-m_1,\ \ell=r m_1-m_2\), \(\Delta=m_0m_2-m_1^2\). The certified reductions show \(\Delta\ne0\) on every algebraic frame. Thus \(k=0\) is impossible at an actual solution and \(e=\ell/k\). Replace \(P_7\) in (1) by \(P_5(T-r)(kT-\ell)\), multiplying its cardinal numerators by \(k\). The cleared value at \(r\) is the constant \(\Delta\). The polynomial in the prospective \(r\) has degree at most three and is divisible by \((r-s)(r-t)\): at each collision the corresponding cleared numerator becomes \(\Delta\), and \(p_RJ_D^*R(t)=vJ_D^*R(s)\) in both rear phases. These two factors are forbidden actual clock collisions. The quotient is a linear polynomial on every checked algebraic frame, with a unit leading coefficient at the selected good reductions.

For the fourth reverse read set \(\sigma=(T-r)(T-s)(T-t)\), and again subtract a multiple of the pure pair from its weighted \(W_3\) row. Its read is zero at \(s,t,r\) and diagonal at \(e\). Pair the pure discrepancy in \(Z_4=\operatorname{Ann}(E_3)\) with the actual supported cubic \(\rho=(T-a)(T-b)(T-c)\), killing the other three zeros. At each remaining clock \(x_i\), \(P_7'(x_i)=\rho(x_i)\sigma_4'(x_i)\) for \(\sigma_4=(T-e)\sigma\). Lagrange interpolation of degree three gives the necessary equation
\[
 B(e)-[T^3]\bigl(B(T)J_D^*\sigma(T)\bmod \sigma_4(T)\bigr)=0. \tag{2}
\]
The following fixed cells give both simple roots of \(C_3\) and reject (2). Each triple is \((r,e,\text{left side of (2)})\); arithmetic is modulo \(p\).

| \(D\) | Rear | \(p\) | \(\theta\) | \(c\) and triple | Other \(c\) and triple |
|---|---|---:|---:|---|---|
| \(2\) | Star | 113 | 0 | \(31:(56,5,110)\) | \(86:(30,55,73)\) |
| \(2\) | Arithmetic | 79 | 10 | \(43:(15,49,41)\) | \(71:(55,31,6)\) |
| \(2+u\) | Star | 127 | 19 | \(18:(119,81,106)\) | \(72:(14,59,99)\) |
| \(2+u\) | Arithmetic | 79 | 10 | \(40:(32,65,55)\) | \(53:(36,29,30)\) |

The replay checks simple \(\theta\) roots, all reduced denominators, the full two-root \(C_3\) splitting with unit leading coefficient, both ordinary and reverse linear pivots, and distinct recovered clocks. The simple \(\theta\) root embeds the abstract degree-12 base in \(\mathbb Q_p\). In that embedding either root of the remaining quadratic lifts uniquely from one of the two residues. The nonzero pivot residues therefore justify the exact elimination, and the final nonzero residue contradicts (2) over either algebraic extension. This is not an extrapolation from finite-field nonexistence and makes no broader positive-characteristic claim.

## 5. Replay scope

Run `python check_six_or_fewer.py` and `python check_seven_labels.py` with Python 3, SymPy 1.14 and python-flint 0.8. Both replays are exact, with no sampled or floating-point inputs. The former runs the low-label Cramer and gcd certificates; the latter proves the clock-field receipts and replays the fixed residue table including both algebraic choices in each frame.

The native module `RKCert.Research.SDIRKEightSevenZeroActiveScalar` verifies the cleared forward primitive pivot, ordinary pencil identities, both reflected primitive relations and the reverse affine cancellation. The companion `proof-audit.lean` gives their axiom receipts under Lean/Mathlib 4.36.0. The types are scalar gates, not an end-to-end rooted-tableau theorem; the saturation ingress and exact polynomial field receipts above remain separate.
