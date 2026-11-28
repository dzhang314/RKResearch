# Both singleton endpoints: no actual three-singleton arithmetic opener

Consider a strict ten-stage SDIRK tableau of ordinary order at least eight over a characteristic-zero field. Require all physical quadratic defects nonzero and exactly seven distinct clock labels, with both physical endpoint labels singleton. Then neither literal prefix can have type **S,S,S with a genuine arithmetic third row**. Its true opposite prefix is necessarily S,D,D: exactly four S labels exist, all consumed by the first three rows and the physical last row. The [separate literal S,S,S star result](../sdirk-eight-all-dirty-seven-quadratic-both-s-sss-star/README.md) handles the other phase. Thus each actual oriented prefix contains at least one D label. Both endpoints are still allowed singleton; no other prefix type is excluded here.

## Four paid singleton values and the two clock-only gates

Set \(y=x-1,\ H=2(m-1),\ m=1/(2\gamma)\); the arithmetic opening is at \(0,u,2u\). Its actual normalized defects are \(1/2,\kappa(u)/2,N(u)/(2D(u))\), with
\[
 \kappa(u)=1+2u-u^2,\quad D(u)=-2+u+4u^2-u^3,\quad
 N(u)=(1+4u-4u^2)D(u)+4u^2(3u-2).
\]
The forward gap is nonzero and not 2 because its first S cannot repeat. Define \(c=(3u-2)/D(u)\), \(a=1-cu\), \(b=c-1/2\). The three actual paid values uniquely give
\[
 R(y)=\tfrac12+a y+b y^2
     =\tfrac12(1+2y-y^2)+c\,y(y-u).
\]
By the [prior affine/constant closure](../sdirk-eight-all-dirty-seven-affine-final/README.md), \(b\ne0\). The other endpoint \(H\) is the fourth S; its original defect \(\mu=R(H)\ne0\), and the reverse to original defect scale is \(2\mu\). Let
\[
 W=R/b,\quad S_4=y(y-u)(y-2u)(y-H),\quad C=A_2+B R.
\]
The [paired-fibre identities](../sdirk-eight-all-dirty-seven-clock/README.md) give \(L_4-RC=\xi S_4\) for a nonzero \(\xi\). Thus the two scalar remainders \(L_4\bmod W=A+B_1 y\), \(S_4\bmod W=A_S+B_S y\) are proportional, yielding \(E=A B_S-B_1 A_S=0\). The scalar \(B_1\) here is just the linear coefficient of the Legendre remainder, not the true paired-fibre \(B\).

Write \(W=y^2+w_1 y+w_0\). Coprimality of consecutive Legendre modes and \(W\mid L_3-F_* L_4\) give the true nonzero inverse determinant
\[
 \delta=A(A-B_1 w_1)+B_1^2 w_0,\qquad
  (A+B_1 y)^{-1}=(A-B_1 w_1-B_1 y)/\delta\bmod W.
\]
Use this exact affine adjugate to obtain \(\delta F_* \bmod W\) without assuming \(W\) splits. The (unnormalized) cubic
\[
 P=(\delta L_3-(\delta F_*)L_4)/W
\]
has three actual doubled labels, and leading coefficient nonzero. A true rear arithmetic pair has \(T(y)=2y-H\), a true rear star has \(T(y)=2H-2-y\), converting the first later D to the second, and their clocks are distinct. In a star the other D label therefore equals \(-[y^2]P/[y^3]P-(2H-2)\); evaluating \(P\) there is a necessary scalar equation, with denominator simply cleared. For an arithmetic pair use variable \(z=y-H\), so \(P_H(z)=P(H+z)=a_3z^3+a_2z^2+a_1z+a_0\); the actual pair is \(z,2z\). Since \(z\ne0\), both \(P_H\) and \(7a_3z^2+3a_2z+a_1\) must vanish there. Their universal resultant divided by the true leading \(a_3\) gives the second scalar gate. Neither phase uses an assumed literal row permutation.

## Exact projection and genuinely paid two-D residues

After clearing just the audited nonzero denominator and guard factors, the \(H\)-degree of \(E\) is five. Project \(E\) and the rear scalar gate in \(H\) to the forward gap \(u\):

| Rear phase | Raw/guarded \(u\) projection degrees | Factor degrees with multiplicity |
| --- | --- | --- |
| Star | 179 / 106 | (70,1),(12,2),(6,2) |
| Arithmetic | 360 / 216 | (144,1),(12,4),(6,4) |

Both smaller factors in each phase give exact linear common \(H\)-components in their abstract irreducible rational fields. In each case the entire component lies on \(\delta=0\), which is already impossible. No numerical filter is used there. The large factors admit the fixed simple places \((p,u,H)=(13,9,2)\) for star and \((23,10,4)\) for arithmetic: the \(u\) factor retains its nominal degree and has a simple specified root. The actual \(H\) is integral in an algebraic closure at this place because the \(E\) row retains degree five with unit leading coefficient. Its only possible residue in the common \(H\) gcd is the specified \(H\).

At those residues all scalar recovery denominators are checked units where used. The cubic has degree three with unit leading coefficient so each actual D clock is integral. Recover \(\xi\) using either nonzero coefficient of \(S_4\bmod W\), then \(C=(L_4-\xi S_4)/R\); both actual identities specialize at the indicated unit pivots. Compute the gcd \(\Gamma\) of \(P\) and \((P(T)-P)/(T-y)\); multiplying a true pair equality by nonzero \(T-y\) in the characteristic-zero field shows the divided-difference test holds before reduction, even if clocks were to collide modulo \(p\).

For the first actual later D \(y\), \(v=H-y\), \(g_2=\mu\kappa(v)\). Let \(g_3=\mu\kappa(v)\) for a rear star, or \(g_3=\mu N(v)/D(v)\) for a rear arithmetic, at clock \(T(y)\). In the arithmetic limb use \(d_3=D(v),\,n=\mu N(v)=d_3g_3\); in a star set \(d_3=1,n=g_3\). At the two true D rows,
\[
\begin{array}{ll}
 X_2=L_4(y)-g_2 C(y), & U_2=g_2(g_2-R(y)),\\
 X_3=d_3^2L_4(T(y))-d_3 n C(T(y)), & U_3=n(n-d_3R(T(y))).
\end{array}
\]
Here \(X_2=B U_2,\ X_3=B U_3\). These are denominator-free even if the actual \(\mu N(v)\) or \(D(v)\) reduce to zero. The actual pair entails \(X_2U_3-X_3U_2=0\), with no need to specialize \(B\) or assume it integral. The replay verifies unit gcd of this row with \(\Gamma\) in both indicated places. That excludes every algebraic residue of the actual D clock; neither \(P\) nor \(\Gamma\) is required to split. Since the reason to choose those places is an embedding of the abstract characteristic-zero \(u\)-field, no finite-characteristic stage lower bound is asserted.

## Replay and Lean scope

Run `SYMPY_GROUND_TYPES=flint python check_sss_arithmetic.py` (SymPy 1.14, python-flint 0.8). The exact fixed-prime checks use the common audited finite fibre helpers; no large compute or cache files are required. The candidate Lean scalar companion verifies the denominator-free two-D comparison and scaled paid row, not the full order ingress and elimination. Together with the SSS-star packet this only excludes S,S,S when both endpoints are singleton. The general 10–11 stage interval is unchanged.

The publication audit independently replayed the corresponding exact arithmetic; the new Lean companions here are draft scalar lemmas, not claimed kernel-checked in this release.
