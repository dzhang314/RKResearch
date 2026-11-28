# Non-overlapping prefixes: rear star with a forward A3 or star

Assume an ordinary order-eight strict ten-stage SDIRK tableau over a characteristic-zero field, all literal quadratic residuals nonzero, exactly seven distinct clocks and exactly one singleton physical endpoint. Use the [unique-singleton topology ledger](../sdirk-eight-all-dirty-seven-quadratic-two-s-dss-arithmetic-new-a2-final/LEDGER.md), orienting from that singleton. The forward opening has two singleton labels and one D; the reverse opening has two D and one singleton. In this packet the known D labels of the two physical prefixes are disjoint. We exclude every **true reverse star**, for a true forward **A3 or star**. A2 against a rear star and the two rear arithmetic phases are outside this packet. The terminal and extra-D overlap exclusions use separate packets.

## One unknown D clock, recovered by pure affine interpolation

Use \(y=x-1,\ H=2(m-1),\ m=1/(2\gamma)\); the original first S is \(0\), actual rear terminal D is \(H\), and the observed forward D is \(d\ne H\). These are two known anchors, not two double occurrences at the same label. The forward phase gives a singleton \(s\), with the two actual forward defects \(f_d,f_s\), and the [literal arithmetic/star pair guards](../sdirk-eight-all-dirty-seven-quadratic-last-rear-terminal-overlap/README.md#literal-pair-data-and-true-affine-factor).

In the [quadratic seven-clock decomposition](../sdirk-eight-all-dirty-seven-clock/README.md), the true affine \(F_*\) interpolates \(L_3/L_4\) at \(H,d\). The true \(\deg F_*=1\) follows by degrees of the D cubic and quadratic singleton graph. Let
\[
 M_3=\frac{L_3-F_*L_4}{(y-H)(y-d)}=L R,\qquad L=l_0+l_1 y,
\]
with centered Legendre polynomials and actual quadratic graph \(R\). As in the terminal-overlap packet, its two paid singleton values fix \(l_0=2M_3(0),\ l_1=(M_3(s)/f_s-l_0)/s\), and \(l_1\ne0\). The third D root is \(e=-l_0/l_1\), and
\[
\begin{gathered}
 a=(f_s-\tfrac12)/s,\quad b=[y^3]M_3/l_1,\quad
 R(y)=\tfrac12+a y+b y(y-s),\\
 E=[y^2]M_3\,l_1-l_1^2a-[y^3]M_3(l_0-l_1s)=0 .
\end{gathered}
\]
The true third D \(e\) must now be the observed nonterminal rear D, because its label is different from both anchors. No graph-root split or sign assumption is needed. The true rear orientation \(y'=H-y\) supplies the other S label \(t_s\) and the two actual reverse phase defects \(\rho_e,\rho_s\), using the D offset \(H-e\). Rear A2, A3 and star would respectively put its S at \(2(H-e),(H-e)/2,2-(H-e)\) in reflected coordinates. Thus both literal orders of a noncentral star use its correct equally paid defects, and not a physical row permutation. The true third-row phases, not hypothetical affine weights, are being used.

## Three singleton reads and two original weighted-D equations

Set \(C=A_2+B R\), \(\mu=R(t_s)\ne0\) and \(\Omega=s t_s(t_s-s)\ne0\). The true reverse/original scale is \(\lambda=\mu/\rho_s\). The quadratic \(Z^\#=\Omega\mu C\) is fixed by the three distinct paid singleton readings:
\[
\begin{split}
Z^\#(y)={}&2\mu L_4(0)(t_s-s)(y-s)(y-t_s)\\
 &-\mu L_4(s)t_s\,y(y-t_s)/f_s+L_4(t_s)s\,y(y-s).
\end{split}
\]
The front D equation fixes
\[
 p_d=f_d(f_d-R(d))\ne0,\qquad
 j_d=\mu\Omega L_4(d)-f_d Z^\#(d)=J p_d,\qquad J=\Omega\mu B.
\]
The true graph-off condition at D follows from the two-root fibre identities, not from making \(A_2\) invertible. Given a reflected D with original clock \(k\) and known normalized defect \(\rho\), its original defect is \(\lambda\rho\) and its equation is
\[
 p_d(\rho_s^2\Omega L_4(k)-\rho_s\rho Z^\#(k))
   -j_d\,\rho(\mu\rho-\rho_s R(k))=0.
\]
Apply this at \(k=e\) with \(\rho=\rho_e\), and at \(k=H\) with \(\rho=1/2\). For a true rear star, \(\rho_e=\rho_s\); since \(\rho_s\ne0\), these are equivalent to the smaller checks
\[
 X=p_d[\Omega L_4(e)-Z^\#(e)]-j_d[\mu-R(e)]=0,\qquad
 Y=p_d[q^2\Omega L_4(H)-q Z^\#(H)]-j_d[\mu-q R(H)]=0,\quad q=2\rho_s.
\]
This uses actual two-sided paid equations, including the terminal diagonal, without any unknown mate at a D or read at a fourth clock.

## Exact exclusion of the two phase pairs

Clear denominators using only the checked nonzero phase, label, Legendre and paid slope/graph factors. Project \(E,X\) and \(E,Y\) separately in \(d\); strip only \(H\)-guards and take the projection gcd. It has these completely checked irreducible factors:

| Front / rear | Projection degrees | \(H\)-factor degree and multiplicity |
| --- | --- | --- |
| A3 / star | 466,558 | (18,2),(4,2) three times,(2,3),(18,8) |
| star / star | 358,456 | (12,1),(4,5),(1,6),(6,6),(2,6),(9,16) |

The verifier fixes each of the twelve factors individually. It takes exact monic \(E\) over the irreducible \(H\)-field and removes only repeated divisors of selected true guards. One uses the simultaneous zero locus of the two affine slopes, not their approximated values. The three quartics with the same tag are distinguished by their exact \(H^2\) coefficient, not library factor iteration order. For \(H=2\), the entire frozen \(X\) row happens to vanish; the retained exact \(E\) row and actual \(Y\) still suffice. The two quadratic factors need no trimming and have a full actual positive \(d\)-degree modulo their fixed prime. Each remaining factor has a prescribed simple good place, carrying the trimmed monic \(E\) with integral coefficients and joint residue gcd one. The [same good-place argument](../sdirk-eight-all-dirty-seven-quadratic-last-rear-extra-overlap/README.md#exhaustive-projection-and-exact-guard-removal) excludes every possible algebraic \(d\), including nonsplit residues. There is no conclusion for arbitrary positive-characteristic fields or other topologies.

## Replay and Lean scope

Run `SYMPY_GROUND_TYPES=flint python check_two_star_charts.py` with SymPy 1.14 and python-flint 0.8. Polynomial fractions are exact FLINT rationals, the projections are ordinary affine resultants; fibre checks are exact rational fields and fixed-prime polynomial gcds. Reuses the exact arithmetic helpers in the terminal/extra-overlap sibling packets. The [candidate Lean scalar companion](../../lean/RKCert/Research/SDIRKEightDirtySevenQuadraticTwoSDisjointRearStar.lean) certifies the denominator-free front and rear paid pair identities and defines no unsafe division; the actual rooted-order ingress and finite verification are not all native Lean. The general stage bound does not change.

The publication audit independently replayed the corresponding exact arithmetic; the new Lean companions here are draft scalar lemmas, not claimed kernel-checked in this release.
