# One singleton endpoint: single-overlap S,D,D versus one later rear double

Consider strict ten-stage SDIRK of ordinary order at least eight over a characteristic-zero field, all physical quadratic defects nonzero, exactly seven distinct clocks, and exactly one singleton endpoint clock. Orient from that singleton by actual weighted mirror if needed. If the front opening is S,D,D and the opposite opening had one later D and one S, then the two sets of doubled clocks could share either one or two labels. The [double-overlap companion](../sdirk-eight-all-dirty-seven-quadratic-sdd-one-extra-double-overlap/README.md) eliminates the two-label case; this packet eliminates the one-label case. The separate [S,D,D versus D,D,D result](../sdirk-eight-all-dirty-seven-quadratic-sdd-ddd/README.md) now implies the opposite opener must be **D,S,S** when the singleton end opens S,D,D. This is a chronology restriction, not a general stage interval change. It needs no signs, clock splitting, or ordered-field structure.

## All clocks in a one-overlap pair

Use \(y=x-1\) after normalizing the diagonal to one, \(H=2(m-1)\), \(m=1/(2\gamma)\), and centered \(t=y-H/2\). The first singleton is \(y=0\), the reverse first double is \(y=H\), and write \(d\) for the other rear D label. Its actual opposite singleton companion \(s\) and the known normalized reverse defects \(\rho_d,\rho_s\) are the [A2, A3 and star table](../sdirk-eight-all-dirty-seven-quadratic-sdd-one-extra-double-overlap/README.md#paid-graph-and-two-vieta-products). Set \(\rho_H=1/2\). The remaining D label \(e\) appears as a forward row, where its known normalized original defect is \(f_e\).

Write \(q\) for the unique reused D label (\(H\) or \(d\)), and \(r\) for the other rear D label. The front pair is \(\{q,e\}\). Let \(f_q\) denote its true known front defect at \(q\). With \(\kappa(z)=1+2z-z^2\) and \(q_{\rm ar}(z)=N(z)/D(z)\) as in the companion:
\[
\begin{array}{c|ccc}
\text{forward phase placement}&e& f_q& f_e\\\hline
\mathrm{A2}\ (q\text{ second})&2q&\kappa(q)/2&q_{\rm ar}(q)/2\\
\mathrm{A3}\ (q\text{ third})&q/2&q_{\rm ar}(q/2)/2&\kappa(q/2)/2\\
\mathrm{star}\ (\text{either order})&2-q&\kappa(q)/2&\kappa(q)/2.
\end{array}
\]
Thus all three D coordinates and both physically observed S coordinates are known in \(H,d\). The star grouping uses equality of the two *known pairs* in the two possible literal orders, not invariance under permuting a proposed method. The ordinary clock and phase guards include distinctness of \(0,s,H,d,e\), nonzero defects and arithmetic denominators, \(m\ne0\), and the singleton first-departure prohibition on forward gap two. The [single-endpoint parity lemma](../sdirk-eight-all-dirty-seven-quadratic-one-singleton-arithmetic/PARITY.md) forbids any centered or antipodal D labels. In particular \(q=H\) and A3 gives \(e=H/2\) and is impossible for each of the three rear phases. This leaves fifteen genuine phase-data charts; both possible values of the reused label and all other placements are retained.

## Graph identification and two paid singleton fits

Use the [seven-clock decomposition](../sdirk-eight-all-dirty-seven-clock/README.md), with affine \(F_*\) of nonzero slope, \(\mathcal Q=L_3-F_*L_4\) and the normalized singleton graph \(R\) proportional to \(\mathcal Q/P\), where \(P\) has the three D roots. Here \(L_j\) are the monic centered Legendre modes evaluated at \(t=y-H/2\). The D Legendre values \(L_4(H),L_4(d),L_4(e)\) are nonzero by coprimality with \(L_3\). Fit \(F_*\) from the two paid D values \(L_3(H)/L_4(H),L_3(d)/L_4(d)\), whose clock difference is nonzero. The protocol for the third D is
\[
 M_3(y)=\mathcal Q(y)/[(y-H)(y-d)], \qquad M_3(e)=0 .
\]
This is exact polynomial division, with no need to invert the value of the graph at a D label. In a genuine tableau the cubic \(M_3\) is proportional to \((y-e)R(y)\), so the \(s\)- and \(0\)-values of \(M_3\) are both nonzero: the two clocks are singleton, not equal to \(e\), and the two defects are nonzero. Normalize \(R(0)=1/2\). The reverse-to-forward residual scale is determined at the paid rear S:
\[
       \lambda=R(s)/\rho_s=-e M_3(s)/[2M_3(0)\rho_s(s-e)] .
\]
This statement permits a repeated root of \(M_3\), a nonsplit \(R\), and an overlap of \(P\) and \(R\) at any D label.

At the unique doubled overlap \(q\), use the two true observed residuals \(f_q,\lambda\rho_q\) in the actual \(L_4-g(A_2+Bg)\) quadratic. Its product gives
\[
 \beta=B\lambda=-L_4(q)/(f_q\rho_q).
\]
Define quadratic polynomials \(T_0,T_1\) on the distinct actual D clocks by the following paid interpolation, so that \(\lambda A_2=T_0+\lambda T_1\):
\[
\begin{array}{c|cc}
 y&T_0&T_1\\\hline
 q&-\beta f_q&-\beta\rho_q\\
 r&L_4(r)/\rho_r&-\beta\rho_r\\
 e&-\beta f_e&L_4(e)/f_e .
\end{array}
\]
The first row is the true Vieta sum; the other two use one observed residual each. Thus the two paid singleton equations are
\[
 \begin{split}
 0&=T_0(0)+\beta/2+\lambda\bigl(T_1(0)-2L_4(0)\bigr),\\
 0&=\rho_s T_0(s)-L_4(s)+\lambda\bigl(\rho_s T_1(s)+\beta\rho_s^2\bigr).
 \end{split}
\]
Clear the displayed \(\lambda\) ratio using only its true nonzero denominator. In neither row do we divide by its coefficient of \(\lambda\). This keeps singular and simultaneously rank-zero fits as actual candidates until the complete specialized gcd test.

## Exact projection and fibres

Write \(E,X,Y\) for the guarded integer polynomial numerators in \(H,d\) of \(M_3(e)\) and the two singleton equations. All nonconstant denominators are checked against the genuine clock/phase and Legendre guards; the polynomial slope and \(M_3(0),M_3(s)\) are additionally proved nonzero as above. In each chart compute separately the integer resultants of \(E\) against \(X,Y\) in \(d\); remove only known nonzero guards in \(H\) alone, and then take the gcd in \(H\). Every \(E\) has degree nine in \((H,d)\). The resulting irreducible factor degrees, with repeats shown as powers, are:

| Unique overlap | Front placement | Rear A2 | Rear A3 | Rear star |
| --- | --- | --- | --- | --- |
| terminal \(H\) | A2 | 8 | 4, 8 | 9 |
| terminal \(H\) | star | 8 | 8 | 4, 8 |
| extra rear \(d\) | A2 | \(2^2\), 4 | 2, 4, 4, 4 | 2, 4, 9 |
| extra rear \(d\) | A3 | 2, 4, 4, 4 | \(2^2\), 4, 4 | 2, 4, 9 |
| extra rear \(d\) | star | 1, 2, 4, 8 | \(1^2\), 2, 4, 8 | 1, \(2^2\), 4, 4 |

Projection imposes no conditions on specialized leading coefficients. Reconstruct the simultaneous gcd of \(E,X,Y\) in \(d\) over each exact irreducible \(H\)-field. There are 39 fields counted by projected factor per branch. All nine degree-two projected factors have unit \(d\)-gcd; every other has a linear \(d\)-gcd except a degree-two \(d\)-gcd at one linear \(H\)-factor. In the nonunit cases all common factors in \(d\) are stripped by actual guards. Across these fields the removals have total degrees 14 from \(s=e\), 2 from \(s=0\), 2 from centered \(d\), 6 from first-departure, and 7 from another genuine front phase guard. The replay labels the cause of each strip, checks every irreducible field, and does not rely on the existence of any real root or on restricting coefficients to a rational field. No positive characteristic or extra normalizations are used, so every characteristic-zero extension is covered.

## Replay and scope

Run `SYMPY_GROUND_TYPES=flint python check_exact_fibres.py` using SymPy 1.14 and python-flint 0.8. This imports the exact projections and guards from `projection.py`. The [Lean companion](../../lean/RKCert/Research/SDIRKEightDirtySevenQuadraticSddOneExtraSingleOverlap.lean) checks two denominator-free scalar gates; the rooted-order ingress and finite exact eliminations form a replayable mathematical proof, not an end-to-end Lean theorem.
