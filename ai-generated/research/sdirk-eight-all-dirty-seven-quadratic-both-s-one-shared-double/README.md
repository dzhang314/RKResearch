# Both singleton endpoints: one shared D in two S,D,D openings is impossible

Let a strict ten-stage SDIRK tableau over a characteristic-zero field have ordinary order at least eight, all ten physical quadratic defects nonzero, and exactly seven distinct clock labels. Suppose both physical endpoint labels are singleton, both actual first-three prefixes are S,D,D, and their doubled labels overlap in exactly one site. This chart is impossible for **every** literal arithmetic/star phase. In particular this includes mixed phases and a shared first later D on both sides. No sign, ordering, root-splitting or finite-characteristic hypothesis is used.

Combining this with the [two-shared exclusion](../sdirk-eight-all-dirty-seven-quadratic-both-s-two-shared-arithmetic/LEDGER.md), **both ends cannot be S,D,D**: zero overlap would require four distinct D labels, and only three exist. See the [complete chronological ledger](LEDGER.md). The [S,S,S exclusions](../sdirk-eight-all-dirty-seven-quadratic-both-s-sss-arithmetic/README.md) then require at least one actual end to have exactly one later singleton. This is not a general ten-stage lower bound; all other both-singleton types are separate.

## Six literal phase meshes

Normalize the common diagonal to one and use \(y=x-1\), endpoints \(0,H\) with \(H\ne0\), half-width \(m=(H+2)/2\), and actual reflected coordinate \(H-y\). For arithmetic the two later offsets are \(u,2u\), in that physical order; their residuals are \(\kappa(u)/2,N(u)/(2D(u))\), where
\[
 \kappa(u)=1+2u-u^2,\quad D(u)=-2+u+4u^2-u^3,\quad
 N(u)=(1+4u-4u^2)D(u)+4u^2(3u-2).
\]
The common input guards include \(u\ne0,2,\ 3u-2\ne0,\ \kappa D N\ne0\): the gap two would force a later repeat of the singleton initial label and the other restrictions are the actual nonzero arithmetic tap/defect inequalities. For star the offsets are \(u,2-u\) with equal residual \(\kappa(u)/2\) and \(u\ne0,1,2,\ \kappa\ne0\). The backward actual \(v\) uses the same formulas in its own normalized coordinates. When a star is used, index its shared label by that offset \(u\) or \(v\); the opposite star ordering replaces the overall second gap by \(2-u\) or \(2-v\) and gives the same **consumed** pair formulas. No reordering of a proposed tableau is used.

Call the shared D \(p\), forward-only D \(q\), and rear-only D \(r\). They are the three distinct D labels, distinct also from \(0,H\). If \(u_i\) is the shared forward offset and \(v_j\) is the shared reverse offset, then \(H=u_i+v_j\), \(p=u_i\), \(q=u_{3-i}\), \(r=H-v_{3-j}\). This gives six pair-data cases after the true weighted mirror: \(\mathrm{AS}_{11},\mathrm{AS}_{21}\) with arithmetic oriented forward, \(\mathrm{AA}_{11},\mathrm{AA}_{12},\mathrm{AA}_{22}\), and \(\mathrm{SS}_{11}\). A subindex is an ordered later D position in arithmetic, but only the chosen shared offset in star. The actual mirror converts \(\mathrm{AA}_{21}\) to \(\mathrm{AA}_{12}\). These cases exhaust the possibilities without assuming a clock or a tableau is reflection-symmetric.

## Exact graph recovery and five paid values of one quadratic

Evaluate the centered monic Legendre modes at \(y-H/2\). By the [seven-clock pair decomposition](../sdirk-eight-all-dirty-seven-clock/README.md),
\[
 Q_0(y)=L_3(y)-F_*(y)L_4(y)
       =\text{nonzero scalar}\,(y-p)(y-q)(y-r) R(y),
\]
with true affine \(F_*\) and true quadratic graph \(R\). Consecutive coprimality ensures \(L_4(p),L_4(q),L_4(r)\ne0\). The actual slope of \(F_*\) is nonzero by \(\deg Q_0=5\). Fit \(F_*\) through \(L_3/L_4\) at \(p,q\) using their distinct labels. Divide \(Q_0\) first by \((y-p)(y-q)\) exactly and then by \(y-r\) with remainder \(E\). An actual candidate has \(E=0\). The quadratic quotient \(R_0\) then gives
\[
 R(y)=R_0(y)/(2R_0(0)),\qquad
 \lambda=2R(H)=R_0(H)/R_0(0),
\]
because \(0,H\) are genuine singleton physical endpoints with original first defect \(1/2\) and reflected first defect \(1/2\). Both quotient values at these endpoints are true nonzero. In particular no division by \(R\) at a doubled label, or any assumption on its own roots, is made.

Let \(f_p,f_q\) be the normalized original defects paid at \(p,q\), and \(\rho_p,\rho_r\) the normalized reverse defects paid at \(p,r\). In the original orientations their latter values are multiplied by \(\lambda\). The shared D Vieta product gives \(\beta=B\lambda=-L_4(p)/(f_p\rho_p)\). Now \(T=\lambda A_2\) is known at **five** actual labels:
\[
\begin{array}{c|l}
 0 & 2\lambda L_4(0)-\beta/2\\
 H & 2L_4(H)-\beta\lambda/2\\
 p & -\beta(f_p+\lambda\rho_p)\\
 q & \lambda L_4(q)/f_q-\beta f_q\\
 r & L_4(r)/\rho_r-\beta\lambda\rho_r.
\end{array}
\]
The \(p\) value is the true shared Vieta sum. At \(q,r\) only the known literal copy is read; the other copy is not guessed. Set \(J(y)=(H-y)T(0)+y T(H)\). A single quadratic with the three shared/end values must satisfy
\[
 p(p-H)\bigl[HT(s)-J(s)\bigr]
       -s(s-H)\bigl[HT(p)-J(p)\bigr]=0\qquad(s=q,r).
\]
These are the two rows \(X,Y\), and the identity does not invert a quadratic coefficient, *or* presume the paid rows have any signs. The known pair data suffice; no actual fourth row or normalized trace is used.

## Exact projections and all guard fibres

The verifier clears integer numerators of \(E,X,Y\) after checking their denominator factors against actual nonzero tap, clock, Legendre, affine/graph, and paid-pair guards. It projects \((E,X)\) and \((E,Y)\) in \(v\) separately and takes the gcd after stripping only true \(u\)-only factors. These are ordinary affine resultants with full generic degree; at any common finite root their Sylvester determinants vanish even if a projected leading coefficient drops. The exact profiles are:

| Case | Raw projected degrees | Guarded projected degrees | Irreducible \(u\)-factors and multiplicities |
| --- | --- | --- | --- |
| AS11 | 180,126 | 180,126 | degree 4,8 each once; \(u+1,2u+1\) both 12 |
| AS21 | 153,153 | 153,153 | degree 4,8 each once; \(u+1,2u+1\) both 12 |
| AA11 | 160,160 | 160,160 | degree 4,8 each once; \(u+1\) 8; \(2u+1\) 12 |
| AA12 | 207,153 | 203,152 | degree 4 twice, degree 8 once; \(u+1,2u+1\) both 12 |
| AA22 | 160,160 | 157,160 | degree 4,8 each once; \(u+1\) 12; \(2u+1\) 8 |
| SS11 | 112,112 | 112,112 | degree 4 twice, degree 8 once; \(u+1\) 8; \(u-3\) 12 |

The four factors per row are exhaustively checked in their own abstract rational fields; this includes the two rational linears rather than inferring a conclusion from a generic rank. In the 12 quartic/octic fibres the exact joint \(v\)-gcd has degree one. It is entirely supported on \(L_4(p)=0\), except for the AA12 and SS11 **quartic** where it lies on the forbidden \(q=r\). In a linear fibre the joint \(v\)-gcd may have degree two or three, and all its roots lie on \(m=0\), except for AS21 and AA22 at \(u=-1\) where they lie on \(v=0\). The verifier checks these **particular** true guard factors exactly, with their repeated powers; a modular projection or a floating candidate enumeration is not involved. Thus all 24 fibres are impossible over arbitrary characteristic-zero extensions.

Run `SYMPY_GROUND_TYPES=flint python check_one_share.py` with SymPy 1.14 and python-flint 0.8. The file pair is independently replayable; no cached rows, external history, or compiled kernel are needed. The linked [Lean scalar companion](../../lean/RKCert/Research/SDIRKEightDirtySevenBothSingletonOneSharedDouble.lean) checks the cleared quadratic interpolation and Vieta identities. The rooted-order reduction and exact elimination are not all native Lean. The general 10–11 stage interval is unchanged.

The publication audit independently replayed the corresponding exact arithmetic; the new Lean companions here are draft scalar lemmas, not claimed kernel-checked in this release.
