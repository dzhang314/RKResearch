# A3 front versus rear D,S,S arithmetic, with a new terminal D clock

Suppose a strict ten-stage SDIRK tableau has ordinary order at least eight over a characteristic-zero field, all physical quadratic defects nonzero, exactly seven different clocks, and precisely one singleton physical endpoint. Orient from the singleton. Its actual first three rows cannot consist of S,S,D with genuine arithmetic followed at the doubled end by genuine D,S,S arithmetic, **when the front D and terminal D clock labels differ**. The [reused-terminal exclusion](../sdirk-eight-all-dirty-seven-quadratic-two-s-dss-arithmetic-reuse/README.md) covers equal labels. The front A2 phase, which has the S,D,S order, is outside this packet's terminal-new claim. No general stage interval changes.

## Actual A3 phase and the common measured affine recovery

Normalize the diagonal to one and write \(y=x-1,\ H=2(m-1),\ m=1/(2\gamma)\). The actual first, second and third front labels are \(0,s,d\) with \(d=2s\), and the genuine forward gap is \(s=d/2\). With \(\kappa(z)=1+2z-z^2,\ D(z)=-2+z+4z^2-z^3,\ N(z)=(1+4z-4z^2)D(z)+4z^2(3z-2)\), the original forward paid residuals on these three rows are \(1/2,\kappa(s)/2,N(s)/(2D(s))\). Their nonzero and actual tap guards include \(s,\kappa(s),D(s),N(s),3s-2\ne0\). The first-departure guard forbids \(s=2\) because the first clock is singleton. No row permutation or identification with front star is used.

The [terminal-new derivation](../sdirk-eight-all-dirty-seven-quadratic-two-s-dss-arithmetic-new-star-front/README.md) is valid for these exact A3 pairs: it needs only the actual measured front S values \(1/2,f_s\) at \(0,s\), the paid D value \(f_d\) at \(d\), and the genuine two arithmetic S readings at \(p=H-v,\ q=H-2v\). From the D anchors \(H,d\), fit \(F_*\) through \(L_3/L_4\), then \(M_3=(L_3-F_*L_4)/[(y-H)(y-d)]\). On the true graph \(M_3=L R\) with affine \(L=l_0+l_1 y\) and \(l_1\ne0\). The known front S measurements give \(l_0=2M_3(0),\, l_1=(M_3(s)/f_s-l_0)/s\); the genuine \(R\) equals \(1/2+a y+b y(y-s)\) with \(b=[y^3]M_3/l_1\ne0\). This determines the third D \(e=-l_0/l_1\) without assuming any graph splitting, discarding Hermite roots, or inverting \(R\) at any D. Legendre coprimality, the physical clock guards and true graph normalizations justify these denominators. The remaining quadratic coefficient equation is called \(E=0\).

Use the same four other paid equations \(\mathcal R,\mathcal N,\mathcal X,\mathcal Y\) described in the [companion](../sdirk-eight-all-dirty-seven-quadratic-two-s-dss-arithmetic-new-star-front/README.md#scalar-rear-ratio-nodal-determinant-and-actual-pair-fits): the cubic graph ratio of the two actual reverse S labels, the nodal determinant of the four physical S labels, the actual singleton \(C\)-fit at the rear third clock, and the terminal D equation after the front has fixed the scaled \(B\). In particular no denominator uses a variable leading coefficient of the ratio, or a postulated pivot of the nodal/paid fits. The guarded degree triples in \((H,d,v)\) of these five exact rows are
\[
 (18,9,0),\quad(10,5,3),\quad(22,11,2),\quad(16,8,8),\quad(26,18,8).
\]
These are computed from A3 physical residuals separately; only the abstract formulas are shared. The [single-end parity lemma](../sdirk-eight-all-dirty-seven-quadratic-one-singleton-arithmetic/PARITY.md) supplies true centered/antipodal clock guards.

## Exact projected factors and fixed local certificates

Set \(\Pi=\operatorname{Res}_v(\mathcal R,\mathcal N)\) after stripping only genuine guards independent of \(v\). Its \((H,d)\)-degree pair is \((84,43)\). Use the guarded integer resultant of \(E,\Pi\) in \(d\). Its degree in \(H\) is 773, with rational irreducible factor-degree/multiplicity list
\[
           (3,1),(4,1),(12,3),(18,8),(18,16),(24,3),(56,1),(170,1).
\]
The specialization-safe resultant necessities hold even if a leading coefficient vanishes in an actual field. Every coefficient denominator and guard factor is accounted for in the source. Each entire factor is excluded by the certified fixed place in this table:

| Degree, multiplicity | Certificate | Prime | \(H\) residue | \(d\) test |
| --- | --- | ---: | ---: | --- |
| 3, 1 | direct | 11 | 4 | \(0\) |
| 4, 1 | trimmed anchor | 11 | 7 | unit anchor gcd |
| 12, 3 | direct | 17 | 5 | \(8\) |
| 18, 8 | trimmed anchor | 23 | 15 | unit anchor gcd |
| 18, 16 | trimmed anchor | 31 | 1 | unit anchor gcd |
| 24, 3 | direct | 101 | 15 | \(59\) |
| 56, 1 | direct | 11 | 0 | \(4\) |
| 170, 1 | direct | 11 | 2 | \(7\) |

The chosen \(H\) roots are simple with leading units for the rational irreducible factors, so each abstract \(H\)-field embeds into the relevant \(\mathbb Q_p\). A direct row checks that the actual positive \(d\)-degree of \(E\) over that \(H\)-field survives reduction; the putative \(d\) is then algebraic and integral at the place. The displayed \(d\) is the entire root set of the reduced \(d\)-gcd of \(E,\Pi\), with total multiplicity checked. At it, at least one of the four integer \(v\)-rows retains full positive degree, forcing \(v\) likewise integral. Their joint reduced \(v\)-gcd is a unit. No original guard is required to remain a unit at these reductions just to evaluate the already-cleared integer equations. In particular the degree-56 place legitimately uses \(H=0\) in residue while \(H\ne0\) in the physical method.

In a trimmed row, work first over the exact abstract irreducible \(H\)-field and remove only actual static-guard-supported factors of \(E\) as a polynomial in \(d\):
- For degree 4 use the proved nonzero \(H,d\) guards independent of \(v\), leaving degree 8 from degree 9.
- For the degree-18 factor of multiplicity 8, use just the two true affine slopes of \(F_*\) and \(L\), leaving degree 8 from degree 9.
- For the degree-18 factor of multiplicity 16, use just the actual \(\kappa(s)\) and \(N(s)\), leaving degree 7 from degree 9.

The resulting monic polynomial is checked integral at the chosen \(H\)-place, and its reduction has unit gcd with the reduction of \(\Pi\), ruling out every actual \(d\) without needing splitting, a guessed curvature, or a finite-place deletion of guard-zero residues. This proves the exclusion over every characteristic-zero field. It does not infer a finite-characteristic absence.

## Replay

Run `SYMPY_GROUND_TYPES=flint python check_front_a3.py` (SymPy 1.14 and python-flint 0.8). This regenerates the exact A3 projections and the eight fixed certificates; there is no dependence on a cache or prime search. The [Lean companion](../../lean/RKCert/Research/SDIRKEightDirtySevenQuadraticTwoSDssArithmeticNewA3Front.lean) checks the arithmetic second-singleton identity and the affine-factor coefficient gate. The full tableau ingress and exact elimination are mathematical proof with independent exact replay, not an end-to-end native Lean theorem.
