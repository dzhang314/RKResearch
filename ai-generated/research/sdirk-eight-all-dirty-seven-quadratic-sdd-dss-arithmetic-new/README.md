# A unique singleton endpoint cannot open S,D,D

Assume a strict ten-stage SDIRK tableau has ordinary order at least eight over a characteristic-zero field, all ten physical quadratic defects nonzero, exactly seven distinct clocks, and exactly one singleton physical endpoint. Orient from that singleton by the actual weighted mirror if necessary. That end **must open S,S,D or S,D,S**. The previous [three-singleton exclusion](../sdirk-eight-all-dirty-seven-quadratic-one-singleton-arithmetic/README.md) rules out S,S,S. A front S,D,D would force a reverse D,S,S [true arithmetic opener](../sdirk-eight-all-dirty-seven-quadratic-sdd-dss-star/README.md). The [reused-terminal arithmetic result](../sdirk-eight-all-dirty-seven-quadratic-sdd-dss-arithmetic-reuse/README.md) and the terminal-new proof here exclude it. This is a chronology result for exactly one singleton physical endpoint, not a change to the general 10–11 stage interval.

## The terminal-new graph and paid scale

Normalize the diagonal to one. Write \(y=x-1\), \(m=1/(2\gamma)\), \(H=2(m-1)\), and evaluate the monic Legendre modes \(L_3,L_4\) at \(t=y-H/2\). The first singleton label is \(0\), the terminal D label is \(H\), and the two observed front D labels \(a,b\) are different from \(H\) in this packet. In the front phase with actual gap \(u\), the options are
\[
(a,b)=(u,2u)\quad\text{in arithmetic},\qquad
(a,b)=(u,2-u)\quad\text{in star}.
\]
Their actual known defects \(f_a,f_b\) are the [literal first-three values](../clock-localized-tail/tied-stage-floor/FIRST-THREE-ROWS-AND-PHYSICAL-LEVEL-OBSTRUCTIONS.md). This uses the actual order, including unequal arithmetic values. Both actual star orders are included as possible values of \(u\), not by assuming a row permutation preserves the method. The singleton first-departure guard forbids \(u=2\).

The [seven-clock decomposition](../sdirk-eight-all-dirty-seven-clock/README.md) gives an affine nonconstant \(F_*\) with \(\mathcal Q=L_3-F_*L_4\) proportional to \(P R\), where \(P\) is cubic on \(H,a,b\) and the singleton graph \(R\) is genuinely quadratic. The coprime Legendre values \(L_4(H),L_4(a),L_4(b)\) are nonzero at the D labels. Fit \(F_*\) through \(L_3/L_4\) at \(H,a\) and divide exactly
\[
 M_3(y)=\mathcal Q(y)/[(y-H)(y-a)],\qquad E:\ M_3(b)=0 .
\]
Use \(W(y)\) for the quadratic quotient in synthetic division of \(M_3\) by \(y-b\); the condition \(E=0\) makes that division exact. The leading coefficient is nonzero by the quadratic graph. Since \(R(0)=1/2\) and \(b\ne0\), the true graph is
\[
                  R(y)=-b W(y)/(2M_3(0)).
\]
Here \(M_3(0)\ne0\), since \(0\) is a singleton with nonzero defect, not a D root. Common roots of \(P,R\), a repeated graph root, and nonsplit graph roots are all retained. In particular no inverse is taken of \(R\) at a D label.

The two actual rear S labels in original coordinates are \(s=H-v,\ p=H-2v\), where \(v\) is the true reverse arithmetic gap. Put \(\kappa=1+2v-v^2\), \(D=-2+v+4v^2-v^3\), \(\widehat q=D-v(v-2)(3v-2)\). The two normalized reverse defects are \(\kappa/2\) and \(\kappa\widehat q/(2D)\) by the literal numerator factor \(N(v)=\kappa\widehat q\). The true guards include nonzero \(v,\kappa,D,\widehat q,3v-2\). No reverse \(v=2\) is discarded simply as a gap. Let \(\mu=\kappa\lambda=2R(s)\ne0\), where \(\lambda\) is the genuine reverse-to-original scale. Rear S ratio gives \(D W(p)=\widehat q W(s)\), or after cancelling the known nonzero \(v\), the polynomial
\[
 \mathcal R=D\big(W_2(2H-3v)+W_1\big)-(v-2)(3v-2)W(s)=0,\quad
 W(y)=W_2y^2+W_1 y+W_0 .
\]
The degree-four terms cancel, leaving at most degree three. No leading coefficient is used as a pivot. In fact this ratio cannot vanish identically on a genuine quadratic mesh: if its constant and cubic coefficients vanish, writing \(w_0=W(H)\), \(w_1=W'(H)\), \(w_2=W_2\) gives \(w_1=2w_2,w_0=-w_2\); its linear coefficient is then \(8w_2\ne0\).

## Three measured singleton values fix the quadratic fit

Set \(C=A_2+B R,\ Z=\mu C,\ J=\mu B\). The three actual singleton equations at the distinct observed clocks \(0,s,p\) specify the degree-two fit uniquely:
\[
                 Z(0)=2\mu L_4(0),\qquad
                 Z(s)=2L_4(s),\qquad
                 Z(p)=2D L_4(p)/\widehat q .
\]
There is no unknown fourth singleton in this interpolation. Each denominator is an observed nonzero scalar or an actual difference between singleton labels. At a front D label \(i=a,b\), put
\[
           p_i=f_i(f_i-R(i)),\qquad j_i=\mu L_4(i)-f_i Z(i).
\]
The true D equation is \(j_i=J p_i\); in particular \(p_i\ne0\) because a D defect is nonzero and is not its singleton graph value. Thus the two measured residuals give
\[
                        \mathcal F=p_a j_b-p_b j_a=0 .
\]
At the actual terminal, the observed original defect is \(\mu/(2\kappa)\). Its D equation implies
\[
        \mathcal T=p_a\big(4\kappa^2L_4(H)-2\kappa Z(H)\big)
                    - j_a\big(\mu-2\kappa R(H)\big)=0.
\]
This follows by multiplying by \(4\kappa^2\), cancelling the true nonzero \(\mu\), and multiplying by \(p_a\). No symbol for an unknown rank is divided out. If one of the affine fits degenerates, the common polynomial roots are still tested together. Graph values at doubles may vanish; no denominator here is such a graph value.

## Specialization-safe exact projections

Write \(E,\mathcal R,\mathcal F,\mathcal T\) also for the guarded integer numerators, in coordinates \(H,u,v\). The verifier checks every nonconstant denominator factor against true clock/phase guards, \(L_4\) at D labels and \(M_3(0)\), and removes only proved nonzero guards. Among them the [single-end parity lemma](../sdirk-eight-all-dirty-seven-quadratic-one-singleton-arithmetic/PARITY.md) forbids centered or antipodal D labels; it applies even over the algebraic closure. First project \(\mathcal R,\mathcal F\) and \(\mathcal R,\mathcal T\) separately in \(v\) to \(U_{\mathcal F},U_{\mathcal T}\). Then project \(E,U_{\mathcal F}\) and \(E,U_{\mathcal T}\) separately in \(u\). At each step strip only guards involving the remaining coordinates. The specialized leading coefficients need not be units for resultant necessity.

For a front arithmetic phase the final projection degrees in \(H\) are 788 and 651. The common irreducible factor degrees and multiplicities are \((2,36),(4,2),(4,9),(36,1),(42,1)\). For a front star the final degrees are 622 and 656, and the factor list is \((1,9),(2,38),(4,9),(18,2),(21,2)\). The \((H,u)\) degrees of the two intermediate projections are \((121,96),(133,85)\) for arithmetic and \((121,78),(133,85)\) for star.

For the six small irreducible \(H\) factors of degree at most four, reconstruct the simultaneous \(u\)-gcd of \(E,U_{\mathcal F},U_{\mathcal T}\) in the exact abstract field. Their raw degrees are \(0,1,1\) for arithmetic in order of increasing degree and then multiplicity, and \(2,0,2\) for star. In every case the \(u\)-gcd is a unit after stripping the true guards involving \(H,u\) alone. This is an exact justification, not exclusion of a residue-guard-zero component.

## Four exact Hensel collision certificates

For each large irreducible \(H\) factor, let \(j\) be as in the table below. Compute the exact monic \(u\)-gcd
\[
       G(u)=\gcd\bigl(E(H,u),\ j^{\deg_v\mathcal R}\,\mathcal R(H,u,H/j)\bigr)
\]
over its rational algebraic \(H\)-field. This polynomial captures the proposed literal collision \(p=0\) when \(j=2\), or \(s=0\) when \(j=1\). Merely observing such a collision modulo a prime does not prove it in the original field; the exact gcd and two uniqueness lifts are essential.

| Front phase | Degree of \(H\) factor | \(j\) | \(\deg G\) | Prime | \(H\) residue | All candidate \(u\) residues | All candidate \(v\) residues |
| --- | ---: | ---: | ---: | ---: | ---: | --- | --- |
| arithmetic | 36 | 2 | 1 | 13 | 10 | 4 | 5 |
| arithmetic | 42 | 1 | 1 | 19 | 4 | 12 | 4 |
| star | 18 | 2 | 2 | 29 | 12 | 8, 23 | 6 for each |
| star | 21 | 1 | 2 | 59 | 45 | 5, 56 | 45 for each |

At each fixed place, the chosen \(H\) root is simple and the leading coefficient of its irreducible factor is a unit. Hensel therefore gives an embedding of the abstract \(H\)-field into \(\mathbb Q_p\). There is no assumption that a coefficient field or the original graph roots split in \(\mathbb Q\) or in \(\mathbb R\). The specialized operative polynomial \(E\) keeps its entire degree in \(u\); hence a putative \(u\) is algebraic and integral at this place under any extension of the embedding. All roots of the reduced simultaneous \(u\)-gcd lie in the residue field and are exactly the ones listed. At each such \(u_0\), the derivative of \(E\) and the derivative of reduced \(G\) are units, and \(G(u_0)=0\bmod p\). The exact \(G\) coefficients are checked integral at the place. Thus the unique Hensel lift of that residue root of \(G\) is also a root of \(E\), and **is the putative \(u\)** by simplicity of \(E\). This proves \(\mathcal R(H,u,H/j)=0\) exactly.

At each reduced \(u_0\) at least one of \(\mathcal R,\mathcal F,\mathcal T\) keeps its full positive degree in \(v\), so \(v\) is likewise algebraic and integral. All roots of their simultaneous reduced \(v\)-gcd are enumerated, with no nonsplit factor skipped; the gcd is linear and its unique root is \(H/j\bmod p\). The derivative of \(\mathcal R\) is a unit there. Since \(H/j\) is already an exact root of the same \(\mathcal R(H,u,v)\), simple-root uniqueness forces \(v=H/j\) exactly. This is an exact clock collision between the first singleton and a rear singleton even if the coefficients are entirely non-real. All four factors are thus excluded without using a fourth-row gate or silently discarding any residue component. No conclusion in characteristic \(p\) is inferred.

## Replay and scope

Run `SYMPY_GROUND_TYPES=flint python check_terminal_new.py` (SymPy 1.14 and python-flint 0.8). It regenerates the integer projections, irreducible factor lists, exact small meshes, and fixed Hensel collision witnesses. There is no prime search or precomputed cache dependency. The [Lean companion](../../lean/RKCert/Research/SDIRKEightDirtySevenQuadraticSddDssArithmeticNew.lean) checks the denominator-free cubic ratio and both paid D scalar gates. The rooted-order ingress, exact projections and collision transfer remain a mathematical proof with independent exact replay, not an end-to-end native theorem.
