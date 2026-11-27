# Closing the dependent detected six-clock Gauss-double census

At the ten-stage strict SDIRK8 floor over a characteristic-zero field, suppose the only nonzero quadratic residual is at the weight-zero physical first stage. There are seven active stages at six distinct active clocks, and for the cubic defect \(\boldsymbol h=(A-\gamma I)\boldsymbol g\), the active \(\boldsymbol h\ne0\) and \(C\boldsymbol h\) are dependent. This packet excludes every such tableau. The [independent six-clock case](../sdirk-eight-silent-one-seven-six-last/README.md) is separate and also closed. Seven or more distinct active clocks and other quadratic-defect families remain outside the result, so the unconditional **10–11** stage interval is unchanged.

## The actual canceled double and global pure-four profiles

Dependence confines the nonzero active \(\boldsymbol h\) to one clock \(r\). The paid first defect moment forces at least two active \(h\)-coordinates there, so exactly the one doubled active clock is \(r\). Let its weights and defects be \(b_1,b_2,H_1,H_2\). Both weights and defects are nonzero. The paid sums \(b_1H_1+b_2H_2=0\) and \(b_1H_1^2+b_2H_2^2=0\) give \(H_1=H_2\ne0\), \(b_1+b_2=0\). The ordinary quadrature thus has **five distinct singleton sites**, each of nonzero possibly signed weight. The tag \(r\) is not assumed Gauss.

The nonsingular cubic scalar Gram leaves a three-dimensional nondegenerate complement on the seven active coordinates. Nonzero isotropic \(h\) cuts its pure-four part to dimension at most two by the paid grade-seven pairings. Both \(h\) and \(L_4(\boldsymbol c)\) are in this part and are independent, since five ordinary singleton clocks cannot all be roots of the quartic. Thus each active pure-four vector is in their span. On all nine quadratic-zero physical coordinates the pure-four space has dimension three: \(\boldsymbol h,C\boldsymbol h\) are independent there at the two distinct literal front clocks with nonzero actual \(h\), and the active independence gives the third generator \(L_4(\boldsymbol c)\). Therefore every actual pure-four read on those nine coordinates, **including both silent zeros**, is
\[
 v_i=(\alpha_v+\beta_v c_i)h_i+\rho_v L_4(c_i).
\]
At ordinary active clocks it is \(\rho_v L_4(c_i)\), and at the two actual \(r\)-copies the reads agree.

## Reverse support and silent transport

Let \(x=c_{10}=1-\gamma\), \(c=c_9=x-\gamma u\), \(k=1+2u-u^2\), \(N=A-\gamma I\), \(M=CA-AC-A^2\), and \(\boldsymbol w=\boldsymbol b^{\mathsf T}M\). The actual reverse identities from the [six-clock anchor](../sdirk-eight-silent-one-seven-six-anchored/README.md) give \(\boldsymbol h^{\mathsf T}B\) in the span of \(\boldsymbol w,\boldsymbol wN\), \(\boldsymbol w(C-xI)=-k\boldsymbol wN\), \(w_{10}=-\gamma^2b_{10}\ne0,\ w_9=-\gamma^2 b_9 k\), and \((\boldsymbol wN)_9=w_{10}A_{10,9}\ne0\). There is no contribution at the invisible first stage, by the paid pairing of \(\boldsymbol w\) with the single supported \(\boldsymbol g\).

For \(k\ne0\), \(\boldsymbol h^{\mathsf T}B=\boldsymbol wP_1(C)\) with \(P_1\) affine. Since \(w_9,w_{10}\ne0\), both terminal defects cannot vanish, and \(r\) is one of \(x,c\). The other clock \(R\) is the unique root of \(P_1\). At \(r\) the actual \(w\) is confined to its two active copies which have opposite weights and the same \(h\); their \(w\)-aggregate is zero and their pure-four contributions cancel. At every other clock except \(R\), \(w\) vanishes. If \(k=0\), \(w\) lives only at \(x\); in \(\boldsymbol h^{\mathsf T}B=\alpha\boldsymbol w+\beta\boldsymbol wN\) the actual terminal or penultimate entries force \(r=x\) or \(r=c\). If \(r=x\), \(\beta=0\) because the penultimate \(h\) is zero, and \(w\) is confined to the two active \(r\)-copies. If \(r=c\), set \(R=x\); again the only remaining support is at the ordinary clock \(R\).

In the cases with a balancing ordinary \(R\), the active \(w_R\ne0\) is balanced by at least one silent coordinate at that clock. The actual paid \(w\)-pairings show that the **weighted silent group** has virtual \(h=0\) and the ordinary pure-four line \(\rho_v L_4(R)\). This follows after removing the canceled \(r\)-contributions, and does not assign \(h=0\) to both physical silents if they share \(R\). If only one holds that balance, however, its actual defect is zero. The two literal front stages have different clocks and both have nonzero \(h\). They therefore cannot both be silent in this balancing case: only one would occur at \(R\), which cannot carry the requisite actual zero defect. Thus both fronts silent is possible only for the now isolated \(k=0,r=x\) chart before its exclusion below.

## Fixed literal front at the double: finite tail tests

At most one literal front is active, since both literal defects are nonzero at distinct clocks. If one is active, it is at \(r=\gamma A_0\) for one of the two normalized literal front values. This fixes \(\gamma=1/(1+A_0)\) when \(r=x\), or \(\gamma=1/(1+A_0+u)\) when \(r=c\).

* **Eighth active and \(k\ne0\).** Its clock differs from the other two active tail clocks and has zero \(h,w\). Thus its reflected quadratic ratio is zero; star, with ratio \(k\), is impossible. The actual cleared arithmetic ratio gives \(4u^3-12u^2+3u+2=0\). If physical row four is active, it is ordinary, since the two \(r\)-copies are already the literal front and a tail. If four is silent, it must participate in the balance at \(R\); it cannot repeat a literal front at \(R\) by the literal three-tap chronology, so it is the sole silent there and its actual \(h=0\). In either case the literal \(H_4\) cubic applies. Its value at \(R/\gamma\) is a unit, excluding the silent-four possibility. If four is active, the two ordinary tail pegs and this third ordinary clock leave two singleton nodes. Their signed \(3\times3\) Hankel determinant must vanish, but is a unit in all finite front/gap fibers.
* **Eighth active and \(k=0\).** The reflected two nonterminal tail clocks are fixed in the two phases and both signs of \(u=1\pm\sqrt2\). For \(r=c\) the previous ordinary reverse balancing argument again gives actual \(H_4=0\) including possibly silent four, which is excluded at its forced \(R=x\). For \(r=x\) and physical four active, \(H_4=0\) holds directly. The same three-peg signed Hankel test excludes these cases. [Replay](dependent_tail.py).
* **Eighth silent.** Its actual \(w_8\ne0\) excludes \(k=0,r=x\). Otherwise there is one active literal front at \(r\), and \(c_8=R\). For \(k\ne0,r=c\) the actual silent clock equation forces \(u=2\); for \(k=0,r=c\) the two fixed gaps apply; if \(r=x\) no gap is needed to fix the diagonal. The two active \(r\)-copies are already at the literal front and tail, and both physical rows four and five are active ordinary. Therefore their actual two-low-front-clock projection applies, regardless of the two silent amplitudes. The earlier [fixed-diagonal both-low replay](../sdirk-eight-silent-one-seven-small/triple_silent8.py) excludes the finite diagonals in every case. No weight normalization at the silent eighth or unproved equality of its defect was used.

## The remaining \(k=0,r=x\) charts

All these cases have an active eighth and the fixed two ordinary tail clocks \(c_9,c_8\), in the two literal reflected phases and both signs. Neither of them is \(r\).

### Both literal fronts silent, ordinary row four

Here physical rows four and five are active. If four is ordinary, its normalized clock \(s\) satisfies \(H_4(s)=0\); the cubic is checked in its exact finite fields. The three known ordinary pegs \(\gamma s,c_9,c_8\) leave two unpegged singleton sites. The signed \(3\times3\) Hankel determinant of their masked moments gives an exact monic degree-nine diagonal projection over the cubic field. Its signed two-by-two pivot is nonzero and reconstructs the two missing singleton nodes. Denominators are checked and any stripped diagonal/pivot zeros are certified impossible by the physical signed Vandermonde factorization.

The actual ordinary \(Ah\) at row four is nonzero (\(H_4=0\) literal chronology), so \(L_4(\gamma s)\ne0\) and the literal read fixes \(\rho_{Ah}\), as does \(\tau_4\) for its own coefficient. If row five is ordinary, its actual no-stage-one-feed three strict moments at the literal clock set give two polynomial comparisons with the \(L_4\) line; they fail at both reconstructed possible nodes. If row five is the physical \(r\)-copy, its two pure-four expressions are affine in its actual unknown \(h_5\). The two literal front ratio reads and the established \(\rho_v\) fix the required affine multipliers. The resulting two affine equations in actual \(h_5\) have unit inconsistency determinant. [Replay](terminal_both_fourth_ordinary.py).

### Fourth stage is the earlier \(r\)-copy, or is physically silent

These are the two remaining physical possibilities: both literal fronts silent with four at \(r\), or one active literal front at \(r\) and physical four silent. In the first write \(\gamma=1/(1+s)\) for its normalized clock \(s\); in the second \(\gamma\) is fixed by the earlier literal \(r\). In both cases row five is active ordinary at a normalized clock \(y\), and row four uses its **actual** \(H_4(s)\) without setting it zero.

For a pure-four read \(v\), let \(\ell_v\) be the affine interpolation of the two literal \(v/h\) ratios, and \(\ell_L\) the affine interpolation of \(L_4(\gamma\,\cdot)/h\) at those literal front coordinates. On row four the global profile gives
\[
 \widehat v(s)=v_4(s)-H_4(s)\ell_v(s)
   =\rho_v\left(L_4(\gamma s)-H_4(s)\ell_L(s)\right)=\rho_v\widehat L(s).
\]
Row five has its actual clean \(v_5^0(s,y)=\rho_v L_4(\gamma y)\). Both hats have the exact padded factors for the two literal clocks, removed because physical four cannot repeat either one. Thus the two necessary cross-polynomials are obtained from
\[
 L_4(\gamma y)\widehat v(s)-v_5^0(s,y)\widehat L(s)=0
\]
with \(v=Ah,\tau_4\) after the padded quotient; for variable diagonal first clear the common \((1+s)^4\) in the Legendre factors. These two literal row-five reads use the three actual strict moments with no stage-one feed, not values assumed for the silent fourth row.

The resultant has a finite regular part of degree 25 (four is \(r\)) or 12 (four is silent). The necessary leading coefficients of the actual fifth polynomials are preserved in those quotients. For fifth \(y\), the two ordinary tail pegs plus \(\gamma y\) give a three-peg signed Hankel, and the other pure-four equation together with it generates a unit in every reduced field. The exact exceptional \(\widehat L=0\) part has degree six or two and is retained separately: the two quotient \(\widehat v\)'s are coprime, so \(L_4(\gamma y)=0\), and the two **actual** pure reads at the ordinary fifth must then both be zero. The replay checks that these never vanish together in the fixed Gauss-clock quotient. This does not treat zero \(\widehat L\) as invertible or omit that component. [Replay](terminal_fourth_special.py).

## Verification

Run `python3 check_dependent_six.py` with `sympy==1.14.0` and `python-flint==0.9.0` in the repository sibling proof tree. The replay checks 40 active-eighth anchored tails, 16 silent-eighth already-known front cuts, eight both-front-silent ordinary-fourth placements, and 24 special-fourth placements. Exact projections precede the unit checks at \((1103,161)\) (or \((1009,285)\) for one ordinary-fourth orientation), with \(2t^2=1\) in the residue field. Every relevant finite factor is retained, with leading degrees and divisions checked. No physical tableau reduction is assumed. The [Lean source](../../lean/RKCert/ReviewedNative/SDIRK8GaussDoubleDependent.lean) verifies weighted virtual balance, signed moment rank and pivot, pure-read cross multiplication, and the terminal support choice on Lean/Mathlib 4.36.0 with standard axioms. The chart and finite arithmetic are source-level.
