# A singleton-end S,D,D opener cannot face a D,S,S star

Suppose a strict ten-stage SDIRK method has ordinary order at least eight over a characteristic-zero field, all physical quadratic defects nonzero, exactly seven distinct clocks, and exactly one singleton endpoint. Orient from the singleton by the actual weighted mirror if necessary. If that end opens **S,D,D**, then the opposite end must open **D,S,S with a genuine arithmetic third row**. The [D,D,D](../sdirk-eight-all-dirty-seven-quadratic-sdd-ddd/README.md) and [one-extra-D](../sdirk-eight-all-dirty-seven-quadratic-sdd-one-extra-single-overlap/README.md) results force D,S,S. This packet excludes its star. It neither excludes the remaining arithmetic phase nor alters the general 10–11 stage interval.

## Actual paired readings and graph axis

Normalize the diagonal to one with \(y=x-1\), let \(H=2(m-1)\), \(m=1/(2\gamma)\), and \(t=y-H/2\). The first row has singleton label \(0\), the terminal D label is \(H\), and the true reverse offset is \(y'=H-y\). The [seven-clock decomposition](../sdirk-eight-all-dirty-seven-clock/README.md) gives \(\mathcal Q=L_3-F_*L_4\), with affine \(F_*\) of nonzero slope, and \(\mathcal Q\) proportional to \(P R\), where \(P\) is cubic on the D labels and \(R\) is the genuinely quadratic singleton graph. Here \(L_j\) are the monic Legendre polynomials evaluated at \(t=y-H/2\). Nonzero \(L_4\) at any D uses consecutive Legendre coprimality, not an assumption about the graph there.

For the *actual* reverse star gap \(v\), its two later offsets are \(v,2-v\), and both normalized defects equal \(\rho=(1+2v-v^2)/2\). In original \(y\)-coordinates the two S labels are \(c\pm(v-1)\), \(c=H-1\). Distinctness and equality of their scaled graph values force the axis \(c\): for a genuinely quadratic polynomial, the difference at two different arguments factors as their difference times the linear coefficient plus the leading coefficient times their sum. Write
\[
 R=rW,\qquad W=(y-c)^2-\Sigma,\qquad r=\frac{1}{2W(0)} .
\]
The nonzero denominator follows from \(R(0)=1/2\). Neither \(\Sigma=0\) nor a common root of \(W,P\) is excluded. We do require \(H\ne2\): otherwise \(c=H/2\), so \(W\) has either an antipodal pair or the centered double root in centered coordinates over the algebraic closure. Both contradict the [single-endpoint parity lemma](../sdirk-eight-all-dirty-seven-quadratic-one-singleton-arithmetic/PARITY.md), without needing splitting over the original field.

Use \(X=(v-1)^2,\ \Delta=X-\Sigma\). The paid reverse scale and terminal original defect are
\[
 \lambda= \frac{2r\Delta}{2-X},\qquad  g_T=\frac{r\Delta}{2-X}.
\]
The star guards are \(X,X-1,X-2,\Delta\ne0\), and \(X-(a-c)^2\ne0\) whenever the label \(a\) is one of the first singleton, the D labels or the fourth singleton. These enforce the actual distinct labels and nonzero defects. Taking \(v-1\) or its negative is **not** a claim that exchanging the physical second and third rows preserves order. Every proposed method already has one of the literal offsets \(v,2-v\) as its actual second offset; applying the true star formula separately to either direction gives the same two consumed clock-defect pairs and the same necessary \(X\)-equations. Hence refuting the equations covers both actual physical orders. The same observation applies to a forward star viewed through its two actual consumed D pairs.

## Exact mesh recovery: terminal used versus terminal new

The first two later forward D labels are \(a=u,b=2u\) for actual arithmetic, or \(a=u,b=2-u\) for a star. Their forward residuals are \(\kappa(u)/2,q_{\rm ar}(u)/2\) or \(\kappa(u)/2,\kappa(u)/2\), respectively, with the [literal arithmetic and star guards](../clock-localized-tail/tied-stage-floor/FIRST-THREE-ROWS-AND-PHYSICAL-LEVEL-OBSTRUCTIONS.md). In particular the singleton first-departure lemma forbids \(u=2\). All partitions below keep the actual phase and physical distinctness.

**Terminal reused.** The two front D labels in pair-data order are \(H,d\). For front arithmetic \(d=2H\); the other order would force a centered D at \(H/2\), forbidden. For a forward star \(d=2-H\) and the physical orders have identical known pair data. Fit \(F_*\) through \(L_3/L_4\) at \(H,d\), and divide exactly
\[
 M_3(y)=\mathcal Q(y)/[(y-H)(y-d)] .
\]
The third D label \(e\) satisfies \(M_3(e)=0\). Its value is already forced by the actual axis:
\[
 e=-[y^2]M_3/[y^3]M_3-2c,
\]
by expanding \((y-e)W(y)\). The cubic leading coefficient is nonzero from the genuinely quadratic graph; no denominator involves \(W(d)\). Substitute in \(M_3(e)=0\), clear only proved nonzero denominators, and retain both exact fields: degree 15 for front arithmetic, degree 10 for front star. Reconstruct \(W\) by monic normalization of the exact quotient \(M_3/(y-e)\). A common root of \(M_3'\) and \(M_3\) was not excluded.

**Terminal new.** The three distinct labels are \(H,a,b\). Fit \(F_*\) through \(H,a\) and put \(M_3=\mathcal Q/[(y-H)(y-a)]\). Two necessities are \(M_3(b)=0\) and \([y^2]M_3+(b+2c)[y^3]M_3=0\). The integer resultant in \(u\), using only true clock, phase, and coefficient guards, has \(H\)-factor degree 24 and squared degree 2 for front arithmetic; only a degree-2 factor to power six for a front star. Exact specialization in the arithmetic quadratic field gives a unit \(u\)-gcd (no mesh); the degree-24 field gives one linear \(u\)-gcd. In the star field the actual projected \(u\)-gcd is an **irreducible quartic** over the degree-two \(H\)-field. The verifier keeps the full extension of degree eight, not just base-field roots or one real orientation. All abstract embeddings are covered because each calculation is over the exact irreducible quotient. Divide \(M_3/(y-b)\) and normalize its leading coefficient to obtain \(W\). The proof never assumes a nonzero specialized resultant leading coefficient or that the roots of \(W\) are distinct.

## Actual singleton quartic and low-degree paid D fits

The true singleton quartic is \(\mathcal H=L_4-R C\), \(C=A_2+B R\). It has singleton roots \(0,c+(v-1),c-(v-1),w\), where \(w\) is the fourth singleton label. Write \(W_0=W(0)\ne0\) and \(L_4\bmod W=l_0+l_1y\). Because the star pair factor \((y-c)^2-X\) reduces to \(-\Delta\), and \(y(y-w)\bmod W=(2c-w)y-W_0\), the nodal identity gives
\[
 l_0\ne0,\quad w=2c+W_0l_1/l_0,\quad
 \mathcal H= \frac{2r l_0}{\Delta}\,y(y-w)(W-\Delta).
\]
Thus the actual scaled quadratic \(C^\#=\Delta C\) is affine in \(X\):
\[
 I=y(y-w),\qquad
 C_0=(L_4+2r l_0 I)/R,\qquad
 C^\#=\Delta C_0-2l_0 I .
\]
This is exact polynomial division in the actual mesh; the remainder vanishes by the nodal equation. In particular the fourth singleton is determined without knowing the star gap or solving a real-root equation. If \(l_0\) vanished the constant nodal component would contradict the true nonzero \(\Delta,W_0\) and quartic leading coefficient, rather than losing a valid singular fit.

For an already observed front D label \(a\) with known defect \(f_a\), set \(J=\Delta B\). Its paid D equation is
\[
          \Delta L_4(a)- f_a C^\#(a)=J f_a(f_a-R(a)).
\]
The right coefficient of \(J\) is nonzero because an actual D defect is nonzero and off the singleton graph. If the terminal is new, solve this line for \(J\) using this true pivot, then impose the second front D line. If the terminal is reused, direct Vieta of its two observed D roots gives \(\beta=B\lambda=-2L_4(H)/f_H\), so \(J=\beta(2-X)/(2r)\), and impose both front D lines. The unused residual at a reused D is not freely chosen. At the actual terminal substitute \(g_T=r\Delta/(2-X)\) and cancel only the known \(\Delta\ne0\); the resulting necessary equation is quadratic in \(X\):
\[
 (2-X)^2L_4(H)-r(2-X)C^\#(H)
       -Jr\bigl[r\Delta-(2-X)R(H)\bigr]=0 .
\]
No unknown affine coefficient is inverted. The quadratic and the respective affine conditions have unit gcd in \(X\) in both reused-terminal exact fields, the terminal-new degree-24 field, and the terminal-new degree-eight tower. The raw gcds are already units before any additional \(X\)-guard stripping. These are direct pair equations, not a numerical fitting step or a claim about permuting stage order. No trace or fourth read is needed to exclude this star phase.

## Replay

Run `SYMPY_GROUND_TYPES=flint python check_reused_terminal.py` and `SYMPY_GROUND_TYPES=flint python check_new_terminal.py` (SymPy 1.14 and python-flint 0.8). The [Lean companion](../../lean/RKCert/Research/SDIRKEightDirtySevenQuadraticSddDssStar.lean) checks three denominator-free scalar identities. The rooted-order ingress and exact field eliminations are a mathematical proof with exact replay, not an end-to-end native Lean or finite-characteristic theorem.
