# Constant reverse numerator with one active literal front

At strict SDIRK8 with ten stages over a characteristic-zero field, take the [eight-active reverse-silent chart](../sdirk-eight-silent-one-eight-reverse-vanish/README.md). Only the first stage has nonzero quadratic defect and it is individually weight-zero. Exactly eight individually active physical stages have distinct clocks. The other weight-zero row has actual reverse read zero. This packet excludes **constant reverse nodal numerator \(T\)** and exactly one active literal front stage (one of physical 2, 3). In conjunction with the earlier two-front constant packet this closes the constant-\(T\) branch with eight distinct active clocks and actual reverse silence. Nonconstant \(T\) with one active literal front, nonzero silent reverse read, repeated active clocks, and nine active rows are separate. No unconditional improvement of **10–11** is claimed.

The inactive literal front keeps its actual known cubic defect and its true early taps. It is not assigned an ordinary profile, weighted virtual profile, or zero cubic defect. Physical four, five, and the three rear rows are all ordinarily active. On the eight active coordinates \(L_4(c_i)=Q h_i\) with constant \(Q\ne0\) in the chosen normalization. Actual pure-four reads lie in the span of \(h,Ch\) there, with actual affine coefficients.

## Literal fourth and fifth project the diagonal

Normalize clocks by \(\gamma\) and cubic defects by \(\gamma^3\). Let \(A_0,B_0\) denote the two literal front clocks, \(a\) their active one, \(H_a\ne0\) its actual defect. With actual fourth normalized clock \(s\), the exact three-tap formula supplies \(H_4(s)\), \(A\boldsymbol h\), and \(\tau_4=A\boldsymbol c^{\odot3}-\boldsymbol c^{\odot4}/4\) at that row. The literal fourth clock differs from \(A_0,B_0\), since padding the actual unique earlier tap solution at either clock would give a physical twin. Also \(H_4(s)\ne0\): a zero would give a zero actual \(A\boldsymbol h\) by the active pure-four profile; the exact gcd of these two literal polynomials is one.

The constant profile is
\[
 H(Y)= \frac{H_a L_4(\gamma Y)}{L_4(\gamma a)}.
\]
The denominator is nonzero by the actual active anchor; the physical fourth must satisfy \(H_4(s)L_4(\gamma a)-H_a L_4(\gamma s)=0\). Divide the exact padded \(s-a\) factor to obtain a cubic \(\Phi(\gamma,s)\), whose leading coefficient in \(s\) is a nonzero factor of \(\gamma^4 H_a\). Thus no genuine fourth leading branch is omitted.

Value ratios of \(\tau_4\) and \(A\boldsymbol h\) at the active literal and active fourth determine their affine \(h\)-multipliers. Use the [literal fifth formulas](../sdirk-eight-silent-one-seven-distinct-one-front-zero/README.md), with actual preceding clocks \(A_0,B_0,s\) and the actual first-stage feed. There are two separate necessary equations for actual normalized fifth \(y\), not just their difference. Clear \(H_4(s)(s-a)\) as needed and use the true actual active \(h_5=H(y)\), clearing \(L_4(\gamma a)\). The padded \(y-a\) root divides exactly. After that removal, the remainders on division by \(y-s\) are exactly multiples of \(\Phi\), checked at the polynomial level. Thus on \(\Phi=0\) divide by the actual nonzero \(y-s\). The two residual fifth equations both have degree at most three in \(y\).

Taking their resultant in \(y\) and discarding only exact \(s=A_0,B_0\) factors produces a necessary \((\gamma,s)\) polynomial, bidegree \((24,27)\). Its resultant with \(\Phi\) has exact degree 180, and removing factors supported at the forbidden strict \(\gamma=0\) or \(L_4(\gamma a)=0\) leaves degree 100 in each of the four literal front choices. To maintain the actual \(s\) guards, first identify the exact diagonals where a fourth root could have \(H_4=0\) or coincide with a literal front. Their common diagonal projection has degree 12. In each such **exact** coefficient quotient remove only the forbidden roots of the fourth polynomial, with the established [exact root removal](../sdirk-eight-silent-one-seven-distinct-one-front-zero/silent_guard.py), not every \(s\)-root at that same diagonal. All remaining fourth roots also satisfy the actual fifth resultant.

## Six active pegs, signed moments, and no Gaussian-value divisions

Use the actual rear \(x,c,d\) as in the [constant-numerator packet](../sdirk-eight-silent-one-eight-reverse-vanish/README.md). The active cubic profile is proportional to \(L_4\), and the same cleared rear relation for constant profile gives the necessary gap polynomial. Removing the exact physical collision factors \(u(u-1)(u-2)\) in rear star and \(u^2\) in rear arithmetic leaves degrees two and five respectively, with leading coefficients nonzero multiples of \(\gamma^4\). No division by a tail defect is made. The terminal/penultimate ratios give the actual affine \(P_1\) shape \(\rho(X)=(X-c)kL_4(x)+(x-X)L_4(c)\), also valid if one tail defect vanishes.

The six active pegs \(\gamma a,\gamma s,\gamma y,x,c,d\) are distinct. Since \(h\) is proportional to \(L_4\) on all active axes, the two paid sums of \(h^2\) and \(c h^2\) determine the actual signed scalar moments of degrees eight and nine from those of degrees below eight. These are **not** set equal to the integrals of \(X^8,X^9\). Let \(D_6\) be the monic polynomial of the six known pegs and \(m_j=\sum_i b_iD_6(c_i)c_i^j\), \(0\le j\le3\). The actual remaining two nodes have signed nonzero masked weights. Their moment equations give the scaled nodal quadratic with coefficient vector
\[
 (m_1m_3-m_2^2,\ m_1m_2-m_0m_3,\ m_0m_2-m_1^2).
\]
The scale \(m_0m_2-m_1^2\) is nonzero at an actual solution by distinctness and nonzero signed masked weights. No inverse of it is required in the replay. This construction remains valid if one of the known or unknown active pegs is Gauss.

By the [eight-active Bézout identity](../sdirk-eight-silent-one-eight-reverse-vanish/README.md), the residue of \(D_6\) times this scaled quadratic in the monic \(L_4\) quotient must be proportional to the residue of \(\rho W_{L_4}^{-1}\). Thus all two-by-two coefficient minors vanish. Testing their span gives a unit in every finite component. No Gauss weights are assigned and no Legendre value at an active peg is divided.

## Replay

Install sympy==1.14.0 and python-flint==0.9.0, then run **python3 check_eight_constant_one_front.py** in this directory. The whole exact diagonal projection and all fourth-root guard refinements precede reduction at \((1097,345)\). Each tested finite fourth fiber retains monicity; at least one cleared fifth equation, or their fixed linear combination, has its true degree-three leading coefficient a unit before taking the common-root fibers. All monic fifth and full tail gaps are retained. The counts of genuine candidate reduced fifth components tested in the four literal choices are \(5,9,7,3\) for each rear phase. These local finite-algebra unit checks do not assume an unknown tableau can be reduced. The saturation, primitive projections and finite atlas are source-level.

The [Lean scalar companion](../../lean/RKCert/ReviewedNative/SDIRK8EightActiveSixPegMoments.lean) is checked on Lean/Mathlib 4.36.0; the [axiom audit](lean-audit-4.36.0.txt) reports standard axioms only. The scope remains the displayed scalar algebra rather than the full chart.
