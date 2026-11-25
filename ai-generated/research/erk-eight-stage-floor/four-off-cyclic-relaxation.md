# The order-eight four-off cyclic module and a feasible physical relaxation

**Result.** The four early off senders impose a three-link Newton-basis chain. The physical clean receivers fix the quadratic-defect polynomial up to scale by their chronology, and force the clean grade-five component to be nonzero. These conditions, the actual clean primitive tests, and the literal first three reverse rows are jointly feasible on a strict physical Fin 10 tableau. The explicit relaxed tableau fails the native early off cubic primitive profile. A short rooted-tree induction proves that, in this saturation model, restoring the two early off monomial profiles would suffice for all order-eight RKOC. This is not a proof of the four-off contradiction or an order-eight method.

Use the notation and exact public-only localization from the accompanying four-off physical note: the unique repeated tag reappears at row 8; rows 6, 7, and 9 are clean; the first nonzero clean clock \(h\) is physical row 4 or 5; \(x=c_6,z=c_7\); the five clean clocks are \(0,h,x,z,1\). Let \(Q=X L_3=X(X-h)(X-x)(X-z)\), \(H_C=(X-1)Q\), \(\phi=I Q\), with \(I\) the zero-constant formal primitive. Let \(P\) be the degree-\(\le2\) polynomial satisfying \(g=P(c)\ne0\) at the off tags and \(g=0\) on clean. Actual levels \(F_3,F_4\) in the proof are \(g\,\mathbb P_1(c),g\,\mathbb P_2(c)\). No two stages are merged.

## 1. Actual Newton module and clean chronology

Order the off clocks by first occurrence \(o_1,\ldots,o_4\). On \(\mathcal O=K[X]/\prod_{i=1}^4(X-o_i)\) use the basis \(N_j=\prod_{i\le j}(X-o_i)\), \(0\le j\le3\). Restricted to the four early off rows, the normalized off-only action is
\[
 (\mathcal T f)(o_i)=\frac{(A(gf(c)))_{\mathrm{first}(o_i)}}{P(o_i)} .
\]
Clean senders give zero to its input. By causality, \(\mathcal T N_j\) vanishes at the first \(j+1\) off clocks. The paid bands cap the degrees of \(\mathcal T1,\mathcal T X\) at one and two, respectively. It follows exactly that
\[
     \mathcal T N_0=\beta N_1,\quad
     \mathcal T N_1=\gamma N_2,\quad
     \mathcal T N_2=\delta_* N_3,\quad \mathcal T N_3=0 .
\]
Here \(\beta\ne0\) by the native independence of \(Ag,g\); the other two coefficients are not asserted nonzero. At clean receivers the first two Newton inputs vanish under \(A\), so their entire off-only action depends on two scalar taps. If the first clean occurs at row 4, its fourth-off \(N_3\) tap is zero by actual causality.

A further true early equation uses the first three off clocks \(o_1,o_2,o_3\). Write \(N_3=X^3-s_1X^2+s_2X-s_3\) and \(P=p_0+p_1X+p_2X^2\), with \(p_0\ne0\) from the first-clean primitive test. Set
\[
    \ell=s_1-s_3p_2/p_0,\quad m=-s_2-s_3p_1/p_0,\quad n=s_3/p_0.
\]
The actual grade-three column \(c^3-\ell c^2-mc-ng\) is zero on the origin and first three off senders. Its \(A\)-image on off rows has polynomial profile \(X^4/4-\ell X^3/3-m X^2/2+P K_2\), \(\deg K_2\le2\). If the first clean is row 5, this profile vanishes at all four off clocks. In particular, as the terminal-coordinate relation is \(Q+P R=S_o\prod(X-o_i)\), one gets the necessary scalar divisibility
\[
 P\mid X^4/4-\ell X^3/3-m X^2/2-uQ
\]
for some scalar \(u\). If the first clean is row 4, the fourth-off evaluation differs by its one earlier clean tap times \(h^3-\ell h^2-mh\). Neither early equation invokes an order-nine payment.

The literal clean-to-clean tap sum, denoted \(A_{CC}\) on clean inputs, satisfies
\[
 A_{CC}P=I P,\qquad A_{CC}(XP)=I(XP)
\]
on clean receivers. Indeed on off tags the corresponding input is \(g\) or \(cg\); both their \(A\)-images vanish at clean receivers. Put \(V=A(c^2g)\) and \(M_4=A c^4-c^5/5\). Their clean restrictions are multiples of \(\phi\) by the paid three-probe \(F_5\) line. Define \(S=X(X-h)P\). On every clean receiver, \(A_{CC}S=I S+p_2 M_4-V\), since the only off contribution is \(A(c^2g-hcg)=V\). For a scalar \(\Theta\) this gives \(A_{CC}S=I S-\Theta\phi\). At \(h,x\) the preceding clean contributions are zero. At 0 and \(h\), its derivative \(S-\Theta Q\) vanishes as well. Therefore
\[
 I S-\Theta\phi=\kappa X^2(X-h)^2(X-x),\qquad
 P=\Theta(X-x)(X-z)+\kappa(5X^2-(4x+3h)X+2hx).
\]
Here \(\kappa\ne0\): if it were zero, then the first-clean test \(I(XP)(h)=0\) would contradict the public Lobatto first-factor gate, unless \(P=0\). That same test fixes \(\Theta:\kappa\) entirely from the chronological clean knots. These three clean equations determine the actual prior clean taps of receivers \(h,x,z\): the sender basis \((P,XP,S)\) has triangular evaluations at \(0,h,x\). Its pivots are nonzero: \(P(0)\ne0\); if \(P(h)=0\), then \(I(XP)\) would have roots \(0,h\) both double and the additional root \(x\), impossible at degree four; and \(P(x)=\kappa x(x-h)\ne0\).

If \(V=\lambda\phi\) on clean, the terminal column identity gives \(M_4=-\phi-R_2V\). Also \(p_2=\Theta+5\kappa\). Hence
\[
             (1+p_2R_2)\lambda=-5\kappa .
\]
Thus the actual clean chronology itself forces nonzero terminal leakage; it cannot furnish terminal vanishing without an additional contradiction. In the repeated-row difference projected onto clean tags, the entries annihilate \(P,XP,X^2P\) by subtracting the corresponding off roots from the pure tests. The terminal entry is zero. If \(P(z)=0\), the three weighted Vandermonde rows force the clean part to be supported solely at \(z\), because \(P(0),P(h),P(x)\ne0\). The pure tests through degree four on the at most five clocks in the union of the off clocks and this singleton would then kill all aggregate effects, contradicting the four nonzero tagged off residues. Therefore \(P(z)\ne0\) as well. The two four-point residue laws are
\[
  \bar\delta_C(a)=C_*/(P(a)Q'(a)),\qquad
  \bar\delta_O(o)=D_*/(P(o)D_O'(o)),
\]
where \(a=0,h,x,z\), \(D_O\) is the monic off hull and \(\bar\delta\) is the aggregate of \(A^\mathsf{T}(e_8-e_i)\). Both constants are nonzero, by the degree-four pure tests and the off-residue nonzero result.

## 2. Explicit feasible relaxation on physical Fin 10 rows

Work in the ordered field generated by \(\sqrt{3/7}\). Choose \(h=1/2\), \(x=(1-\sqrt{3/7})/2\), \(z=1-x\). Thus \(xz=1/7\). Put four off clocks at physical rows 1–4, in order \(x,0,h,z\), with clean rows \(0,5,6,7,9\) at \(0,h,x,z,1\); duplicate the **off** tag of row 1 at row 8. The coincident clocks on different tags are intentional. The off hull is precisely \(Q\). Let \(W\) be the five exact Lobatto weights, \(W(0)=W(1)=1/20\), \(W(x)=W(z)=49/180\), \(W(h)=16/45\). Set \(b_8=1,b_1=-1\), other off weights zero, and clean weights \(W\).

For \(\kappa=1\), the exact shape above has \(\Theta=7(3-8x)/11\), obtained by the first-clean condition. Its values at \(0,h,x,z\), respectively, are
\[
 (3+3x)/11,\qquad (13-20x)/44,\qquad x(x-h),\qquad 31/14-5x/2,
\]
all nonzero. Scale this polynomial and \(\Theta,\kappa\) by \(x/(2(h-x))\) so that \(P(x)=-x^2/2\). At every off physical tag prescribe \(g=P(c)\), and at clean tags prescribe \(g=0\).

**Early rows.** In the Newton basis on \(O\), let \(f_0,f_1,f_2,f_3\) be the coefficients of \(X/P\bmod Q\) and \(t_0,t_1,t_2,t_3\) those of \(1+X^2/(2P)\bmod Q\). Then \(t_0=0\) and \(f_0,f_1,f_2\ne0\): \(f_0=-2/x\), \(f_1=-2/x^2\) by the first two off clocks \(x,0\), and at the third clock \(h\) the linear interpolation of the earlier values is negative while \(h/P(h)>0\). Define \(\mathcal T\) by the Newton shift with coefficients \(t_1/f_0,t_2/f_1,t_3/f_2\). This is a strictly lower operator in those four evaluations. Use the physical early off submatrix given by
\[
       A_{OO}=\mathrm{diag}(P(o))\,\mathcal T\,\mathrm{diag}(1/P(o)).
\]
For each early off receiver fill its origin tap to make \(A1=c\). This does not alter \(A c\) or any off action. The defining equality \(\mathcal T(X/P)=1+X^2/(2P)\) now ensures **literal** \(g=A c-c^2/2\) at all early off rows. \(Ag\) and \(A(cg)\) have the desired affine and quadratic off profiles.

**Early clean rows.** At \(a=0,h,x,z\) define the clean-to-clean taps from the three triangular equations \(A_{CC}(P,XP,S)=(IP,I(XP),F)\), \(F=\kappa X^2(X-h)^2(X-x)\), using exactly the earlier clean indices. All four off senders are earlier than \(h,x,z\). Choose their taps at each such receiver by unique four-node interpolation so that for every polynomial \(G\) of degree \(\le3\) their off contribution is \((I G)(a)-(A_{CC}G)(a)\); at row 0 it is zero. This gives actual clean \(A c=c^2/2\), \(Ag=A(cg)=0\), and all four pure primitive rows. Since \(X^2P-p_2Q\) represents the off input \(c^2g\) at those knots and \(A_{CC}Q=0\), it gives \(V(a)=(\Theta-p_2)\phi(a)=-5\kappa\phi(a)\).

**Duplicate and terminal.** Put \(\eta=1-x\), \(v_z=1-z\). On the clean nonterminal tags set the row difference \(\bar\delta_C(a)=C_*/(P(a)Q'(a))\) normalized by \(\bar\delta_C(z)=W(z)v_z^2/(2b_8\eta)\), and set \(\bar\delta_O(o)=-\bar\delta_C(o)\) and \(\bar\delta_C(1)=0\). Before physical row 8 these are literal independent tag columns. Define row 8 to be row 1 plus this difference. It equals row 1 on the model space \(\mathcal E_4=\mathbb P_4(c)+g\,\mathbb P_2(c)\): cancellation is termwise on pure clocks, and the weighted off residues kill the three defect directions. Consequently literal \(c,g,Ag,A(cg)\) have the declared values there.

Use capital \(B\) for the tag weight vector, \(B_C=W,B_O=0\). Choose the terminal tagged row uniquely by
\[
 W(1)\mathcal A_9 = B y - \sum_{a=0,h,x,z} W(a)\mathcal A_a-b_8\bar\delta ,
\]
where \(\mathcal A_a\) are the just-defined clean rows summed into sender tags. This is strict in the physical column indices. Split its off \(x\) tap by assigning \(A_{9,8}=b_8\eta/W(1)\) and subtracting this from the aggregate when assigning \(A_{9,1}\). This gives literal \(J_0=0\), including the two individual coordinates of the duplicate. Pairing the displayed terminal equation with pure degree-\(\le3\) tests gives the terminal primitive rows by exact polynomial quadrature and \(I\)-integration by parts; pairing with \(g,cg,c^2g\) gives \(0,0,-5\kappa\phi(1)\). In the last application use \(\sum_C W(a)\phi(a)=0\), from the Lobatto orthogonality of \((1-X)Q\). The terminal row therefore has actual clean \(g=0\) and all the low clean tests.

**Literal second and third reverse rows.** Both can be verified with no data from the early monomial defects. On clean sender columns the aggregate sums over the three nonterminal nonzero clean receivers satisfy
\[
 \sum_{a\in C}W(a)y_a^k A_{CC}(a,u)
       = W(u)y_u^{k+1}/(k+1)+\lambda_k\bar\delta_C(u),
 \quad k=1,2,
\]
with \(\lambda_1=-b_8\eta,\ \lambda_2=-2b_8\eta v_z/3\). At \(u=z,1\) this is the definition and strictness. At \(u=x\), the only nonzero later canonical receiver in these probes is \(z\); the clean equation for \(S\) gives \(A_{z,x}=(z-x)r\), \(r=W(x)(1-x)^2/[W(z)(1-z)^2]=z^2/x^2\). The residue ratio is \(\bar\delta_C(x)/\bar\delta_C(z)=-F'(z)/F'(x)=r(1-2(z-x)/v_z)\); the last equality follows from \(H_C''(z)=20L_3(z)=0\), or \(\sum_{a\ne z}(z-a)^{-1}=0\). These identities give both columns at \(x\). The differences now supported only on \(0,h\) kill \(P,XP\), by the exact clean \(I P,I(XP)\) actions and the polynomial identity \(\int_0^1 y^k I G=\int_0^1 y^{k+1}G/(k+1)\). Their degrees are within seven. As \(P(0),hP(h)\ne0\), the two remaining columns follow.

For every test on the four off sender columns take its degree-\(\le3\) pure interpolant \(G\). The defining off tap residual \(I G-A_{CC}G\), paired with the same quadrature identity, gives \(-\lambda_k\bar\delta_C(G)=\lambda_k\bar\delta_O(G)\). Thus all tagged-column equations follow. Adding the duplicate's weighted difference \(b_8\eta^k\bar\delta\) gives the aggregate \(J_1=0\) and \(J_2=\xi\bar\delta\), \(\xi=b_8\eta(3\eta-2v_z)\). On the actual row-8 coordinate the literal values are \(-b_8\eta^2,-b_8\eta^3\), since only terminal follows and its reflected clock is zero. Hence the physical rows satisfy exactly
\[
 J_1=-b_8\eta^2(e_8-e_1),\qquad
 J_2=\eta J_1+\xi A^\mathsf T(e_8-e_1).
\]
In particular they annihilate the model state space \(W\) and \(\mathcal E_4\), respectively. This uses every late receiver and all four off sender columns, but no asserted equality of these model spaces to the actual tree spans.

## 3. Exact failed early profile, and why the missing constraints matter

The tableau deliberately does **not** satisfy native order eight. At early off clocks \(x,0\) the normalized second primitive residual \((A c^2-c^3/3)/g\) takes values \(2x/3,x\), so if it were affine it would have to be \(x-X/3\). At the third early off clock \(h\), all earlier clocks are \(0\) or \(x\), so \(A c^2=x A c\) at that row. Matching the affine profile there would require \(P(h)=(1-3x)/4\). The explicit normalized value is \(x(13-20x)/(44(1-2x))\); equality, using \(x^2-x+1/7=0\), would give \(x=1/14\), not a root of that quadratic. Thus the native early \(mDef_2\) band already fails. The clean/late and Newton restrictions cannot by themselves prove the desired contradiction.

There is a useful sufficiency converse explaining the remaining RKOC. For any literal tableau with the above type of tagged support, signed quadrature exact through degree seven, off masses zero, actual \(c=A1,g=A c-c^2/2\) and \(g=P(c)\) on off, suppose the following hold:

1. \(Ag,mDef_2\in g\,\mathbb P_1(c)\), and \(A(cg),mDef_3\in g\,\mathbb P_2(c)\).
2. For \(\mathcal E_4=\mathbb P_4(c)+g\,\mathbb P_2(c)\), \(A\mathcal E_4\subset W\).
3. \(J_0=0,\ J_1\in W^\perp,\ J_2\in\mathcal E_4^\perp\) as literal physical rows.

Then HasOrder 8 follows. To see this, use the native normalized unary and root-join identities: a grade-\(d\) column is \(c^d+f\); unary integration sends its defect to \((d+1)(mDef_d+Af)\); multiplication gives the two clock-shifted defects plus their product. In grades at most four the defect recursion closes in the off bands \(g\,\mathbb P_{d-2}\), using \(g^2=P(c)g\), so all their reflected probes vanish by off cancellation. Grade five is state-valued by condition 2. Its unary defect from an old off band is killed for reflected exponents \(k=0,1,2\) by \(J_0,J_1,J_2\); the pure \(mDef_4\) is paid by the same rows and exact scalar beta integration. In grade six, unary transported grade-five defects are paid for \(k=0,1\) by \(J_0,J_1\), with \(mDef_5\) paid on pure \(c^5\in W\). In grade seven the single needed unary probe follows from \(J_0\). Multiplication by clock powers lowers the available probe degree as required; any product of two genuine defects through grade seven has both factors of grade at most five, and at least one of grade at most four. It is therefore state-valued and supported only on the canceled off tags. All remaining probes vanish. This uses the same reviewed \(\Phi\) and forest normalization, not simplified-order conditions substituted as an alternative predicate.

The explicit relaxation meets all of this except the two **early off** pure primitive profiles in item 1, of which the first fails as above. Thus a proof of the four-off endpoint can concentrate on those early physical constraints along with the Newton, clock and terminal-profile equations; the late clean/cyclic quotient alone is feasible. No held p8 evidence, searches, network, Lean, or checkout edits were used.
