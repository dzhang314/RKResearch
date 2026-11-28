# Reverse-silent support and a constant numerator cut at eight active stages

At the ten-stage strict SDIRK8 floor over a characteristic-zero field, assume stage one is the **only** physical row with nonzero quadratic defect and has zero output weight. An active stage means \(b_i\ne0\) individually, not a nonzero per-clock aggregate. For exactly eight active physical stages with nonzero reverse factor, if the remaining silent stage's actual reverse read vanishes, that stage is among physical rows 2, 3, 4. With eight distinct active clocks and this vanishing read, there is then an affine reverse nodal numerator \(T\) whose multiplication by the cubic defect is a multiple of the quartic Legendre profile. This packet excludes the subchart in which \(T\) is constant and both literal front stages are active. The unrestricted interval stays **10–11**.

## Physical support without a distinct-active-clock assumption

Put \(C=\operatorname{diag}(\boldsymbol c)\), \(B=\operatorname{diag}(\boldsymbol b)\), \(N=A-\gamma I\), \(M=CA-AC-A^2\), \(\boldsymbol h=N\boldsymbol g\), \(\boldsymbol w=\boldsymbol b^{\mathsf T}M\). In the eight-active branch let \(\zeta\ne1\) be the unique other weight-zero stage. Write \(x=c_{10}=1-\gamma\), \(u=(x-c_9)/\gamma\ne0\), and \(k=1+2u-u^2\). The [actual reverse identities](../sdirk-eight-silent-one-six-detected/README.md) give \(Z_3=\langle\boldsymbol w,\boldsymbol wN\rangle\), \(w_1=0\), \(w_{10}=-\gamma^2b_{10}\ne0\), and \(\boldsymbol w(C-xI)=-k\boldsymbol wN\).

Before the split in \(k\), \(\boldsymbol e_\zeta\in F_4\) is equivalent to \(w_\zeta=(\boldsymbol wN)_\zeta=0\), because the scalar rows already vanish there. For \(k\ne0\), the four scalar rows \(\boldsymbol b^{\mathsf T}C^j\) (\(0\le j\le3\)) and two pure rows \(\boldsymbol w,\boldsymbol w C\) span \(W_3\). All six vanish at stage one. If \(w_\zeta=0\), they also vanish individually at \(\zeta\), so the actual coordinate columns \(\boldsymbol e_1,\boldsymbol e_\zeta\) belong to \(F_4=\operatorname{Ann}(W_3)=ME_2\) by [saturated duality](../sdirk-eight-saturation/README.md). They are the only possible axes in the active restriction kernel; hence its pure-four rank is exactly two. If \(w_\zeta\ne0\), the kernel is precisely the first axis and the active pure-four rank is exactly three. At nine active stages the rank is always exactly three, since the sole silent axis is already in \(F_4\).

When \(w_\zeta=0\), take the preimage \(\boldsymbol v=M^{-1}\boldsymbol e_\zeta\in E_2\). The matrix \(M\) is lower triangular of diagonal \(-\gamma^2\ne0\), so every predecessor entry of \(\boldsymbol v\) is zero. Its grade-two form is \(p(\boldsymbol c)+\alpha\boldsymbol g\), \(\deg p\le2\). If \(\zeta\ge5\), physical zero rows \(2,3,4\) are predecessors and their clocks \(a,b,c_4\) are distinct. The first two are the [literal front clocks](../sdirk-eight-silent-oneclock/README.md). Either equality \(c_4=a\) or \(c_4=b\) gives the padded earlier row by the unique [literal fourth three-tap solve](../sdirk-eight-silent-two-unequal/README.md), hence a forbidden twin. That solve moves the \(2\gamma h_4/3\) term of the actual cubic read into the coefficient of stage one; the scalar determinants at the three literal predecessor clocks are nonzero in both front phases. Thus \(p=0\), and the first predecessor with \(g_1\ne0\) forces \(\alpha=0\). This contradicts \(M\boldsymbol v=\boldsymbol e_\zeta\). Consequently \(\zeta\in\{2,3,4\}\); both literal fronts active means \(\zeta=4\).

## Eight distinct active clocks with actual \(w_\zeta=0\)

If \(k=0\), \(\boldsymbol w\) is supported on clock \(x\). With eight distinct active clocks, \(w_1=w_\zeta=0\) would leave only \(w_{10}\ne0\) there and contradict its zero sum. Thus \(k\ne0\) in this chart. At least one literal nonzero cubic defect is active. The active restrictions of \(\boldsymbol h,C\boldsymbol h\) are independent: a dependence would confine the nonzero defects to one nonzero-weight stage, contradicting the first paid defect moment. They span the rank-two active \(F_4\), so every actual pure-four read is an affine clock multiple of \(h_i\) on active axes.

Let \(D\) be the monic polynomial of the eight distinct active clocks. Interpolate \(T(c_i)=D'(c_i)w_i\) and \(S(c_i)=D'(c_i)w_i h_i\). The six zero scalar moments of \(\boldsymbol w\) give \(\deg T\le1\). The three paid moments \(\boldsymbol w C^j\boldsymbol h=0\), \(0\le j\le2\), give \(\deg S\le4\). These follow directly by expanding the basis \(D(X)/(X-c_i)\); the silent contributions actually vanish. Since \(S(c_i)=T(c_i)h_i\), ordinary precision through degree seven and the five paid moments of \(\boldsymbol h\) give
\[
 I(X^j S)=\sum_{i:\,b_i\ne0} b_i c_i^j T(c_i)h_i=0
 \qquad(0\le j\le3).
\]
Thus \(S=\sigma L_4\), with \(L_4=70X^4-140X^3+90X^2-20X+1\). Here \(T\ne0\) by \(w_{10}\ne0\). If \(S=0\), nonzero \(h_i\)'s would be confined to the sole possible root of \(T\), which was just excluded. In particular \(L_4(c_i)=Q(c_i)h_i\) with \(Q=T/\sigma\). By \(k\ne0\), the actual row \(\boldsymbol h^{\mathsf T}B\in Z_3\) has the form \(\boldsymbol wP_1(C)\) with \(P_1\) affine and nonzero. So \(D'(c_i)b_i h_i=P_1(c_i)T(c_i)\). These facts do not require every \(h_i\) to be nonzero.

Write \(W_F(X)=I((F(X)-F(Y))/(X-Y))\) for formal integration in \(Y\) over \([0,1]\). On this chart,
\[
 L_4 W_D-DW_{L_4}=\sigma^{-1}P_1 T^2.                         \tag{1}
\]
Indeed \(W_D(c_i)=b_iD'(c_i)\) by precision seven and the exact physical cardinal polynomials. The two sides agree at eight sites by \(b_i h_i=P_1(c_i)w_i\) and \(T(c_i)h_i=\sigma L_4(c_i)\). The left degree is at most three: expand
\[
 I\!\left(\frac{D(X)-D(Y)}{X-Y} L_4(Y)
 -\frac{L_4(X)-L_4(Y)}{X-Y} D(Y)\right)
\]
and use \(I(Y^jL_4(Y))=0\) for \(j\le3\). The right degree is at most three too. No ordinary precision above seven is used. Identity (1) remains valid for nonconstant \(T\) and at actual active Gaussian clocks.

## Constant \(T\), both literal fronts active: full exclusion

Here \(h_i=L_4(c_i)/Q\) at all eight active rows, with constant \(Q\ne0\). The two literal front defects give the exact degree-four diagonal polynomial from \(L_4(\gamma A_0)/H_a=L_4(\gamma B_0)/H_b\) in each front phase. The exact field \(2t^2=1\) retains both signs. Physical four is the extra silent; five, eight, nine, and ten are ordinarily active.

Write \(c=x-\gamma u\), \(d=x-\gamma(2-u)\) in the reverse star phase or \(d=x-2\gamma u\) in arithmetic. Put \(H=-2+u+4u^2-u^3\), \(J=4u^3-12u^2+3u+2\). The affine \(P_1\) and the actual normalized reverse ratios give the necessary equations
\[
 (2-u)L_4(c)-uL_4(d)+k(2u-2)L_4(x)=0,\qquad
 H L_4(d)+2J L_4(c)-kJ L_4(x)=0
\]
in the two phases, respectively. They hold even when an active tail defect vanishes. The exact script removes only factors corresponding to forbidden \(u=0,k=0\) or collisions among the five physical active clocks \(\gamma A_0,\gamma B_0,x,c,d\). The four gap degrees (front, rear: star before arithmetic) are \(0,5,2,4\).

The actual tail ratios \(w_{10}/b_{10}=-\gamma^2\), \(w_9/b_9=-\gamma^2k\) fix the shape
\[
 \rho(X)=(X-c)kL_4(x)+(x-X)L_4(c)
\]
of \(P_1\) up to a nonzero scalar. The ratios are nonzero independently of \(h\) at either peg. Rescale \(L_4\) to its monic form. By (1), \(D=L_4 U_4+\lambda V\) with monic quartic \(U_4\) and \(V\equiv-\rho W_{L_4}^{-1}\pmod{L_4}\), \(\deg V<4\); the inverse is checked in the monic Legendre quotient. The five pegs determine the four lower coefficients of \(U_4\) and scalar \(\lambda\) by a five-by-five Cramer system. Dividing its exact solution \(D\) by the five pegged factors yields a monic cubic containing the three missing active clocks, in particular the actual fifth. No division by a Legendre value or cubic defect at a tail peg occurs.

At actual fifth apply the [literal fifth cross elimination](../sdirk-eight-silent-one-seven-six-anchored/README.md). The two pure-four lines are anchored by the two actual front defects; the silent fourth keeps its own actual cubic defect from the three-tap solve. Eliminate its unknown clock from the \(A\boldsymbol h\) and \(A\boldsymbol c^{\odot3}-\boldsymbol c^{\odot4}/4\) reads by their proportional coefficients, not by assigning that silent row the active profile. Substitute \(L_4(\gamma y)/Q\) for the normalized active fifth defect. This required polynomial in \(y=c_5/\gamma\) is a unit modulo the normalized missing cubic in every retained component.

## Reproduction and scope

In the repository proof tree, install sympy==1.14.0 and python-flint==0.9.0, then run **python3 eight_constant.py** in this directory. The exact gap projections precede reduction. At the good split \((1103,t=161)\), all reduced monic diagonal and full gap fibers are retained. The five-peg determinant and missing-cubic fifth test are units in all seven reduced diagonal fibers with their full monic gap algebras. Monic finite-algebra norm units certify the characteristic-zero exclusions without reducing the unknown actual tableau or deleting a component modulo the prime. The [native Lean file](../../lean/RKCert/ReviewedNative/SDIRK8EightActivePureSupport.lean) verifies triangular preimage localization, the quadratic predecessor cut, the quartic moment kernel, and the weighted nodal product. It compiles on Lean/Mathlib 4.36.0 with only standard axioms. The tableau saturation, interpolation, and finite replay are mathematical arguments.

Remaining eight-active cases include repetitions, \(w_\zeta\ne0\), and \(w_\zeta=0\) at eight distinct clocks with either one active literal front or nonconstant \(T\). For nine distinct active clocks the reverse factor cannot vanish, by the same terminal-support zero-sum argument; (1) is not asserted in that case.
