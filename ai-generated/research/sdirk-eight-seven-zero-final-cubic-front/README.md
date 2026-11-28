# Final seven-zero chart: both cubic first-zero placements are impossible

Let \(A,\mathbf b\) be a strict ten-stage SDIRK tableau of ordinary order at least eight over a characteristic-zero field, with common nonzero diagonal \(\gamma\), nodes \(\mathbf c=A\mathbf1\), and quadratic residuals \(\mathbf g=A\mathbf c-\mathbf c^{\odot2}/2\). Assume there are exactly seven physical residual zeros at seven distinct literal clocks, and the three physical off-zero clocks are pairwise distinct. The second reflected residual ratio is nonzero.

**Result.** The first zero cannot be physical row 3 or physical row 4 after a star front. This packet handles a silent physical eighth row and a live reflected star; the [paid supported-quartic argument](../sdirk-eight-seven-zero-supported-quartic/README.md) rules out live reflected arithmetic for **every** forward placement. Thus under these hypotheses the first three physical rows must be off in an arithmetic phase. No global stage interval changes.

## 1. A fourth reverse affine gate

Use \(A'=A/\gamma,\ \mathbf x=\mathbf c/\gamma,\ D=1/\gamma\), \(I_D(T^j)=D^j/(j+1)\), and \(U=\ker\operatorname{diag}(\mathbf g)\). All three off weights are silent and the pure row \(\mathbf z^\mathsf T=-\mathbf b^\mathsf T(CA-AC-A^2)/2\), \(C=\operatorname{diag}(\mathbf c)\), is supported on \(U\), by the [paid census](../sdirk-eight-seven-eight-zero-census/README.md). Its first six zero moments make it a nonzero barycentric row on the seven distinct zero sites. The last two rows are live zeros at \(s=x_{10}=D-1,\ t=x_9=s-v\). The literal eighth row must itself be a zero: if it were off, it would be silent but the ghost would require \(z_8\ne0\). Write \(r=x_8\). Let \(P_4\) be the monic nodal polynomial for the four earlier zero clocks, let \(e\) be the last of those four, and put \(P_7=P_4(T-s)(T-t)(T-r)\). Its ordinary cardinal polynomial is \(B(T)=I_{D,X}((P_7(X)-P_7(T))/(X-T))\), so \(B_i=B(x_i)=b_iP_7'(x_i)\).

In the live reflected star, the two ratios are \(\kappa=B_s/B_t=1+2v-v^2\ne0\) and \(B_t=B_r\). In the ghost, \(B_r=0,\ \kappa B_t=B_s,\ r=s-2v\), and \(H(v)=v^3-4v^2-v+2=0\). Use a degree-two weighted row with a scalar profile \(R\) such that its entries at \(s,t,r\) vanish after subtracting a constant multiple of \(\mathbf z^\mathsf T\). In the ghost choose \(R=(T-s)(T-t)\) and subtract zero. In the live case choose \(R(s)=1,\ R(t)=R(r)=\kappa\); the ratios ensure a common multiple to subtract, including at \(s\). The corrected input is supported on \(U\) and vanishes on all rows after \(e\), regardless of off-row interleaving. Its right \(A'\) read at \(e\) is diagonal.

The pure discrepancy from the scalar \(J_D^* R\) lies in \(Z_3=\langle\mathbf z^\mathsf T,\mathbf z^\mathsf TC'\rangle\), \(C'=\operatorname{diag}(\mathbf x)\); the two pure rows are independent at \(s,t\). After multiplying by nodal derivatives it is an affine function of the clock, passing through \(-B_sJ_D^*R(s),-B_tJ_D^*R(t)\) at \(s,t\). At \(e\) it is \(B_e(R(e)-J_D^*R(e))-B_sR(s)\), with the last term coming from the common pure correction. Hence
\[
 \begin{split}
 0={}&(t-s)\bigl[B_e(R(e)-J_D^*R(e))+B_s(J_D^*R(s)-R(s))\bigr]\\
 &+(e-s)\bigl[B_tJ_D^*R(t)-B_sJ_D^*R(s)\bigr]. \tag{1}
 \end{split}
\]
The prospective weight \(b_e\) need not be nonzero. This is an actual fourth reverse diagonal, not a permutation of the first three rear constraints.

## 2. Gap-free star constraints and fixed ghost moments

For the star put \(m=D-2,\ Y=T-m,\ \delta=v-1\). The rear sites in \(Y\) are \(1,-\delta,\delta\). Put \(H_j=I_D(P_4Y^j)\). The [three ordinary and cardinal relations](../sdirk-eight-seven-zero-silent-double-final/README.md#3-the-star-cancels-its-gap) give \(H_1=H_0,\ H_3=H_2,\ H_2=2H_0\), and \(B_t=B_r=H_0\ne0\). This applies with all of \(\deg P_4=4\) unknown, not just to a partially fixed nodal polynomial. The normalized star profile in (1) is \(R=2-Y^2\), with \(J_D^*R=4/3-2Y+Y^3/3\). Write \(y=e-m\), \(F(y)=2/3+2y-y^2-y^3/3\), and \(C_e=I_D(P_4/(T-e))\). Ordinary division of the rear cubic at \(e\) gives
\[
 B_e=H_0(1+y^2-\delta^2)+(y-1)(y^2-\delta^2) C_e .
\]
The affine pure values at the two symmetric sites give
\(B_e F(y)=H_0[\,2/3+2y-(1+y/3)\delta^2\,]\).
Substitute the previous display and cancel the forbidden collision factor \(y^2-\delta^2\ne0\). The fourth reverse gate becomes
\[
                      H_0(F(y)-1-y/3)+(y-1) C_e F(y)=0,       \tag{2}
\]
independent of the rear gap. This cancellation also covers \(\delta\) or \(e\) in an algebraic extension; only actual distinctness is used.

For the ghost use (1) directly. The three masks on the unknown monic nodal completion are the full known-node mask from \(I_D(P_7)=0\), its divided pair from \(\kappa B_t=B_s\), and the mask from \(B_r=0\). Their coefficients are exact in the cubic rear gap field.

## 3. The exact diagonal projection and two forward cases

Let \(a\) be the first forward zero. If this is **physical row 3**, the [literal front calculation](../sdirk-eight-seven-zero-three-clock-five-label/README.md#3-three-forward-placements-in-one-good-reduction) gives \(a=1+2u,\ Q(u)=4u^3-12u^2+3u+2=0\), with \(u\) the actual front gap. If it is **row 4 with a star front**, the residual graph is \(P_0=2T-1-T^2/2\) and its first primitive gives the same equation for \(a\) via the auxiliary \(u=(a-1)/2\); in this case \(u\) need not equal the actual front gap. This is because \(6(JP_0-P_0)(1+2u)=-2Q(u)\).

Write \(P_4=(T-a)Q_3\), with \(Q_3\) monic on the other three early zeros. In either rear mode the three ordinary rows form a Cramer system on its coefficients. The joint gcd of the pivot and its three numerators is \(D^6\) up to a unit, so there is no singular monic solution at \(D\ne0\). Divide by \(D^6\) and use the cleared \(\widehat Q_3=\Delta Q_3\) in (1) or (2). The actual \(e\) is a root of \(Q_3\). The resultant in \(e\) has raw \(D\) degree 81 in the live star and 99 in the ghost. Divide out only exact factors supported on \(D,\Delta\), forbidden node collisions, and the known nonzero first \(L_D(a)\) (also \(H_0=B_t\) in star). The nonzero \(L_D(a)\) guard follows from the [actual first supported reads](../sdirk-eight-seven-zero-three-clock-five-label/README.md#2-ordinary-projection-and-actual-supported-forward-reads), not from a residue sample. The remaining projection degrees are 14 and 18.

At each exact diagonal candidate, recover \(Q_3\) by the unit-tested ordinary pivot, include every possible fourth reverse \(e\), and test both orders \((b,c)\) of the remaining two early zero labels. The actual second supported graph gate \(\mathcal G(P_0;a,b)\) is nonzero in the front-star case. For a row-3 first zero, the two actual graph and cubic reads give
\[
 P=P_0+\lambda R_0,\quad R_0=(T-1)(T-1-u),\qquad
 \mathcal G(P;a,b)=0,\quad \mathcal D((T-d)R_0)=0.
\]
Here \(d\) is the third physical off clock. The pivots \(\mathcal G(R_0;a,b)\), \(P(a)\) and \(\mathcal D(R_0)\) are units in every selected fiber. The [two-donor third forward read](../sdirk-eight-seven-zero-three-clock-five-label/README.md#3-three-forward-placements-in-one-good-reduction) then gives a nonzero augmented determinant for each direction. No division by a prospective output weight is used.

| Rear | Exact coefficient primitive | \(p\) | Simple primitive residue | All reduced \(D\) roots | Directed early pairs |
|---|---|---:|---:|---:|---:|
| Live star | \(u\), degree 3 | 13 | 4 | 14 | 28 |
| Silent row 8 | \(u+2v\), degree 9 | 127 | 91 | 18 | 36 |

All relevant leading coefficients and ordinary and graph pivots are checked in the finite extensions over these simple embeddings of the exact fields. The surviving exact projection is nonzero and has unit leading coefficient; any algebraic \(D\) root reduces to one of the checked geometric roots. The monic \(Q_3\) gives all three early candidates in those fibers. Hence the local computations exclude every characteristic-zero coefficient field, rather than asserting an extrapolation from prime-field absence.

## 4. Replay and scope

Run `python check_fixed_front.py star` and `python check_fixed_front.py ghost` using SymPy 1.14 and python-flint 0.8. Saturated rooted ingress and the algebraic elimination are source-level. The chart with first three off rows in arithmetic and first zero at physical four is not excluded by this packet.

The [Lean scalar companion](../../lean/RKCert/Research/SDIRKEightSevenZeroFinalCubicFront.lean) and local proof audit pass on Lean/Mathlib 4.36.0. The full tableau argument remains mathematical.
