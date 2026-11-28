# Eight active clocks: exclusion of a shared Gauss root with reverse-silent fourth

This is the nonconstant shared-root companion to the [eight-active reverse-silent packet](../sdirk-eight-silent-one-eight-reverse-vanish/README.md). Work at the ten-stage strict SDIRK8 floor over a characteristic-zero field. Only stage one has nonzero quadratic defect and is ordinarily silent. Exactly eight active physical stages have distinct clocks; the remaining silent stage has zero actual reverse read and both literal front rows are active. The latter silent stage is therefore physical four. Let \(T\) be the affine reverse nodal numerator of the earlier packet; here it is nonconstant and shares its root \(r\) with \(L_4\). This packet excludes this entire branch. A coprime nonconstant \(T\), fewer active fronts, or other physical supports are separate; the unrestricted interval stays **10–11**.

## A physical Gaussian atom, not a second weight-zero row

The earlier packet gave \(T(c_i)h_i=\sigma L_4(c_i)\) and \(\boldsymbol h^{\mathsf T}B=\boldsymbol wP_1(C)\), with \(\sigma\ne0\) and \(P_1\) affine nonzero; \(k=1+2u-u^2\ne0\) holds here. Put \(P=\sigma L_4/T\), a nonzero cubic with \(P(r)\ne0\) since \(L_4\) is simple. At every active clock different from \(r\), \(h_i=P(c_i)\). If \(r\) were not active, the four paid signed moments of \(h\) against degrees zero through three and ordinary precision seven would make \(P\) orthogonal to the whole cubic scalar span, impossible by its nonsingular Hilbert matrix.

At the unique active row of clock \(r\), \(T(r)=D'(r)w_r=0\) forces \(w_r=0\) because its ordinary clock is simple. Then \(b_r h_r=P_1(r)w_r=0\) forces \(h_r=0\); its ordinary weight \(b_r\) is nonzero by hypothesis. The first paid defect moment alone now gives the precise mass
\[
 b_r=\nu=I(P)/P(r).
\]
It is the usual Gaussian atom, not a physically silent stage. It cannot be at the two literal fronts, whose cubic defects are nonzero. It cannot be at the terminal or penultimate, whose actual \(w\)'s are nonzero. Its only possibilities are physical rows 5, 6, 7, 8.

## Seven remaining clocks and an affine Bézout identity

Remove the known Gaussian atom from the signed ordinary rule, obtaining \(I_\circ(f)=I(f)-\nu f(r)\) through degree seven on the seven actual nonhole clocks. Write \(D_7=D/(X-r)\), and let \(U=L_4/(X-r)\), rescaled monic. The identity \(D'(c_i)=(c_i-r)D_7'(c_i)\) at every nonhole site gives \(D_7'(c_i)w_i=\tau\) for a constant \(\tau\ne0\), since \(T=\tau(X-r)\). The actual cubic defect at these sites is a nonzero constant multiple of \(U\). For \(\deg f\le4\), the difference \(f(X)-f(r)\) is an \((X-r)\) multiple of degree at most three, so \(I_\circ(Uf)=0\) by the four ordinary orthogonal moments of \(L_4\) and \(I(U)=\nu U(r)\).

Define \(W^\circ_S(X)=I_\circ((S(X)-S(Y))/(X-Y))\). The exact signed cardinal read gives \(W^\circ_{D_7}(c_i)=b_iD_7'(c_i)\). Then
\[
 U W^\circ_{D_7}-D_7 W^\circ_U=\kappa P_1
\]
for a nonzero scalar \(\kappa\): the two sides agree at the seven nonhole clocks by \(b_i h_i=P_1(c_i)w_i\). The degree of the first term in the integrand after the usual Bézout subtraction is at most one by \(I_\circ(Y^jU)=0\) for \(j\le4\). In the second term the coefficient of \(X^2\) vanishes by \(I_\circ(D_7)=0\), using ordinary precision seven. This proves the affine identity without requiring precision eight or a nonzero defect at any particular nonhole clock.

## Exact literal exclusions

The two literal front readings of the affine \(T/\sigma\) determine its root. Use the full homogeneous \(L_4\)-root test from the [seven-active hole packet](../sdirk-eight-silent-one-seven-distinct-hole/README.md); it removes only zero diagonal, zero slope, and vanished Legendre values at the two known nonzero-defect fronts. The retained exact diagonal factors have degree twelve in each front phase over \(2t^2=1\), including both signs of \(t\).

If physical eight is the hole, then its reverse \(w_8=0\). In reverse star \(w_8/b_8=-\gamma^2 k\ne0\) excludes it. In reverse arithmetic, write \(x=c_{10}=1-\gamma\), \(u=(x-c_9)/\gamma\), and \(c_8=x-2\gamma u\). Its \(w_8=0\) forces \(J(u)=0\), where \(J(u)=4u^3-12u^2+3u+2\) is the cleared arithmetic ratio numerator after the nonzero \(k\) factor. The forced \(u=(x-r)/(2\gamma)\) gives a unit in every exact diagonal component. No coefficient of that cleared ratio is inverted.

Otherwise all three tail clocks are known nonhole pegs once the gap is fixed. At the three actual tail positions use the profile \(P\), and eliminate the affine \(P_1\) by the same [tail equations](../sdirk-eight-silent-one-eight-reverse-vanish/README.md), replacing \(L_4\) with \(P\). In both front cases the reverse star gap is an exact constant after structural removal. In reverse arithmetic it is a cubic. Removed factors are only forbidden \(u=0,k=0\) and collisions among the five distinct active nonhole pegs and the active hole. The two nonzero terminal reverse ratios fix the shape of \(P_1\) up to scale by the affine interpolant with values \(P(x)\) and \(P(c_9)/k\). Legendre or defect values at those pegs are not divided.

Using the modified affine Bézout identity, recover \(D_7=U U_4+\lambda V\), with \(U_4\) monic quartic and \(V\equiv-P_1(W^\circ_U)^{-1}\pmod U\). The five nonhole pegs determine all four lower coefficients of \(U_4\) and the scalar \(\lambda\) by exact Cramer. The determinant, the inverse in the cubic quotient and all divisions are checked by units. The missing nonhole polynomial is quadratic. If physical fifth is a nonhole stage, its normalized clock must be a root of this quadratic and of the ordinary literal fifth cross equation with its true profile \(P\); they have a unit resultant. If fifth is the hole, the literal fifth equation instead takes \(h_5=0\) at \(r/\gamma\) and is a unit on the diagonal field. Neither calculation assigns an ordinary or weighted virtual amplitude to the silent fourth.

## Replay

Install sympy==1.14.0 and python-flint==0.9.0 and run **python3 eight_shared_gauss.py** in this repository proof directory. The exact diagonal and gap projections precede the split \((1103,t=161)\). Both real-candidate signs are retained via the quadratic front field, not an ordering assumption. The full monic gap fibers in all six reduced arithmetic components, and the physical eighth and fifth hole tests in every diagonal component, give units. These are good-reduction norm arguments in finite algebras, not reduction of an assumed tableau. The [native Lean file](../../lean/RKCert/ReviewedNative/SDIRK8EightActiveGaussHole.lean) checks the actual signed atom recovery and reverse numerator deflation on Lean/Mathlib 4.36.0. The saturation, interpolation, and scalar finite replay remain source-level.
