# One active literal front: coprime numerator and a Gaussian terminal

Consider the ten-stage strict SDIRK8 floor over a characteristic-zero field. Only the individually weight-zero first stage has nonzero quadratic defect. There are eight individually active rows at distinct clocks, the extra silent has actual reverse read \(w_\zeta=0\), and exactly one literal early front is active. Use the [reverse-silent reduction](../sdirk-eight-silent-one-eight-reverse-vanish/README.md). This packet excludes the subchart where \(T\) is nonconstant and coprime to \(L_4\), and the actual terminal clock is Gauss. In particular, the ordinary terminal weight is not set equal to a prescribed Gaussian mass. A Gauss penultimate/eighth or a non-Gauss rear, and the other active-count branches, are separate. The unrestricted interval stays **10–11**.

## Literal fourth and fifth in a fixed Gauss coefficient algebra

Write \(x=c_{10}=1-\gamma\), \(r=x\) with \(L_4(r)=0\), so \(\gamma=1-r\). The active cubic defect satisfies \(L_4(c_i)=Q(c_i)h_i\) with \(Q=T/\sigma\) affine nonconstant and coprime to \(L_4\), up to the common normalization of the cubic read. In this case \(T,w_i,Q(c_i)\) are nonzero at every active clock. Since terminal \(h_{10}=0\) and \(w_{10}\ne0\), its actual affine reverse multiplier \(P_1\) has the unique root \(r\). Neither the penultimate nor eighth can have zero cubic amplitude. Unlike the [shared-root Gaussian atom](../sdirk-eight-silent-one-eight-shared-gauss-one-front/README.md), here \(T(r),w_{10}\) are nonzero.

Normalize time by \(\gamma\) and cubic defects by \(\gamma^3\). If \(a\) is the active literal clock and \(s=c_4/\gamma\), the two true active amplitude reads \(H_a,H_4(s)\) determine the affine denominator. Neither amplitude is zero. For fourth, its zero would force the actual \(A\boldsymbol h\) read to vanish by the active pure-four lines, but the exact literal fourth \(H_4,A\boldsymbol h\) gcd is one. Also \(s\ne A_0,B_0\) by the unique literal three-tap solve, as in the [one-front constant case](../sdirk-eight-silent-one-eight-constant-one-front/README.md). For calculations the homogeneous normalized denominator and numerator are
\[
 Q_*(Y)=(s-Y)H_4(s)L_4(\gamma a)+(Y-a)H_a L_4(\gamma s),\qquad
 P_*(Y)=H_aH_4(s)(s-a)L_4(\gamma Y).
\]
Their quotient is the actual nonzero-scale normalized active profile, with no assumed profile value at the silent literal front.

The two literal fifth conditions are obtained from the actual preceding clocks \(A_0,B_0,s\), the known stage-one feed, and the affine pure-four slopes pinned at \(a,s\). Their detailed coefficient construction is the same as in the one-front constant packet with these homogeneous polynomials. The common \(H_4(s)\) is nonzero and cancelled. The physical fifth cannot be either occupied active \(a\) or \(s\); both exact factors \(Y-a,Y-s\) divide out, leaving cubics. No factor at the *silent* literal clock is removed. The exact fifth resultant has \(s\)-degree 21 in each of the four early modes, and leaves degree seven after the true \(H_4(s),s-A_0,s-B_0,Q_1,\operatorname{Res}(Q,L_4),L_4(\gamma s)\) guards. This computation uses the full fixed monic \(r\) quotient, not selectively chosen Gaussian roots.

## Actual trailing ratios and a rational signed mask

At the three active rear clocks write \(c=x-\gamma u\) and \(d=x-\gamma(2-u)\) in star or \(d=x-2\gamma u\) in arithmetic. The actual affine multiplier is proportional to \(X-r\); \(x=r\) forbids using a terminal-amplitude denominator. With \(H,J,k\) as in the [arithmetic rear packet](../sdirk-eight-silent-one-eight-coprime-arithmetic/README.md), the two necessary tail equations are \((2-u)h_9-u h_8=0\) in star and \(H h_8+2J h_9=0\) in arithmetic. Multiply only by the known nonzero active denominators. The exact physical factors \(u(u-1)(u-2)\) and \(u^2\) divide out respectively, giving a quadratic and quintic in \(u\). Both actual leading coefficients have gcd one with the degree-seven fourth polynomial. Their degrees are retained in every finite fiber.

Write the physical affine denominator as \(q(X)=\gamma Q_{*,0}+Q_{*,1}X\). The [paid rational moment solve](../sdirk-eight-silent-one-seven-distinct-anchors/README.md) determines \(\Lambda(f)=\sum_i b_i f(c_i)/q(c_i)^2\) through degree nine. It uses ordinary precision seven and the signed \(h,h^2\) moments; it does not treat \(q\) as polynomially invertible on all \(X\). The actual \(q\) pole is not a Legendre root, which licenses the two inverse moments in that solve.

The six distinct known ordinary pegs are \(\gamma a,\gamma s,\gamma y,r,c,d\) where \(y\) is actual fifth. Let their monic product be \(D_6\), and use \(m_j=\Lambda(X^jD_6)\), \(0\le j\le3\). The scaled remaining nodal quadratic has coefficients
\[
 (m_1m_3-m_2^2,\ m_1m_2-m_0m_3,\ m_0m_2-m_1^2).
\]
Its leading coefficient is nonzero at an actual solution since the two missing physical stages have distinct clocks and nonzero signed masked weights. The replay does not divide by this coefficient. By the eight-active Bézout formula, the residue of \(D_6\) times this quadratic modulo monic \(L_4\) is proportional to the residue of \((X-r)q^2 W_{L_4}^{-1}\). All six two-by-two minors of the two coefficient vectors are thus zero.

## Actual sixth read, without declaring a reduced ghost impossible

The minors alone need not be units. To finish, actual sixth is one of the two missing nodes. Its actual normalized strict moments at \(A_0,B_0,s,y\), after removing the known stage-one feed, follow from its cubic profile \(P_*/Q_*\) and its true affine \(\tau_4\) line. Use the same actual marked-tap construction as in the [reverse-star sixth gate](../sdirk-eight-silent-one-eight-coprime-star/README.md), now with the affine pure-four lines pinned by **active** \(a,s\). In detail, set \(\Delta=H_4(s)(s-a)\), and clear each moment by \(\Delta Q_*(Y)\) for a candidate sixth \(Y\). For the fourth scalar moment use \(\Delta\ell_{\tau}(Y)\), a known affine polynomial, times \(P_*(Y)\) in the cleared read. Let \(M\) be the marked scalar sum from \(F_3(X)=(X-A_0)(X-B_0)(X-s)\). Let \(D_A\) be the required strict \(A\boldsymbol h\) minus the quadratic defect interpolant read through \(A_0,B_0,s\), all with the same cleared factor. With that interpolant \(H_2\), both differences see the same actual tap to fifth. Therefore
\[
   Q_*(y)F_3(y)D_A + M\{Q_*(y)H_2(y)-P_*(y)\}=0 .
\]
This is a degree-at-most-five polynomial in the sixth clock, with no division by the marked value or the fifth denominator. It remains valid when fifth shares the earlier **silent** literal clock. Its padded resultant with the scaled remaining quadratic must be zero. Together with the six nodal minors the span gives a unit in every retained local component. No accidental residue collision or zero leading term of the scaled quadratic is discarded.

## Replay and formal scope

Install sympy==1.14.0 and python-flint==0.9.0 and run **python3 check_eight_coprime_one_front_terminal.py** in this proof directory. It uses the paired [shared-root one-front packet](../sdirk-eight-silent-one-eight-shared-gauss-one-front/README.md) for its exact coefficient and finite evaluation interfaces, not for a Gaussian mass assumption. All monic factors of the four simple Gaussian parameters and the exact fourth polynomial are retained at the good split \((1129,203)\). A true degree-three leading fifth unit is checked before every local common-root computation; both full tail fibers are checked with their exact degrees. The four early modes have 15, 14, 12, and 8 candidate fifth components per rear phase, all excluded. The finite unit argument does not reduce an unknown tableau. The [native marked-read and tail file](../../lean/RKCert/ReviewedNative/SDIRK8EightActiveCoprimeTerminalReads.lean) states the independent scalar identities. Saturation, finite projections, and arithmetic replay remain source-level.
