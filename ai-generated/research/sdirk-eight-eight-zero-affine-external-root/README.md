# External affine reverse root: exact Cauchy-transfer and fifth-read gates

This is a reduction, **not** an exclusion. Consider the remaining eight-distinct-zero chart for strict ten-stage SDIRK of ordinary order at least eight over characteristic zero. Use \(A'=A/\gamma\), \(\mathbf x=\mathbf c/\gamma\), \(D=1/\gamma\), \(U\) the coordinate space on the eight zero-residual rows. The two off rows are the silent physical rows 1 and 2, at distinct clocks. Let \(P_8\) be the monic polynomial of the eight zero labels, and suppose the reverse numerator is affine with root \(\rho\) outside those labels:
\[
 z_iP'_8(x_i)=\Theta(x_i-\rho)\quad(i\in U),\qquad
 \Theta\ne0,\quad P_8(\rho)\ne0 .
\]
The root may still equal an off clock; no assumption about that is needed. Set \(I_D(T^j)=D^j/(j+1)\). For any polynomial \(F\) define the divided mean
\[
 {\cal C}_F(\rho)=I_D\!\left(\frac{F(T)-F(\rho)}{T-\rho}\right)
\]
where the polynomial division is exact. The one functional needed for the pure modes is
\[
 \Lambda_\rho(V)=P_8(\rho){\cal C}_V(\rho)-{\cal C}_{P_8}(\rho)V(\rho).
\]

## 1. A single shape equation linear in the unknown early monic quadratic

A degree-at-most-seven interpolant \(V\) of \((C'-\rho I)\mathbf f\) on \(U\), for \(C'=\operatorname{diag}(\mathbf x)\) and \(\mathbf f\in F_4|_U\), has degree at most five. This follows from the two pure tests \(\mathbf z^\mathsf T,\mathbf z^\mathsf T C'\) and the leading Lagrange coefficient formula. Multiplying ordinary tests by \(C'-\rho I\) gives \(I_D(T^jV)=0,\ 0\le j\le2\), placing \(V\) in the shifted Legendre space \(\langle L_3,L_4,L_5\rangle\).

The ordinary constant test on \(\mathbf f=V(\mathbf x)/(\mathbf x-\rho)\) is exactly \(\Lambda_\rho(V)=0\). Indeed \(P_8\) vanishes at the weighted sites, and ordinary exactness on the degree-seven divided polynomial gives
\[
 {\cal C}_{P_8}(\rho)
    =-P_8(\rho)\sum_{i\in U} b_i/(x_i-\rho).
\]
Then split \(V(T)=V(\rho)+(T-\rho)\cdot\) a polynomial in the ordinary test. Conversely, \(V\in\langle L_3,L_4,L_5\rangle\) with \(\Lambda_\rho(V)=0\) gives an actual \(F_4|_U\) profile: the three other ordinary tests follow by splitting \(T^j-\rho^j\), and the two pure tests follow by degree. In equations,
\[
 (C'-\rho I)F_4|_U
      =\ker\Lambda_\rho\cap\langle L_3,L_4,L_5\rangle,
\]
a two-dimensional plane. Pairing is exact because the relevant products are of degree at most seven and all reverse rows are supported on \(U\).

Let \(a,b,c\) be the first three actual zero reads, and \(\alpha(c),\eta(c)\) the already verified supported transfer coefficients. Define the cleared transfer functional
\[
 {\cal T}_\rho(V)=(a-\rho)(b-\rho)V(c)
   -\alpha(c)(c-\rho)(b-\rho)V(a)
   -\eta(c)(c-\rho)(a-\rho)V(b).
\]
The literal transfer says that \({\cal T}_\rho\) vanishes on the above two-plane. In particular the nonzero \(V_4=(T-\rho)L_4\) is in its kernel: \(\Lambda_\rho(V_4)=0\), and \({\cal T}_\rho(V_4)=0\) is the usual \(C_3(c;D)=0\) times nonzero factors. The three \(L_3,L_4,V_4\) form a basis because \(V_4\) has degree five with nonzero lead. Consequently the necessary external-root gate is
\[
 \Lambda_\rho(L_3){\cal T}_\rho(L_4)-
 \Lambda_\rho(L_4){\cal T}_\rho(L_3)=0,\qquad
 \bigl(\Lambda_\rho(L_3),\Lambda_\rho(L_4)\bigr)\ne(0,0).
\]
The nonzero pair is forced by the actual rank two, not an imposed generic minor. No exceptional central root \(\rho=D/2\) is removed.

Write the early modes as \(\sigma(T)P_2(T)\), with \(\sigma=(T-a)(T-b)(T-c)\) and \(P_2=(T-d)(T-e)\). In the finite-gap phases \(P_8=\sigma P_2(T-s)(T-t)(T-r)\), so both \(P_8(\rho)\) and \({\cal C}_{P_8}(\rho)\) are linear in the coefficients of \(P_2\). The gate is therefore a third homogeneous row beside the two ordinary relative-cardinal rows from the finite-gap proof, with no assumption about an ordinary moment pivot.

In the live star it is also **gap-free**. Set \(m=D-2,\ Y=T-m,\ w=\rho-m,\ P_5=\sigma P_2,\ R=P_5(Y-1)\). The two ordinary masks \(I_D(R(Y+w))=0\), \(I_D(P_5[(1-w)Y-(2-w)])=0\) from the [affine star proof](../sdirk-eight-eight-zero-affine-early-star/README.md#2-both-cardinal-tests-and-the-jump-are-gap-free) hold for the external root as well; their derivation divides only by rear clock differences and \(\rho\) not equal to a rear clock. For \(P_8=R(Y^2-\delta^2)\),
\[
 \mathcal C_{P_8}(\rho)
       =(w^2-\delta^2)\mathcal C_R(\rho)+I_D(R(Y+w))
       =(w^2-\delta^2)\mathcal C_R(\rho),\qquad
 P_8(\rho)=(w^2-\delta^2)R(\rho).
\]
Thus the Cauchy functional can use \(R(\rho),\mathcal C_R(\rho)\) instead, without the free star gap. The denominator \(w^2-\delta^2\) is nonzero by externality.

## 2. Exact fourth and fifth read conditions

At grade five the same argument, with only the pure row \(\mathbf z^\mathsf T\) among the annihilators \(W_2\), yields
\[
 (C'-\rho I)F_5|_U=\ker\Lambda_\rho\cap\langle L_2,L_3,L_4,L_5,L_6\rangle .
\]
The interpolant now has degree at most six, and the two multiplied ordinary tests have degree at most seven. This space has dimension four. The **first four actual zero reads** detect it: every scalar cubic has an actual supported \(E_3\) representative, and its values on the first four distinct zero clocks form an invertible evaluation map. Multiplication by the normalized \(M=C'A'-A'C'-(A')^2\) maps \(E_3\) into \(F_5\); on the first four zero reads its principal triangular block has diagonal \(-1\) and no off input contributes. Thus the four pure reads detect all of \(F_5|_U\); multiplying by the four nonzero \((x_i-\rho)\) preserves detection.

For the cubic \(\sigma\), fit \(V\in\ker\Lambda_\rho\cap\langle L_3,L_4,L_5\rangle\) from the first two values \(-(a-\rho)J\sigma(a),-(b-\rho)J\sigma(b)\). The first-two rank detects the fit; at the actual fourth zero \(d\) the diagonal condition is
\[
 V(d)=(d-\rho)(\sigma(d)-J\sigma(d)).
\]
For the supported quartic \(\tau=(T-d)\sigma\), the actual first four inputs vanish. Fit \(W\in\ker\Lambda_\rho\cap\langle L_2,\ldots,L_6\rangle\) from \(-(\,x_i-\rho\,)J\tau(x_i)\) at \(a,b,c,d\) and the one Cauchy equation. The actual fifth zero \(e\) gives the additional necessary read
\[
 W(e)=(e-\rho)(\tau(e)-J\tau(e)).
\]
Both fits can be written as cleared linear-system determinant tests, without declaring a nonliteral pivot unit. These are exact ordinary-order-eight reductions, not a proof that no external-root chart survives.
