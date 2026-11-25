# Fixed SDIRK(11,8): whole-box signs for the five scalar chart guards

**Exact source-level certificate, not Lean.** On the full original closed rectangle
\[
13/32\le s\le14/32,\qquad 1/8\le t\le13/100,
\]
the four old cardinal numerators have signs \((-,+,-,+)\), and the residual numerator \(J_0>0\). This uses no seed root equation, calibration sign, evaluation at selected parameters, subdivision, root evaluation/refinement, compiler, or Git. The result is scoped to the fixed eleven-stage chart. It does not assert existence of its parameters or verify the Runge–Kutta order conditions.

## The compact five-moment form

Put \(u=(1,a,s,t)\), \(a=(1+s)/2,\ z=a+s,\ z_2=2z=1+3s,\ w=2u=(2,1+s,2s,2t)\). The polynomial variable \(Y\) is on the normalized unit interval; write \(I\) for the zero-constant primitive and \(I_1\) for evaluation of that primitive at 1. Set
\[
Z_Y(Y)=\prod_{j=0}^3 (z_2Y-w_j),\quad
R_i(Y)=\prod_{j\ne i}(z_2Y-w_j),\quad
p_{ij}=840\, I_1(Y^j R_i(Y)),\quad 0\le j\le4.
\]
These are integer polynomials in \(s,t\): the integrands have degree at most 7 and 840 is divisible by every primitive denominator \(1,\ldots,8\). Put \(m_j=840\,I_1(Y^j Z_Y)=z_2p_{1,j+1}-w_1p_{1j}\) for \(j=0,\ldots,3\). Equivalently \(m_j=z_2p_{i,j+1}-w_ip_{ij}\) for any \(i\).

Let
\[
D'=m_0m_2-m_1^2,\quad N'_1=m_1m_2-m_0m_3,\quad
N'_0=m_1m_3-m_2^2,\quad \mathcal N_Y=D'Y^2+N'_1Y+N'_0.
\]
In the previous signed-node certificate the unnormalized moment determinant \(D=z_2^2D'>0\), so \(D'>0\). Orthogonality and the two-by-two solve give \(\mathcal N_Y(Y)=(D'/z^2)B_*(zY)\). This is an identity of polynomial coefficients before choosing any quadratic root.

**Interior weights.** The four compact signed polynomials are
\[
G_i=\det[p_{i,j+k}]_{0\le j,k\le2}.
\]
Indeed, expansion along the first row gives
\[
840\,I_1(R_i\mathcal N_Y)=
\det\begin{pmatrix}
p_{i0}&p_{i1}&p_{i2}\\m_0&m_1&m_2\\m_1&m_2&m_3
\end{pmatrix}=z_2^2G_i.
\]
The last equality follows by the triangular row transform from the three Hankel rows, with diagonal \(1,z_2,z_2\) and two subdiagonal entries \(-w_i\). On the other hand, \(R_i(Y)=8\prod_{j\ne i}(zY-u_j)\), so for the actual original numerator \(\Omega_i=z^{-1}I_z[B_*(X)\prod_{j\ne i}(X-u_j)]\) this proves
\[
G_i=(840\cdot32\,D'/z_2^4)\Omega_i .
\]
The factor is strictly positive. Each guard has bidegree no larger than \((9,3)\); \(G_3\) is independent of \(t\), because the omitted node is \(t\), and the normalization \(z\) does not use it.

**Residual rank.** In the previous notation \(J(X)=(X-s)(X-t)(X-1)\), \(J_0=z^{-1}I_z[(X-a)B_*(X) (I J)(X)]\). The same \(R_1(Y)=8J(zY)\) supplies the rank guard. Set
\[
a_j=
 12\!\left[\frac{z_2}{j+2}(p_{10}-p_{1,j+2})
   -\frac{w_1}{j+1}(p_{10}-p_{1,j+1})\right],\quad j=0,1,2,
\qquad
G_J=\det\begin{pmatrix}a_0&a_1&a_2\\m_0&m_1&m_2\\m_1&m_2&m_3\end{pmatrix}.
\]
To see that this is the needed primitive integral, use
\(I_1[Y^j I R_1]=(I_1R_1-I_1[Y^{j+1}R_1])/(j+1)\), verified on a monomial. Thus \(a_j=12\cdot840\,I_1[Y^j(z_2Y-w_1)I R_1]\) with all coefficients integral. Expansion of the determinant and the exact scale \(I R_1(Y)=(8/z)(I J)(zY)\) give
\[
G_J=12\cdot840\,I_1[(z_2Y-w_1)\mathcal N_Y I R_1]
=(12\cdot840\cdot128\,D'/z_2^3)J_0 .
\]
Hence its strict sign is the original residual guard sign. This polynomial has bidegree at most \((12,3)\).

As an independent scaling cross-check, I also formed the raw integer polynomials in \(v=2X\), with NB(v) the denominator-cleared quadratic from the earlier node sign script. The raw signs are for \(840\cdot32D\,\Omega_i\) and \(12\cdot840\cdot128D\,J_0\), respectively. Exact coefficient comparison gave these as \(z_2^6G_i\) and \(z_2^5G_J\) in all five cases. This check compared integer coefficients, not values at parameters.

## Exact signed data and reproduction

The standalone **sdirk118_guard_sign_certificate_20261125.js** computes the smaller determinants and certifies all five uniform signs using BigInt alone. It was executed from full readback. Transform \(s=(13+S)/32,\ t=(25+T)/200\) with \(S,T\) in \([0,1]\). For bidegree \((m,n)\), obtain the transformed power coefficient array \(c_{kl}\) multiplied by \(32^m200^n\). The integer Bernstein coefficient at \((i,j)\), on common scale \(32^m200^n m!n!\), is
\[
\sum_{k\le i,\ \ell\le j} c_{k\ell}\binom{i}{k}\binom{j}{\ell}
 \ k!(m-k)!\,\ell!(n-\ell)! .
\]
This is the familiar binomial conversion from monomials; both Bernstein bases are nonnegative and each sums to one on the closed box. Thus a strictly signed minimum or maximum proves the polynomial has that strict sign everywhere, endpoints included. No root-specific comparison or subdivision is used.

Canonical script output (name, \(m,n\), minimum, maximum, positive common scale):
```text
Omega0 9 3 -1262758160642915567716490280960 -669364354399255693516800000000 612849837292577095680000000
Omega1 9 3 410537585922285356236800000000 883124998747301463705507594240 612849837292577095680000000
Omega2 9 3 -1092383335406941791458175221760 -345133187859393097113600000000 612849837292577095680000000
Omega3 9 0 9500653180184877043200 38202012309716552908800 12767704943595356160
J0 12 3 96296338477971377220208656384000000000 116198364802726945918706130034989465600 26508059778292179478039756800000000
```


The original six-node order is \(b_*<0<t<s<a<1<z<c_*\) by the separate signed-node audit. Thus the denominators \(B_*(u_i)Z'(u_i)\) for the four old weights have the same signs \((-,+,-,+)\), so their actual weights are positive under those node guards. The two exterior weights' nonzero property still follows independently from \(D_\mu>0\) as in the existence audit; this certificate does not assert their signs or positive abscissae.

**What is still open.** These five signs need no further branch or pivot choice mathematically and can be encoded by one reusable tensor Bernstein identity plus the five finite coefficient arrays in Lean. The affine calibration endpoint signs remain completely separate; this work does not prove them or the exact real branch instantiation. Neither the symbolic coefficient check nor the saved script is a kernel-checked Lean theorem.
