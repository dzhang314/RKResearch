# The independent first-ghost mark collapses the old affine-slope-minus-one profile

**Result.** In the normalized invisible-six DIRK11/13 no-late chart
with a genuine first reverse gap, the old affine slope \(\ell_1=-1\)
forces the direct, noncontact \(F_n\) profile. In particular the
apparently separate direct \(F_1\) profile is impossible in the
live reciprocal \(\alpha=1,\ \beta=1,2\) counts, by the
[exact direct Fn slope-minus-one exclusion](../dirk11-thirteen-invisible-six-alpha-one-direct-fn-minus-one/README.md).
The exceptional \(r=0\) and denominator-loss cases are ruled out
before using any middle ghost or value of a diagonal at \(V,B\).
The argument works over characteristic-zero fields and is not a
whole DIRK11 stage exclusion.

## 1. The true extra paid first-ghost mark

Use the
[literal early-ghost calculus](../dirk11-thirteen-invisible-six-alpha1-five-zero/README.md)
and
[old-profile census](../dirk11-thirteen-invisible-six-early-profile-census/README.md).
The true reverse prefix is \(T,v,u,w,z\).
Write \(W(f)=b_{\rm wt}f(Y)\), \(Y=1-c\),
\(N=A^{\mathsf T}\) in reverse order, and
\(R=Y^3+c_2Y^2+c_1Y+c_0\) for the old three clocks.
The quadratic representative \(m=G/(Yb_{\rm wt})\bmod R\)
has only live values there; put \(P=Ym\), \(P_0=YR\) and
\(P_1=YP-\kappa P_0\) with \(\kappa=[Y^2]m\).
These three comparator columns match the terminal and old donor
samples exactly where used. The true first ghost has zero weight,
\(G_z\ne0\), and literal diagonal \(d_z=0\), and
\(\ell(z)=W_0(z)=0\) where \(W_0=IP_0/P\bmod R\).
Here \(\ell=IP/P\bmod R\), \(\rho=I^2P/P\bmod R\).
The separate true marked fit is
\[
 N(YG-W(P_1))
   =G(Y\ell-\rho-\kappa W_0)-W(IP_1).
\]
At \(z\) its left side is zero: the old and terminal differences
are exactly zero, and its own column has diagonal zero. The
weighted primitive is also zero there. Consequently \(\rho(z)=0\).
When \(\ell_1=-1\), this is **not** a consequence of the usual
integration-by-parts identity
\((1+\ell_1)\rho=\ell^2+\delta W_0\).

## 2. Integer coefficient certificate for the bridge

At slope \(-1\), the lower-degree and monomial old fits are not
possible by the exact affinity census. Scale the old quadratic
to \(m=Y^2+rY+s\). With \(\ell=z-Y\), the literal polynomial
identity \(IP=\ell P+\frac54 P_0\) gives
\[
 c_2=(16r-12z)/15,\quad c_1=(18s-12zr)/15,\quad
 c_0=-4zs/5.
\]
In particular \(s,z\ne0\) since \(c_0\ne0\).
Set \(D=2r^2-9s\), \(R_c=15R\), and
\[
 \begin{aligned}
 T&=60I^2P/Y=10sY^2+5rY^3+3Y^4,\\
 Q&=(-9r^2+48s)Y^2+(8r^2z+3rs-42sz)Y-2rsz.
 \end{aligned}
\]
The exact integer polynomial identity is
\[
 D T-6mQ=R_c\big((4r^2-21s)Y-rs\big).
\]
It has no scale or leading-factor exception.
Also \(m(-2r/3)=-D/9\) and \(R_c(-2r/3)=4(r+z)D/3\);
thus if \(D=0\), \(m\) would vanish at an old root, impossible.
The live old \(m\) values and the integer certificate give
\(10D\rho=Q\), as a degree-at-most-two identity.
Evaluate at \(z\):
\[
 10D\rho(z)=-z\big(z(r^2-6s)-rs\big).
\]
The true \(\rho(z)=0\) and \(z\ne0\) force
\(z(r^2-6s)=rs\). The coefficient identities then give
\[
 r(c_1+6s)=6c_2s.
\]
If \(r=0\), this forces \(c_2=0\), hence \(z=0\) by its
coefficient formula, impossible. Also
\(16rs=15(c_2s-c_0)\), so the old noncontact factor is live.

If \(c_1+6s\ne0\), the last relation is the direct \(F_n\)
ratio, with \(c_2\ne0\). The old affinity equation multiplied
by \((c_1+6s)^2\) gives \(3s F_n(s)=0\) on that ratio,
so it is genuinely the full direct \(F_n\) chart.
The ordinary and coefficient proofs do not assume any value
for the carrier parameter or use a reflection of the old profile.

## 3. The ratio-loss case is a pure ordinary contradiction

If \(c_1+6s=0\), then \(c_2=0\). The same coefficients give
\[
 z=4r/3,\quad s=4r^2/27,\quad c_1=-8r^2/9,\quad
 c_0=-64r^3/405,\quad 225c_0^2+8c_1^3=0.
\]
The actual ordinary quintic is the Jacobi pencil
\(T_5=(J_5+\mu J_4)/132\). Recover \(\mu=-J_5(V)/J_4(V)\),
deflate at the distinct regular \(V,B\), and express the old
coefficients \(c_j\) using its live common leader \(132J_4(V)\).
**clock.py** projects the two just-derived ordinary conditions
separately. Removing only rational content and, for the second
condition, \(J_4(V)^3\), their exact resultants in \(B\) are
nonzero constants times \(J_4(V)^2 f_{12}\) and
\(J_4(V)^6 f_{36}\). The two remaining polynomials are coprime
over \(\mathbb Q\); \(J_4(V)\ne0\) at any actual ordinary
clock. Thus the ratio loss is impossible without using
\(\beta=1\) or \(2\).

This proves the old-profile bridge in all stated counts.
For \(\beta=1,2\) the existing degree-60 slope-minus-one
certificate now covers direct \(F_1\) as well. The
[five-prefix extension](../dirk11-thirteen-invisible-six-alpha-one-slope-minus-one-beta-zero/README.md)
applies in the live \(\beta=0\) count.

**Replay.** Run **python3 old-fit.py** and **python3 clock.py**
with SymPy and python-flint 0.9. The latter accelerates the
exact projected factorization. This packet states the actual
rooted ingress and verifies the complete integer coefficient
certificate in source.
