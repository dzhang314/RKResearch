# Reverse kernel columns across the first two gap transitions

**Result and scope.** Take the normalized no-late invisible-six DIRK11/13
chart over a characteristic-zero field, with the live reciprocal
multiplier, one first-gap ghost \((\alpha=1)\), and at least one middle
ghost \((\beta\ge1)\). The first literal middle ghost has zero diagonal
and is the root of a genuine affine polynomial with live leader.
For \(\beta=1\), the first literal ghost after the fifth regular reverse
row also has zero diagonal and satisfies an additional affine clock
gate. No direct/alternate old-profile assumption or division by a
diagonal is required. Ghost and unrelated regular clocks may coincide.
These are scoped restrictions; the unrestricted real stage interval
stays **13–14**.

Use the true order spaces from the
[early census](../dirk11-thirteen-invisible-six-early-profile-census/README.md),
[live old-profile calculus](../dirk11-thirteen-invisible-six-alpha-one-live-cubic/README.md)
and [first-middle gate](../dirk11-thirteen-invisible-six-alpha-one-live-first-middle/README.md).
Write \(Y=1-c\), \(N=A^{\mathsf T}\) in literal reverse order,
\(W(f)=b_{\rm wt} f(Y)\), \(I\) for the zero-constant primitive,
and \(H=H_{\rm bary}\) for the clean barycentric row. The prefix is
\(T,v,u,w,z,V,x\); when \(\beta=1\) it continues \(B,y\). Here
\(z,x,y\) are distinct literal zero-weight ghosts; \(v,u,w,V,B\)
are the five distinct nonendpoint ordinary clocks with live weights.
At the terminal \(Y_T=0\) and \(G_T=H_T=0\). The live reciprocal
samples are \(H/G=U_r\) at the ordinary sites and \(H=0\), \(G\ne0\),
\(U_r\ne0\) at the ghost sites. Here \(U_r\) has degree at most three.

## 1. A true reverse column and its first literal pivot

Set \(R=(Y-v)(Y-u)(Y-w)\), \(P_0=YR\), \(P_5=(Y-V)P_0\),
and \(P=Ym\) from the old interpolation, so \(W(P)=G\) on the
literal terminal and old triple. Put \(k=G_V/b_V\) and
\[
 K_*=\frac{(V-z)(k-P(V))}{P_0(V)},\qquad
 Q_4=(Y-z)P+K_*P_0,\qquad D=(Y-z)G-W(Q_4).
\]
Here \(P_0(V)\ne0\), but \(V-z\) has not been divided by.
The column \(D\) vanishes through \(V\): the terminal and old
fits are exact, its zero-weight entry at \(z\) is killed by
the mark, and the \(V\) cancellation is the definition of \(K_*\).
Its next literal coordinate is \(D_x=(x-z)G_x\ne0\).

Let \(\mathcal R=CA-AC-A^2\) and
\(\mathcal C=YN-NY-N^2=\mathcal R^{\mathsf T}\).
The actual \(\mathcal C D\) belongs to
\(Z_6=G\mathcal P_3+H K_{\rm coeff}\).
The weighted part tests only
\(\mathcal R E_4\subset F_6\) with charge \(4+6+1=11\).
The \(G\) part pairs \(G\in E_7^\perp\) with
\((Y-z)\mathcal R E_4\subset E_7\).
The terminal coordinate is zero by literal lower triangularity.

Evaluation on the prefix through \(V\) is injective on \(Z_6\).
If \(GQ+\theta H\) is zero there, the old triple gives
\(Q+\theta U_r=\mu R\) with constant \(\mu\). Its \(V\)
entry gives \(\mu=0\), and \(Q(z)=0\) on the ghost \(z\)
then gives \(\theta=0\), since \(U_r(z)\ne0\).
By triangularity \(\mathcal C D\) vanishes through \(V\)
and hence globally. At its first supported input row \(x\),
its literal value is \(-d_x^2D_x\): \(YN-NY\) has zero
diagonal and \(N^2\) has diagonal \(d_x^2\).
It follows that \(d_x=0\).

## 2. The affine fit actually has a live leader

Write \(\ell=IP/P\bmod R\), \(\rho=I^2P/P\bmod R\) and
\(W_0=IP_0/P\bmod R\), where the polynomial \(Y\) factor
cancels before using the live old \(m\) values. The old
affine \(\ell\) and quadratic-or-lower \(\rho,W_0\) satisfy
the genuine whole-row fits
\[
 \begin{aligned}
 N(G-W(P))&=G\ell-W(IP),\\
 N(YG-W(P_1))&=G(Y\ell-\rho-\kappa W_0)-W(IP_1),\\
 NW(P_0)&=W(IP_0)-G W_0 ,
 \end{aligned}
\]
where \(P_1=YP-\kappa P_0\) and \(\kappa=[Y^2]m\).
The exact integration-by-parts formula
\(IP_1=YIP-I^2P-\kappa IP_0\) gives
\[
 ND=G L-W(IQ_4),\qquad L=(Y-z)\ell-\rho+K_*W_0 .
\]
The two ghost reads yield \(L(z)=L(x)=0\), because \(ND\)
vanishes through \(V\) and also at \(x\) by \(d_x=0\).
If \(L=0\), \(IQ_4\) is zero at the four distinct live
weighted sites \(v,u,w,V\), and at the polynomial origin.
It has degree at most five, hence is a scalar times \(P_5\).
But its derivative at 0 is \(Q_4(0)=0\), whereas
\(P_5'(0)=-V R(0)\ne0\), forcing \(IQ_4=0\) and \(Q_4=0\).
This contradicts \(Q_4(r)=(r-z)P(r)\) at the three distinct
old roots \(r\), since all their \(P(r)\) are live.
Thus
\[
 L=\lambda(Y-z)(Y-x),\qquad \lambda\ne0 .
\]
In particular \(L/(Y-z)\) is exactly affine even when the
old affine slope is \(-1\) or another apparent leader drops.

The same four weighted sites and the polynomial origin,
applied to \(IQ_4-\lambda(Y-x)Q_4\), now give
\[
 IQ_4=\lambda(Y-x)Q_4+\eta P_5,\qquad
 \eta=(1/5-\lambda)[Y^4]Q_4 .
\]
This compares leaders without dividing by that of \(Q_4\).
Equivalently \(ND=\lambda(Y-x)D-\eta W(P_5)\).
Also \(\eta=0\) iff \(x=0\): for \(x=0\) the left and
matched terms vanish to order at least two at zero,
while \(P_5\) has a simple root; if \(\eta=0\) and
\(x\ne0\) the two sides would have different orders at
zero, since \(Q_4\ne0\) and \(\lambda\ne0\).

## 3. Another pivot and affine gate after the fifth regular row

Assume \(\beta=1\), so \(B\) immediately follows \(x\) and \(y\)
immediately follows \(B\). Set
\[
 \omega=\frac{(B-x)D_B}{W(P_5)_B},\qquad
 E=(Y-x)D-\omega W(P_5).
\]
The denominator is live by the genuine weight and distinct
ordinary clock at \(B\); \(B-x\) is not divided by.
The new column is zero through \(B\) including \(x\),
and \(E_y=(y-x)(y-z)G_y\ne0\).

The true \(\mathcal C E\) lies in
\(Z_7=G\mathcal P_4+H\mathcal P_1\): the weighted part
has degree at most five (charge \(5+5+1=11\)),
and the \(G\) part multiplies \(\mathcal R E_3\subset F_5\)
by at most two marks, hence pairs only with \(E_7\).
On a zero-prefix element, its five ordinary samples
force \(Q+\Theta U_r=0\) identically by degree four.
The ghost samples \(z,x\) then force the affine
\(\Theta=0\). By triangularity \(\mathcal C E=0\),
and \(-d_y^2 E_y=0\) gives \(d_y=0\).

Let \(Q_5\) be the actual polynomial in
\(W(IP_5)-NW(P_5)=GQ_5+\theta H\), with
\(\deg Q_5\le3\). The weighted zero prefix forces roots \(z,x\).
From \(\mathcal C D=0\) and the formula for \(ND\) one gets
\[
 (1+\lambda)N((Y-x)D)=(Y-x)ND+\eta NW(P_5).
\]
No \(1+\lambda\) is inverted. At \(y\), \(NE_y=0\),
and \(NW(P_5)_y=-G_y Q_5(y)\). It follows that
\[
 \lambda(y-x)=\nu\left(\frac{Q_5}{(Y-z)(Y-x)}\right)(y),
 \qquad \nu=\eta-(1+\lambda)\omega .
\]
Only the two distinct ghost differences and \(G_y\) were
cancelled. In particular \(\nu\ne0\) and \(Q_5(y)\ne0\).
The affine equation may be an identity; uniqueness of \(y\)
is not asserted. At \(B\), with \(e=D_B/W(P_5)_B\),
the same transfer gives
\[
 d_B[(1+\lambda)(B-x)e-\eta]
     =(B-x)[\lambda(B-x)e-\eta].
\]
The coefficient of \(d_B\) is \(-\nu\), now known live.
If \(d_B\ne0\), then \(B\ne x\): a coincidence would give
\(\eta=0\), hence \(x=0\), contrary to \(B\ne0\).

A further genuine test uses the same quintic weight input,
whose only weighted donor at \(y\) is the physical row \(B\).
If \(\mathcal C W(P_5)=GQ_c+H\Theta\), then
\[
 (y-B-d_B)Q_5(y)+Q_c(y)=0 .
\]
Here \(\Theta\) is affine and \(Q_c\) is degree at most four.
Because the row is zero on the old triple and \(V\), there is
a scalar \(\chi\) with
\[
 Q_c=\chi(Y-V)R-\Theta U_r,\qquad
 \chi J_4(B)=-d_B^2 U_r(B).
\]
At \(z,x\), \(Q_c=0\) by the same true weighted prefix;
these determine the two values of \(\Theta\) without a
division by \(\chi\). Thus the test is quadratic after
dividing both polynomial factors \(Y-z,Y-x\). This is
a separate additional necessary gate, not a global closure.

The rooted grade ingress and new parameter restrictions
above are exact written arguments. A separate Lean
adapter can check the literal commutator and scalar pivots;
this source-only receipt does not claim an audited
end-to-end Lean tableau theorem.
