# Universal late fourth clock pin and the consecutive fifth split

**Results.** In the normalized characteristic-zero DIRK11/13
[four-marked-pair plus slack chart](../dirk11-thirteen-invisible-local-slack-chronology/README.md)
with the slack after the fourth weighted nonendpoint reverse debut,
the monic old cubic \(P=Ym\) has
\(m(X)=X^2+rX+r^2/(r+6)\) in \(X=Y/V\) coordinates.
This is a consequence of the actual fourth primitive and does not
assume a particular next row. If the immediate next row is the
distinct fifth \(B\), then its diagonal is live even if \(G_B=0\).
With live \(G_V\), the clean coefficient \(\theta\) is zero
exactly when the actual fifth \(G/b_{\rm wt}\) matches the
four-site weighted interpolant \(\widehat P\) defined below.
This is a necessary decomposition, not a new exclusion or a change
to unrestricted real DIRK11 **13–14**.

## 1. Universal second primitive at the fourth

Use \(Y=1-c,\ N=A^{\mathsf T}\) in actual reverse chronology,
\(W(U)=b_{\rm wt}U(Y)\), zero-constant primitive \(I\), and
the genuine reflected cubic \(G\) in the common monic gauge.
The
[late first-completion result](../dirk11-thirteen-invisible-local-late-early-completion/README.md)
gives literal prefix \(T,v,u,w,V\). No marked completion or
silent slack preceded \(V\), the fourth is a true mismatch
with \(d_V=0\), and its four actual old/fourth weighted
primitive samples are paid.
Write \(R=(Y-v)(Y-u)(Y-w)\), \(P_0=YR\), \(P=Ym\),
\(D_0=G-W(P)\), \(\mathcal C=YN-NY-N^2\).
The actual fits are
\[
 ND_0=G\ell-W(IP),\qquad
 N(YD_0)=G(Y\ell-\rho)-W(I(YP)),\qquad
 NW(P_0)=W(IP_0)-GW_0,\qquad \mathcal C D_0=0 .
\]
Here \(\ell\) is affine with slope \(\lambda\), and
\(IP=\ell P+\delta P_0,\ \delta=1/4-\lambda\ne0\).
The two degree-at-most-two interpolants \(\rho,W_0\) use
the actual \(I^2P/P,IP_0/P\) values at the three old clocks.
At the actual fourth
\[
 k_V\ell(V)=IP(V),\quad k_V\rho(V)=I^2P(V),\quad
 k_VW_0(V)=IP_0(V),\quad e=\ell(V)\ne0 .
\]
These do not divide by \(k_V=G_V/b_{{\rm wt},V}\).

Define affine \(\Psi=(I^2P-\rho P)/(\delta P_0)\):
its numerator vanishes at zero and the three old clocks
and has degree at most five. Set \(F=IP/Y,\ J=I^2P/Y\).
Then
\[
 J=\Psi F+\Xi m,\qquad \Xi=\rho-\Psi\ell .
\]
Indeed \(F-\ell m=\delta R\). The constant equation yields
\(m(0)\ne0\) and \(\ell(0)\ne0\) since \(\delta R(0)\ne0\).
The old \(m\) values are live, hence \(m,R\) are coprime:
\(F\bmod m\) is invertible.
In any coordinate with \(P\) monic, for \(m=Y^2+rY+s\)
the exact formulas (checked in **identities.py**) are
\[
 \Psi(Y)=\frac{(4r^2-21s)Y-rs}{5(2r^2-9s)},\qquad
 \Xi(Y)=-\frac{Y[(r^2-6s)Y-rs]}{10(2r^2-9s)} .
\]
The multiplication determinant of \(F\bmod m\) is
\(-s^2(2r^2-9s)/144\), paying every factor in these expressions.

At the fourth, \(I^2P(V)=k_V\rho(V)\) and
\(\ell(V)(k_V-P(V))=\delta P_0(V)\).
Thus \(\Psi(V)=\rho(V)/\ell(V)\), i.e. \(\Xi(V)=0\).
Scale \(X=Y/V\), with \(N,G\) scaled by \(1/V,1/V^3\)
respectively and the old interpolant still monic.
Then \(\Xi(1)=0\) gives \(r^2=(r+6)s\).
Since \(s\ne0\), \(r\ne0,-6\); also \(2r+3\ne0\)
by the determinant guard.
In this normalized coordinate the exact identities become
\[
 \Psi(X)=\frac{(4r+3)X-r}{5(2r+3)},\qquad
 \Xi(X)=\xi\,X(X-1),\quad \xi=-\frac r{10(2r+3)}\ne0 .
\]
This proof did not use any condition on the affine slope
or on subsequent completions. It works even in the absent
fourth prefix before that separate exclusion.

## 2. Consecutive fifth: true diagonal liveness and companion dichotomy

Continue in normalized coordinates (fourth now 1) and let
\(b=B/V\ne0,1\). Suppose fifth is the next literal row.
If \(d_B=0\), the actual \(\mathcal C D_0\) there forces
the tap from \(V\) to \(B\) to be zero:
\(D_0\) had first nonzero support at \(V\), all earlier
\(ND_0\) is zero, and the commutator is
\((b-1)N_{B,V}D_{0,V}\) in this branch.
Thus \(ND_0,N(XD_0)\) also vanish there.
The two paid scalar fits give \(k_B\ell(b)=IP(b)\) and
\(k_B\rho(b)=I^2P(b)\); consequently
\(\Xi(b)(k_B-P(b))=0\) by the \(\Psi,\Xi\) identities.
But \(\ell(b)(k_B-P(b))=\delta P_0(b)\ne0\) from the
actual affine fit. This contradicts \(\Xi(b)\ne0\).
Therefore \(d_B\ne0\) whether or not the fifth \(G\) is live.

Let \(\Delta=\delta/e\),
\(\widehat P=P+\Delta P_0\),
\(\widehat D=D_0-\Delta W(P_0)\).
Its literal prefix through fourth is zero; put
\(f=k_B-\widehat P(b)\).
The two actual commutators \(\mathcal C\widehat D
=-\Delta\mathcal C W(P_0)\) and
\(\mathcal C[(X-1)D_0]\) belong to
\(Z_6=G\mathcal P_3+K_{\rm coeff}H\), and vanish
through the fourth. This is the true budget \(4+6+1=11\)
on weighted parts and the single clock mark pairing \(G\)
only against \(E_7\). Their zero-prefix subspace is a line:
the four distinct live \(G\) weighted debuts determine a
unique cubic multiplied by the companion coefficient
\(\theta\) (the actual \(H/G\) samples on each).
In particular \(\theta=0\) implies the entire commutator
\(\mathcal C W(P_0)=0\), not merely its fourth read.

At \(B\), \((\mathcal C\widehat D)_B=-d_B^2 b_{{\rm wt},B} f\).
Thus \(\theta=0\) implies \(f=0\).
Conversely if \(f=0\) then
\(D_{0,B}=b_{{\rm wt},B}\Delta P_0(b)\ne0\), and
\(\mathcal C[(X-1)D_0]_B=-d_B^2(b-1)D_{0,B}\ne0\).
It spans the same zero-prefix line. The vanishing
\(\mathcal C\widehat D_B\) then proves \(\mathcal C\widehat D=0\)
globally and \(\theta=0\).
Thus \(\theta=0\) if and only if \(f=0\).
If \(f\ne0\), the true common-line ratio gives the
matched commuting column
\[
 D=(X-a)D_0-q W(P_0),\quad
 a=1+(b-1)(k_B-P(b))/f,\quad q=(1-a)\Delta ,
\]
with zero prefix through \(B\).
This branch does not preclude a later numerical contact at \(a\).

## 3. Exact scalar handles for the matched fifth

When \(\theta=0\) the entire \(\widehat D\) commutes and
vanishes through fifth. Its true \(N\)-fit is
\(N\widehat D=G K_0-W(I\widehat P)\) with \(K_0=\ell+\Delta W_0\).
At the actual fifth this means \(k_B=\widehat P(b)\) and
\(k_BK_0(b)=I\widehat P(b)\).
The polynomial integration-by-parts identities
\((1+\lambda)\rho=\ell^2+\delta W_0\) and
\((1+\lambda)I^2P=\ell IP+\delta IP_0\) give
\[
 \begin{aligned}
 eK_0&=\ell[(1+\lambda)\Psi-\lambda(X-1)]+(1+\lambda)\Xi,\\
 eI\widehat P&=IP[(1+\lambda)\Psi-\lambda(X-1)]+(1+\lambda)\Xi P .
 \end{aligned}
\]
Insert the live \(k_B-P(b)=\Delta P_0(b)\) and the
actual \(g_B=k_BK_0(b)-I\widehat P(b)=0\).
The resulting necessary cleared equation is
\[
 2\lambda(1+\lambda)((4r+3)b-r)
 -10(2r+3)\lambda^2(b-1)-(1+\lambda)r b=0 .
\]
It independently forbids slopes \(0,-1\) in this
matched branch. For the normalized old scalar cubic
\(R=X^3+c_2X^2+c_1X+c_0\), the previous exact affine
identity and \(s=r^2/(r+6)\) give
\[
 (r+6)(r+3)c_0-r(r+6)c_1+3r^2c_2-2r^3=0,\quad
 \delta=\frac{r^3}{4U},\quad U=r(r+6)c_1-r^3-(r+6)^2c_0\ne0 .
\]
The ratio follows from the linear-in-\(X\) affine
coefficient and uses only \(r,s,\delta\) live.
These exact gates are useful for the remaining matched
case but do not themselves imply it impossible.

**Replay:** run **python3 identities.py** with SymPy.
It reconstructs the exact second-primitive and coefficient
identities above. Actual reverse rank and literal pivots
are the written proof; no new native theorem is asserted.
