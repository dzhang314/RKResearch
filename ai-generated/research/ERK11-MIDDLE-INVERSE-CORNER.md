# Opposite-corner inverse Gram test of the four-carrier chart

Assume the [six–five–six four-carrier reductions](ERK11-FOUR-CARRIER-MIDDLE-GATES.md)
with **both** boundary middle clocks new. This includes the entire stated
ordered-field branch, but the proof uses no ordering. Set
\(z=c_6/\theta\), \(t=(1-c_{12})/(1-\theta)\). The new neighbors are
\(x=(7z-8)/(6z-7)\), \(y=(7t-8)/(6t-7)\), respectively. The paid
chronology has \(z,t\notin\{0,1/2,1\}\), and \(x\notin\{0,1/2,1,z\}\)
with the reflected guards for \(y\). Define
\[
 \alpha(z)=-\frac{(z-1)^2}{z(7z-8)},\quad
 P(X)=330X^4-480X^3+216X^2-32X+1,\quad
 D(q)=35(1980q^4-1344q^3+324q^2-32q+1).
\]
Then an actual chart necessarily satisfies the following condition,
independent of the unknown middle rows 8, 9, 10 and of the adjoint
scale:
\[
 \alpha(z)\alpha(t)+P(1-\theta)\alpha(z)
             +P(\theta)\alpha(t)+D(\theta(1-\theta))=0 .
\]
In particular if \(\theta=1/2\),
\((\alpha(z)-3/8)(\alpha(t)-3/8)=11/16\).
This adds a finite condition, not an exclusion of the entire branch.

Use the actual stage evaluations \(L,R\) of the two anchored lifts at
middle physical stages 7–11, with columns indexed by bases \(X^n\) and
\((1-X)^m\) respectively (\(1\le n,m\le5\)). Let
\(H_{n,m}=n!m!/(n+m+1)!\), \(B_M=\operatorname{diag}(b_7,\dots,b_{11})\).
The paid rooted tests give \(L^\mathsf T B_M R=H\).
The integer matrices \(W=27720 H\) and \(N=H^{-1}/210\) below satisfy
\(WN=132I\), so \(H\) and both middle evaluation matrices are invertible
with only paid pivots. Thus \(R H^{-1}L^\mathsf T=B_M^{-1}\); the
opposite-corner entry (physical 11,7) is zero.

To calculate that corner, let \(U\) be the functional of the actual
left-zero lift read at row 7, expressed in normalized \(X=c/\theta\).
The interpolation nodes are \(1/2,1,z\); their clean values
are \(1/8,-1/2,F(z)\), with \(F(X)=X^2(1-X)\). At their new successor
\(x\) the clean value is \(F(x)\).
Let \(\ell_1(X)\) denote the quadratic Lagrange cardinal of node 1 and
put \(S=-F(x)\ell_1(x)\ne0\).
For \(2\le n\le5\), write
\(X^n=X^2-F(X)J_n(X)\); here \(\deg J_n\le2\), \(J_n(1)=n-2\)
(including \(J_2=0\)). The lift of \(-F J_n\) cancels by clean
interpolation except at the node 1, where \(F(1)=0\) and the actual
clean value is \(-1/2\). Thus \(U(X^n)=U(X^2)+(n-2)S\).
The literal zero of the unary lift of \(P_0=X^2(X-1)^2\) at this
row says \(U(X^5/5-X^4/2+X^3/3)=0\), so \(U(X^2)=2S\).
Put \(\alpha=U(X)/S-1\); we obtain \(U(P)=S(P'(1)+\alpha P'(0))\)
for every model polynomial with \(P(0)=0\) and degree at most five.
The earlier grade-four alias \(P_1=X(X-1)(X-1/2)(X-z)\) is zero at
all interpolation nodes, with \(U(P_1)=P_1(x)\). Since
\(P_1(x)/S=(1-z)/(2x)\), the ratio is
\[
  \alpha=\frac{(z-1)(1-x)}{xz}
         =-\frac{(z-1)^2}{z(7z-8)}.
\]
All cancelled factors are explicit in the new-clock guard. The reversed
argument gives the same functional with \(z,x\) replaced by \(t,y\).
After scaling back to physical coordinates and removing the nonzero
factors \(\theta S\) and its reflected counterpart, the two corner rows
are \((1+\alpha(z),2\theta,3\theta^2,4\theta^3,5\theta^4)\) and
\((1+\alpha(t),2(1-\theta),3(1-\theta)^2,4(1-\theta)^3,5(1-\theta)^4)\).

For reproducibility, the integer matrices are
\[
 W=\begin{pmatrix}
4620&2310&1386&924&660\\
2310&924&462&264&165\\
1386&462&198&99&55\\
924&264&99&44&22\\
660&165&55&22&10
\end{pmatrix},\quad
 N=\begin{pmatrix}
1&-16&72&-120&66\\
-16&248&-1080&1740&-924\\
72&-1080&4560&-7140&3696\\
-120&1740&-7140&10920&-5544\\
66&-924&3696&-5544&2772
\end{pmatrix}.
\]
Multiply the two rows against \(N\): the coefficient on their product
of endpoint adjustments is 1, and the other terms are exactly the three
polynomials in the displayed condition. The integer inverse check,
this expansion, and its half-clock specialization are checked in
`ERK11MiddleInverseGate.lean`. The literal lift identities,
rooted tests and matrix argument are mathematical, not native RK
Lean claims.
