# A compact ordinary-plateau law without recovering the ghost scale

**Scope.** In the fixed fully pivotable neighboring singleton width chart \(s=c_9=c_8\notin\{0,1,a,d\}\), take the actual two full plateau pairs, the two calibrated hulls, and their shared profile \(P=\gamma P_*, Q=\gamma Q_*\), \(\gamma\ne0\). The scalar identities are characteristic zero with the inherited width/tableau guards; the applications inherit their ordered-field proof of the mixed pivots. This is a more compact transverse law for the [live-cross finite-width result](ERK11-NONZERO-TEN-TWELVE-NEIGHBOR-K-LIVE-REGULAR-FINITE.md). It does not by itself enumerate or exclude the finite survivors.

## Recover the whole ordinary-measure numerator, not an inverse over eight roots

Let \(D_s\) be the monic hull of the eight active singleton labels (with the shared label \(s\) included once), \(\Omega=X(X-1)(X-a)(X-d)\), and \(\rho=J_0/(uv)=-b_9\Omega(s)\). Take \(R=\Omega Q_*\) and \(M_R(Z)=\int(R(X)-R(Z))/(X-Z)\). The ordinary quadrature paid to degree ten gives the polynomial numerator identity
\[
 \underbrace{D_s M_R-\rho Q_*(s)\frac{D_s}{X-s}}_{A(X)}
 +\gamma\underbrace{P_*^2 X(X-1)}_{B(X)}
 =Q_*\,\Omega D_s\sum_i\frac{b_i}{X-c_i}.
\]
Indeed the active singleton part of \(\sum b_i R(c_i)/(X-c_i)\) equals \(\gamma P_*^2 X(X-1)/D_s\) by partial fractions, since the singleton ordinary weight is \(\gamma P_*^2/(D'Q_*)\) and \(D=(X-a)(X-d)D_s\). The actual dormant row adds the separate negative \(\rho\) term, even though its clock is already among the singleton roots. The endpoints and the pair labels are killed by \(\Omega\), and the carrier weights cancel at their common clock. This proves the identity, not just its familiar remainder modulo \(Q_*\).

The quotient \((A+\gamma B)/Q_*\) is therefore \(\Omega D_s\sum b_i/(X-c_i)\). At a plateau \(x=a\) or \(d\), the right-hand side at \(X=x\) is \(\Omega'(x)D_s(x)B_x\), where \(B_x\) is the ordinary two-row weight. No evaluation division by \(Q_*(x)\) is used. If the plateau also equals an endpoint, \(\Omega'(x)=0\) and the displayed equality is still true: the actual ordinary measure has a simple pole at the pooled clock, and the factor \(\Omega\) has a double zero, so both sides give zero regardless of the endpoint share. Thus this step does not demand a separate \(x\notin\{0,1\}\) condition.

## An affine equation in the common scale

For \(x\in\{a,d\}\), let \(y\) be the other plateau, \(D'(x)=(x-y)D_s(x)\), and set
\[
 p=P_*(x),\quad q=Q_*(x),\quad t=B_{\tau,*}(x),\quad
 g_x=M_R(x)-\rho Q_*(s)/(x-s).
\]
The paid third interpolant normalized by the same scale satisfies \(P_* B_{\tau,*}-Q_*^2=\lambda_* D_s\). The ordinary numerator read above says
\[
 q\,x(x-1)D'(x)B_x=D_s(x)g_x+\gamma p^2x(x-1).
\]
The actual first state of the calibrated pair is \(f_a=-a^2/2\) on the left and \(f_d=-4Q_*(e)/P_*(e)\) on the right, where \(e=1-b/2\). The right formula follows because the reflected half-clock state is \(b^2/8\) and the reflected plateau state is \(-b^2/2\), and both use the same reflection scale. The half-clock \(P_*(e)\) is live.

The two-row condition on the ordinary mass and three response pools is, after clearing their live common scale,
\[
 (q-fp)^2-\left(p-\frac{fD'(x)B_x}{\gamma}\right)(t-fq)=0.
\]
Multiply through by \(\gamma q x(x-1)\) and use the numerator read. The cancellation
\[
 q\bigl[(q-fp)^2-p(t-fq)\bigr]+fp^2(t-fq)
 =(q-fp)(q^2-pt)
\]
and the third model identity give, after removing only \(D_s(x)\ne0\),
\[
 \boxed{ f(t-fq)\,g_x-\gamma\lambda_* x(x-1)(q-fp)=0. }
\]
This holds even when \(P_*(x)=0\), \(Q_*(x)=0\), or \(x\) is an endpoint. It uses the actual two rows, not a second-pool projectivity. It does not divide by a ghost remainder coefficient or compute \(B_x\) via singleton inverses.

## Compact polynomial form with no cubic-response reconstruction

For a polynomial \(H\) of degree at most \(m\), let \(H^{[m]}(U,V)=\sum_j H_j U^j V^{m-j}\). Write \(P_*=p_0+p_1X\) and
\[
 D_\lambda=D_s^{[8]}(-p_0,p_1),\qquad
 L_\lambda=-\bigl(Q_*^{[4]}(-p_0,p_1)\bigr)^2 .
\]
The true \(D_\lambda\) is live. If \(p_1\ne0\), the root of \(P_*\) cannot be a singleton and evaluation gives \(\lambda_*D_\lambda=L_\lambda\). If \(p_1=0\), the same equality follows by comparing degree-eight coefficients; \(p_0\ne0\) and \(D_s\) is monic. Thus no degree-one guard is needed for this homogeneous formula.

Multiply the boxed equation by \(p(x-s)D_\lambda\); replace \(p(t-fq)=q(q-fp)+\lambda_*D_s(x)\). Define
\[
 \begin{split}
 u_x &= f\,[D_\lambda q(q-fp)+L_\lambda D_s(x)]
             \bigl((x-s)M_R(x)-\rho Q_*(s)\bigr),\\
 v_x &=-L_\lambda(x-s)x(x-1)p(q-fp).
 \end{split}
\]
Then \(u_x+\gamma v_x=0\). This can be weaker at \(p=0\); the boxed law is the precision fallback there. For the ghost equations set \(r_j=[X^j](A\bmod Q_*)\), \(s_j=[X^j](B\bmod Q_*)\). Thus the true scalar tests include
\[
 u_x s_j-v_x r_j=0\quad\text{for every remainder index }j,\qquad
 u_a v_d-u_d v_a=0 .
\]
No scale pivot is canceled. One may clear the model leading coefficient in a fixed-degree pseudo-remainder implementation; loss of its degree remains a separate guard if using the generic representation.

## Independent exact right-plateau witness

Use the same exact coefficient witness \((p,a,b)=(17,7,7)\) on the irreducible first-pool curve \(F=0\) as in the live-cross finite-width proof. There \(K_0=12\bmod17\), both pool projectivities pass, and \(D_s'(s)=0\) in the residue only. The short companion starts with the verified fitted profiles from that proof. It obtains \(D_\lambda=14,L_\lambda=13\), and at the right plateau \(x=d=11\), \((f,p,q)=(5,2,11)\), \(u_d=15,v_d=4\). The constant ghost coefficients are \(r_0=3,s_0=1\), so the independent cleared mark is
\[
 u_d s_0-v_d r_0=3\bmod17\ne0.
\]
There is no cubic-response reconstruction, no inverse modulo \(D_s\), and no division by the constant ghost coefficient in this mark. The left version with the extra \(p\) factor vanishes at this residue because \(P_*(a)=0\), rather than pretending the right and left marks are both independently nonzero there. The earlier finite-width conclusion stands, and the new law is a smaller polynomial expression for a future explicit elimination.
