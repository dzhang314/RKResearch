# The late mismatched fifth cannot be headless or be followed by a fourth/fifth return

**Scope.** In the normalized characteristic-zero DIRK11/13
[four-marked-pair plus silent slack chart](../dirk11-thirteen-invisible-local-slack-chronology/README.md),
consider the remaining late prefix with consecutive distinct weighted fourth
and fifth debuts \(V,B\), live \(G_V\), and both mismatches established in
the [fourth pin](../dirk11-thirteen-invisible-local-late-fourth-pin/README.md)
and [matched-fifth exclusion](../dirk11-thirteen-invisible-local-late-matched-fifth/README.md).
Then the fifth **must** have \(G_B\ne0\), and neither a marked nor a
silent immediate next row may reuse the fourth or fifth numerical clock.
The other possibilities with live \(G_B\) are not ruled out here: an old
clock (marked completion or silent reuse), or a silent origin. This holds
over characteristic zero without ordering. It is not a new unrestricted
DIRK11 stage bound (real interval **13–14**).

## 1. Fifth scalar from actual lower-triangular rows

Use the actual reverse \(N=A^{\mathsf T}\), gauge \(X=Y/V\), \(z=V\)
literal and \(b=B/V\) normalized. The first three old weighted debuts have
distinct normalized clocks \(v_1,v_2,v_3\), monic hull \(R\), common
monic head fit \(P=Xm\), and \(P_0=XR\). The nonzero fourth is at \(X=1\).
Write \(W(Q)=b_{\rm wt}Q(X)\) and \(\mathcal C=XN-NX-N^2\).
Use the true fits and prior scalar pin
\[
\begin{aligned}
D_0&=G-W(P),& ND_0&=G\ell-W(IP),\\
N(XD_0)&=G(X\ell-\rho)-W(I(XP)),&
NW(P_0)&=W(IP_0)-GW_0,\\
\mathcal C D_0&=0,& IP&=\ell P+\delta P_0.
\end{aligned}
\]
Here \(I\) is zero-constant primitive, \(\ell\) affine of slope \(\lambda\),
\(\delta=1/4-\lambda\ne0\), \(e=\ell(1)\ne0\), \(\Delta=\delta/e\).
In the normalized fourth pin,
\[
m=X^2+rX+r^2/(r+6),\quad r(r+6)(2r+3)\ne0,\qquad
\Psi=\frac{(4r+3)X-r}{5(2r+3)},\quad
\Xi=\xi X(X-1),\quad \xi=-\frac{r}{10(2r+3)}.
\]
The exact old polynomial identities are
\(\rho=\Psi\ell+\Xi,\ I^2P=\Psi IP+\Xi P\) and
\((1+\lambda)\rho=\ell^2+\delta W_0\); none divides by \(1+\lambda\).

Let \(\widehat P=P+\Delta P_0,\ \widehat D=D_0-\Delta W(P_0)\)
and \(K_0=\ell+\Delta W_0\), so
\(N\widehat D=G K_0-W(I\widehat P)\).
The introduced \(\widehat D\) has zero prefix through \(1\).
At \(B\) set \(k=G_B/b_{{\rm wt},B},\ t=b-1\),
\(\kappa=k-P(b),\ f=k-\widehat P(b)\ne0\),
\(u=k\ell(b)-IP(b),\ j=k\rho(b)-I^2P(b)\).
The actual fifth diagonal \(d_B\) is live by the [fourth pin](../dirk11-thirteen-invisible-local-late-fourth-pin/README.md#2-consecutive-fifth-true-diagonal-liveness-and-companion-dichotomy).
Since \(ND_0\) vanishes before \(B\), commutation gives \(j=d_Bu\).
To see the second first-support identity directly, set
\(h_B=IP_0(b)-kW_0(b)\). The only earlier nonzero weighted
\(P_0\) input and earlier nonzero \(D_0\) input are at fourth \(1\),
with \(D_{0,V}=\Delta W(P_0)_V\); both \(ND_0,NW(P_0)\)
vanish there. Thus \(NW(P_0)_B\) pays the actual fourth-to-fifth tap,
which yields
\[
u=\Delta h_B+d_B f,\qquad
j=t\Delta(h_B-d_B P_0(b))=t(u-d_B\kappa).
\]
Define \(v=t\kappa/f,\ a=1+v,\ \eta=u/f=e+\lambda v\).
Subtraction gives a live contact guard \(v-t=t\Delta P_0(b)/f\ne0\).
The displayed row identities give
\[
d_B(\eta+v)=t\eta,\qquad j/f=\Psi(b)\eta+\xi b v .
\]
The first forbids \(\eta+v=0\) since \(t\ne0\), \(e\ne0\).
Set \(y=\eta/(\eta+v)\) and \(D_y=(1+\lambda)y-\lambda=e/(\eta+v)\ne0\).
Then \(d_B=t y,\ y\ne0\), \(v=e(1-y)/D_y\), and
\[
t y^2-\Psi(b)y-\xi b(1-y)=0. \tag{B}
\]
This degree-two equation has a live leading coefficient and requires
neither \(k\ne0\) nor a slope or slope-plus-one division.

## 2. The next literal row and the fourth/fifth returns

The [fourth pin](../dirk11-thirteen-invisible-local-late-fourth-pin/README.md#2-consecutive-fifth-true-diagonal-liveness-and-companion-dichotomy)
pays the commuting column
\[
D=(X-a)D_0-qW(P_0),\quad q=(1-a)\Delta,\qquad
\mathcal C D=0,\quad ND=G L-W(IQ_4),
\]
where \(Q_4=(X-a)P+qP_0\) and
\(L=(X-1)\ell-\rho-vK_0\). The actual \(D,ND\) prefix
is zero through \(B\). At the next row \(i\) of clock \(x\),
the literal \((\mathcal C D)_i=-d_i^2D_i=0\) gives \(d_i D_i=0\)
and \((ND)_i=0\). If marked, compare with the actual prior
weighted mate of the same clock, whose \(ND\) read is also zero.
Their distinct normalized heads give \(L(x)=0\). If silent,
its zero weight and live \(G_i\) give \(L(x)=0\) directly, also
at the origin where there is no prior weighted mate. For a
nonendpoint there is a prior weighted mate and hence \(IQ_4(x)=0\)
as well. In the marked case the live head difference is
\(w=G_i-b_i G_{\rm first}/b_{\rm first}\); for a silent row it is
\(w=G_i\). Thus \(D_i=w(x-a)\), including \(x=a\); only away
from that contact do we conclude the actual \(d_i=0\).

The universal identity \(eK_0=(1+\lambda)\rho-\lambda(X-1)\ell\)
now yields \(D_y L=y(X-1)\ell-\rho\). Hence the first next-row
gate is
\[
\rho(x)=y(x-1)\ell(x). \tag{N}
\]
There is no assumption that \(x\) differs from \(a\) in this equation.

* **Next fifth clock \(x=b\).** Dividing only by \(y\ne0\), (B)
  gives \(\Psi(b)-t y=-\xi b(1-y)/y\). Substituting
  \(\rho(b)=\Psi(b)\ell(b)+\xi b t\) in (N) with
  \(\xi b\ne0\) forces \(y t=(1-y)\ell(b)\).
  Since \(\ell(b)=e+\lambda t\), this is \(tD_y=e(1-y)\),
  i.e. \(v=t\), contradicting the live contact guard.
* **Next fourth clock \(x=1\).** Here (N) yields
  \(0=\rho(1)=e\Psi(1)\), hence \(r=-1\).
  If \(a=1\), then \(v=0,\ y=1\) and (B) would require
  \(\Psi(b)=t\) although \(r=-1\) gives \(\Psi(b)=-t/5\).
  Consequently \(d_i=0\) at this repeat. Also \(K_0(1)=0\).

To finish the fourth-clock case use the actual rank line already paid
in the fourth pin, \(\mathcal C\widehat D=\gamma(H-GU_3)\).
Here \(U_3\) is the cubic interpolating \(H/G\) at the four live
first debuts, and \(H/b_{\rm wt}=XJ_4(zX)\) at nonendpoint
weighted rows after a common scale. At \(B\),
\(\mathcal C\widehat D\) reads \(-d_B^2 b_{{\rm wt},B}f\ne0\);
therefore \(\gamma\ne0\).
If the next row of clock \(x\) has \(d_i=0\),
its only possible earlier inputs to \(\widehat D,N\widehat D\)
are the fifth \(B\), of ratio \(d_B\). Thus its commutator read is
\((x-b-d_B)(N\widehat D)_i\). On subtracting a weighted
mate's read (or just taking the read on a silent row), this
gives \(\gamma U_3(x)+(x-b-d_B)K_0(x)=0\).
For mates earlier than \(B\), both reads are zero there.
If the mate is \(B\), its literal
\(-d_B^2 b_{{\rm wt},B} f=(-d_B)(N\widehat D)_B\) gives the same
subtraction, though that fifth-return case is already excluded.
At \(x=1\) this forces \(\gamma U_3(1)=0\), impossible as
\(U_3(1)=J_4(z)/k_V\ne0\) by the live fourth and the
coprime ordinary Jacobi hull. Both silent and marked fourth
returns are excluded.

## 3. A headless fifth would give a finite clock algebra

If \(G_B=0\), then \(B\) is the unique singly weighted
unmarked interior, and the silent slot is the origin:
the nonorigin slack has a live weighted twin, and all marked
weights have live \(G\). The first next row is either a
marked old/fourth completion or the silent origin (actual
dirty and literal origin must come later than the remaining
weighted nonendpoint rows). The headless \(B\) cannot have
a fifth-clock repeat. We check every remaining option.

The first two fifth identities in §1 imply
\(j(u+t\kappa)=t u^2\) before any ratio cancellation.
With \(k=0\) this is
\[
 I^2P(b)[IP(b)+tP(b)]-t\,IP(b)^2=0.
\]
Set \(F=IP/X,\ J=I^2P/X\); since \(b\ne0\), divide by \(b^2\),
then multiply by \(240(r+6)^2/b^2\ne0\).
The resulting polynomial is the quartic-in-\(r\) function
**old_gate(r,b)** in **projection.py**; the code verifies the
exact coefficient identity before arithmetic.
It is applied here at fifth, not at an older sampled clock.

The monic ordinary degree-five interior hull is
\((J_5+\alpha J_4)/132\), with
\(J_4(Y)=42Y^4-84Y^3+56Y^2-14Y+1\) and
\(J_5(Y)=(2Y-1)(66Y^4-132Y^3+84Y^2-18Y+1)\).
Remove its fourth root \(V=z\) to obtain the normalized quartic
\[
 H_4(X,z)=[J_5(zX)J_4(z)-J_4(zX)J_5(z)]/(X-1),\quad
 h=132z^5J_4(z)\ne0 .
\]
The actual \(b\) is a root; divide \(H_4/h\) by \(X-b\)
to obtain \(R=X^3+c_2 X^2+c_1 X+c_0\).
Use the exact old affinity
\[
 A(r)=r^3-(c_0-c_1+3c_2)r^2/2
             -(9c_0-6c_1)r/2-9c_0=0,\qquad
 U=r(r+6)c_1-r^3-(r+6)^2c_0,\quad
 \delta=r^3/(4U).
\]
Here \(U\ne0\) and \(\ell(0)=-\delta c_0/[r^2/(r+6)]\)
are already paid by the fourth fit. The rank-three
monic \(A\)-norm of **old_gate** over the rank-four \(b\)
algebra has common denominator \(h^9\) and its numerator
has \(z^{27}\) as content up to constants; only live
factors have been removed. The outer resultant of
the content-free numerator with \(H_4\) has degree 195 and,
up to scalar, exactly \(z^{15}J_4(z)^{15}D_{120}(z)\),
where \(D_{120}\) is irreducible. Two independent fixed
rational direct resultant calculations audit the
coded multiplication norm. Since \(z,J_4(z)\ne0\), the
actual clock lies in the single remaining algebra.

Pseudodivision gives a linear \(b\)-relation with leader
coprime to \(D_{120}\). For \(r\), reduce **old_gate** modulo
\(A\) at this \(b\), obtaining \(T_2\). Then
\(U_2=[r^2]T_2 A-rT_2\) and
\([r^2]T_2 U_2-[r^2]U_2 T_2\) give an undivided linear
relation at the actual common root. The checked residue
linear leader is a unit. It uniquely reconstructs \(r\).
The checker then reconstructs both \(P(b),P_0(b)\) and
\(f=-P(b)-\Delta P_0(b)\), and checks the units required
to recover \(v=-tP(b)/f\). No assertion instantiates \(r\)
or \(b\) from a merely modular root.

**Replay.** With Python, SymPy and python-flint, run
**python3 identities.py** and
**python3 project.py --prime 101 --prime 107**.
The second command first does the exact projection and
then degree-preserving residue arithmetic in the monic
\(D_{120}\) algebra. It checks \(eL(1)\), \(eL(1/z)\)
and the entire old cubic norm of \(eL\) are units separately
for both primes. Every invoked denominator, including
the linear \(r\)-leader and original leading coefficient
before making \(D_{120}\) monic, is checked on reduction.
These modular tests certify the corresponding
characteristic-zero units: over the local coefficient
ring at the chosen prime the multiplication determinant
reduces to a unit. The old cubic norm check includes all
three old clocks and does not select one via a modular
root. The selected primes are computation witnesses
for characteristic zero only, not restrictions on the
actual characteristic-zero coefficient field.

The rooted/chronological bridge is the written proof
above using the cited exact predecessor flags; the
packet makes no new native Lean claim.
