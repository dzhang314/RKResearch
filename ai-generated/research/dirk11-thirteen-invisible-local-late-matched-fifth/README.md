# A consecutive fifth in the live-fourth late chart must have a live companion

**Result.** In the normalized characteristic-zero DIRK11/13
[four-marked-pair plus slack chart](../dirk11-thirteen-invisible-local-slack-chronology/README.md),
suppose the slack is later than fourth, \(G_V\ne0\), and the
fifth weighted nonendpoint \(B\) immediately follows fourth \(V\).
Then the companion coefficient of the actual \(\mathcal C W(P_0)\)
is nonzero. Equivalently the fifth cannot match the four-site
interpolant \(\widehat P\).
This excludes the full consecutive matched branch, allowing
an absent fifth head at the start of the argument and retaining
every possible later repeat or silent label. It does not exclude
the mismatched fifth or another immediate row type, and does not
alter unrestricted real DIRK11 **13–14**.

## 1. True matched fifth and its two polynomial gates

Use \(Y=1-c\), \(N=A^{\mathsf T}\) in literal reverse order,
\(I\) the zero-constant primitive and \(W(U)=b_{\rm wt}U(Y)\).
Use all the
[universal late fourth fits](../dirk11-thirteen-invisible-local-late-fourth-pin/README.md)
in normalized \(X=Y/V\), with \(N,G\) scaled by \(1/V,1/V^3\)
in the common monic gauge. Write \(z=V\) for the **literal**
fourth clock and \(b=B/V\) for the normalized fifth; the fourth
has normalized clock \(1\). The actual prefix here is
\(T,v,u,w,V,B\), with no completion or silent row before \(B\).
The normalized old hull is \(R=X^3+c_2X^2+c_1X+c_0\),
\(P_0=XR,\ P=Xm,\ m=X^2+rX+s\).
The actual paid fourth primitive gives
\[
 s=r^2/(r+6),\qquad r\ne0,-6,-3/2 .
\]
The true affine fit is \(IP=\ell P+\delta P_0\),
\(\delta=1/4-\lambda\ne0\), where \(\lambda\) is the
slope of \(\ell\), \(e=\ell(1)\ne0\).
Use \(D_0=G-W(P)\), \(\Delta=\delta/e\),
\(\widehat P=P+\Delta P_0\), \(\widehat D=G-W(\widehat P)\).
Here \(\mathcal C=XN-NX-N^2\).
The zero-companion consecutive-fifth case has
\(\mathcal C\widehat D=0\) globally and
\(\widehat D\) zero through \(B\), by the cited dichotomy.
In particular \(k_B=G_B/b_{{\rm wt},B}=\widehat P(b)\);
the actual \(N\) fit gives \(k_B K_0(b)=I\widehat P(b)\)
with \(K_0=\ell+\Delta W_0\).
No division by \(k_B\) is needed.

Write \(U=r(r+6)c_1-r^3-(r+6)^2c_0\). The three
actual nonleading coefficients of
\(\delta R=IP/X-\ell m\) give
\[
 \begin{aligned}
 A(r)&=r^3-\tfrac12(c_0-c_1+3c_2)r^2
                -\tfrac12(9c_0-6c_1)r-9c_0=0,\\
 &\delta=r^3/(4U),\qquad \ell(0)=-\delta c_0/s,\qquad U\ne0.
 \end{aligned}
\]
The monic cubic \(A\) is just the cleared affine
coefficient combination in the previous packet.
The actual matched fifth condition there gives
\[
 2\lambda(1+\lambda)((4r+3)b-r)
 -10(2r+3)\lambda^2(b-1)-(1+\lambda)rb=0 .
\]
It uses the genuine \(N\widehat D\) entry at the fifth,
not an assumed later zero pivot or a fifth-head model;
its guard includes \(k_B-P(b)=\Delta P_0(b)\ne0\).
Set \(U_a=U-r^3,\ U_b=5U-r^3\). Multiplying that
condition by \(16U^2\), using
\(\lambda=U_a/(4U)\), \(1+\lambda=U_b/(4U)\), gives
\[
 M(r)=2 U_a U_b((4r+3)b-r)
        -10(2r+3)U_a^2(b-1)-4 U U_b r b=0 .
\]
Only necessary polynomial equations are used below;
no real order, preferred slope root or choice of \(\lambda\)
is presumed.

## 2. Two exact norms and their live reconstruction

The ordinary degree-seven nodal hull vanishes on all
ordinary weights. Its paid first four moments imply
that the five distinct nonendpoint sites have monic hull
\((J_5+\alpha J_4)/132\), by the fixed rational
\(Y(1-Y)\) Gram test in the
[same-fourth projection](../dirk11-thirteen-invisible-local-fourth-return/README.md#2-slope-different-from-minus-one-the-new-degree-24-field).
The two Jacobi polynomials are coprime and
\(J_4(z)\ne0\). Removing the literal fourth \(z\) and
scaling \(Y=zX\) gives the complement numerator
\[
 H_4(X,z)=[J_5(zX)J_4(z)-J_4(zX)J_5(z)]/(X-1),
 \qquad h=\operatorname{lc}_X H_4=132z^5J_4(z).
\]
Its actual fifth root is \(b\). Writing \(H_i\) for raw
coefficients of \(H_4\), the actual old coefficients are
\(c_2=H_3/h+b,\ c_1=H_2/h+b c_2,\ c_0=H_1/h+b c_1\).

In **projection.py**, first work in the degree-four
\(b\) algebra using \(H_4/h\). Its power-basis coefficients
are exact polynomials in \(z\) divided by a common
\(h^\nu\). Reduction of a high \(b\)-power uses precisely
\(h b^4=-\sum_{i=0}^{3}H_i b^i\); each such step pays one
extra factor of \(h\) in the denominator. Addition aligns
depths, and an exact factor of \(h\) may be cancelled only
when divisible in every numerator entry.
Over this algebra take the determinant of multiplication
by \(M\) modulo the monic cubic \(A\), in the basis
\(1,r,r^2\). At any actual \(z,b,r\), evaluation at the
actual \(r\) is a nonzero functional on that multiplication
matrix and annihilates its image because \(M(r)=0\).
Thus the determinant vanishes at the actual \(z,b\).
Its computed power-basis numerator has content proportional
to \(z^{28}\), a live factor. Removing this gives a cubic
\(T_3(b,z)\). The script also checks three independent exact
specializations by directly taking a scalar \(r\) resultant
before reducing in \(b\); the primary computation is the
exact quotient determinant, not a finite-sampling inference.

The exact outer resultant of \(H_4,T_3\) has degree 239
and factors, up to a nonzero rational scalar, as
\[
 z^{15}\,E_4(z)^6\,J_4(z)^{11}\,D_{156}(z),\qquad
 E_4(z)=66z^4-144z^3+108z^2-32z+3 .
\]
The degree-156 factor is irreducible.
The \(z,J_4\) guards are live. If \(E_4(z)=0\),
the exact relation \(J_5(z)+J_4(z)=2zE_4(z)\) would
make the literal five-interior hull \((J_5+J_4)/132\)
with root 0. This is impossible: those are five
nonendpoint sites, independently of the actual origin
weight. Hence \(D_{156}(z)=0\).

Two checked polynomial pseudodivisions of \(H_4,T_3\)
give a degree-one relation in \(b\) with leading
coefficient coprime to \(D_{156}\), so the actual \(b\)
is an exact live ratio in that clock field.
To recover \(r\), let \(T_2=M\bmod A\) in the actual
monic \(r\)-algebra, with degree at most two and
coefficient \(t_2\) at degree two.
Then \(U_2=t_2A-rT_2\) has degree at most two, and
\(W_1'=t_2 U_2-[r^2]U_2\,T_2\) has degree at most one.
The notation \([r^2]\) means the coefficient, not a
division. This linear polynomial vanishes at an actual
common root even if a prior apparent degree fell.
Its coefficient of \(r\) is a unit in the degree-156
rational algebra by either good reduction checked below;
thus the actual \(r\) is the unique live ratio.
The code also verifies both reduced equations on this
reconstruction. No unguarded slope or root factor
is selected to reach the final tests.

## 3. No allowable row after the matched fifth

At the literal next row \(i\) after \(B\), the only
possibilities are a marked completion at one of the
five ordinary numerical labels, or the silent slack.
The latter has clock the actual origin or an unmarked
ordinary twin. The actual dirty and origin rows cannot
precede all remaining marked completions: the dirty
row is first nonzero forward and they have nonzero
forward clock, and the actual origin is the literal
first forward row. No other physical slots exist in
this support chart. All five first weighted debuts are
in the matched zero prefix.

For a marked completion of clock \(x\),
\(\widehat D_i=b_i(k_i-k_{\rm first})\ne0\), since
the earlier first mate is matched and the two normalized
heads differ. For the silent slack \(\widehat D_i=G_i\ne0\).
Thus the actual \(\mathcal C\widehat D=0\) at its first
nonzero support forces its own diagonal zero, hence
\(N\widehat D_i=0\).
Comparing the true \(N\widehat D\) fit with its original
weighted mate in the repeat case, and using \(b_i=0\)
in the silent case, gives \(K_0(x)=0\).

We exclude this using the numerator of the true fit
\[
 eK_0(X)=\ell(X)[(1+\lambda)\Psi(X)-\lambda(X-1)]
                     +(1+\lambda)\Xi(X),\quad
 \Psi=\frac{(4r+3)X-r}{5(2r+3)},\quad
 \Xi=-\frac{rX(X-1)}{10(2r+3)} .
\]
Its image is a unit for \(x=1,b,1/z\) in the whole
ordinary degree-156 field. In the full monic old cubic
extension it is a unit for **every** old root:
the norm over that cubic is a unit in the base.
Thus every physical repeat or silent possibility is
excluded. In particular the proof does not require
the slack to use the origin or discard a reused old clock.

## Reproduction and field lifting

Run **python3 project.py --prime 101 --prime 107** with SymPy
and python-flint (checked with 0.9). The outer arithmetic
and all rational resultants and pseudodivisions in
**projection.py** are exact. Its scalar audits are
independent cross-checks, not the reason the norm is valid.
The two checked finite reductions are of the **full**
monic degree-156 base. Every numeric denominator and its
degree-preserving leader, the \(b,r\) ratio denominators,
and the \(U,r,s,\delta,e,1+\lambda,2r+3\) guards used in
the verified final formulas are invertible in the checked
reductions (explicit inverses are checked before division).
The old extension norm retains all three roots.
An inverse over the full residue model gives a nonzero
multiplication determinant in the corresponding fixed
rational basis, so every exact guard and output unit lifts.
No actual tableau, weights, or choice of embedding need
be prime-integral. Prime 103 is not used: a residue guard
can be nonunit there.
No complete native Lean tableau theorem is asserted.
