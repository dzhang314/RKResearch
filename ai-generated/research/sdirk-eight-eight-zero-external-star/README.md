# External affine root: the entire live reflected star is impossible

Consider strict ten-stage SDIRK of ordinary order at least eight over a characteristic-zero field. Suppose the quadratic residual \(\mathbf g=A\mathbf c-\mathbf c^{\odot2}/2\) has exactly eight physical zeros at eight distinct clocks. The two other rows are at physical positions 1, 2, have distinct clocks, and are individually silent. The reverse quadratic numerator is affine with a root \(\rho\) outside the eight zero labels, as in the [external-root setup](../sdirk-eight-eight-zero-affine-external-root/README.md). Here the three literal rear rows are in the live reflected star phase.

**Result.** This entire chart is impossible in characteristic zero, without any weight-sign hypothesis. The proof removes the external root and the free reflected gap analytically before doing a small exact projection. Together with the onsite and constant-numerator exclusions, this closes the full live-star phase for exactly eight physical zeros. It does not yet close the external finite-gap phases or change the 10–11 stage interval.

## 1. Gap-free moments and a necessary nonzero mean

Use \(A'=A/\gamma\), \(\mathbf x=\mathbf c/\gamma\), \(D=1/\gamma\), \(I_D(T^j)=D^j/(j+1)\). Let \(s=D-1,\ m=D-2,\ Y=T-m,\ w=\rho-m\). The first five actual zero labels are \(a,b,c,d,e\); write \(\sigma=(T-a)(T-b)(T-c)\), \(P_5=\sigma(T-d)(T-e)\), and \(n_j=I_D(Y^jP_5)\). The exact gap-free ordinary masks from the [affine live-star proof](../sdirk-eight-eight-zero-affine-early-star/README.md#2-both-cardinal-tests-and-the-jump-are-gap-free) give
\[
        n_2+(w-1)n_1-w n_0=0,\qquad (1-w)n_1-(2-w)n_0=0.
\]
In particular
\[
        n_2=2 n_0,\qquad (1-w)(n_1-n_0)=n_0.             \tag{1}
\]
There is no sign or positivity assumption.

For the Cauchy functional \(\Lambda_\rho\) use the gap-free effective node mask \(P=P_5(Y-1)\), as in the external note. In particular \(P_5(\rho)\ne0\) and \(w\ne1\). If \(n_0=0\), (1) gives \(n_1=0\), and
\[
        \Lambda_\rho(P_5)=-P_5(\rho) I_D(P_5)=0.
\]
The last identity follows from \({\cal C}_{P}(\rho)=(w-1){\cal C}_{P_5}(\rho)+I_D(P_5)\), with \({\cal C}\) the divided mean. Thus \(P_5\) would be a transformed \(F_5|_U\) profile: it has degree five, its first two ordinary means are zero, and its Cauchy functional is zero. It vanishes at the first four detecting reads of \(F_5|_U\) and yet not at the rear labels, a contradiction. This proves \(n_0\ne0\), hence \(n_1-n_0\ne0\) by (1). The external root can in fact be recovered as \(w=1-n_0/(n_1-n_0)\), but the proof below will not need to substitute this root into a polynomial projection.

## 2. A general two-row Cauchy collapse

Suppose a transformed pure trace has the form
\[
 W=(Y-w)E+(U+VY)P_5,\qquad
 I_D(W)=I_D(YW)=\Lambda_\rho(W)=0
\]
for a polynomial \(E\) in the degree range of the actual reads below. Put \(E_j=I_D(Y^jE)\). The Cauchy row simplifies because
\[
 \Lambda_\rho((Y-w)E)=P(\rho)E_0,\qquad
 \Lambda_\rho((U+VY)P_5)=-(U+V)P_5(\rho)n_0.
\]
For the second identity, factor \(P=P_5(Y-1)\) and cancel the contribution from the divided mean of \(P_5\); the remaining numerator divided by \(Y-w\) is \(-(U+V)P_5\). Hence
\[
 (U+V)n_0=(w-1)E_0.
\]
The two ordinary rows are
\[
 U n_0+V n_1=-E_1+wE_0,\qquad
 U n_1+V n_2=-E_2+wE_1.
\]
Using (1) gives the following **actual necessary** identities:
\[
 V=\frac{E_0-E_1}{n_1-n_0},\qquad
 U=\frac{E_1-2E_0}{n_1-n_0},\qquad
 I_D((Y^2-2)E)=0.                                      \tag{2}
\]
For example the two expressions for \(U,V\) follow by subtracting the Cauchy row from the first ordinary row and using \((w-1)n_0^{-1}=-(n_1-n_0)^{-1}\). Substitution in the second row gives \(E_2=2E_0\) using both identities of (1). Neither the recovery nor the necessary mask uses signs, and the required nonzero mean has already been proved.

## 3. Literal fourth and fifth reads give two linear recoveries and one extra row

Set \(\xi_d=d-m,\ \xi_e=e-m\) and \(E=\sigma-J\sigma\), where \(J\) integrates from zero in the original \(T\) coordinate. The [three-coefficient read proof](../sdirk-eight-eight-zero-affine-external-root/READ-MASKS.md) applies to the actual supported cubic \(\sigma\) and quartic \(\tau=(Y-\xi_d)\sigma\). Their preceding literal inputs vanish. In each case after enforcing the tested diagonal, the quadratic factor of the image is \(Y-w\) plus an affine polynomial times the tested-clock factor. Thus the fifth-read transformed pure error is
\[
 W_5=(Y-w)(\tau-J\tau)+(U_5+V_5Y)P_5 .
\]
The actual grade-five pure space requires its two ordinary rows and its Cauchy row to vanish. Applying (2) gives
\[
 I_D((Y^2-2)(\tau-J\tau))=0.
\]

The actual fourth-read error has the form \(W_4=(Y-w)E+(U+VY)\tau\). It satisfies three ordinary zero means and \(\Lambda_\rho(W_4)=0\) at grade four. Multiply by \(Y-\xi_e\). The product satisfies the two means and the Cauchy constraint required in (2), because
\[
 \Lambda_\rho((Y-\xi_e)W_4)
     =P(\rho)I_D(W_4)+(w-\xi_e)\Lambda_\rho(W_4)=0.
\]
It has the form in (2) with \(E\) replaced by \((Y-\xi_e)E\). Consequently \(I_D((Y^2-2)(Y-\xi_e)E)=0\). In particular the two late labels obey
\[
 \begin{aligned}
 \xi_d L_0&=L_d,& L_d&=I_D((Y^2-2)[Y\sigma-J(Y\sigma)]),\\
 \xi_e L_0&=L_e,& L_e&=I_D((Y^2-2)Y E),\\
 &&L_0&=I_D((Y^2-2)E).
 \end{aligned}                                                    \tag{3}
\]
These equations do not divide by \(L_0\); the exact singular case is checked below. The tests are actual chronological diagonals, not imported shifts of a collocation tableau.

A further \(\rho\)-free constraint comes from the **unmultiplied** fourth-read constant row. Write \(e_j=I_D(Y^j E)\), \(t_j=I_D(Y^j\tau)\). Apply (2) to \((Y-\xi_e)W_4\) and substitute its coefficients \(U,V\) back into \(I_D(W_4)=0\), multiplying by \(n_1-n_0\). The part from \((Y-w)E\) becomes
\((n_1-n_0)e_1+(2n_0-n_1)e_0\) by (1); the two remaining contributions are \((E_1-2E_0)t_0+(E_0-E_1)t_1\), where \(E_0=e_1-\xi_e e_0,\ E_1=e_2-\xi_e e_1\). Using \(n_0=t_1-\xi_e t_0,\ n_1=t_2-\xi_e t_1\) cancels \(\xi_e\) exactly. The remaining constraint is
\[
 (2t_1-t_2)e_0+(t_2-2t_0)e_1+(t_0-t_1)e_2=0.            \tag{4}
\]
This is linear in \(\xi_d\) and uses no \(\rho\), independent of the reflected gap.

## 4. Exact diagonal projection with every pivot branch retained

The actual first-three gate gives \(a=1+2u,\ Q(u)=0,\ b^2-(2u+4)b+1+2u=0\) and \(C_3(c;D)=0\). The replay verifies the exact degree-six field with primitive \(u+b\), its inverse maps, and the front quadratic. Write \(M_j=I_D(Y^j\sigma)\) and \(R_j=M_{j+2}-2M_j\). Let
\[
 F_j=(2M_{j+1}-M_{j+2})e_0+(M_{j+2}-2M_j)e_1+(M_j-M_{j+1})e_2,\quad j=0,1.
\]
The actual ordinary row \(n_2=2n_0\) and (4) read \(R_2-(\xi_d+\xi_e)R_1+\xi_d\xi_e R_0=0\) and \(F_1-\xi_d F_0=0\). With (3) the two cleared necessary equations are
\[
 A_0=L_0^2 R_2-L_0(L_d+L_e)R_1+L_dL_e R_0=0,\qquad
 A_1=L_0 F_1-L_d F_0=0 .
\]
They apply without a moment-recovery determinant from quadrature. At \(L_0=0\), (3) gives both \(L_d=L_e=0\) as additional necessary equations.

Set \(C_3=\ell_2 c^2+\ell_1 c+\ell_0\). At \(\ell_2\ne0\), scale \(L=\ell_2 c\) and reduce each polynomial in its monic quadratic algebra \(L^2+\ell_1L+\ell_2\ell_0=0\). The scaled norm of \(p+qL\) is \(p^2-pq\ell_1+q^2\ell_2\ell_0\); an actual equation forces its norm zero regardless of split or repeated quadratic roots. Strip only \(\ell_2\) factors and a possible power of \(D=0\).

| Projection | Raw norm degrees | After the \(\ell_2\) guard | After the \(D\) guard | Exact common gcd degree |
|---|---|---|---|---:|
| \(L_0,L_d,L_e\) | \(20,22,22\) | \(16,18,18\) | \(16,18,18\) | 0 |
| \(A_0,A_1\) | \(62,58\) | \(50,46\) | \(46,42\) | 0 |

Thus the singular common pivot is impossible and the two generic equations have no actual root. For the leading drop \(\ell_2=0\), \(\gcd(\ell_2,\ell_1)=1\) in the exact initial field. Substitute \(c=-\ell_0/\ell_1\) with cleared powers of \(\ell_1\) and check the two common gcds against \(\ell_2\) separately. Both are constant. These are exact characteristic-zero polynomial gcd checks, not inferences from a finite residue sample.

## 5. Replay and native scope

Run `python check_external_star.py` with SymPy 1.14 and Python-flint 0.8. The [Lean companion](../../lean/RKCert/Research/SDIRKEightEightZeroExternalStar.lean) is staged scalar source (not a fresh stock build in this packet). It states the scalar mask eliminations and the cancellation in (4); the actual flag and exact number-field ingress are the source proof. In particular no degree-eight ordinary quadrature condition or order-nine assumption is used.
