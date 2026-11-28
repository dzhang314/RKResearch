# DIRK12/15: finitely many late-fourth-ghost ordinary four-live prefixes

Consider real ordinary fifteen-stage order-twelve DIRK, \(C(2),f_5=3\), in the truly weighted-invisible four-distinct-cubic-dirty-ghost frame. Use either the [nine-site early reverse return](../dirk12-fifteen-rank3-invisible-nine-site-early-return/README.md) or [ten-site earliest extra reflected zero](../dirk12-fifteen-rank3-invisible-ten-site-early-zero/README.md) chronology. Suppose exactly three ghosts precede the first ordinary nonzero live row \(a\), **those three ordinary ghost clocks are nonzero**, and the remaining ghost occurs before the next ordinary nonzero live row \(b\). The fourth ghost clock is otherwise general; in particular it is not assumed zero.

Then the first four nonzero ordinary live clocks \((a,b,c,e)\) are confined to a **finite algebraic set**, independent of any ghost amplitudes. More precisely \(x=b/a\) belongs to the zero set of a nonzero scalar polynomial over \(\mathbb Q\) specified by finite quotient-algebra operations below. For each admissible \(x\), there are at most five \(a\); for each such pair at most five \(y=c/a\); and for each such triple at most four \(t=e/a\). This is a finite projection, not a claim that the set is empty, nor a claim of a new unrestricted lower bound. Real DIRK12 remains **15–16**. If one of the three early ghost clocks is numerical zero, the elimination here does not apply. The [late numerical-zero fourth ghost](../dirk12-fifteen-rank3-invisible-late-zero-exclusion/README.md) is already completely impossible; its exact arithmetic certifies the regular specialization used here.

## Actual data and scalar coordinates

Write \(X=\mathbf c/a\) on the tableau, \(\bar A=A/a\) and \(\bar R=(CA-AC-A^2)/a^2\), and let \(J\) be scalar integration from zero and \(\mathcal I(F)=(JF)(1)\). Write \(L_j\) for the \(j\)-th shifted Legendre polynomial. The first four ordinary nonzero live labels are unique physical rows in these chronologies, and the literal ordinary origin is the only ordinary live numerical zero. The actual ordinary pure spaces are denoted by \(F_j\).

Let \(z\) denote the fourth ghost clock divided by \(a\). By the [fourth-ghost proof](../dirk12-fifteen-rank3-invisible-ordinary-ghost-chronology/README.md), the ordinary \(a,b\) diagonals are zero,
\[
 z=\frac{x(5x-2)}{3(2x-1)},\quad
 x\notin\{0,1/2,3/5,1\},\quad z\ne1,x,\quad aL_6'(a)\ne0,
\]
and
\[
 (2x-1)L_6'(ax)=x^3(2x^2-6x+5)L_6'(a).
\]
From the [genuine common grade-four mask and third live row](../dirk12-fifteen-rank3-invisible-third-ordinary-live/README.md) one has
\[
 \begin{split}
 D&=2xy-x-3y^2+2y\ne0,\qquad
 \omega=\bar A_{cc}=\frac{y(x-y)(y-1)}{2D},\\
 0&=(2x-1)D L_6'(ay)+y^2P(x,y)L_6'(a),\\
 P(x,y)&=-10x^2+(20x^2+5x)y+(-18x^2-6x)y^2\\
 &\hspace{2cm}+(6x^2+8x-3)y^3+(2-4x)y^4 .
 \end{split}
\]
Its two invalid factors \(y-1,y-x\) may be removed because the actual \(y\) is distinct from \(1,x\). In these two target reverse chronologies, the top \(L_7'\) tap coefficient \(\gamma\) is nonzero by the genuine mixed grade-six reverse calculation. Throughout that calculation \(\varepsilon_{12}\) is the **actual unpaid** twelfth moment, not set to zero.

## A geometry-free four-ghost moment transform

Put \(P_2(T)=10T^2-12T+3\) and \(N(T)=T(T-1)(5T-3)/2\). The true grade-three mask \(\mathbf V\) from the fourth-ghost proof has scalar profile \(\kappa X(10X^2-12aX+3a^2)\) in the **physical** unnormalized variable \(X\). The three early ordinary ghost clocks \(p_i\) in normalized units are all nonzero. Thus their actual amplitudes are \(h_i=\kappa a^3p_iP_2(p_i)\), where \(\kappa\ne0\) and \(P_2(p_i)\ne0\). In particular the mask uses the actual physical cubic defect with coefficient one, not the bare scalar alternative triggered by a ghost already at zero.

The true primitive of \(\mathbf V\) has an affine correction \(Q_{\rm av}\) times \(\mathbf h\). Set \(\ell(T)=-Q_{\rm av}(aT)/a\) and \(B_0(T)=N(T)-\ell(T)P_2(T)\). Its three distinct roots are the early \(p_i\) by the actual zero reads at those ghosts. Its leading coefficient \(C_0=5/2-10[T]\ell\) is nonzero: otherwise it has degree at most two and three distinct roots, making \(N\) a multiple of \(P_2\), which are coprime. In particular \(B_0(z)\ne0\) by distinctness of ghost clocks. Put
\[
 m=\frac{4x-3}{x},\quad
 T_0=(z-1)P_2(z)-mN(z),\quad
 D_\ell=z-1-m\ell(z),\quad H=\frac{h_*}{\kappa a^3}\ne0 .
\]
For the actual \(b\)-tap \(q=A_{b,g_*}\), its two genuine primitive identities \(q\mathbf U_{g_*}=f_b,\ q(A\mathbf V)_{g_*}=l_b\) have known ratio \(f_b/l_b=m\). The normalized entries in this equality are \((z-1)[zP_2(z)-H]\) and \(zN(z)-\ell(z)H\), respectively. Thus \(H D_\ell=z T_0\). The exact identity
\[
 T_0[zN(z)-\ell(z)H]=(z-1)H B_0(z)
\]
follows without dividing by \(z\) or \(D_\ell\). Moreover
\[
 \frac{T_0}{z-1}=\frac{5x(x-1)^2}{6(2x-1)^2}\ne0 .
\]
This also verifies that the normalized late primitive is nonzero.

Write \(Q_*=(64/3)-40T,\ E_*=(30T^2-28T+1)/3\); the exact identity is \(Q_*N+E_*P_2=1\). Define \(\sigma=Q_*(z)(z-1)+mE_*(z)\). The following exact rational function identity holds:
\[
\begin{aligned}
  \sum_{i=1}^3\frac{\widetilde w_i}{T-p_i}+\frac{\widetilde w_*}{T-z}
   &=
    \frac{1}{(T-z)P_2(T)B_0(T)}
     -\frac{Q_*(T)}{(T-z)P_2(T)}
     +\frac{\sigma}{T_0(T-z)},\\
 \widetilde w_i&=\frac1{(p_i-z)P_2(p_i)B_0'(p_i)},\qquad
 \widetilde w_*=\frac{z}{H B_0(z)}.
\end{aligned}
\]
Indeed the first two terms share reduced numerator \(E_*+Q_*\ell\) over \((T-z)B_0(T)\). Their early residues have the displayed values by \(Q_*N+E_*P_2=1\), and at \(z\) the exact identity
\((E_*+Q_*\ell)(z)T_0+\sigma B_0(z)=D_\ell\)
gives the late residue. These proper rational functions have no polynomial part. No evaluation inverse at \(P_2(z)\) is required, and the formula works even at \(z=0\).

Let \(M_k=\sum_i\widetilde w_i p_i^{k-1}+\widetilde w_*z^{k-1}\) be the coefficient of \(T^{-k}\) of this identity at infinity. For \(k=1,\ldots,5\) the moments \(M_k=m_k\) depend only on \(x\): put \(m_1=\sigma/T_0\) and \(m_{k+1}=z m_k+b_k\) for \(k=1,\ldots,4\), where
\[
 (b_1,b_2,b_3,b_4,b_5)=(4,8/3,2,8/5,33/25)
\]
are the first five coefficients of \(-Q_*/P_2\) at infinity. For \(k=5\), the actual next increment is \(M_6-zM_5=b_5+1/(10C_0)\): the additional rational term has lowest order \(T^{-5}\) after multiplication by \(T-z\). Set \(\mathcal M_z(T^k)=m_k\) on \(TP_4\). Direct polynomial identities yield, for \(W=T^2(T-1)^2(T-x)\),
\[
       \mathcal M_z(W)=\mathcal M_z(W')=0,\qquad
       \mathcal M_z(TF)=z\mathcal M_z(F)+8\mathcal I(F)\quad(F\in TP_3).
\]
Here \(P_d\) is the space of polynomials of degree at most \(d\); \(TP_4\) has input degrees one through five.

## The actual normalized live row functional

Set
\[
 R_6(s)=L_6'(as)/L_6'(a),\qquad
 G_j(s)=s[L_j'(as)-R_6(s)L_j'(a)]\quad(j=5,7).
\]
By the actual rank-two ordinary ghost taps and the zero ordinary \(a\)-tap to the fourth ghost, their formula in normalized coordinates on a nonterminal ordinary live row \(s\) is
\[
 \bar A_{s,g}=\ell_g\big[\nu a(p_g-z)s L_6'(as)
                                  +\alpha G_5(s)+\gamma G_7(s)\big],\qquad
 \ell_g=\frac{1}{h_g D_4'(ap_g)} .
\]
Here \(p_g\) ranges over \(p_1,p_2,p_3,z\), and \(D_4\) is the monic ghost hull in physical units. In particular \(\ell_g p_g=\frac{C_0}{\kappa a^6}\widetilde w_g\). This product identity still holds for the possible late numerical zero since both sides vanish there.

The ordinary \(a\)-row integrates through input degree four exactly and has scalar nodes \(0,p_1,p_2,p_3\) only. The same actual polynomial-division computation as in the late-zero proof, now with arbitrary affine \(\ell\), gives
\[
 \nu=\frac{\kappa a^5}{8C_0 L_6'(a)},\qquad
 \eta/a^5=\frac{1/(80C_0)-1/600}{L_6'(a)} .
\]
For the first, the monic nodal polynomial \(TB_0/C_0\) has integral zero since \(\mathcal I(TP_2)=\mathcal I(T^2P_2)=\mathcal I(TN)=0\). Its integral after multiplication by \(T\) is \(-(1+2[T]\ell)/(120C_0)\). Thus the actual \(a\)-row read of \(T^3 P_2\) is \(1/60-10\mathcal I(T^2B_0)/C_0=1/(8C_0)\), by division of the quintic by the quartic nodal hull, not via hypothesized local quintic exactness. The second follows from the actual zero at \(a\) of \(AC^2\mathbf V\): the degree-five input has scalar primitive reading \(\kappa a^6/60\), and its mixed cubic-ghost contribution has scalar amplitude \(\nu aL_6'(a)\), giving \(10\kappa \eta-\nu=-\kappa a^5/(60L_6'(a))\).

It follows that the **actual** normalized ordinary live-only row functional, on every scalar test \(F\in TP_4\), is
\[
 \mathcal A(F)(s)=(JF)(s)-sR_6(s)\mathcal I(F)-B(s)\mathcal M_z(F),\quad
 B=\frac{C_0}{\kappa a^6}(\alpha G_5+\gamma G_7).
\]
Indeed for degrees \(k\le4\) the \(\nu\)-mode ghost read is \(sR_6(s)(M_{k+1}-zM_k)/8=sR_6(s)/(k+1)\). In degree five the genuine quintic error \(\eta\) cancels the \(C_0\)-dependent part of that read exactly, leaving \(33/200+1/600=1/6\) after removing \(sR_6(s)\). The other ghost read is exactly \(B(s)m_k\). A nonzero constant scalar input is not used in the functional.

The exact tap values for \(B\) are
\[
 \begin{split}
 B(x)&=\frac{x^3(x-1)^2}{2}\,\frac{T_0}{z-1}
            =\frac{5x^4(x-1)^4}{12(2x-1)^2},\\
 B(y)&=B(x)\theta,\qquad
 \theta=-\frac{y^3(y-1)^3(3x^2-2xy-2x+y)}
                        {x^3(x-1)^3D}.
 \end{split}
\]
For the first note \(B(x)=C_0(q/a)/(\kappa a^6\ell_{g_*})\) and \(q(A\mathbf V)_{g_*}=\kappa a^5 x^3(x-1)^2/2\). Substitute the scaled late primitive and its identity with \(T_0\) above. The second is the true third-to-second late tap ratio, since the \(\nu\) term is zero at the fourth ghost. For the generic finite projection argument below a possible zero two-mode interpolation determinant is expressly retained as an exceptional scalar value of \(x\); it has not been assumed absent.

## The same true two fourth-row equations for general \(z\)

Put \(P_0(T)=T(T-1)(T-x)(T-y)\). In characteristic zero on any actual prefix, \(\mathcal A(P_0)\) and \(\mathcal A(TP_0)\) are multiples of \(P_0\): both live scalar profiles vanish on the earlier available live support at each of \(0,1,x,y\). Then set
\[
 d=\mathcal A(P_0)/P_0,\quad
 E_5=\mathcal A(TP_0)/P_0-Td,\quad V=\mathcal A(W),\quad
 Z\in\langle G_5,G_7\rangle,\quad (Z(x),Z(y))=(0,-\omega^2W(y)).
\]
The genuine grade-four \(\mathbf Q\) here has scalar \(W'\) and literal ghost-zero entries; \(\bar A\mathbf Q\) is ghost-zero and has scalar \(W\). Thus \(Z\) is the actual pure grade-seven profile of \(\bar R(\bar A\mathbf Q)\), not merely an interpolation imposed on a scalar approximation. Its vanishing at the first live clock puts it in the stated two-mode plane by the actual \(7+4=11\) grade pairing. At \(x,y\) its readings are the actual triangular ones above. The quartic denominator below divides exactly on any actual prefix as in the [late-zero calculation](../dirk12-fifteen-rank3-invisible-late-zero-exclusion/README.md); indeed \(V,W,Z\) vanish at \(0,1,x\), and \(V(y)=\omega W(y)\). Define
\[
 E_7=\frac{(T-y-\omega)V-d[V+(T-y-\omega)W]-Z}{P_0}.
\]
At the actual fourth ordinary live row \(t\), \(\bar A_{ee}=d(t)\) from the genuine grade-five nodal profile. Only the preceding \(y\) row and its own diagonal have nonzero \(W\) support at that cut. Thus the literal formula for \(\bar R\) gives \(E_5(t)=E_7(t)=0\). The degree bounds are \(4,5\), respectively.

## A nonzero norm obstruction in the scalar \(x\) coordinate

This step uses specialization of **known scalar coefficient polynomials**, not reduction of an unknown real tableau. Let \(U=\mathbb Z_{(271)}[x]_{(271,5x-2)}\), the localization at the indicated maximal ideal. Its residue field specializes \(x\) to \(2/5\) at the prime \(271\). The simple rational parameter denominators in the formulas above, including those in \(z,T_0\), are units there.

Make the polynomial
\((2x-1)L_6'(Ax)-x^3(2x^2-6x+5)L_6'(A)\)
monic in a fresh variable \(A\); its leading coefficient is a unit in \(U\) by the known quintic at \(x=2/5\). In the resulting free rank-five quotient algebra, \(A\) and \(L_6'(A)\) are units, since their reductions are units at all five simple residue roots. Multiplication matrices over \(U\) certify this and all subsequent unit claims: an element is a unit if its multiplication determinant is a unit, by applying the inverse matrix to \(1\).

Similarly form the \(Y\) equation for the third clock and divide by \((Y-1)(Y-x)\) in that algebra. This division is exact: both evaluations are zero by the two-clock equation, and \(x-1\) is a unit. The remaining leading coefficient is \(-3(2x-1)5544A^5\), a unit. Make monic and adjoin its root \(Y\). The resulting algebra is finite free rank 25 over \(U\), with the usual successive monomial basis. Its reduction is the product of the eleven residue fields enumerated in the late-zero verifier. Thus \(Y,Y-1,Y-x,D\) and the two-mode evaluation determinant on \(x,Y\) are all units in the rank-25 algebra: their reductions were all checked in every field. Now use the two-mode interpolation to form \(B,Z\), and the formulas for \(d,E_5,E_7\). **For the coefficient-algebra construction**, polynomial divisions by \(P_0\) are Euclidean quotients by a monic polynomial, whether or not their remainders are zero. On any actual tableau satisfying these clock equations the remainders are zero by the actual prefix proof, so these generic quotient operations specialize to the actual exact quotients.

Take the degree-\((4,5)\) Sylvester determinant of \(E_5,E_7\) in this algebra. At \(x=2/5\), \(\mathcal M_z\) and \(B(x)\) specialize exactly to the earlier late-zero formulas; all other ingredients are unchanged. The earlier exact replay checks **both degrees and gcd one in every residue factor**, so the Sylvester determinant is a unit in the rank-25 algebra. In particular its \(25\times25\) multiplication determinant is a unit in \(U\). This is not an assumption that all physical real clocks have a common good finite place.

Each of these operations (monic normalization and inversion, finite free multiplication, monic division and Sylvester determinant) uses only finitely many inverses in \(U\). Explicitly, all inversions in a finite algebra use its multiplication determinant and adjugate. Thus they descend to a localization of \(\mathbb Q[x]\) by finitely many nonzero scalar polynomials. An exact obstruction polynomial is the product of their numerator and denominator guards, including the numerator of the final multiplication determinant. It is nonzero: their chosen representatives are all units at \((271,5x-2)\). For any actual real \(x\) outside these finitely many zeros, evaluation at its actual \(a,y\) defines an algebra homomorphism into \(\mathbb R\) preserving the final Sylvester unit. This contradicts the real common root \(t\) of the genuine fourth-row equations. This proves finiteness of the first ratio; neither the size nor the set of real roots of this nonzero univariate obstruction is computed here.

For an admissible fixed \(x\), the equation in \(a\) has degree at most five and is nonzero: vanishing of both its constant and linear coefficients would give \((2x-1)(x-1)=0\). With \(a\ne0\), its third-clock equation leaves at most five \(y\) after removing the two invalid factors.

## Finiteness of the fourth clock even on bad scalar specializations

This last step avoids dividing by the two-mode determinant at an actual possible zero of a guard. It uses the actual tap polynomial \(B\), not its construction by interpolation. Put \(F=P_0,\ I_i=\mathcal I(T^iF),\ N_i=\mathcal M_z(T^iF)\) for \(i=0,1\). The actual numerator \(P_0E_5\) is
\[
 -J^2F-T R_6(T)(I_1-TI_0)-B(T)(N_1-TN_0),
\]
by \(J(TF)-TJ(F)=-J^2F\). The actual \(B\) has degree seven because \(\gamma\ne0\) and \(a\ne0\). If this numerator vanished identically, its degree-eight term would give \(N_0=0\), so \(N_1=8I_0\) by the moment recurrence. If \(I_0=0\), the equation then makes \(J^2F\) a multiple of \(TR_6\). The first has a zero of order at least three at 0, whereas \(R_6(0)=-42/L_6'(a)\ne0\); hence the multiple would be zero, contradicting \(F\ne0\). If \(I_0\ne0\), divide the identity by \(T\). Both \(B/T\) and \(R_6(T)(TI_0-I_1)\) lie in \(\langle L_5'(aT),L_6'(aT),L_7'(aT)\rangle\). For the second this follows from the neighboring-mode multiplication identity for \(T L_6'(aT)\), verified by polynomial coefficients. Hence \(J^2F/T\) lies in that span. Its degree is five, so the \(L_7'\) component must vanish. But it has a double zero at the origin, and the \(0\)-value and first-derivative determinant of \(L_5'(aT),L_6'(aT)\) there is \(7560a\ne0\). This again forces \(J^2F=0\), a contradiction. Thus on every actual candidate \(E_5\) is nonzero of degree at most four, even if a coefficient guard for the generic construction vanishes.

Finally a quick exact range restriction, independent of all norms: the quadratic in \(x\) obtained from the \(z\)-formula has discriminant \(4(9z^2-9z+1)\), so \(z\) avoids the open interval between \((3-\sqrt5)/6\) and \((3+\sqrt5)/6\). This is not an exclusion of all positive \(z\).

## Verification and scope

Run the local exact symbolic checks and the independent existing specialization checker:

    python3 -B verify.py
    python3 -B ../dirk12-fifteen-rank3-invisible-late-zero-exclusion/verify.py

The first uses exact SymPy polynomials and rational functions. The second uses the Python standard library and exhaustively verifies the eleven residue fields of total degree 25. No floating-point data, positivity of signed individual weights, reduced unknown tableau, or unpaid moment assertion enters the result. The stage-space and finite-free-algebra argument is mathematical; no full native Lean proof is claimed here.

The [actual fourth-diagonal split](../dirk12-fifteen-rank3-invisible-late-fourth-diagonal/README.md) further gives a fixed fourth ratio on the nonzero-diagonal branch and low-degree root equations on the zero-diagonal branch.

The [early-zero late-fourth extension](../dirk12-fifteen-rank3-invisible-late-early-zero/README.md) proves the same scalar geometry and finiteness when the third early ghost has numerical clock zero. Thus all late-fourth placements in the two specified high-site charts satisfy this live-clock projection.
