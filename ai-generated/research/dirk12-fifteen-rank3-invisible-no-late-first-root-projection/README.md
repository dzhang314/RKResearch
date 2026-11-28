# DIRK12/15: finite no-late prefixes with a third zero ghost and first Legendre root

Use the real ordinary fifteen-stage order-twelve \(C(2),f_5=3\) invisible high-site equality frame of the [no-late half-clock exclusion](../dirk12-fifteen-rank3-invisible-no-late-half-clock/README.md), with either the nine-site early reverse return or the ten-site earliest extra reflected zero. Assume four distinct dirty ghosts occur before the first ordinary live nonzero \(a\), that the ordinary numerical-zero ghost is physically third, and \(L_6'(a)=0\). The second nonzero ordinary live clock \(b\) is now arbitrary, not a prescribed half-clock.

**There are only finitely many algebraic first-four ordinary live prefixes \((a,b,c,e)\) in this chart.** A nonzero scalar obstruction polynomial in \(x=b/a\) is specified by finite quotient-algebra operations. Conditional on \(x\), the coordinates \(a,c/a,e/a\) have at most five, five and four successors, respectively. This does not compute the admissible finite set or claim that it is empty. Its specialized half-clock \(x=1/2\) is already impossible. The overall real DIRK12 interval remains **15–16**.

The physical zero-ghost and live weight assumptions are exactly those of the source chart. All ordinary scalar tests below have actual grade at most six or are genuine commutator words of grade seven. No scalar degree-twelve moment is paid or set equal to its integral; no unknown tableau is reduced modulo a prime.

## Physical first and second rows

Write \(x=b/a,\ y=c/a,\ t=e/a\) and \(T=\mathbf c/a\). Keep \(J\) the ordinary primitive from zero, \(\mathcal I(F)=JF(1)\), \(\bar A=A/a\), \(\bar R=(CA-AC-A^2)/a^2\). The actual nonzero ghost clocks and their moment contributions are exactly those in the half-clock proof, independent of \(x\), because they followed from \(L_6'(a)=0\) and the true no-late third-zero geometry. Thus for any scalar \(F\in TP_4\) its actual ordinary live-only row functional is
\[
  \mathcal A(F)(s)=JF(s)-r(s)\mathcal I(F)-k(s)\mathcal K(F),\qquad
  \mathcal K(F)=\mathcal I(TF)-\epsilon[T^5]F,
\]
with \(r\in s\langle L_5'(as),L_6'(as),L_7'(as)\rangle\) and \(k(s)=\lambda s L_6'(as)\) for a nonzero \(\lambda\). The top Jacobi coefficient of \(r\) is nonzero because the actual two chronologies force \(\gamma\ne0\) by their true mixed reverse grade-six ratios using the **unpaid** \(\varepsilon_{12}\).

The ordinary first diagonal is zero, \(r(1)=1,\ k(1)=0\). Write \(W=T^2(T-1)^2(T-1/2)\), \(D_b=5x^2-5x+1\). By the actual first-root affine-mask argument, \(W'(x)\ne0\) and the second actual diagonal and pivot satisfy
\[
 \beta=\bar A_{bb}=\frac{W(x)}{W'(x)}
                     =\frac{x(x-1)(2x-1)}{2D_b},\qquad D_b\ne0 .
\]
The two true first ghost-tap rows are independent, so \(L_6'(a x)\ne0\) (otherwise both reduce to the one common ghost factor). For \(Q_x=T(T-1)(T-x)\), the three nodal tests \(Q_x,TQ_x,T^2Q_x\) of degrees \(3,4,5\) have no available ordinary live values at row \(x\). The first two determine \(r(x),k(x)\) with determinant \(D_b/3600\); the third pays the exact quintic correction. This yields
\[
\begin{split}
 r(x)&=\frac{x^3(15x^3-49x^2+55x-20)}{D_b},
 & k(x)&=-\frac{30x^3(x-1)^3}{D_b},\\
 \epsilon&=-\frac{7x^2-7x+2}{1260},
 & k(s)&=k(x)\frac{s L_6'(as)}{xL_6'(ax)} .
\end{split}
\]

## Actual third row and any degeneracy of its scalar pivot

Put \(P_0(T)=Q_x(T)(T-y)\), \(D=2xy-x-3y^2+2y\), \(S=3x^2-2xy-2x+y\). The true live-only numerical outputs of \(P_0,TP_0\) are zero at the actual \(y\)-row. The two mode equations have coefficient matrix
\[
    \begin{pmatrix}\mathcal I(P_0)&\mathcal K(P_0)\\
    \mathcal I(TP_0)&\mathcal K(TP_0)\end{pmatrix}
\]
and right-hand column \((JP_0(y),J(TP_0)(y))^{\mathsf T}\). Its determinant is \(-D_bD/10800\) and the adjugate numerator for \(k(y)\) is \(-y^3(y-1)^3 S/360\). If \(D=0\), consistency requires \(S=0\), but
\(\operatorname{Res}_y(D,S)=-3x(x-1)D_b\ne0\). Thus \(D\ne0\) on actual candidates; the solve is valid and in particular
\[
             k(y)=\frac{30y^3(y-1)^3 S}{D_b D}.
\]
Let \(r_y\) denote the other coordinate of that same explicit solve. The true third diagonal and tap from the second live row are obtained by now testing \(Q_x\) and \(P_x=T(T-1)/(x(x-1))\):
\[
\begin{split}
 \omega&=\frac{JQ_x(y)-r_y\mathcal I(Q_x)-k(y)\mathcal K(Q_x)}{Q_x(y)}
              = \frac{y(x-y)(y-1)}{2D},\\
 \tau&=JP_x(y)-r_y\mathcal I(P_x)-k(y)\mathcal K(P_x)-\omega P_x(y).
\end{split}
\]
The first formula divides only by the literal distinct-clock guard, and the second uses \(P_x(1)=0,P_x(x)=1\). They are actual physical coefficients even when \(\beta\ne0\). No unproved separate commutator read is needed to obtain them.

Comparison with \(k(y)/k(x)\) gives the genuine third-clock equation
\[
 x^2(x-1)^3 D L_6'(ay)+ y^2(y-1)^3 S L_6'(ax)=0 .
\]
In the quotient where \(L_6'(a)=0\), the factors \(y-1,y-x\) are exact: evaluate at \(1,x\) and use \(x-1\ne0\). Its degree-seven leading coefficient is \(-3x^2(x-1)^3\,5544 a^5\ne0\), so the residual equation has degree five.

## A paid fourth row even when the second diagonal is nonzero

The true no-late affine mask \(\mathbf Q\) has scalar \(W'\) and zero at all ghosts and the first ordinary live nonzero row. Its actual primitive \(\bar A\mathbf Q\) is zero on ghosts and has \(W\) on live rows. The true pure grade-seven \(Z\), the nonterminal live profile of \(\bar R(\bar A\mathbf Q)\), is in the three-mode space \(s\langle L_5'(as),L_6'(as),L_7'(as)\rangle\) by the genuine \(7+4=11\) pairing. Its literal first three reads are
\[
              Z(1)=0,\quad Z(x)=-\beta^2W(x),\quad
              Z(y)=(y-x-\omega-\beta)\tau W(x)-\omega^2W(y).
\]
In contrast to the half-clock, the actual \(W(x)\) may be nonzero. It would be invalid to discard its contribution or the true indirect path through the third row.

Whenever the three-mode evaluation determinant on \(1,x,y\) is nonzero, interpolate \(r,Z\) from their specified reads. Define \(d=\mathcal A(P_0)/P_0\), \(E_5=\mathcal A(TP_0)/P_0-Td\), \(V=\mathcal A(W)\). Their first two divisions are exact on an actual prefix. Define cubic scalar cardinals
\[
 P_b=\frac{T(T-1)(T-y)}{x(x-1)(x-y)},\qquad
 P_c=\frac{T(T-1)(T-x)}{y(y-1)(y-x)},
 \qquad B_d=\mathcal A(P_b)-dP_b,\quad C_d=\mathcal A(P_c)-dP_c.
\]
At the actual \(t\), the numerical quantities \(d(t),B_d(t),C_d(t)\) are precisely its actual diagonal and taps to \(b,c\), by the scalar nodal and cardinal reads. Put \(M=T-y-\omega\) and
\[
 E_7=\frac{MV-d(V+MW)+ W(x)[(y+\omega-x-\beta)B_d-\tau C_d]-Z}{P_0}.
\]
The square-bracket correction pays both the earlier live \(b\) contribution and the indirect path through \(c\). In fact at \(t\) the actual \(\bar R\) read is
\[
 (t-x-\beta-d(t))B_d(t)W(x)
   +(t-y-\omega-d(t))C_d(t)W(y)
   -C_d(t)\tau W(x)-d(t)^2W(t).
\]
Substituting \(V(t)=B_d(t)W(x)+C_d(t)W(y)+d(t)W(t)\) gives the claimed numerator. Thus \(E_5(t)=E_7(t)=0\). The last division is exact on every actual prefix: at \(0,1\) all relevant live scalar reads vanish; at \(x\), the artificial taps \(B_d(x),C_d(x)\) are \(\beta-d(x),0\) and \(V(x)=\beta W(x)\), which gives \(Z(x)\) regardless of \(d(x)\); at \(y\) the artificial taps are \(\tau,\omega-d(y)\) and \(V(y)=\tau W(x)+\omega W(y)\), which gives \(Z(y)\) independently of \(d(y)\). The degree bounds are four and five, with the correction terms of degree at most seven before division. At \(x=1/2\) the \(W(x)\)-correction vanishes exactly, reducing to the existing half-clock equations.

## Finite obstruction and the fourth-clock degree at exceptional pivots

Use \(U=\mathbb Z_{(43)}[x]_{(43,2x-1)}\). Adjoin \(a\) via the monic normalization of \(L_6'(a)\), and then \(Y\) via the monic residual third-clock polynomial above. Both leading coefficients are units: reduce \(x\) to \(1/2\) modulo \(43\) and use the five nonzero \(a\) residues of the existing exact certificate. The factor strip in this rank-five coefficient algebra is exact since \(x-1\) is a unit and both evaluations vanish. The resulting algebra is finite free of rank 25 over \(U\). Its residue factors are exactly the eleven fields checked independently in the half-clock proof. Hence all formula guards, including \(L_6'(ax),Y,Y-1,Y-x,D_b,D\) and the three-mode evaluation determinant, are units in that algebra, certified by their multiplication determinants.

Construct \(r,k,Z,d,E_5,E_7\) in the finite algebra. For this coefficient-algebra step use formal Euclidean quotients by the monic \(P_0\), whether or not their remainders vanish; on an actual prefix they are the exact quotients just proved. The \((4,5)\) Sylvester determinant is a unit because its reduction is one in the sense of being nonzero in each of the eleven residue fields (the specialized polynomials have both degrees and gcd one). Its multiplication determinant is a unit in \(U\). Over \(\mathbb Q[x]\), the entire construction needs inversion of only finitely many nonzero scalar polynomials: simple scalar leading coefficients and all multiplication determinants, including this last one, with inverses by adjugates. Their numerator/denominator product is a nonzero polynomial because its selected representatives all reduce to nonzero values at \(x=1/2\) modulo \(43\). For any real \(x\) off its zeros, evaluation at an actual \(a,y\) would preserve the Sylvester unit, contrary to the true fourth-row shared root. This is a nonzero exact projection equation, not an assertion about integrality of an arbitrary unknown real \(x\).

Fix an exceptional possible \(x\). There are at most five genuine \(a\) and five \(y\) for each \(a\) as proved. For all actual prefixes, **even if the three-mode determinant were zero**, use the actual \(r,k\) in \(E_5\). Its numerator is
\[
 -J^2P_0-r(T)(I_1-TI_0)-k(T)(K_1-TK_0),\qquad
 I_i=\mathcal I(T^iP_0),\quad K_i=\mathcal K(T^iP_0).
\]
If identically zero, its degree-eight term forces \(I_0=0\) because the actual \(r\) has degree seven. Dividing by \(T\) then puts \(J^2P_0/T\) in \(\langle L_5'(aT),L_6'(aT),L_7'(aT)\rangle\), using that \(T L_6'(aT)\) lies in the neighboring-mode span. As its degree is five it belongs to the first two modes. It has a double zero at zero, but the two-jet determinant of those modes there is \(7560a\ne0\); this would make \(J^2P_0=0\), impossible. Thus the actual \(E_5\) is nonzero and of degree at most four, giving the claimed finite fourth fiber including all exceptional pivot values.

Run the exact rational polynomial identities and the independent specialization:

    python3 -B verify.py
    python3 -B ../dirk12-fifteen-rank3-invisible-no-late-half-clock/verify.py

These establish a mathematical finite projection with an exact residue certificate, not a complete Lean stage-order theorem.
