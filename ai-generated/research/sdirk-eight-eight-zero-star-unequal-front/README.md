# Live-star paired rear repeat: unequal cardinals at one of the first three early rows

Consider strict ten-stage SDIRK of ordinary order at least eight over a characteristic-zero field, with common nonzero diagonal \(\gamma\). Let \(\mathbf c=A\mathbf1,\ \mathbf g=A\mathbf c-\mathbf c^{\odot2}/2\). Suppose exactly eight physical zeros have seven distinct zero labels. The [preceding census](../sdirk-eight-eight-zero-late-mate/README.md) leaves the two distinct individually silent off rows at physical positions 1 and 2, and a live reflected star with repeat \(q\) connecting physical row 8 or 9 to an early row. Let \(p\) be the other singleton pair label, and \(B(q),B(p)\) the grouped ordinary cardinal numerators. The [equal-cardinal case](../sdirk-eight-eight-zero-star-equal-cardinal/README.md) is excluded separately.

**Result.** If \(B(q)\ne B(p)\), the early mate cannot be any of physical rows 3, 4, 5. This covers both orientations and does not assume a nonzero ordinary weight at the early copy. Thus in the characteristic-zero seven-label chart, the early mate must now be row 6 or 7. This is not a positive-characteristic claim or a general 11-stage lower bound.

## 1. The pure singleton profile and its literal early jump

Normalize \(A'=A/\gamma,\ \mathbf x=\mathbf c/\gamma,\ D=1/\gamma\), and put \(U=\ker\operatorname{diag}(\mathbf g)\). Use \(I_D(T^j)=D^j/(j+1)\) and the monic seven-label polynomial \(P_7\). The split-free gate (1) of the equal-cardinal proof says that for each \(\mathbf f\in F_4|_U\) there is a scalar polynomial \(S\) of degree at most four representing it on the singleton labels, with
\[
 I_D((T-q)T^jS)=0\quad(0\le j\le2),\qquad
 f_{\rm early}(q)=S(q)+\chi I_D(S),\quad
 \chi=\frac{P'_7(q)}{B(p)-B(q)} .
\]
The jump concerns the **early** physical copy. The reverse test row used to derive it vanishes at the rear physical copy. There is no division by an individual weight.

The tilted moments are equivalent to \(I_D(T^j S)=q^j I_D(S)\), \(0\le j\le3\). Hence the scalar singleton space is the span of \(L_{4,D}\) and the scaled reproducing kernel
\[
 K(T,q)=\sum_{j=0}^3(2j+1)D^{6-2j}L_{j,D}(T)L_{j,D}(q),
 \qquad I_D(T^jK)=D^6q^j\quad(0\le j\le3).
\]
The Hilbert Gram matrix on degree at most three is nonsingular, so the only additional mean-zero mode of degree at most four is \(L_{4,D}\). Conversely the map from the actual rank-two \(F_4|_U\) to this scalar span is injective: if \(S=0\), the jump gate gives zero at the early copy, and orthogonality to \(\mathbf z^\mathsf T\) gives zero at the remaining rear copy, whose actual pure coordinate is nonzero. This uses no early live-weight assumption. It follows that the two scalar modes are actual, and their early profiles are \(L_{4,D}\) and \(K(T,q)\) with the single correction \(\chi D^6\) at the early \(q\).

## 2. Three homogeneous rows on the unknown early quadratic

Write the five early zero labels in order as \(a,b,c,d,e\), and assume \(q\in\{a,b,c\}\). Set
\[
 s=D-1,\quad m=D-2,\quad p=2m-q,\quad \kappa=2-(q-m)^2,\qquad
 \sigma=(T-a)(T-b)(T-c),\quad P_2=(T-d)(T-e).
\]
The two star orientations produce the same equations. Let \(U_2=\sigma/(T-q)\), \(U_3=U_2(T-s)\), \(U_5=\sigma(T-s)(T-p)\). Then \(P_7=U_5 P_2\), and the ordinary precision and the **singleton** rear ratio give
\[
  I_D(U_5P_2)=0,\qquad
  I_D\left(\left[\kappa U_5/(T-p)-U_5/(T-s)\right]P_2\right)=0 .
\]
Without claiming a ratio on either physical copy of \(q\), we have
\[
 B(p)-B(q)=(p-q)I_D(U_3P_2),\qquad
 P'_7(q)=(q-p)U_3(q)P_2(q).
\]
Thus the jump is \(-D^6 U_3(q)P_2(q)/I_D(U_3P_2)\), with the denominator nonzero exactly in the unequal-cardinal case.

Use the same real chronology as in the [constant-numerator chart](../sdirk-eight-eight-zero-constant-barycentric/README.md#3-actual-early-reads-give-two-equations-before-any-moment-division), but with the actual repeated-clock jump described here. The first two supported primitive rows of \(Z_2=(T-a)(T-b)\), \(Z_3=T Z_2\) determine the whole \(F_4|_U\) profile. The third actual read determines transfer coefficients \(\alpha(c),\beta(c)\) such that every pure value at the physical \(c\) is \(\alpha(c)\) times its physical \(a\)-value plus \(\beta(c)\) times its physical \(b\)-value. The front equations are
\[
 a=1+2u,\qquad Q(u)=0,\qquad b^2-(2u+4)b+1+2u=0,\qquad C_3(c;D)=0 ,
\]
where the last one is the transfer on \(L_{4,D}\). Put \(w_q=-\alpha(c),-\beta(c),1\) for \(q=a,b,c\), respectively, and \(E_K=K(c,q)-\alpha(c)K(a,q)-\beta(c)K(b,q)\). Transfer on the second mode, now accounting for the **early** jump, gives
\[
  E_K I_D(U_3P_2)-w_q D^6 U_3(q)P_2(q)=0 .
\]
The replay divides the coefficients \(E_K,w_q U_3(q)\) by the exact factor \((c-a)(c-b)\), valid since the labels are distinct. For example when \(q=a\), \(U_3(q)\) has factor \(a-c\) and \(\alpha(c)\) has factor \(c-b\); when \(q=c\), both factors are in \(U_3(q)\). This divided shape equation and the two ordinary rows are linear in the two coefficients and monic leading coefficient of \(P_2\). Their determinant \(A_0(D,c)\) is zero even at an ordinary recovery rank drop.

## 3. Exact collision factors and the required first-two rank

The initial field is the degree-six field with primitive \(u+b\). The replay verifies irreducibility, inverse coordinates and all front equations. Write \(C_3=\ell_2c^2+\ell_1c+\ell_0\). At \(\ell_2\ne0\), scale \(L=\ell_2 c\) and reduce the cleared \(A_0\) to \(A+B L\) in \(L^2+\ell_1 L+\ell_2\ell_0=0\). The exact norm degrees are 84 for \(q=a,b\) and 100 for \(q=c\). Strip only factors of \(\ell_2\) and forbidden scalar clock collisions. For \(q=a,b\), after stripping \(\ell_2\) the degree is 64; removing \(D^{12}\) and squares from \(q=s\) and \(p=s\) leaves 48. For \(q=c\), the degree after \(\ell_2\) is 72 and after \(D^{12}\) it is 60.

In the last case there are two additional degree-six factors \(C_3(D-1;D)\), \(C_3(D-3;D)\), divided out **exactly**. On the first factor the exact branch remainder \(A+B\ell_2(D-1)\) is zero; on the second the corresponding remainder with \(D-3\) is zero. On both factors \(B,\ell_2\) are units at the fixed good reduction below with degree preserved, so any hypothetical actual root there forces \(c=D-1=s\) or \(c=D-3\), making \(p=s\). Both are forbidden. The guarded residual is therefore degree 48 in all three cases.

For the actual \(L_{4,D},K\)-with-jump basis, the determinant of its first two literal rows is nonzero, because those two evaluations detect \(F_4|_U\). By third-row transfer, the oriented two-row determinant on the two early singleton labels (use row pair \((b,c)\), \((c,a)\), or \((a,b)\)) equals \(w_q\) times that actual first-two determinant. On those singleton evaluations **there is no jump**, so this determinant is a known polynomial. For \(q=a,b\), divide it by \(c-b,c-a\), respectively; these factors are nonzero at actual labels. Call the result \(E\).

Take the norm of the scaled \(E\) and its exact gcd \(H\) with the degree-48 norm. In all cases the gcd has degree 30. If the scaled remainder of \(E\) is \(E_0+E_1 L\), the exact congruence \(E_0 B-E_1 A=0\bmod H\) identifies the actual branch. In the fixed reduction \(B,\ell_2\) and the scaled norm of \(w_q\) are units throughout \(H\), with degree preserved. Thus an actual root on \(H\) leads to rank zero in the above two-row determinant without \(w_q=0\). This contradicts the literal first-two rank. The complementary factor is degree 18. No factor was discarded on the basis of a finite rank drop.

## 4. Full guarded quotient and actual fourth-read rejection

For all three cases the fixed simple primitive residue is \(p_{\rm res}=17,\ z_0=11\). The whole degree-18 quotient, not just its rational roots, is checked. The replay verifies \(D,\ell_2,B\) units, reconstructs \(c=-A/(B\ell_2)\), and checks the ordinary two-by-two recovery determinant and \(I_D(U_3P_2)\) are units. The ordinary rows recover the monic \(P_2\), and the split-free formula gives the jump. The corrected two-mode evaluation at the first two physical rows is invertible throughout this quotient.

For the supported cubic \(\sigma\), the actual first three reads vanish, so its discrepancy has known first-two inputs \(-J\sigma(a),-J\sigma(b)\). Solve for the coefficients of its \(L_4,K\)-with-jump profile using the invertible first-two read. At physical row 6, label \(d\), the actual read is diagonal; \(d\) is a singleton. Thus the discrepancy there is represented by the **uncorrected** two scalar modes, and a necessary polynomial equation at \(d\) is \(\sigma(d)-J\sigma(d)\) minus the fitted two scalar modes, after clearing the first-two determinant. This polynomial vanishes at the two preceding singleton labels as well. Divide by their monic product \(U_2\), not by all of \(\sigma\), since the physical repeated label may have a jump. The resulting quadratic must vanish at one of the two roots of \(P_2\). Reduction modulo monic \(P_2\) gives a linear remainder whose quadratic norm is a unit throughout the degree-18 quotient. This excludes both possible assignments of \(d,e\).

For \(\ell_2=0\) the leading-drop polynomial preserves its degree at the same primitive residue, and \(\ell_1\) is a unit there. Substituting \(c=-\ell_0/\ell_1\) makes \(A_0\) coprime to it, eliminating this branch without any ordinary or jump pivot.

The simple primitive residue embeds the exact coefficient field into a local characteristic-zero field. Leading-coefficient units force hypothetical diagonal and prospective \(P_2\) roots integral in any extension of that valuation; the unit pivots above justify each recovery. The finite quotient therefore checks every algebraic candidate, including nonsplit residue factors. Distinctness is imposed in the exact field before canceling collision factors, not assumed preserved under reduction.

## 5. Replay and native scope

Run `python check_unequal_front.py SLOT` for `SLOT=0,1,2` (early \(q=a,b,c\)) with SymPy 1.14 and Python-flint 0.8. Each mode verifies its fixed degree-preserving residue, with no search. The [Lean companion](../../lean/RKCert/Research/SDIRKEightEightZeroStarUnequalFront.lean) checks the cleared reproducing-kernel moments and scalar determinant transfer. The actual split-free jump is checked in the equal-cardinal companion. Chronology and exact number-field projections are the mathematical proof and Python replay, not an unconditional native order theorem.
