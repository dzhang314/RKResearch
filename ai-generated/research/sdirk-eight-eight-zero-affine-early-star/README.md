# Eight distinct zero clocks: early live affine root, reflected star

Consider a strict ten-stage SDIRK tableau of ordinary order at least eight over a characteristic-zero field. Let \(\mathbf c=A\mathbf1,\ \mathbf g=A\mathbf c-\mathbf c^{\odot2}/2\), and suppose exactly eight physical zeros of \(\mathbf g\) have eight distinct clocks. The [low-label reduction](../sdirk-eight-eight-zero-low-labels/README.md) puts the two individually silent distinct off rows at physical positions 1 and 2. The [constant-numerator](../sdirk-eight-eight-zero-constant-barycentric/README.md) and [silent-root](../sdirk-eight-eight-zero-silent-pure-root/README.md) exclusions then leave a nonconstant affine reverse barycentric numerator and require a nonzero ordinary weight whenever its root is an actual zero label.

**Result.** In the live reflected star branch, the affine numerator root cannot be any of the first three actual zero labels (physical rows 3, 4, 5). Both star orientations are included, and the reflected gap stays free throughout the elimination. The ghost and live arithmetic phases are separate. This does not improve the global stage interval.

## 1. The single live root has a split-free pure jump

Use \(A'=A/\gamma,\ \mathbf x=\mathbf c/\gamma,\ D=1/\gamma\), \(C'=\operatorname{diag}(\mathbf x)\), and \(U=\ker\operatorname{diag}(\mathbf g)\). Let \(P_8\) be the monic eight-label polynomial, \(I_D(T^j)=D^j/(j+1)\), and \(B(x)=I_D(P_8/(T-x))\) for a label \(x\). The reverse pure quadratic row satisfies \(z_i P'_8(x_i)=\Theta(x_i-q)\), \(\Theta\ne0\), with the affine root \(q\) at an actual early zero label. Write \(b_q\ne0\) for its ordinary weight.

For \(\mathbf f\in F_4|_U\), take the degree-at-most-seven interpolant \(V\) of \((C'-qI)\mathbf f\). The two pure tests \(\mathbf z^\mathsf T,\mathbf z^\mathsf T C'\) force its degree-seven and degree-six coefficients to vanish, by the leading cardinal coefficient formula. The ordinary tests \(\mathbf b^\mathsf T(C')^j\), \(0\le j\le3\), imply \(I_D(T^j V)=0\) for \(0\le j\le2\). At \(q\) the interpolant is zero, so \(S=V/(T-q)\) has degree at most four, represents \(\mathbf f\) on all other zero labels, and \(I_D(T^j S)=q^jI_D(S)\) for \(0\le j\le3\). The original ordinary constant test gives
\[
             f(q)=S(q)-I_D(S)/b_q
\]
at the **actual physical** root. The map \(\mathbf f\mapsto S\) is injective, since \(S=0\) forces the remaining value zero by the same identity. As the pure rank is two, the basis consists of \(L_{4,D}\) and the [scaled degree-three reproducing kernel](../sdirk-eight-eight-zero-star-unequal-front/README.md#1-the-pure-singleton-profile-and-its-literal-early-jump)
\[
 K(T,q)=\sum_{j=0}^3(2j+1)D^{6-2j}L_{j,D}(T)L_{j,D}(q),\qquad
 I_D(T^jK)=D^6q^j\quad(0\le j\le3),
\]
with the extra value \(-D^6/b_q\) at \(q\) in the second mode only. No correction is inserted at a different clock or at a stage whose pure numerator is nonzero.

## 2. Both cardinal tests and the jump are gap-free

Write \(a,b,c,d,e\) for the first five zero labels and \(P_5\) for their monic polynomial. In the live rear star let \(m=D-2,\ Y=T-m\), and use \(s=m+1,\ t=m+\delta,\ r=m-\delta\) for actual rear rows \(10,9,8\) (either sign of \(\delta\)). Put \(\kappa=2-\delta^2\ne0\), \(w=q-m\). The actual rear pure/ordinary ratios are \(\omega,\omega\kappa,\omega\kappa\). With the **affine** barycentric numerator, these give the two **relative cardinal** equations
\[
 (t-q)B(r)=(r-q)B(t),\qquad
 (t-q)B(s)=\kappa(s-q)B(t).
\]
These are not the constant-numerator ratios.

The first difference is \(2\delta I_D(P_5(Y-1)(Y+w))\), hence its gap-free mean is zero. It then gives \(B(t)=(\delta-w)I_D(P_5(Y-1))\). Because \(q\ne t\), the second relative ratio reduces to
\[
   I_D(P_5(Y^2-\delta^2))=\kappa(1-w)I_D(P_5(Y-1)).
\]
Writing \(m_j=I_D(Y^jP_5)\), subtract the first mean row from this last relation. The remaining expression is
\[
        (\delta^2-1)\bigl[(1-w)m_1-(2-w)m_0\bigr].
\]
Since \(\delta^2=1\) would make one of \(t,r\) equal \(s\), the two gap-free masks acting on \(P_5\) are
\[
           (Y-1)(Y+w),\qquad (1-w)Y-(2-w).
\]
Ordinary precision is degree seven; no equation \(I_D(P_8)=0\) is added.

For the jump, write \(P_5=(T-q)\widehat P_4\). The first mask is also \(I_D(\widehat P_4(Y-1)(Y^2-w^2))=0\), so
\[
 B(q)=(w^2-\delta^2)I_D(\widehat P_4(Y-1)),\qquad
 P'_8(q)=(w^2-\delta^2)(w-1)P'_5(q).
\]
The factor \(w^2-\delta^2\ne0\) by the actual clock separation. Therefore
\[
           b_q=\frac{I_D(\widehat P_4(T-s))}{(w-1)P'_5(q)} .
\]
The individual-weight jump uses this **actual ordinary weight**, and its recovery is independent of the free star gap as well.

## 3. Front equations, exact exceptional factors, and the fourth read

Put \(\sigma=(T-a)(T-b)(T-c)\), \(P_2=(T-d)(T-e)\), so \(P_5=\sigma P_2\). Here \(q=a,b,c\). Write \(V_3=(\sigma/(T-q))(T-s)\). The jump in \(K\) is \(-D^6 V_3(q)P_2(q)/I_D(V_3P_2)\). Both ordinary masks in section 2, multiplied by \(\sigma\), give homogeneous rows on the coefficients \((v_0,v_1,1)\) of \(P_2\).

The [actual first-three ingress](../sdirk-eight-eight-zero-star-unequal-front/README.md#2-three-homogeneous-rows-on-the-unknown-early-quadratic) follows from the silent distinct two-off-row configuration, not a separate phase assumption. It gives \(a=1+2u,\ Q(u)=0,\ b^2-(2u+4)b+1+2u=0\) and the true third-read transfer \(f(c)=\alpha(c)f(a)+\beta(c)f(b)\) for pure profiles. Transfer on \(L_4\) is \(C_3(c;D)=0\); on \(K\) it is
\[
 E_K I_D(V_3P_2)-w_q D^6 V_3(q)P_2(q)=0,
\]
where \(E_K=K(c,q)-\alpha(c)K(a,q)-\beta(c)K(b,q)\), with \(w_q=-\alpha(c),-\beta(c),1\) in the three cases. The row divides by \((c-a)(c-b)\) exactly, as in the paired-repeat proof: the transfer residual has both factors, and the product \(w_qV_3(q)\) has them by the other early labels and the endpoint transfer values. This is a third homogeneous row. The three-row determinant \(A_0(D,c)\) vanishes without assuming an ordinary pivot.

The replay verifies the exact degree-six initial field and uses \(C_3=\ell_2c^2+\ell_1c+\ell_0\). With \(L=\ell_2 c\), reduce a cleared \(A_0\) to \(A+B L\) in the monic scaled quadratic. Its exact norm has degree 82 for \(q=a,b\) and 90 for \(q=c\). After stripping factors of \(\ell_2\), \(D^{12}\), and the two powers from \(s=q\) when \(q=a,b\), the respective degrees are 48 and 54. The last chart has the exact degree-six factor \(C_3(D-1;D)\), rejected by the exact branch congruence \(A+B\ell_2(D-1)=0\) modulo that factor and unit \(B,\ell_2\) there: an actual root would force \(c=s\).

The rank factor is obtained as in the paired-repeat proof, without using a finite rank failure as a reason to discard roots. The oriented \(L_4,K\) determinant on the other two first-three labels equals \(w_q\) times the actual first-two determinant of \(L_4,K\)-with-jump. Divide the oriented determinant by \(c-b,c-a,1\) in the three cases, respectively. The scale-norm of the resulting polynomial \(E\), stripped of \(\ell_2\), gives the exact degree-30 factor of the degree-48 projection. If its scaled remainder is \(E_0+E_1 L\), then \(E_0 B-E_1 A=0\) modulo this factor. With the unit checks on \(B,\ell_2\) and the scaled norm of \(w_q\), this forces the actual first-two basis determinant zero, contrary to the first-two detecting reads. The surviving exact diagonal factor has degree 18.

Use the entire degree-18 residue quotient to recover \(c\) and \(P_2\) with the checked ordinary pivot, and the physical jump with the unit \(I_D(V_3P_2)\). For the supported cubic \(\sigma\), the first three actual inputs vanish. Fit its primitive discrepancy from its two first pure values \(-J\sigma(a),-J\sigma(b)\) in the actual corrected basis. At the next actual zero \(d\), now different from \(q\), the read is diagonal and the two modes have **no** correction there. Clear the basis determinant in the difference between \(\sigma-J\sigma\) and that profile, and divide by the monic product of the two preceding labels other than \(q\). Its degree is at most two; it must vanish at \(d\). In the full quotient its residue modulo the recovered monic \(P_2\) has a unit quadratic norm. Thus neither assignment of \(d,e\) succeeds.

| Actual root | Simple primitive residue | Guarded residual degree |
|---|---:|---:|
| \(a\) or \(b\) | \(p_{\rm res}=17,\ z_0=11\) | 18 |
| \(c\) | \(p_{\rm res}=13,\ z_0=9\) | 18 |

The \(\ell_2=0\) branch is checked separately at each fixed residue with \(\ell_1\) a unit and constant gcd after substituting \(c=-\ell_0/\ell_1\) in \(A_0\). The arithmetic checks preserve leading coefficients of every exact diagonal guard and candidate factor. A simple primitive residue gives an embedding of the initial field into a local characteristic-zero field. Hypothetical diagonals and recovered monic \(P_2\) roots are integral in the valuation extension; the unit pivots justify reduction. The full quotient norm covers all roots, not just prime-field candidates. The result is characteristic-zero and does not assert the same outcome in the residue characteristics.

## 4. Replay and native scope

Run `python check_affine_star.py SLOT` for `SLOT=0,1,2` (root \(a,b,c\)), with SymPy 1.14 and Python-flint 0.8. The [Lean companion](../../lean/RKCert/Research/SDIRKEightEightZeroAffineStarMasks.lean) checks the two gap-free star scalar factorizations and a divided-mean identity also usable with an external root. Native kernel and transfer identities are in the earlier paired-repeat module. The saturated tableau ingress and exact field projections remain source proofs.

The new companion is included as source; its independent stock Lean replay was not completed at publication.
