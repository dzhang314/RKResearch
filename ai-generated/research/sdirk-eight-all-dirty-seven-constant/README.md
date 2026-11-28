# A seven-clock all-dirty strict SDIRK8 floor cannot have a constant singleton residual

Assume a strict ten-stage SDIRK tableau of ordinary order at least eight over a characteristic-zero field, with no literal zero quadratic residual, and exactly seven distinct clocks. Use the [seven-clock decomposition](../sdirk-eight-all-dirty-seven-clock/README.md): there are three doubled labels \(\mathcal D\) and four singleton labels, and \(Q=P R_2\) with cubic \(P\) and \(\deg R_2\le2\). Each singleton has residual \(g=R_2(t)\) while both physical copies at every double have \(g\ne R_2(t)\).

**Conclusion.** \(R_2\) is nonconstant. This packet closes the constant graph with doubled endpoints; the [companion](../sdirk-eight-all-dirty-seven-clock/README.md) already forbids singleton endpoints. Together they exclude the constant graph entirely over characteristic zero. They do not exclude the affine or quadratic graph, a general seven-clock all-dirty tableau, or a ten-stage tableau in another support stratum. All restrictions here allow signed weights.

## The trace gate and its normalization

Write \(x=c/\gamma\) and \(\ell=2m=1/\gamma\) for the right endpoint in the normalized diagonal-one coordinates, and \(t=x-m\). Let \(A\) now denote the normalized tableau, \(\mathbf g\) its normalized quadratic residual and \(G=\operatorname{diag}(\mathbf g)\); retain the original weights \(\mathbf b\) with sum one. Let \(A^\star=B_b^{-1}A^{\mathsf T}B_b\) with \(B_b=\operatorname{diag}(\mathbf b)\), in the original index order. It becomes the actual weighted mirror after reversing the index order. All weights are nonzero by the [Legendre complete intersection](../clock-localized-tail/tied-stage-floor/SIMPLE-LEGENDRE-COMPLETE-INTERSECTION-AND-WEIGHTS.md). Its residual is a nonzero scalar multiple of \(\mathbf g\) (with the same index order), and its clock is \(\ell-\mathbf x\).

Let \(E_j\) be the full evaluated weighted-degree-at-most-\(j\) stage space, with \(E_{-1}=0\). The [actual forward and reverse primitive congruences](../clock-localized-tail/tied-stage-floor/EXACT-PREFIX-DIAGONAL-RECONSTRUCTION.md) for \(f\in E_j\) have errors in \(G E_{j-1}\), for \(0\le j\le6\); the reverse filtration is the same by affine clock reflection and residual scaling. Their exact scalar primitives add to the integral over the whole normalized interval, which is **\(\ell\,\mathbf b^{\mathsf T}f\)**, not \(\mathbf b^{\mathsf T}f\). The factor \(\ell\) is necessary because the paid weights represent the normalized average on that interval. Consequently
\[
 S=G^{-1}(A+A^\star-\ell\,\mathbf1\mathbf b^{\mathsf T})
 \quad\hbox{satisfies}\quad S E_j\subset E_{j-1}.
\]
As \(E_6\) is full, \(S\) is nilpotent. Its ordinary trace is zero. Both matrix diagonals in the sum are one, so
\[
                  2\sum_i\frac1{g_i}=\ell\sum_i\frac{b_i}{g_i}.             \tag{1}
\]
This field argument applies on the entire all-dirty floor, not only the seven-clock chart. In unscaled coordinates the same gate is \(2\gamma\sum_i 1/g_i=\sum_i b_i/g_i\).

In the constant seven-clock graph \(R_2=r\ne0\), \(F=0\) and \(P=(B/r)L_3\). Thus \(\mathcal D\) consists of the centered nodes \(0,\pm am\), \(a^2=3/5\). Put \(H=L_4-r(A_2+Br)\) as before. At \(d\in\mathcal D\), the grouped \(\nu_i=b_i g_i\) mass is \(\omega_d=BH_3/(P'(d)H(d))\) and its \(g\)-weighted mass is \(r\omega_d\). By the actual two-root equation, \(\sum 1/g=A_2(d)/L_4(d)\) at that double, and \(1/g=(A_2(d)+Bg)/L_4(d)\) on each copy. Since the total \(\nu\) is zero, the *total* \(\sum b_i/g_i=\sum\nu_i/g_i^2\) can be computed by subtracting \(1/r^2\) on every stage: singleton terms then vanish. The double contributes
\[
 \omega_d\left[\frac{A_2(d)(A_2(d)+Br)}{L_4(d)^2}
                  +\frac{B}{L_4(d)}-\frac1{r^2}\right]
 = \frac{-H_3}{L_3'(d)L_4(d)}
      \left[\frac1r+\frac{A_2(d)}{L_4(d)}\right].
\]
Here the cancellation is \(-H(L_4+rA_2)/(r^2L_4^2)\) inside the bracket, and all displayed denominators are nonzero by the complete intersection. The three factors \(w_d=-H_3/(L_3'(d)L_4(d))\) are \(4/9\) at \(0\) and \(5/18\) at \(\pm am\), summing to one. Thus (1) gives the reusable linear condition
\[
              \frac{8-\ell}{r}+
                     \sum_{d\in\mathcal D}(2-\ell w_d)\frac{A_2(d)}{L_4(d)}=0.        \tag{2}
\]
Only exact signed weighted averages and the nilpotent trace are used.

## Endpoint and prefix census

The doubled label set is symmetric. Thus the endpoint labels \(\pm h\), \(h=m-1\), are either both singleton (closed in the companion) or both doubled, including a shared label when \(h=0\). In the latter case either \(m=1\), or \(h=am\) after choosing a sign of \(a\), so \(m=1/(1-a)\). All finite choosers are therefore over the single quadratic \(\mathbb Q(a)\). Write \(\lambda\ne0\) for the factor converting mirror-normalized residuals to original normalized residuals; the mirror has constant singleton residual \(r/\lambda\) and quadratic coefficient \(\lambda^2B\). The notation D/S below means a doubled/singleton **clock label** at the actual physical row, not a zero residual or a zero weight.

The exact first-three gate at either end uses \(u=x_2-1\), \(\kappa=1+2u-u^2\), \(q=2g_3\): arithmetic \(x_3=1+2u,\ q=q_{\rm num}/D_0\), where \(D_0=-2+u+4u^2-u^3\) and \(q_{\rm num}\) is as in the companion; or star \(x_3=3-u,\ q=\kappa\). Every genuine branch has \(u,\kappa,q\ne0\); star excludes \(u=1,2\), and nonzero-tap arithmetic excludes \(3u=2\) and \(D_0=0\). If both second and third labels are singleton, then \(q=\kappa\). The exact arithmetic factorization
\[
 q_{\rm num}-\kappa D_0=u(u-2)(3u-2)(u^2-2u-1)
\]
leaves only \(u=2\), but then \(g_2=r=g_1=1/2\), contradicting that the first label is doubled. Thus D,S,S forces star. If the second is singleton and third doubled, star is also impossible: it would give the same residual on a double and on a singleton. The replay may temporarily enumerate such overinclusive candidate prefixes for its mixed-second census (this only strengthens its exclusion).

At any literal double \(d\), \(g_+g_-=-L_4(d)/B\) and \(A_2(d)=L_4(d)/g-Bg\) on either copy. A clock shared by the two disjoint prefixes gives \(B\lambda=-L_4(d)/(g_{\rm f}g_{\rm r})\) and forces unequal physical residuals \(g_{\rm f}\ne\lambda g_{\rm r}\). Each singleton prefix location instead forces \(H=0\) at that reflected or original centered clock, and distinct singleton locations must be different physical clocks. The four supplied checks exhaust the following mutually exhaustive possibilities:

| Second-row labels | Third-row split | Exact check |
|---|---|---|
| Both D | All third labels | `check_const_double_ends.py` |
| One D, one S | All third labels, using mirror to start on the D second | `check_const_one_second.py` |
| Both S | At least one D third, chosen forward via mirror | `check_const_two_single_seconds.py` |
| Both S | Both S third, hence genuine stars | `check_const_double_star.py` |

**Both D second.** The second clocks are selected from the two other fixed doubled labels. Both literal third phases are evaluated; all available paired product comparisons are enforced. If either third is doubled, consistency of \(B\lambda\) already rejects the pair of prefixes. Otherwise \(r=q_{\rm f}/2\) and \(\lambda=q_{\rm f}/q_{\rm r}\) are fixed. The known doubled readings fix two or three actual values of \(A_2\); in the two-value case (2) fixes the missing value because \(2-\ell w_d\ne0\) in both diagonal fields. In the three-value case (2) remains a test. Required singleton zeros of the reconstructed quartic reject the rest. Each diagonal has 16 two-ended combinations; none passes.

**Exactly one D second, or both S second with a D third.** A D third paired with an S second has only the two admissible doubled clock labels and two exact prefix modes: the mode and \(x_3\) determine the second clock. With D,S,S on one side alone, its star gap is the only possible free scalar \(u\); the mixed-second script conservatively also tests the uniform arithmetic candidate \(u=2\). When a forward singleton already pins \(r\) and the mirror has a singleton, \(\lambda=r/r_{\rm r}\) is known and all doubled fits, (2), and all located singleton \(H\) zeros are affine in the one \(B\). With two known double values, solve (2) for the third; otherwise keep (2) as another affine equation. For fixed \(u\), test exact affine consistency and \(B\ne0\). For free \(u\), all two-by-two minors of the affine system must vanish; their numerator gcd is a unit after removing **only** nonzero guards. The code also asserts that every denominator cleared belongs to declared nonzero guards.

The only remaining form within these two rows of the table has an all-doubled forward triple. The paired product fixes \(M=B\lambda\), the mirror singleton residual is \(r_{\rm r}\), and \(r=\lambda r_{\rm r}\). All three \(A_2\)-values are \(L_4(d)/g_{\rm f}(d)-M g_{\rm f}(d)/\lambda\). Multiplying (2) by \(\lambda\) gives
\[
  T_0\lambda=M T_1-(8-\ell)/r_{\rm r},\quad
  T_0=\sum_d\frac{2-\ell w_d}{g_{\rm f}(d)},\quad
  T_1=\sum_d (2-\ell w_d)\frac{g_{\rm f}(d)}{L_4(d)} .
\]
The genuine \(T_0=0\) case is not divided: the right side must vanish and the singleton requirements are still affine in \(\lambda\); the code checks their exact equations or guarded minors together with that scalar right side. Thus no infinite families are discarded merely by assuming affine pivots.

**Both D,S,S stars.** All singleton rows are used in the two prefixes. With \(X=(u-1)^2\), \(Y=(u_{\rm r}-1)^2\), their actual centered node product is
\[
 H(t)=((t-(2-m))^2-X)((t+(2-m))^2-Y).
\]
In particular \(X,Y\notin\{0,1,2\}\) by the genuine star and residual guards; \(r=(2-X)/2\) and \(\lambda=(2-X)/(2-Y)\). At the two physical endpoints, \(g=1/2\) in the respective normalized orientation, and \(H(-h)=(1-X)((3-2m)^2-Y)\). Put \(C=L_4(h)+(3-2m)^2\). The first U equation gives \(B=-4(C-Y)/(2-X)\); the mirror equation gives \(B\lambda^2=-4(C-X)/(2-Y)\). Hence \((C-2)(Y-X)=0\) after clearing the nonzero guards. Exactly \(C\ne2\) in both diagonal fields. Thus \(X=Y,\lambda=1\). At \(m=1\) the two actual endpoint pairs coincide, impossible. At the other diagonal, substitute \(B=-4(C-X)/(2-X)\) and \(A_2=(L_4-H)/r-Br\) into (2) and multiply by \(r\). The quadratic terms in \(X\) cancel between \(-H(d)\) and \((C-X)(2-X)\), leaving a checked nonconstant linear polynomial over \(\mathbb Q(a)\), which fixes \(X\).

Only the doubled labels remain for the fourth row. The first D,S,S triple has actual quadratic interpolant \(T_2(x)=-1+2x-x^2/2\), even though its two singleton positions were not solved individually. Use the actual affine fourth read from the companion:
\[
 g_4\!\left(\tfrac43-\tfrac{\kappa+4}{3\kappa}(x_4-1)\right)
                  =-1+3x_4-\tfrac32x_4^2+\tfrac16x_4^3,\qquad \kappa=2-X.
\]
At the two noncentral doubles each spare residual is \(-L_4(h)/(B/2)\), since one actual root \(1/2\) was used by the two ends. At the central double the gcd tests the affine read directly against \(U(0,g_4)\). None passes. No division by the affine fourth coefficient or square-root choice is needed, so free fourth residuals and all coefficient-field extensions are covered.

## Replay and native scope

In this folder run `python check_const_double_ends.py`, `python check_const_one_second.py`, `python check_const_two_single_seconds.py`, and `python check_const_double_star.py`. Tested with SymPy 1.14 and flint ground types. All calculations are exact. The [Lean scalar companion](../../lean/RKCert/Research/SDIRKEightDirtySevenConstant.lean) is staged source for the rational simplification and polynomial factors. The nilpotent trace and tableau chronology bounds are documented mathematics with exact replays, not end-to-end native Lean. No finite-characteristic claim is made.
