# Live-star paired rear repeat: equal grouped cardinals

Consider strict ten-stage SDIRK of ordinary order at least eight over a characteristic-zero field. Let \(\mathbf c=A\mathbf1,\ \mathbf g=A\mathbf c-\mathbf c^{\odot2}/2\), with common nonzero diagonal \(\gamma\). Assume exactly eight physical zeros of \(\mathbf g\) at seven distinct zero labels. The [earlier reductions](../sdirk-eight-eight-zero-late-mate/README.md) leave the two distinct individually silent off rows at positions 1 and 2, and only a live reflected star with one of physical rows 8 or 9 repeating a clock from rows 3 through 7. Write \(q\) for the repeated clock and \(p\) for the other member of that reflected pair, which is a singleton. This packet excludes the case \(B(q)=B(p)\) for the **grouped** ordinary cardinal numerators.

## 1. A split-free repeated-clock gate

Use \(A'=A/\gamma,\ \mathbf x=\mathbf c/\gamma,\ D=1/\gamma\), \(C'=\operatorname{diag}(\mathbf x)\), \(U=\ker\operatorname{diag}(\mathbf g)\). Let \(P_7\) be the monic seven-label polynomial, \(I_D(T^k)=D^k/(k+1)\), and \(B(x)=I_D(P_7/(T-x))\). In particular
\[
 B(q)=P'_7(q)(b_{\rm early}+b_{\rm rear})
\]
uses both physical copies. Write \(s=x_{10}=D-1\), \(m=D-2\), so the star pair is \(q,p=m\pm\delta\), \(\kappa=2-\delta^2\ne0\). The reverse pure quadratic row \(\mathbf z^\mathsf T\) has constant nonzero **grouped** barycentric numerator \(\Theta\): its six scalar moments vanish and it has a nonzero terminal singleton. Its actual star coordinates satisfy \(z_s=\omega b_s\) and \(z_i=\omega\kappa b_i\) at both members of the actual rear pair. These are the literal star ratios, with \(\omega\ne0\). Thus
\[
      B(s)=\kappa B(p),\qquad
      \Theta=\omega B(s)=\omega\kappa B(p).
\]
No equality between either weight at the repeated \(q\) and its aggregate is used.

As in the [early–rear rank proof](../sdirk-eight-eight-zero-early-rear/README.md#1-a-two-dimensional-forward-pure-space-produces-a-fourth-gate), multiplication by \(C'-qI\) sends \(F_4|_U\) into the span of \(L_{3,D},L_{4,D},L_{5,D}\) on the seven labels. This follows because \(F_5|_U\) has rank four, the difference of the two repeated coordinates is not in \(W_2\), and equality at that pair cuts \(F_5|_U\) to the three indicated Legendre modes. For any \(\mathbf f\in F_4|_U\), its product \((C'-qI)\mathbf f\) has such a polynomial trace, vanishing at \(q\). Divide it by \(T-q\) to get a polynomial \(S\) of degree at most four. It represents \(\mathbf f\) at every singleton, and
\[
 I_D((T-q)T^j S)=0\quad(0\le j\le2).
\]
No assertion that it represents either copy of \(q\) is made.

Let \(\mathbf w^\mathsf T=\mathbf z^\mathsf T-\omega\kappa\mathbf b^\mathsf T\). This row annihilates \(F_4|_U\), and vanishes at the **actual** two rear pair rows. Therefore
\[
 \mathbf w^\mathsf T(\mathbf f-S(\mathbf x))
   =w_{\rm early}\bigl(f_{\rm early}(q)-S(q)\bigr),\qquad
 \mathbf w^\mathsf T S(\mathbf x)=-\omega\kappa I_D(S).
\]
The grouped weight \(w_{\rm early}+w_{\rm rear}=w_{\rm early}\) is \(\omega\kappa(B(p)-B(q))/P'_7(q)\). After clearing these nonzero factors,
\[
 (B(p)-B(q))\bigl(f_{\rm early}(q)-S(q)\bigr)=P'_7(q) I_D(S).        \tag{1}
\]
This does not divide by the ordinary weight or pure coordinate of the early copy, and remains valid if that copy is silent.

## 2. Equal cardinals reduce to an already certified gap-free chart

If \(B(p)=B(q)\), then (1) gives \(I_D(S)=0\); the three tilted moments give \(I_D(T^jS)=0\) for \(j=1,2,3\). Thus \(S\) is on the line of \(L_{4,D}\). The singleton restriction of \(F_4|_U\) has dimension one because it contains this nonzero degree-four trace at six distinct singleton labels. Since \(F_4|_U\) has dimension two, there is a nonzero pure coordinate profile supported on the two copies of \(q\).

Let \(a,b,c\) denote the first three zero clocks in physical rows 3, 4, 5. The actual \(F_4|_U\) is detected by its first two zero reads, so \(q=a\) or \(q=b\): otherwise the pure profile just found would vanish at both detecting coordinates. Let \(\ell\) be the other of \(a,b\). With \(Z_2=(T-a)(T-b), Z_3=T Z_2\), their supported primitive discrepancies on singleton labels lie on the \(L_{4,D}\) line. The two primitive values at \(\ell\) are not both zero by the invertible first-two matrix, hence \(L_{4,D}(\ell)\ne0\). The supported cubic
\[
 S_3(T)=JZ_3(\ell)Z_2(T)-JZ_2(\ell)Z_3(T)
\]
has pure discrepancy zero at \(\ell\), hence at all singleton labels. It kills both actual early donor inputs \(a,b\), whether or not the early copy of \(q\) is silent. Its read at the third early zero \(c\) is diagonal. This gives the same independent cubic \(R_\ell(c)=(S_3(c)-JS_3(c))/(c-\ell)=0\) and the usual \(C_3(c;D)=0\) as in the [silent pure-root proof](../sdirk-eight-eight-zero-silent-pure-root/README.md#4-silent-and-star-a-finite-forward-cubic-and-diagonal-quartic).

The four early labels not in the rear pair are \(\ell,c,d,e\); write \(P_4=(T-\ell)(T-c)(T-d)(T-e)\). The ordinary nodal polynomial \(P_7=P_4(T-s)(T-p)(T-q)\) has mean zero, since its degree is seven and it vanishes at every weighted label. The now valid grouped equalities \(B(p)=B(q)\), \(B(s)=\kappa B(p)\) give precisely the same gap-free masks on \(P_4\):
\[
     T-s,\qquad (T-s)(T-m)^2,\qquad (T-m)^2-2.
\]
These are just the difference of the two cardinal means, the ordinary nodal mean with its squared-gap term canceled, and the second ratio after canceling \(1-\delta^2\ne0\) by label distinctness. Thus the checked star fibres for \(\ell,c,D\) and the two unknown other labels apply **unchanged**, with residue controls \((79,36)\) and \((103,73)\) according as \(q=a\) or \(q=b\). Their third-clock cubic accounts for \(c\), and their diagonal quartic gcd covers all algebraic roots of \(D\), not just prime-field values. Both orientations of the reflected pair are included.

## 3. Replay and scope

Reuse the independently checked star replay:
```text
python ../sdirk-eight-eight-zero-silent-pure-root/check_silent_pure_root.py star
```
It needs SymPy 1.14 and python-flint 0.8. The [Lean companion](../../lean/RKCert/Research/SDIRKEightEightZeroStarEqualCardinal.lean) checks the split-free scalar cancellation and equal-cardinal inference under their explicit guards. The saturation and chronology above are the source proof. This excludes equal grouped cardinals over characteristic-zero fields; the unequal case and global ten-stage question are separate.
