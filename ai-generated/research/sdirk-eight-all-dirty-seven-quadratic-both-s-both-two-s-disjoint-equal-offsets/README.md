# Disjoint two-later-singleton prefixes: no same-phase equal-offset chart

Assume the [disjoint (1,1) seven-clock scope](../sdirk-eight-all-dirty-seven-quadratic-both-s-both-two-s-disjoint-scale/README.md): strict ten-stage SDIRK, ordinary order at least eight over a characteristic-zero field, both physical endpoints singleton, exactly seven distinct clocks and all ten literal quadratic defects nonzero. Each physical endpoint prefix uses one later S and one later D, with no shared D, and both have the **same true phase** and the same normalized later S offset \(a=b\). This packet excludes A2A2, A3A3, SS. No real ordering, nonnegative weights, or tableau reflection symmetry is assumed.

## Paid reflection, odd cubic, three possible fourth labels

Normalize the diagonal to one, \(y=x-1\); endpoints are \(0,H\). Put \(h=H/2,\ m=h+1,\ w=y-h\). The pair data, including later defects, are the [actual arithmetic/ star formulas](../sdirk-eight-all-dirty-seven-quadratic-both-s-both-two-s-disjoint-rank/README.md). If \(a\) is the common later S offset, the actual common D offset in each side's own normalized axis is \(p=a/2,2a,2-a\) for A2,A3,star. In a star either actual noninitial D order gives the same two paid defects and the same second-defect scalar \(\kappa\), by its own formula.

At \(a=b\) with one S tap law, the two actual scale lines for \(R\) and \(K=\lambda(A_2+B R)\) are satisfied at \(\lambda=1\) by the reflection of their paid four S values. Their simultaneous rank zero is [already impossible](../sdirk-eight-all-dirty-seven-quadratic-both-s-both-two-s-disjoint-rank/README.md). Therefore the actual scale is \(\lambda=1\); this statement is about pair data, not about all tableau rows. Let \(f_s,g\) be the paid later S and D defects; they are nonzero. Set \(x_s=a-h,\ d=p-h\); the four S labels are \(\pm h,\pm x_s\) and the observed D labels \(\pm d\), all distinct. Both actual \(R\) and \(C=A_2+B R=K\) are even about the center because their endpoint reads are equal. Thus
\[
 R(w)=\tfrac12+r(w^2-h^2),\quad
 r=\frac{f_s-1/2}{x_s^2-h^2}\ne0,\qquad
 C(w)=2L_4(h)+c(w^2-h^2),\quad
 c=\frac{L_4(x_s)/f_s-2L_4(h)}{x_s^2-h^2}.
\]
Coprime consecutive Legendre polynomials imply \(L_4\) is coprime to \(R\) in the true projection \(Q_0=L_3-F_*L_4\). The true affine quotient \(F_*=(L_3/L_4)\bmod R\) is odd since \(R,L_4\) are even and \(L_3\) odd. Therefore \(Q_0/R\), the true cubic on the three D labels, is odd. Its other actual D is at the center \(w=0\). This holds even if \(R\) has a repeated root.

Put \(\sigma=(d^2-3m^2/5)/L_4(d)\), the actual nonzero slope of \(F_*\) paid at \(d\). The first clock row is the necessary graph identity
\[
 \eta_R=h^2-\frac{1}{2r}
    =\frac{1}{\sigma}+\frac{6m^2}{7}-d^2=\eta_Q,
 \qquad
 Q_0=-\sigma w(w^2-d^2)(w^2-\eta_Q).
\]
With the paid D defect \(g\), the true graph-off guard \(g-R(d)\ne0\) and Vieta fix
\[
 B=\frac{L_4(d)-g C(d)}{g(g-R(d))}\ne0,\quad
 A_2=C-BR,\quad g_{\rm mate}=-L_4(d)/(B g)\ne0 .
\]
By evenness this is the unused mate value at **both** \(\pm d\). The singleton nodal quartic is
\[
 J_S(w)=L_4-R C=j(w^2-h^2)(w^2-x_s^2),\qquad j=1-r c\ne0 .
\]
All four S are consumed by the two endpoint prefixes. The other four physical stages are the two observed-D mates and two center-D copies.

## Exact ordinary trace, without a split residual assumption

Use the [normalized nilpotent trace](../sdirk-eight-all-dirty-seven-constant/README.md#the-trace-gate-and-its-normalization), \(\sum 1/g_i=m\sum b_i/g_i\). The unweighted side is exactly
\[
 4+2/f_s+A_2(0)/L_4(0)+2A_2(d)/L_4(d),
\]
where the D terms use the inverse sums of their two Vieta roots. No ordering of those roots is needed.

For the weighted side, set \(p_3(w)=w(w^2-d^2)\) and \(H_3=4m^6/175\), the normalized centered \(L_3\) squared norm. Write \(\nu_i=b_i g_i\). The [exact Cauchy residue formulas](../sdirk-eight-all-dirty-clock-census/FIBRE-RESIDUES.md) grouped by clock give \(B H_3/(P' J_S)\) at D and \(B H_3/(P J_S')\) at S, where \(P\) is the actual elimination cubic, \(P R=BQ_0\). Here \(P=-B\sigma p_3/r\), so set \(J_\nu=-r H_3/\sigma\). At a doubled label \(w\), the aggregate \(\sum \nu_i g_i\) is \(R(w)\sum \nu_i\) by the second Cauchy numerator. The true fibre equation \(L_4=g(A_2+B g)\) also gives
\[
 (A_2+B g)^2=A_2^2+B L_4+A_2 B g .
\]
Thus the grouped summands for \(b/g=\nu/g^2\), respectively at D and S, are
\[
 V_D(w)=\frac{J_\nu\,[A_2(w)^2+B L_4(w)+A_2(w)B R(w)]}
                   {p_3'(w)J_S(w)L_4(w)^2},\qquad
 V_S(w)=\frac{J_\nu}{p_3(w)J_S'(w)R(w)^2}.
\]
All denominators are true nonzero by distinct simple S/D labels, nonzero graph-off and Legendre guards and the paid graph/curvature. The exact weighted sum is \(V_D(0)+2V_D(d)+2V_S(h)+2V_S(x_s)\). This expression does not assume the two D residuals are split in an auxiliary field. It uses the actual Cauchy aggregate and applies also if \(R\) and \(p_3\) share a root.

## Both actual fourth reads and exact contradiction

Let \(T_2\) be the quadratic through the three genuine first forward residual values at actual \(x=1,1+a,1+p\) (these preserve the true paid pair values, not an arbitrary tap order). Write \(b_x,c_x\) for its linear/quadratic coefficients. The [literal fourth gate](../sdirk-eight-all-dirty-seven-clock/README.md#literal-fourth-reads-including-singular-pivots) is
\[
 C_4(w)g=N_4(w),\quad C_4=1-\Lambda+b_x+c_x\Delta,\quad N_4=T_2-JT_2 ,
\]
with \(x=1+h+w,\ \Lambda=1+(x-1)/\kappa,\ \Delta=4/3+2(\kappa+1)(x-1)/(3\kappa)\), and primitive \(J\) from zero. The paid first-three profiles and actual \(\kappa\) of the two genuine orientations are identical in their own coordinates. Therefore the **same** affine gate applies to each fourth in its own axis. If either fourth is a noncentral mate, then one of \(g_{\rm mate} C_4(d)-N_4(d)=0\) or \(g_{\rm mate}C_4(-d)-N_4(-d)=0\) is necessary. Otherwise both distinct physical fourth rows are the two distinct residuals at center, with scale \(\lambda=1\). They solve the identical affine test, so \(C_4(0)=N_4(0)=0\) is necessary; do not discard this singular affine case.

Project the graph row in \(a\) against trace, the two mate tests, and the two center tests separately. These are ordinary exact resultants even if a later leading coefficient drops. Only actual nonzero \(H\)-guards are stripped. The exact profiles are:

| Phase | Five projected degrees (trace, +, −, center coeff, center constant) | Common factors for either mate branch | Center branch |
| --- | --- | --- | --- |
| SS | 47,32,29,11,9 | one degree 12 | none |
| A3A3 | 73,55,48,23,17 | degrees 1 and 12 | none |
| A2A2 | 121,82,78,26,26 | degrees 1,3,24 | none |

Every listed factor is irreducible and simple; the plus/minus outer factors agree, but both actual rows are checked in their exact fields independently. At each of the twelve projected mate fibres the exact joint \(a\)-gcd has degree one. The degree 12 and 24 factors lie entirely on the true forbidden \(L_4(d)=0\); the small degree 1/3 factors are on \(t=H-a=0\), which would repeat the first singleton label. The exact audits keep all field embeddings and do not invoke real order, a finite-prime filter, or an invertible fourth pivot.

Run `SYMPY_GROUND_TYPES=flint python check_equal_offsets.py` with SymPy 1.14 and python-flint 0.8. The replay is self-contained. The [Lean scalar companion](../../lean/RKCert/Research/SDIRKEightDirtySevenBothSingletonBothTwoSDisjointDiagonal.lean) verifies the inverse-square clearing and two-center-read gate; the full trace and rooted-order ingress are mathematical with exact replay. This closes the same-phase equal-offset chart only. The general stage interval is unchanged.

The exact arithmetic was independently replayed. The accompanying Lean scalar statement is a draft, not asserted kernel-checked in this release.
