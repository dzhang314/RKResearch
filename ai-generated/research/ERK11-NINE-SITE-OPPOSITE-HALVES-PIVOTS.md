# Opposite-half different-free ERK11: no mixed-width or contact pivot drops

**Scope.** Continue the [opposite-halves finite chart](ERK11-NINE-SITE-OPPOSITE-HALVES-FINITE.md).
The four calibration sites are distinct, left extras are \(\{e,t\}\),
right extras are \(\{h,s\}\), \(t\ne s\), and the genuinely new
dormant clock is physical \(8,9,10\). Over a characteristic-zero
field with those actual premises, all widths have
\[
             H\ne0,\quad J_0\ne0,\quad R_{33}\ne0,\quad U_F\ne0,
 \qquad R_{33}=\frac{U_{4,4}(a,b)-T_4(a)T_4(b)}{ab}.
\]
Moreover the actual middle bilinear always has \(U_B\ne0\).
Thus both linear rows recover the same **unique** free-label
assignment at a fixed width pair and dormant clock. This
excludes every zero-pivot branch, not the remaining regular
finite width or dormant fibers.

## 1. Exact width projections forbid the exceptional loci

In the earlier finite atlas, let \(D,F,B\) denote the three
**reduced width polynomials** obtained by resultant in the
dormant clock, with the first projection from \(D_c\) and
the other two from \(N_F,N_B\). Each vanishes at a true
width pair. These polynomials have already removed only
width factors contained in independent live guards.
No divisions by the contact slopes were used there.

The four width equations to test are \(W=H,J_0,R_{33},U_F\).
The formula for \(R_{33}\) is polynomial division, checked
exactly; the visibly live \(a,b\) are not hypotheses about
sign. \(U_F=f_{10}-f_{01}\) depends only on \(a,b\) because
the first derivative contact is bilinear in the free labels
with width-only coefficients. In each width equation remove
only exact common divisors with the live width guards from
the original atlas before projecting \(W\) against \(D,F,B\)
by \(b\)-resultants. The respective \(a\)-degrees and monic
common gcd are:
\[
\begin{array}{c|r|c|c}
 \text{position}&W&(\deg_a\operatorname{Res}_b(W,D),
    \deg_a\operatorname{Res}_b(W,F),
    \deg_a\operatorname{Res}_b(W,B))&
    \text{common gcd}\\ \hline
 9&H &(200,272,272)&1\\
 9&J_0 &(200,272,272)&1\\
 9&R_{33} &(300,408,408)&1\\
 9&U_F &(390,524,540)&(a-2)^4\\ \hline
 8&H &(224,272,248)&1\\
 8&J_0 &(224,272,248)&1\\
 8&R_{33} &(336,408,372)&1\\
 8&U_F &(436,524,490)&(a-2)^4
\end{array}
\]
The two actual active orders give these same degree and gcd
receipts separately. The width realignment at physical 10
is reflection, exactly as in the finite atlas.
A true width solution with \(W=0\) has a common zero of
the three resultants, even if some polynomials drop degree
at that solution. The only nonconstant gcd would force
\(a=2\), i.e. \(h=1\), not a permitted calibration. Therefore
all four width quantities are live. The calculation uses
exact rational arithmetic only; it does not infer real
signs or reduce an unknown tableau modulo a prime.

## 2. The middle slope also cannot vanish

Use the earlier notation
\(B(u,v)=A_0uv+B_0u+C_0v+D_0\).
The exact model identities, checked on the same rational
polynomials, are
\[
 B_0-C_0=-HJ_0,\qquad
 633719116800000\,(A_0D_0-B_0C_0)
  =-a^2b^2 J_0 R_{33}.
\]
In the middle-dormant chart \((u,v)=(t,s)\) or \((s,t)\),
so the slope of the scaled linear row is
\(U_B=\pm(B_0-C_0)\ne0\).

In the edge chart \((u,v)=(z,s)\) or \((z,t)\), it is
\(U_B=\pm(A_0z+C_0)\). Its zero would force
\(B_0z+D_0=0\) by the actual middle equation; then
\[
       A_0D_0-B_0C_0
       =A_0(B_0z+D_0)-B_0(A_0z+C_0)=0,
\]
contrary to the displayed width determinant and all newly
proved-live factors. This is the same scalar affine
consistency gate already audited in the
[asymmetric center atlas](ERK11-NINE-SITE-ASYMMETRIC-CENTER-ATLAS.md).
No syntactic pivot is treated as automatically nonzero.

Finally, with the same free-root scale \(Y=\Delta t\), the
actual equalities now give
\[
       Y=-V_F/U_F=-V_B/U_B,\qquad
       t=Y/\Delta,\qquad s=(\Sigma-Y)/\Delta.
\]
The shifted Hankel \(\Delta\) was independently live.
Thus the finite atlas now has at most **one** ordered
free-label assignment per width, dormant clock and active
order instead of a choice of two. Exact exclusion of all
retained regular width fibers remains open.

The standalone replay reconstructs the widths and both
sets of projections in this note. The small ring-level
row compatibility and affine identities have Lean
counterparts in the existing scalar packets; the resultant
receipt is not claimed to be a Lean kernel computation.
