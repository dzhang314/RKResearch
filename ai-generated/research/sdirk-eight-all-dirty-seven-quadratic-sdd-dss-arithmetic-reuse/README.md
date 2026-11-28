# S,D,D versus rear D,S,S arithmetic: no reused terminal D

Consider an all-dirty strict ten-stage SDIRK tableau of ordinary order at least eight over a characteristic-zero field, with exactly seven distinct clocks and exactly one singleton physical endpoint. Orient from that singleton, by genuine weighted mirror if necessary. Suppose the front opening is S,D,D and the reverse opening is D,S,S with a true nonzero-tap arithmetic third row. The terminal D clock **cannot occur in the front pair**. Both true forward phases are covered. The case where the terminal clock label is new is separate. This is not a change to the general 10–11 stage interval, and no coefficient ordering or field splitting is assumed.

## Geometry and a nonvanishing graph-ratio pivot

Normalize the diagonal to one. Use \(y=x-1\), \(H=2(m-1)\), \(m=1/(2\gamma)\), and evaluate the monic Legendre modes \(L_3,L_4\) at \(t=y-H/2\). The endpoint labels are \(0,H\), with \(H\ne0\). By the [seven-clock decomposition](../sdirk-eight-all-dirty-seven-clock/README.md), the genuinely quadratic singleton graph \(R\), normalized by \(R(0)=1/2\), satisfies \(\mathcal Q=L_3-F_*L_4\propto P R\) where \(P\) is cubic on the three D labels and \(F_*\) is affine of nonzero slope.

In the reused-terminal chart the front D labels are \(H,d\). Forward arithmetic gives \(d=2H\); putting \(H\) third would make \(d=H/2\) a centered D and is forbidden by the [single-end parity lemma](../sdirk-eight-all-dirty-seven-quadratic-one-singleton-arithmetic/PARITY.md). In forward star \(d=2-H\), with equal front defect values in either actual order. Let \(f_H,f_d\) be those actual known D defects. Fit \(F_*\) at \(H,d\) using \(L_3/L_4\). The D Legendre values are nonzero by consecutive coprimality. The quotient
\[
                   M_3(y)=\mathcal Q(y)/[(y-H)(y-d)]
\]
is exact, and equals a nonzero scalar times \((y-e)R(y)\) where \(e\) is the third D label. In particular \(M_3(e)=0\), with no assumption that it is a simple root or that the residual graph splits.

The late two original S labels are \(s=H-v,\ p=H-2v\), for the true reverse gap \(v\). Write
\[
 \kappa=1+2v-v^2,\quad D=-2+v+4v^2-v^3,\quad
 \widehat q=D-v(v-2)(3v-2).
\]
The genuine reverse normalized S defects are \(\kappa/2,\ \kappa\widehat q/(2D)\); indeed the literal third numerator \(N(v)\) equals \(\kappa\widehat q\). All \(v,\kappa,D,\widehat q,3v-2\) are nonzero as paid guards. In particular \(v=2\) is **not** eliminated solely as a gap, since the reverse first label is doubled. Let \(\lambda\ne0\) be the actual reverse-to-original defect scale and \(\mu=\kappa\lambda\). The graph readings satisfy
\[
 R(s)=\mu/2,\quad R(p)=\mu\widehat q/(2D),\quad
 \mu=-e M_s/[M_0(s-e)]
\]
where \(M_0=M_3(0), M_s=M_3(s), M_p=M_3(p)\) are all nonzero. These follow from \(M_3\propto(y-e)R\), and \(0,s,p\) being singleton with nonzero defects and distinct from D labels. They do not invert \(R\) at any D label.

Comparing the two S readings gives \(D M_p(s-e)=\widehat q M_s(p-e)\). Put
\[
 \mathcal A=(D M_p s-\widehat q M_s p)/v,\qquad
 \mathcal B=(\widehat q M_s-D M_p)/v .
\]
Their initially cleared \(v\) factors cancel polynomially by direct expansion (\(s=p=H,\ \widehat q=D\) at \(v=0\)). Their values satisfy
\[
       \mathcal A+\mathcal B e=0,\quad
       \mathcal A+s\mathcal B=\widehat q M_s,\quad
       \mathcal B(s-e)=\widehat q M_s\ne0 .
\]
Thus the apparently singular ratio pivot is **necessarily nonzero** in any actual tableau. In particular the recovery
\[
          e=-\mathcal A/\mathcal B,\qquad
          \mu=\mathcal A/(M_0\widehat q)
\]
is valid in the whole genuine chart. Here \(\mathcal A\ne0\) also follows because \(e\ne0\) and \(\mathcal B\ne0\). This avoids a spurious missing zero-determinant branch.

## Two paid singleton fits in addition to the third D condition

The two consumed residuals \(f_H,\lambda/2\) at the overlapping D label \(H\) are distinct, since the physical clock-defect pairs are distinct in the [complete intersection](../sdirk-eight-all-dirty-clock-census/README.md). Their product in \(L_4-g(A_2+Bg)\) gives \(\beta=B\lambda=-2L_4(H)/f_H\). Set \(\lambda A_2=T_0+\lambda T_1\) with these actual interpolation rows:
\[
 \begin{array}{c|cc}
  y&T_0&T_1\\\hline
 0&-\beta/2&2L_4(0)\\
 H&-\beta f_H&-\beta/2\\
 d&-\beta f_d&L_4(d)/f_d .
 \end{array}
\]
The first row is the true first-singleton equation, the second is Vieta's sum, and the last is the true observed front residual at \(d\). The three clocks are distinct, so the interpolation uses only known nonzero differences. Define
\[
 \begin{aligned}
 F_s&=4L_4(s)-2\kappa T_0(s), & G_s&=2T_1(s)+\beta\kappa,\\
 F_p&=4D^2L_4(p)-2\kappa\widehat q D T_0(p),&
 G_p&=2\widehat q D T_1(p)+\beta\kappa\widehat q^2 .
 \end{aligned}
\]
The two paid S equalities are \(F_s=\mu G_s,\ F_p=\mu G_p\), directly from \(L_4=g(A_2+Bg)\) at the actual S stages. Thus after substituting the forced scale the necessities in \(H,v\) are
\[
 \begin{split}
 E&=\mathcal B^3 M_3(-\mathcal A/\mathcal B)=0,\\
 X&=M_0\widehat q F_s-\mathcal A G_s=0,\qquad
 Y=M_0\widehat q F_p-\mathcal A G_p=0 .
 \end{split}
\]
The first expression is the *homogeneous* expansion of a cubic; neither of the latter equations divides by a coefficient of an affine fit. Cases of vanishing \(G_s\) or \(G_p\) are included.

## Exact polynomial contradiction

Clear denominators only against true phase guards, actual clock distinctness, Legendre values at D labels, the nonzero graph values above, and the proved ratio pivot. The physical third D is different from \(0,H,d,s,p\), is not centered or antipodal to another D, and \(L_4(e)\ne0\). The two observed residuals at \(H\) are distinct, so the literal guard \(\mu-2\kappa f_H\ne0\) is also allowed. The normalized front singleton gives the [first-departure guard](../clock-localized-tail/tied-stage-floor/FIRST-THREE-ROWS-AND-PHYSICAL-LEVEL-OBSTRUCTIONS.md) against a forward gap of two. For a forward star, either actual \(H,d\) order has the same paid pair data; no arbitrary exchange of stages is used.

The guarded degrees \((\deg_H,\deg_v)\) of \(E,X,Y\) are respectively \((18,9),(20,5),(20,8)\) for front arithmetic and \((18,9),(14,5),(14,8)\) for front star. Project \(X,Y\) and \(X,E\) separately in \(v\) by integer resultants. After dropping only allowed \(H\)-guards, the degrees in \(H\) are 173 and 229 for front arithmetic, and 127 and 179 for front star. Their exact gcd is a unit in both cases. Polynomial resultant necessity does not require a nonzero specialized leading coefficient. All conclusions apply over every characteristic-zero field without full splitting or trace/fourth conditions.

## Replay

Run `SYMPY_GROUND_TYPES=flint python check_reused_terminal.py` (SymPy 1.14 and python-flint 0.8). The [Lean companion](../../lean/RKCert/Research/SDIRKEightDirtySevenQuadraticSddDssArithmeticReuse.lean) checks the nonvanishing ratio pivot and scale clearing. The tableau ingress and exact projections are separate mathematical proof and replay, not a full native Lean or finite-characteristic theorem.
