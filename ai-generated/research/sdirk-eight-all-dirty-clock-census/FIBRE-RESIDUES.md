# Further field restrictions on the surviving all-dirty clocks

Keep the all-dirty strict ten-stage hypotheses of the [clock census](README.md). Use the centered pair coordinates and polynomials \(U,V,P,Q\) defined there, and \(H_3=I(L_3^2)\ne0\). The five-double exclusion makes \(P\not\equiv0\). This note is a scalar diagnostic, not a further stage lower bound.

The actual clock polynomial, counting a doubled clock twice, is proportional to
\[
       W(t)=L_4(t)P(t)^2-A_2(t)P(t)Q(t)-B Q(t)^2 .
\]
At a singleton \(P(t_i)\ne0\) (otherwise \(P=Q=0\) forces both quadratic \(U\)-roots to appear, sharing the same label; the complete intersection is simple and exhausted by the physical pairs). Then \(W=P^2 U(t,Q/P)\) near that point, with \(W'(t_i)=-B P(t_i)J_i\ne0\), \(J_i=U_tV_g-U_gV_t\). At a doubled label, \(P=Q=0\). Its two roots in \(g\) are different, say \(g_1,g_2\); differentiating the elimination relation \(B V-FU=Q-gP\) gives
\[
 J_i=(g_i-g_j)(Q'-g_iP'),\qquad
 [ (t-t_i)^2]W=-B(Q'-g_1P')(Q'-g_2P').
\]
Here the right side in the second identity is the coefficient in the expansion at the double, and is nonzero by the two simple Jacobians. Thus the double has exactly multiplicity two. Together the physical roots have degree ten, which is also the upper degree of \(W\), leaving no extraneous projections.

The weight formula \(b_i g_i J_i=-H_3\) then yields exact Cauchy numerators:
\[
 \sum_i\frac{b_i g_i}{T-t_i}=\frac{B H_3 P(T)}{W(T)},\qquad
 \sum_i\frac{b_i g_i^2}{T-t_i}=\frac{B H_3 Q(T)}{W(T)} .
\]
At a singleton the residues follow from \(W'\) and \(g_i=Q/P\). At a double they follow by summing the two reciprocal Jacobians (or the two \(g_i/J_i\)) above. Both sides have at most simple poles at clock labels and vanish at infinity, so equality of these residues proves the formulas over the coefficient field. In particular at a double, its grouped \(b g\) aggregate vanishes **exactly when \(P'\) also vanishes there**, not merely because the pair is doubled. If there are seven labels, all three doubled labels are simple roots of the nonzero cubic \(P\), so all the grouped pure coordinates are nonzero. More generally canceling one factor per doubled clock gives its grouped pure barycentric numerator explicitly.

There is a separate residual-level restriction independent of clock grouping. There are at least four distinct nonzero \(g\) values: if there were at most three, the polynomial \(1-\prod_\nu(1-g/g_\nu)\) would have no constant term, degree at most three, and equal one on every physical row, contrary to the paid zero pure moments and ordinary mass one. A fixed level appears at at most four rows by \(U(t,g_\nu)\); if it appears four times then \(V(t,g_\nu)\) is identically zero, since it has degree at most three. The coefficient of \(t^3\) in that identity gives \(1-g_\nu [t^3]D_3=0\), so at most one level can appear four times. If there are exactly four levels, the paid moments \(\sum_i b_i g_i^j\) and \(\sum_i b_i t_i g_i^j\), \(0\le j\le3\), give a nonzero ordinary mass on every level and zero centered first moment on each level, by interpolation at the four nonzero levels (equivalently the mass vector evaluates interpolants at \(g=0\)). Thus any singleton level must be at the centered clock, and any endpoint with a singleton residual level forces \(m=1\). None of this uses signs or a real ordering.
