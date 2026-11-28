# Sole genuinely nonliteral fifth transport, star rear

This excludes the indicated ten-stage strict SDIRK8 chart over a characteristic-zero field. The cubic defect is detected and there are seven distinct ordinarily active clocks; exactly the physically weight-zero first stage has nonzero quadratic residual, \(k\ne0\), and the affine active profile is nonconstant and coprime to \(L_4\). Exactly one literal front \(a\) is ordinarily active. Actual physical fourth \(s\) is active, and physical fifth \(y\) is the sole actual nonliteral reverse contributor at \(z=\gamma y\), not an ordinary node. The active eighth is star. The arithmetic eighth and the other nonliteral positions are not covered by this packet. The global **10–11** interval is unchanged.

## True anchors and possible zero at fifth

The actual weighted fifth transport equals that physical stage's own defect and pure-four reads because it is the sole reverse contributor at its site. The \(\gamma\)-normalized clocks \(a,s,y\) are actual values. Use the true ordinary \(a,s\) as the two anchors of the active rational profile:
\[
 Q(Y)=H_4(s)L_4(\gamma a)(s-Y)+h_aL_4(\gamma s)(Y-a),\qquad
 P(Y)=h_aH_4(s)(s-a)L_4(\gamma Y).
\]
Here the actual \(H_4(s)\ne0\) is an ordinary active defect, not the virtual fifth amplitude. This fixes \(Q,P\) independently of actual \(y\). It gives \(Q(y)h_y=P(y)\) also at the sole transported fifth. The genuine \(h_y\) **may be zero**; in particular no \(L_4(z)\ne0\) assumption enters.

The proof uses the [previous pure-four two-anchor front](../sdirk-eight-silent-one-seven-distinct-coprime-nonliteral-fourth-finite/README.md), but rebuilds its resultant: the actual ordinary fourth **may equal the other literal silent clock** \(b\). Its strict cubic read uses the identity of the cubic nodal product on \(a,b,s\), valid with a repeated clock. The projected \(Ah\) scalar interpolation uses the corresponding exact polynomial identity; it does not divide by \(s-b\). The fifth itself has \(y\ne a,s\) because its transport site is separate from all ordinary sites. The padded fifth equations \(E_T,E_A\) and their primitive cross \(D(s,Y)\) are used after only true prior-root factors and \(H_4(s)\) factors. Eliminating the fifth amplitude divides by the actual nonzero \(H_4(s)\), never by \(h_y\). The padded resultant of \(E_T,D\) gives \(J(\gamma,s)\), of \(s\)-degree \(16/17\) and diagonal degree 12 for the two literal front types. No \(s-b\) guard is removed.

## Affine transport equation from the reflected star gap

Write \(x=1-\gamma,\ c=x-\gamma u,\ d=x-\gamma(2-u),\ v=u-1,\ V=v^2,\ k=2-V\), and \(q(X)=\gamma Q(X/\gamma)\). Denote \(X_z=x-z,\ U=q(x)X_z,\ l=\gamma L_4(x)\). The genuine chronological factors \(q(x)\) and \(X_z\) are nonzero. Write the exact centered cubic
\[
 \frac{L_4(c)-kL_4(x)}{u}=p_0+p_2V+v(p_1+p_3V)
\]
and \(b_0=q(x)+q_1 X_z-\gamma q_1,\ b_1=-\gamma q_1\). The two reflected tail reads are
\[
 U(p_0+p_2V)+l(2-V)b_0=0,\qquad
 U(p_1+p_3V)+l(2-V)b_1=0.
\]
Their affine cross has an exact factor \(U\), so the [guarded cross](../../lean/RKCert/ReviewedNative/SDIRK8FourthRearSaturation.lean) requires
\[
 K(\gamma,s,Y)=U(p_0p_3-p_2p_1)+l[b_0(2p_3+p_1)-b_1(p_0+2p_2)]=0
 \quad\text{at }Y=y,\ z=\gamma Y .
\]
After true source factors this polynomial is **affine in \(Y\)**. Eliminate it against \(D(s,Y)\) by a padded resultant, without assuming its actual \(Y\)-slope nonzero. This gives an independent \(B(\gamma,s)\) of \((s,\gamma)\)-degrees \((12,39)\). Exact specialization at \(\gamma=1\) preserves both \(s\)-degrees and makes the pair \(J,B\) coprime in all four phases, so the padded diagonal \(G=\operatorname{Res}_s(J,B)\) is nonzero.

## Exact whole diagonal and residue fifth/gap

Reconstruct \(G\) over \(\mathbb Q(t)\), \(t^2=1/2\), using both split evaluations of height-bounded integral coordinates in \(\mathbb Z[\sqrt2]\). With nominal \(s\)-degrees \(m,n\), cleared inputs, and the submultiplicative basis norm \(\lVert A+\sqrt2B\rVert=\sum|A|+2\sum|B|\), the coefficient bound is \((m+n)!\lVert J'\rVert^n\lVert B'\rVert^m\). A CRT product exceeding twice the bound gives a unique centered result. Independent full reduction at \((1103,161)\) preserves the exact degree **768/807** (star/arithmetic literal front).

No diagonal or finite residue root is deleted by a modular guard. At each reduced diagonal factor at least one actual \(s\)-equation has surviving nominal lead. Use the resulting monic local algebra and impose both necessary \(s\)-equations. At each retained \(s\), at least one of the necessary \(y\)-polynomials \(D,K,E_T,E_A\) has surviving nominal lead, making \(y\) integral; their common roots are all retained. In each surviving \(y\)-algebra at least one tested linear combination of the two centered slopes is a unit, so \(V\) is integral. Use the full monic quadratic \(v^2-V\), retaining both signs even on a ramified residue, then test both actual affine reads and the pole-free five-node determinant.

Its five ordinary pegs are \(\gamma a,\gamma s,x,c,d\), **not** \(z=\gamma y\). The determinant exists by the [exact paid rational Bézout identity](../sdirk-eight-silent-one-seven-distinct-anchors/README.md), and is evaluated by Newton divided differences without dividing any coincident residue pegs. The generated residual ideal contains a unit in every retained component. Thus this star eighth chart has no realization. The [native receipt](../../lean/RKCert/ReviewedNative/SDIRK8NonliteralFifth.lean) kernel-checks zero-amplitude elimination, the actual ninth affine identity, and the literal repeated-clock cubic read on Lean/Mathlib 4.36.0. The concrete diagonal and finite arithmetic are source-level.

Run `python3 check_nonliteral_fifth_star.py` in the sibling proof tree with `sympy==1.14.0` and `python-flint==0.9.0`. It recomputes all exact coefficients and verifies all four orientations with no private cache.
