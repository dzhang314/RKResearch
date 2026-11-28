# Both literal fronts silent, arithmetic rear: a finite-profile gate

This packet is a **finite reduction**, not an exclusion. Use the [detected seven-distinct active strict SDIRK8 chart](../sdirk-eight-silent-one-seven-distinct-anchors/README.md) at ten stages over a characteristic-zero field. Only the individually weight-zero first stage has nonzero quadratic residual, \(k\ne0\), and \(Q\) is affine nonconstant coprime to \(L_4\). Neither literal front is active. The eighth, ninth, and terminal stages are active with arithmetic eighth geometry. The [star rear](../sdirk-eight-silent-one-seven-distinct-coprime-no-front-star/README.md) is separately excluded. This packet proves that only finitely many complete clock/weight profiles are possible in the arithmetic placement; it does not say whether any is realized by a tableau.

Write \(\boldsymbol w=\boldsymbol b^{\mathsf T}M,\ \boldsymbol h=N\boldsymbol g\), \(N=A-\gamma I,\ M=CA-AC-A^2\). The two physically silent literal clocks are distinct and there must be a separate reverse aggregate at one of them. It is provided by the **sole** actual silent at \(z=\gamma a\), with \(a\) its normalized clock and \(h_a\ne0\) its known actual normalized defect. Its actual amplitude and pure-four reads equal the transported rational profile; the other silent literal at \(b\) does not transport. All seven physical stages four through ten are active. In particular \(L_4(z)=Q(a)h_a\ne0\) despite \(z\) being inactive.

## Arithmetic tail and exact guard transfer

Let \(x=1-\gamma,\ c=x-\gamma u,\ d=x-2\gamma u,\ k=1+2u-u^2\). At active sites the ratio is \(w_i/b_i\propto L_4(c_i)/(q(c_i)(c_i-z))\). As in the [shared-literal arithmetic proof](../sdirk-eight-silent-one-seven-distinct-coprime-shared-arithmetic/README.md), put
\[
 \mathcal A=(x-z)L_4(c),\quad \mathcal B=k(c-z)L_4(x),\quad
 F=(\mathcal A-\mathcal B)/u.
\]
The actual affine shape is proportional to \(q(X)=\gamma\mathcal B-F(X-x)\). The arithmetic eighth equation is
\[
 H(x-z)L_4(d)(c-z)+T(d-z)(2\mathcal A-\mathcal B)=0,
\quad H=-2+u+4u^2-u^3,\quad T=4u^3-12u^2+3u+2.
\]
After exact forbidden \(\gamma,u\) powers, call it \(R(\gamma,u)=0\). It depends only on the actual reverse-root clock \(z\), not on which literal is ordinarily active. Thus the shared arithmetic \(R\) transfers **exactly** by letting its silent literal label be the sole transported literal here. Its exact \(u\)-degree is five; the coefficient gcd in \(\gamma\) is one.

The appropriate nonzero diagonal guards are \(\gamma,\ x-z,\ L_4(x),\ L_4(z)\), not the nonzero \(L_4\) guard of a nonexistent active literal. Both forbidden active Gauss-tail contacts have exact diagonal resultants, \(\operatorname{Res}_u(R,L_4(c))\) and \(\operatorname{Res}_u(R,L_4(d))\). With these guards their squarefree degrees are 32 each, and their exact gcd is one in all four orientations. The rational norm of the first is irreducible of degree 64, while the second has rational norm factor degrees 40 and 12 (the latter squared). The degree-four common contact from the earlier chart is absent precisely because \(L_4(z)\) is now forbidden. This is an exact transfer, not accidental modular vanishing. For an eventual exclusion the affected diagonal roots must **not** be deleted wholesale: keep other \(u\) roots and remove just the exact \(u\)-factors meeting a forbidden Gauss tail, as in the shared arithmetic proof.

## Smaller literal fifth elimination

The active normalized profile is \(Q_0(Y)h=P(Y)\), with \(Q_0(Y)=L_4(\gamma a)q(\gamma Y)\) and \(P(Y)=h_a q(\gamma a)L_4(\gamma Y)\). The actual fourth \(s\) satisfies \(\Phi=(Q_0H_4-P)/(Y-a)=0\), after the earlier padded \(a\) factor. Its \(H_4(s)\ne0\) by the coprime ordinary active profile. For each of the two pure-four reads, use actual \(a\) (sole transported) and actual fourth \(s\) as affine slope anchors, not the other silent literal. For active fifth \(y\) its two cleared reads have the form
\[
 H_4(s)T_0(s,y)+T_1(s,y)h(y)=0,\quad
 H_4(s)A_0(s,y)+A_1(s,y)h(y)=0.
\]
Eliminate \(h(y)\) first. The necessary determinant \(T_0A_1-A_0T_1\) is independent of \(\gamma,u\); its earlier padded factors \(y-a,y-s\) divide exactly. The resulting \(D(s,y)\) has bidegree \((3,3)\), and its \(y\)-coefficient gcd over \(\mathbb Q(t)[s]\) is one. Use this smaller \(D\) against the padded \(\tau_4\) profile equation \(E_T\) after substituting \(h=P/Q_0\). In \(E_T\) the remainder from the \(y-s\) division is exactly its defect-free strict read at \(s\) times \(\Phi(s)\). Thus a genuine fifth is a common root of \(D,E_T\). The first resultant \(J=\operatorname{Res}_y(D,E_T)\) has \(s\)-degree 21 for a star front, 23 for arithmetic front, \(u\)-degree nine, and diagonal degree 30.

## Exact nonzero projection and the full profile census

In the branch where the \(u\)-leading coefficient of \(R\) is nonzero, let \(U\) be the monic degree-five arithmetic tail quotient over the rational diagonal coefficient field. It is not assumed irreducible. The \(s\)-resultant of \(\Phi,J\) in \(U\), followed by its multiplication norm in that quotient, is a necessary scalar diagonal equation. At any actual \((\gamma,u)\) evaluation at its actual \(u\) is a nonzero linear functional on the five-dimensional quotient (the constant coordinate reads 1). It annihilates multiplication by an element vanishing at that root, so the multiplication determinant is zero.

This norm is **not the zero rational function**. It suffices to specialize exactly at \(\gamma=1\) (not asserted to be an RK diagonal). In each of all four literal orientations, the tail leading is nonzero there, and the norm of the fourth \(s\)-leading coefficient is also nonzero. Thus the fourth leading coefficient is a unit in the specialized tail quotient. Use an exact pseudo-remainder of \(J\) by \(\Phi\), then the small Sylvester determinant, which differs from the original resultant only by a power of that unit. Its multiplication norm is exact nonzero in \(\mathbb Q(t)\), checked by arithmetic. The symbolic diagonal numerator therefore has finitely many roots. Add the exact roots of the tail leading coefficient from the omitted branch. No good reduction or guessed degree of a reduced norm is needed for this finite gate.

For each such \(\gamma\), the primitive coefficient gcd of \(R\) ensures only finitely many \(u\), including at its lower degree. For each pair, \(\Phi\) is not identically zero: \(Q_0H_4=P\) as polynomial identity would force the genuine affine \(q\) to divide \(L_4\), contrary to coprimality. Thus there are finitely many actual fourths. The primitive \(y\)-content of the exact \(D(s,y)\) gives finitely many actual fifths for each fourth. This supplies five actual ordinary pegs \(x,c,d,\gamma s,\gamma y\). The [signed rational moment mask](../sdirk-eight-silent-one-seven-distinct-anchors/README.md) on those five pegs gives the exact missing quadratic for the two remaining active clocks. Its \(2\times2\) Hankel determinant is nonzero for an actual tableau because there are two distinct remaining ordinary nodes with nonzero signed masses. Its roots give at most two labels for those last clocks, and the ordinary quadrature weights are uniquely determined by the first seven scalar moments on seven distinct nodes. Hence the entire actual clock/weight profile is among finitely many choices. This is not finiteness of all strict tableau entries.

## Replay and remaining scope

Run `python3 check_nofront_arithmetic_finite.py` in the sibling proof tree with `sympy==1.14.0` and `python-flint==0.9.0`. It reuses the finite six-clock and literal companions and the exact [shared arithmetic](../sdirk-eight-silent-one-seven-distinct-coprime-shared-arithmetic/README.md) projection helpers. The nonzero specialization, content and Gauss guard checks are exact over \(\mathbb Q(t)\), \(2t^2=1\). Auxiliary modular coprimality only certifies exact degree-preserving coprimality in the existing factor helpers; there is no modular-absence claim about this chart. The [native Lean lemma](../../lean/RKCert/ReviewedNative/SDIRK8NormProjection.lean) kernel-checks the root-evaluation norm implication on Lean/Mathlib 4.36.0.

To finish this chart, expand or otherwise certify the finite symbolic diagonal norm and test the retained actual fourth/fifth and signed masks, keeping the exact leading-zero and Gauss-tail branches. The one-active-literal nonliteral sole-balance chart is separate: the second physical silent can be four, five, six, or seven with either active rear, or eight with its silent geometry. In that chart the extra reverse root is not at either literal clock, and a transport at fifth need not have nonzero defect. The unrestricted strict SDIRK8 interval remains **10–11**.
