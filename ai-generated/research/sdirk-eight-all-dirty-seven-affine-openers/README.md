# Seven all-dirty clocks with an affine singleton graph: two full opener slices

Assume a strict ten-stage SDIRK tableau over a characteristic-zero field has ordinary order at least eight, no zero physical quadratic residual and exactly seven distinct clocks. Use the [seven-clock decomposition](../sdirk-eight-all-dirty-seven-clock/README.md): the three doubled clock labels (type D) are the simple roots of the cubic \(P\), the four singleton clock labels (type S) are the roots of \(H=L_4-R(A_2+BR)\), and \(Q=P R=B L_3-F L_4\). Singleton residuals equal \(R\); **neither** physical copy of a doubled label has that graph residual, even if \(R=0\) there. In this note \(R\) is affine and nonconstant (the constant case is [already excluded](../sdirk-eight-all-dirty-seven-constant/README.md)). Thus \(F\) is a nonzero constant by degree comparison.

**Conclusions.** Both endpoints cannot have doubled labels. Each actual orientation prohibits three leading singleton labels. Also:
1. If both endpoints are singleton, at least one orientation's second row is doubled.
2. If exactly one endpoint is singleton, its own second row must be doubled.

These conclusions retain all signed weights and field extensions. They do not eliminate the affine graph under every chronological ordering. No stage bound is changed.

## Scaled clock polynomial, endpoint and opener facts

Normalize the diagonal to one, the right endpoint to \(\ell=1/\gamma\), and use the doubled-centered clock coordinate \(y=2x-\ell\). The coefficients \(L_3,L_4\) are consecutive monic Legendre modes in \(t=y/2\). Define integer-scaled forms
\[
 J_3(y)=5y^3-3\ell^2y,\qquad
 J_4(y)=35y^4-30\ell^2y^2+3\ell^4.
\]
In particular \(L_4(t)=J_4(2t)/560\). If \(z\) is the doubled-centered coordinate of the unique zero of \(R\), \(Q(z/2)=0\); hence \(J_3(z),J_4(z)\ne0\) by coprimality and \(F\ne0\). The three D-label coordinates are precisely the roots of
\[
 K(y,z;\ell)=\frac{J_3(y)J_4(z)-J_4(y)J_3(z)}{y-z}.        \tag{1}
\]
The quotient is a **polynomial**; its value at \(y=z\) is the divided-difference derivative. This reduction retains \(P,R\) common roots, not just distinct ones. It follows from \(Q=P R\) and the nonzero scale \(B,J_4(z)\). If both endpoints were doubled, \(Q\) would vanish at the centered pair \(\pm(\ell/2-1)\). Oddness of \(L_3\), evenness of \(L_4\) and \(F\ne0\) would make both consecutive modes zero there, impossible also if the labels coincide.

In either genuine orientation the first three tests are the [literal gates](../clock-localized-tail/tied-stage-floor/FIRST-THREE-ROWS-AND-PHYSICAL-LEVEL-OBSTRUCTIONS.md): \(x_1=1\), \(u=x_2-1\ne0\), \(g_1=1/2\), \(g_2=\kappa/2\), \(\kappa=1+2u-u^2\ne0\). For arithmetic \(x_3=1+2u\) and \(g_3=q_{\rm num}(u)/(2D(u))\) with \(D=-2+u+4u^2-u^3\) and \(q_{\rm num}=(1+4u-4u^2)D+4u^2(3u-2)\). The legal arithmetic guards include \(D,3u-2\ne0\). For star \(x_3=3-u\), \(g_3=\kappa/2\) with \(u\ne1,2\). Different initial labels are genuine because the known first-three gate came from stage saturation and the literal taps.

If the first two rows are S, the affine slope of \(R(x)\) in the uncentered \(x\)-coordinate is \((2-u)/2\), so \(u\ne2\). If the first three are S, star cannot fit the graph, as its two different clocks would share a residual. Arithmetic would predict \(2g_3=1+4u-2u^2\), forcing
\[
 q_{\rm num}-(1+4u-2u^2)D=2u^2(u-1)^2(u-2)=0.
\]
Thus \(u=1\) and \(R(x)=x/2\). In fact this graph with the first two S is impossible regardless of the third label. When \(u=1\), \(A\mathbf g=\mathbf g\odot(\mathbf x+\mathbf1)/2\) by the actual paid grade-three clock relation, while \(A\mathbf x=\mathbf x^{\odot2}/2+\mathbf g\) by the definition of the normalized residual. Thus \(\mathbf e=\mathbf g-\mathbf x/2\) satisfies \(A\mathbf e=(\mathbf x/2)\odot\mathbf e\). At the **first** nonzero entry of \(\mathbf e\) strict triangularity with diagonal one forces \(x=2\). That is already used by the singleton second row: no doubled row can use that label. There is at least one nonzero entry of \(\mathbf e\) because doubled pairs lie off graph. This proves no three initial S rows and also excludes \(R=x/2\) in the two-early-S chart, with no fourth-coefficient inversion.

## Both endpoints and both second rows singleton

Orient the original pair data with actual first and last \(x=1,\ell-1\). The actual first S normalization gives \(R(x)=(x-1+a)/(2a)\) for a unique nonzero \(a\). The reverse normalization uses nonzero \(b\) in the same formula after reversing and scaling the residuals. The graph zero in the original orientation is \(x_0=1-a\), and in the reverse orientation \(x_0'=1-b=\ell-x_0\). Thus
\[
 \ell=2-a-b,\qquad z=b-a .
\]
The second S clock is \(x_2=3-1/a\) and the reverse second \(x'_2=3-1/b\). The preceding opener argument forces both third labels D. Their possible doubled-centered coordinates are
\[
 \begin{array}{c|cc}
 &\text{arithmetic}&\text{star}\\ \hline
 y_3 & 8+a+b-4/a & a+b+2/a\\
 y'_3 & 8+a+b-4/b & a+b+2/b .
 \end{array}
\]
Equation (1) must vanish in the corresponding original or reverse coordinate (the latter has reflected graph zero \(-z\)). All four S labels are now occupied by these two actual disjoint prefixes. Since \(R\) is affine, \(H\) is monic quartic and is precisely the product of their four uncentered clock factors. Its graph-zero value is
\[
 H(x_0)=(-a)(-2-a+1/a)b(2+b-1/b)
       =(a^2+2a-1)(b^2+2b-1).
\]
Here and in the next section \(H(x)\) denotes evaluation with \(t=x-\ell/2\). By definition the same value is \(L_4(x_0-\ell/2)=J_4(z)/560\). This yields one symmetric degree-four equation in \(a,b\). For each phase A/A, A/S up to reflection, and S/S, the replay forms the three pairwise resultants in \(a\) of the two cubic-evaluation numerator equations and this quartic. Their gcd in \(\mathbb Q[b]\) is one, so no common solution over any characteristic-zero extension is possible; the argument even permits extra roots from clearing guards. Only literal prefixes and graph/clock masks were used.

## Exactly one endpoint doubled and a singleton second at the other end

Use the weighted mirror to orient the singleton endpoint first. Here \(a\ne0,1\) still represents the graph, and \(b=2-\ell-a\) denotes the reflected-zero offset without assuming that the reverse first row is on the graph or that \(b\ne0\). The reverse first row is doubled, with original doubled-centered coordinate \(y_e=\ell-2=-a-b\). The forward third D coordinate \(y_f\) has the same two phase formulas as above. These two labels may coincide: the known forward third and the literal terminal are different physical rows that can consume the two roots at one label.

Apply (1) at \(y_e,y_f\). Exact resultant elimination in \(b\) has only the guarded factors \(a,a-1\) and the following irreducible factors:

| Forward third phase | Mesh field degree with \(y_f=y_e\) | Mesh field degree with \(y_f\ne y_e\) |
|---|---:|---:|
| Arithmetic | 9 | 22 |
| Star | 8 | 20 |

For each factor the gcd in \(b\) is linear; the reconstruction verifies both equations and the stated coincidence flags. All field embeddings are covered. For distinct anchors the third D label follows from the cubic coefficient sum, with no further extension. For coincident anchors the other two D labels are the two roots of an irreducible quadratic over the mesh field, retained together in the degree-18 or degree-16 tower. There is no assumption on real roots.

Write \(v=x'_2-1\) in the reversed orientation. If both its second and third labels are S, they must be arithmetic because a star would equate distinct values of the affine graph. They have normalized reverse labels \(1+v,1+2v\). Their original graph residuals are \(-(b+v)/(2a),-(b+2v)/(2a)\), scaled by the same nonzero conversion \(\lambda\) from reverse to original. Hence
\[
 q_{\rm num}(v)(b+v)-\kappa(v)D(v)(b+2v)=0 .
\]
Together with the two forward S labels these are again all four S labels. Their quartic product at \(x_0\) must equal \(J_4(z)/560\). The two resulting univariate polynomials have exact gcd one in all four mesh fields, without dividing by \(R\) at any D label.

For the remaining reverse reads, try every ordered placement of the other two D labels and both concrete phases. If both reverse second and third are D, neither phase yields such a triple in any of the four meshes. If just one is D, the chosen label and phase determine both clocks; the remaining reverse S gives one additional original singleton, with its nonzero residue \(R(x)\) fixing \(\lambda\) from its known reverse residual. Now set \(C=A_2+B R\); its three values at the observed S clocks are \(L_4/R\), fixing its entire degree-two polynomial. At the forward third D clock \(x_f\) with known \(g_f\), use
\[
 B=\frac{L_4(x_f-\ell/2)-g_f C(x_f)}{g_f(g_f-R(x_f))}
\]
with the nonzero denominator from the nowhere-zero chart and genuine off-graph D pair. The code tests both known reverse D pairs using \(U=L_4-g C-Bg(g-R)\), checking distinct physical pairs in the shared-label case. All eight options in each reconstructed field fail. These checks do not require \(R\ne0\) at a doubled clock; the only \(L_4/R\) reads are at actual S clocks. No reverse clock order, weight positivity, or singular affine read is assumed.

## Replay and Lean scope

Run `python check_both_singleton_ends.py` and `python check_one_doubled_endpoint.py` (the second imports the sibling `reconstruct_one_end.py`). The tested environment used SymPy 1.14 with flint ground types. The [Lean scalar companion](../../lean/RKCert/Research/SDIRKEightDirtySevenAffineOpeners.lean) checks on Lean/Mathlib 4.36.0 for the divided-difference and affine opener numerator identities. The complete chronology, resultants, and exact tower arithmetic are in this source proof and replays, not an end-to-end Lean theorem. See the [exact replay](exact-replay.txt) and [kernel audit](lean-4.36.0.txt). No finite-characteristic inference is made.
