# A fourth paid shelf from two additional actual row functionals

The construction extends [the length-three proof](MIXED-THREE.md) when \(r\ge4\) and \(d\ge p+3\). It does not extend the boundary case \(d=p\) or establish the balanced target orders.

Use the same canonical early bank, \(\gamma=-1/6\), and first four physical anchors. Choose all remaining sites distinct and interior. In the reverse order, denote the two sites immediately after the four anchors by indices \(4,5\). Choose a scalar rule \(b\) with nonzero weights and failed degree-\(p\) scalar moment as in PROOF.md. Write \(H_i=h_i/(\gamma^2b_i)\). In addition to the first four values of \(H\), choose \(H_4,H_5\) so that the actual six-site columns
\[
                     1,\ \beta,\ \beta^2,\ \beta^3,\ H,\ \beta H
 \tag{1}
\]
have independent evaluations. This is a nonempty exact condition: in the determinant as a polynomial in \(H_4,H_5\), the coefficient of \(H_4H_5\) is, up to sign, \((\beta_5-\beta_4)\) times the ordinary four-site Vandermonde determinant of the first four distinct \(\beta\)'s. Also avoid the one value of \(H_4\) that would make its adjacent tap zero; that linear nonvanishing was proved in PROOF.md. Both conditions can therefore be met simultaneously over the real algebraic numbers. Prescribing these six coordinates of \(h\) is legitimate, because the other \(d-6\ge p-3\) sites can satisfy its true common-factor moment equations with a Vandermonde.

For the first six reverse rows, use the literal old four-equation completion, preserving all existing pivots; at index 5, set the tap to index 4 nonzero before solving its first four pivots. The partial rows through index 5 now fix their quantitative values of the two genuine new reads \(q_3=(bM^3)T,\ z=(hM)T\). On later coordinates choose both rows freely so that
\[
 q_3 E(F)=\ell((LY^3)F),\qquad z E(F)=0
       \quad\text{for }F\in(X-\alpha)\mathbb P_{\le p-6}.
 \tag{2}
\]
These are just \(p-5\) moment equations per row. The \(d-6\) remaining distinct sites, with nonzero factors \(X_i-\alpha\), give full Vandermonde rank and can complete them. At every remaining reverse row, use the six actual pivots (1) to impose its six literal responses at once: the lower four from PROOF.md and the two desired entries (2). All pivots are strictly earlier and all arithmetic remains in the real algebraic numbers.

A full nonzero strict adjacent path can still be kept. At index 6, the tap to index 5 depends nontrivially on at least one of the two new desired coordinates. Otherwise the coordinate functional of that tap would lie in the span of the four old input rows on the six pivots; it is zero at the first four slots, so their invertibility there would force it identically zero, contradiction. Prescribe the two values at index 6 to avoid a zero tap, and fill (2) on the other \(d-7\ge p-5\) distinct sites. All later adjacent taps are outside the six-pivot set and can be chosen arbitrarily nonzero.

This pays **all** word responses through length four at the actual target budget. In fact every length-three input lies in \(b\mathbb P_{\le3}(M)+h\mathbb P_{\le1}(M)\), with the formal model carried by the first term and zero by the second, as proved by the four-row construction. Multiplication by \(T\) of every basis row except \(bM^3,hM\) is already known from the four equations; it has the proper model through (2)'s smaller source grade. The remaining two basis rows are exactly (2). True marks of old paid rows are covered by the one-degree tighter source budget, since multiplying by a mark preserves the actual common-factor ideal. Therefore all genuine separated contacts through length four hold. The rooted-spine proof yields actual ordinary order at least \(m+4\).

For the balanced target-order shapes \(p=16,20\) one has \(d=L(r)\ge p+3\); these have, respectively, actual rooted order at least \(12,14\) and all target-budget length-four contacts. These are not target-order stage upper bounds. The \(p=12,\ d=p\) variant remains at the previously verified length-three shelf; no extension of its genericity conditions is assumed here.
