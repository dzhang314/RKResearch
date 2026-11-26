# Exact causal rank of a bank of successive pure probes

Let \(A\) be an actual explicit prefix and let \(\Pi_m\) give the exact derivative polynomial \(g_t\) on its rooted columns through size \(m\). All spaces are over a field with the relevant small denominators invertible. Let \(\mathbf c\) be its clocks. Use \(I_y\coloneqq\int_0^y\). Write \(F_k\) for its actual image of tree combinations through size \(k\) with zero exact polynomial.

We want to add successive pure probes at specified sites \(x_1,\ldots,x_h\), exact in their individual derivative profiles through size \(m+1\). A later probe may use earlier ones through the actual contrasts
\[
                L_j\coloneqq E_{mathrm{new},j}-\operatorname{ev}_{x_j}\Pi_m .
\]
These annihilate every actual child through size \(m\). Hence the incoming row
\[
                 I_{x_i}\Pi_m+\sum_{j<i}\lambda_{ij}L_j
\tag{1}
\]
has the required exactness and clock. If the old size-through-\(m\) columns span the old raw stage space, these are all possible incoming rows with that exactness and those predecessors. Indeed the new coordinates through size \(m\) form the graph of the corresponding point evaluations of \(\Pi_m\); its full annihilator is exactly the span of the displayed differences.

## Which discrepancies actually consume rank

Let \(\mathcal Z\) be the space of formal tree combinations through size \(m+2\) with both exact polynomial zero and all old coordinates zero. Define \(U\) to be the image of \(\mathcal Z\) under the following linear read: for each size-\((m+2)\) unary root \([t]\), contribute its coefficient times \(g_t-\Pi_m\boldsymbol\Phi_t\), leaving all other roots out. This definition uses only actual old data, and does not treat formal assignments as rank evidence.

At a unary root of size \(m+2\), the new row discrepancy is the primitive of the negative old child residual plus the chosen earlier point evaluations of that residual. Branching roots at this size have all children of size at most \(m\), so they have no discrepancy. Consequently the increase in \(\dim F_{m+2}\) after adding the probes is exactly
\[
  \operatorname{rank}\left{
      -I_{x_i}|_U+\sum_{j<i}\lambda_{ij}\operatorname{ev}_{x_j}|_U:1\le i\le h
                         \right}.
\tag{2}
\]
To see why this is the *increase*, restrict the new ordinary pure span to the old rows. The kernel of the restriction is precisely the image of \(\mathcal Z\) on the new rows. Since each \(\mathcal Z\) expression has zero model, that image uses exactly the displayed discrepancies.

The minimum of (2), for this order and these sites, is the number of indices \(i\) satisfying
\[
  I_{x_i}|_U\notin
  \operatorname{span}\bigl( I_{x_j}|_U,\operatorname{ev}_{x_j}|_U:j<i\bigr).
\tag{3}
\]
In fact the span of earlier residual rows together with earlier point evaluations is independent of the preceding coefficient choices: adding back those point evaluations gives the same span as using the primitives. If a new primitive belongs to this span, the next coefficients can make its residual row lie in the earlier residual-row span. Otherwise its residual always supplies a new independent direction. This proves the exact minimum successively, rather than counting unmeasured interpolation dimensions. Over a paid ring it is a construction when the indicated linear equations have paid solutions; a field containment alone does not certify an integral unit pivot.

## A way to measure \(U\) without a large new family of rooted combinations

Assume again that the old size-through-\(m\) data span the entire old raw stage space. Let \(K\) be the polynomial images of formal combinations through size \(m+1\) whose old data are zero. Let \(W\) be the old actual span of formal-zero combinations through size \(m+2\) that use no unary root of size \(m+2\). If \(I\) denotes the full lower primitive polynomial, then
\[
       U=\{P\in K:(IP)(\mathbf c)\in W\},\qquad
       F_{m+2}=W+\{(IP)(\mathbf c):P\in K\}.
\tag{4}
\]
For the first inclusion in each direction, a high unary child can be replaced by a lower combination with identical old raw data; its nominal polynomial is necessarily \(\Pi_m\) of that data. Subtracting separates a zero-raw child with polynomial \(P\in K\). Its unary lift has zero old data and nominal polynomial \(I P\). Subtracting the same polynomial represented by normalized bush trees makes a formal-zero expression whose old data are \(-(IP)(\mathbf c)\). These bush corrections do not use a high unary root. Conversely, each polynomial in \(K\) has by definition an old-zero child representative, and any lower-size unary terms after its lift may remain in \(W\). Its total unary child discrepancy is exactly \(P\); low child terms contribute zero. One can therefore make the pure witness vanish physically exactly when its bush data belong to \(W\). This proves both equalities.

For the redesigned eight-row prefix through size five, its next ambiguity space is the three-dimensional set
\[
   K=\{P\in K_0[X]_{\le5}:P(0)=0,\ P(x)=\kappa(x)P(1),                                  P(z)=\kappa(z)P(1)\},
\]
where \(K_0\) is the coefficient field. The three old exact readings through six give the inclusions, and their rank is exact: the five old pure directions on the first six rows extend to the eighth with patterns \((\kappa(x),\kappa(z))\) times their stage-five coordinate, and all eight old raw coordinates are spanned already at size five. The rank formula for the old joint model then leaves exactly three nominal ambiguity dimensions. At size seven, a non-unary new discrepancy on rows seven and eight can only come from child sizes \(5+1\). Modulo the lower pure directions its two-coordinate contribution is proportional to
\[
          B\coloneqq((x-1)\kappa(x),(z-1)\kappa(z)).
\]
This direction is attained by adjoining a root leaf to the pure size-six direction \(A(C\mathbf f)\), whose old fifth coordinate is \(-1/6\). Thus (4) reduces the genuine first-usable-row test to restrictions of three primitive functionals on this measured space, without treating the remaining grade-seven stage count as resolved. In particular no new fitting or arbitrary-data clock equality should be claimed from a finite list of local stages alone.
