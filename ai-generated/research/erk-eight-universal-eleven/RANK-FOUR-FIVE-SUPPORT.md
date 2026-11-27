# A rank-four eleven-stage rational order-eight tableau needs at least six physically defective rows

For strictly lower triangular \(A\), let \(\boldsymbol c=A\boldsymbol1\), \(C=\operatorname{diag}(\boldsymbol c)\), and let \(E_q\) span the actual reviewed stage columns \(\boldsymbol\Phi_t(A)\) of trees with at most \(q+1\) nodes. Write \(V_m\) for the actual defect span through trees of size \(m\), after subtracting each tree's correctly normalized bush. Thus \(V_5= {\rm zeroSpace}(A,4)\subseteq E_4\). Its physical support \(S\) is the set of coordinates on which at least one vector in \(V_5\) is nonzero. Complementary physical rows are called pure.

**Claim.** If a rational tableau has 11 physical rows, order eight, and \(\dim V_5=4\), then \(|S|\ge6\). In particular rank four with exactly five defective rows is impossible, even when the terminal row is pure and the five defective rows are dispersed arbitrarily. This does not exclude the [known rank-three rational method](../erk-eight-rank3-four/README.md) and does not decide the universal factorial localization.

## Native and mathematical scope

The [Lean module](../../lean/RKCert/ReviewedNative/ERK8ProjectedReverseLine.lean) proves the following support-free pieces for the reviewed trees over fields:

* **no_stationary_second_seed**: once the first reverse seed is zero, the second cannot have zero transpose image while its clock multiple stays on its own line.
* **strict_transpose_zero_of_tail** and **strict_transpose_line_zero_at_tail**: the transpose image vanishes at and after the last nonzero source index; when that index is nonzero in a one-dimensional destination restriction, this kills the whole restriction.
* **projected_prefix_zero** and **projected_prefix_with_line_zero**: distinct-clock Vandermonde uniqueness with no extra site, or with one additional site represented by a line of nonzero aggregate mass.

Run **lake build RKCert.ReviewedNative.ERK8ProjectedReverseLine**. Lean 4.36 reports standard axioms only. The site-counting case split below is a mathematical argument using these native lemmas, not a claimed fully native formalization.

## Paid right and left restrictions

The explicit midpoint budget gives
\[
7+\dim V_5+\dim\operatorname{span}\boldsymbol J_0\le 11,\qquad
\boldsymbol J_k=(k+1)A^{\mathsf T}\big(\boldsymbol b\odot(\boldsymbol1-\boldsymbol c)^k\big)
 -\boldsymbol b\odot(\boldsymbol1-\boldsymbol c)^{k+1}.
\]
Rank four forces \(\boldsymbol J_0=\boldsymbol0\). The last weight is nonzero: otherwise one deletes the unused terminal row, contrary to the [ordered-field order-eight floor of eleven](../erk-eight-stage-floor/README.md). The strict last column and the first pointwise reverse balance now force \(c_{11}=1\). Therefore \(J_{1,11}=0\).

The second seed \(\boldsymbol J_1\) is nonzero; otherwise its image and clock multiple would be zero, violating the reviewed reverse-flag growth. Alternatively, the output zeroth and first moments guarantee some index \(i\) with \(b_i(1-c_i)\ne0\); at the latest such index the second seed equals \(-b_i(1-c_i)^2\ne0\). The paid order shows
\[
\boldsymbol J_1\perp E_5,\qquad C\boldsymbol J_1,\ A^{\mathsf T}\boldsymbol J_1\perp E_4,\qquad
\boldsymbol b,\ C\boldsymbol b\perp V_5 .
\]
These pairings are the ordinary reflected second balance on trees through size six, its clock and unary lifts, and forward output moments with at most one appended leaf. In particular the first row weight here annihilates clock powers through degree five, and the two lifts through degree four.

If \(|S|=5\), write \(L\) for the one-dimensional annihilator of \(V_5\) restricted to \(S\), and take a nonzero spanning vector \(\boldsymbol\ell\) on \(S\). Every one of the displayed row restrictions to \(S\) belongs to \(L\). Whenever a nonzero element of \(L\) and its clock multiple both belong to \(L\), all nonzero coordinates of \(\boldsymbol\ell\) have one common clock \(f\). In that case the line contributes **one** scalar clock if \(\sum_{i\in S}\ell_i\ne0\), and **no** scalar clock if this sum is zero. This is an exact statement about the summed rule, not an assumption that individual weights vanish or have the same sign.

Stage 1 is pure at clock zero. The [rational endpoint support theorem](../erk-eight-factorial-escape/PURE-HEAD-OBSTRUCTION.md) requires at least six distinct *available* sites including zero for any exact degree-seven rule, even if a listed site has weight zero.

## The sorted support cases

In every case write \(\boldsymbol w=A^{\mathsf T}\boldsymbol J_1\) and \(j\) for the latest physically nonzero coordinate of \(\boldsymbol J_1\). Strictness gives \(w_k=0\) for \(k\ge j\). The arguments show that \(\boldsymbol J_1\) is supported at a single clock (not necessarily at a single physical row), and that \(\boldsymbol w=\boldsymbol0\).

1. **Four defective rows.** The rank implies that \(V_5\) is the full coordinate space on \(S\), so \(\boldsymbol b,\boldsymbol J_1,\boldsymbol w\) all vanish there. In particular the terminal row lies outside \(S\). The seven pure positions have at least six distinct clocks. The second seed is zero at the terminal position and on \(S\), so its six possible physical coefficients have zero sums at each clock by its six moments. Being nonzero, it is an opposite-coefficient pair at the unique repeated pure clock. The later index \(j\) of that pair is nonterminal. Before \(j\) there are at most five pure positions, with distinct clocks, since both \(j\) and the terminal row are excluded. Five moments kill the entire transpose image there and therefore on every row.

2. **Five defective rows with defective terminal.** Because \(b_{11}\ne0\), \(\boldsymbol b|_S\) spans \(L\) and is nonzero at the terminal coordinate. Its clock multiple belongs to \(L\), so \(L\) is carried at clock 1 only. Thus the zero terminal coefficient of the second seed forces \(\boldsymbol J_1|_S=\boldsymbol0\); the same is true of \(\boldsymbol w|_S\) because its terminal coefficient is also zero. There are six pure positions. The output can use only one other scalar site, so at least five pure clocks are distinct. A nonzero second seed on the six pure positions, with every fibre sum zero, must be the unique pure repeated pair. Dropping the later member leaves at most five pure predecessor positions with distinct clocks, so the transpose image is zero.

3. **Five defective rows, pure terminal, second seed zero on \(S\).** Here the second seed lives on five possible nonterminal pure positions. Its six moments give zero aggregates. It is nonzero, so there is a repeated pure clock between two of those positions. To meet the six-site output requirement, the six pure positions must have exactly five distinct clocks, one pair, and \(\boldsymbol b|_S\) must supply one additional clock \(f\) differing from every pure clock. In particular \(\boldsymbol b|_S\ne\boldsymbol0\), its line is mono-clock (use \(C\boldsymbol b\)), and its aggregate mass is nonzero. The seed is exactly the opposite-coefficient pure pair. Before its later member there are at most four distinct pure predecessor clocks, excluding both that member and terminal. A possible nonzero restriction \(\boldsymbol w|_S\) can add the one separate site \(f\); its nonzero total mass is a faithful read of the line. Thus five moments kill the pure coefficients and the line coefficient.

4. **Five defective rows, pure terminal, second seed nonzero on \(S\), line mass zero.** Since \(C\boldsymbol J_1|_S\in L\), the line is mono-clock. It contributes no effective site to the output rule, regardless of the separate coefficients of \(\boldsymbol b|_S\). Thus the six pure clocks are all distinct. The second seed's line contribution also has zero aggregate, so its pure coefficients are individually zero by its six moments and the zero terminal component. Its latest nonzero coordinate \(j\) lies in \(S\) with \(\ell_j\ne0\). Strictness gives \(w_j=0\), which kills the entire restriction \(\boldsymbol w|_S\) by one-dimensionality; it is not necessary to interpolate to a zero-mass extra site. At most five pure predecessor positions remain, with distinct clocks, so interpolation kills the rest.

5. **Five defective rows, pure terminal, second seed nonzero on \(S\), line mass nonzero.** This line is again mono-clock at \(f\). The second seed has at most six effective sites (five nonterminal pure positions plus \(f\)), so its six moments force all aggregates zero. Its line contribution is nonzero and has nonzero mass. Consequently \(f\) coincides with a nonterminal pure clock. The available output sites are thus contained in the six pure positions, so these must all be distinct. The second seed is carried only on \(S\) at clock \(f\) and the unique nonterminal pure row \(i\) at \(f\). If its latest source \(j\) is in \(S\), then \(\ell_j\ne0\) and the strict zero \(w_j=0\) kills the whole line restriction, leaving at most five distinct pure predecessor sites. If \(j=i\), then the pure predecessor list has at most four positions (excluding \(i\) and terminal), none at \(f\). A possible \(S\) restriction contributes one separate site, whose mass is faithful. The same five-moment interpolation forces all coefficients zero.

Support below four is impossible by rank. These cases exhaust the remaining possibilities with \(|S|\le5\).

In all cases \(C\boldsymbol J_1=f'\boldsymbol J_1\) for the active clock \(f'\), and \(A^{\mathsf T}\boldsymbol J_1=\boldsymbol0\). Since the first seed is zero, the first reverse space is \(\operatorname{span}(\boldsymbol J_1)\). The second reverse space is generated by this line, its reflected clock multiple, its transpose image and the same second seed. It still has rank one, contradicting the native reverse growth floor of two. No equality or merger of raw physical rows, or claim about the next reverse seed, is needed.

## The six-site arithmetic bottleneck extends through seven defective rows

More generally, suppose a rank-four rational eleven-stage candidate has at most seven defective rows. On \(S\) the annihilator \(M\) of \(V_5\) has dimension \(k=|S|-4\le3\). The four vectors \(\boldsymbol b|_S,C\boldsymbol b|_S,C^2\boldsymbol b|_S,C^3\boldsymbol b|_S\) all belong to \(M\), by the paid forward order. The number of distinct clocks among the nonzero defective output coordinates is therefore at most \(k\), by Vandermonde. Together with pure rows this gives at most seven nominal scalar sites, including both endpoints (stage 1 pure, and the live terminal either pure or in the clock-1 defective group).

If there are seven distinct nominal sites, the pure sites are distinct and disjoint from exactly \(k\) defective-active clocks. The \(k\) clock restrictions of \(\boldsymbol b|_S\) span \(M\), one line per defective-active clock, by Vandermonde again. A zero aggregate on any nonterminal defect line removes its entire clock from the output, leaving at most six sites including both endpoints. Otherwise every nonterminal defect line has nonzero mass. The second seed \(\boldsymbol J_1\) has zero terminal entry, so it loses the whole clock-1 component: if the terminal is defective, its output clock-line generator has nonzero terminal coefficient. Thus \(\boldsymbol J_1\) lives on at most six scalar sites with faithful aggregations, and its six zero moments would force it to vanish. That is impossible. Hence a seven-site scalar escape from the factorial arithmetic in this rank-four branch needs at least eight physically defective rows.
