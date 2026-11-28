# Twelve active rows: a finite width projection for dormant-center aliases

**Scope.** Continue the all-live half-clock, two-carrier, both-new order-eleven equality chart with ten nonzero-first-pool labels, twelve active rows, both full plateau pairs, and dormant physical row 9. If its clock belongs to \(\{0,1,a,d\}\), all possible **width pairs** \((a,d)\) lie in a finite algebraic set over any ordered field. No equality of widths is assumed; in particular this advances the unequal-width alias charts left open by the [symmetric exclusion](ERK11-NONZERO-TEN-TWELVE-SYMMETRIC-CENTRAL-ALIAS-EXIT.md). It does not exclude the finite exceptional width pairs or assert that all stage or flank parameters are finite at localization poles. No unrestricted stage interval changes. Over characteristic zero the same projection applies under the initial mixed-moment and alias-specific live guards of the symmetric proof; ordering only earns those guards and excludes the double-zero central alias here.

## 1. The actual width equation and the redundant width contact

Use the exact [aliased reciprocal diagonal](ERK11-NONZERO-TEN-TWELVE-SYMMETRIC-CENTRAL-ALIAS-EXIT.md#1-a-reciprocal-diagonal-gives-a-width-only-equation), derived from the true physical-9 reciprocal weight and the four actual grade-five mixed payments, with no width symmetry. In the orientations \(\zeta=d\) and \(\zeta=0\), let \(\mathcal D(a,d)\) be the polynomial
\[
 [\widehat L,\widehat R]-S\,\mathscr P(a)\mathscr Q(d)
\]
with its listed live factors removed. The exact divisions are respectively by \(a^3d(d-1)(a-d)\) and \(ad(d-1)^3\), up to irrelevant nonzero rational scalars. The two polynomials have bidegrees \((8,13)\) and \((10,8)\) in \(a,d\). Distinct plateaus and the ordered double-zero exclusion earn these width factors.

The outer reciprocal off-diagonal \([L_7,R_{11}]=0\) is **not a second width law** in these orientations. In fact the cleared projective width expression
\[
 [\,l_1D_L^0-l_0D_L^a,\ r_1 D_R^1-r_0D_R^d\,]
\]
is an exact polynomial multiple of \(\mathcal D(a,d)\), using the hatted central rows in \(l_j,r_j\). The replay checks this exact division. If either slope row vanishes, that polynomial gives no extra constraint either. Other actual row contacts remain available; the finite projection below uses the genuine flank profile equations rather than counting this redundant width identity again.

For each of the two \(\mathcal D\)'s, the exact rational gcd of its coefficients as a polynomial in \(d\) is 1 in \(\mathbb Q[a]\). Thus **no value of \(a\)** in any characteristic-zero extension makes the \(d\)-polynomial identically zero. This protects later exceptional widths, including leading-degree drops; it is not inferred from the sample place.

## 2. A finite-free regular atlas and its explicit exceptional set

Keep the same exact [two flank profile systems](ERK11-NONZERO-TEN-TWELVE-SYMMETRIC-CENTRAL-ALIAS-EXIT.md#3-one-flank-profile-determinants-of-degree-at-most-four), with \(u=c_6,w=c_{12}\). They are valid without symmetry on the live width-pivot chart. Write \(f_{L,0},f_{L,1}\) and \(f_{R,0},f_{R,1}\) for the two degree-at-most-four flank determinants after their *exact* forbidden factors. Index 0 uses the opposite central row, index 1 the opposite derivative row. Let \(M\) be the actual twelve-row, eight-column profile system: three rank-zero moments, two left and two right outer sample rows, and all five coefficient equalities between the left and right quartic descriptions. Its columns are the coefficient pairs of \(P,A+BX,\widetilde P,D+EX\), in that order. An actual tableau gives a nonzero vector \(c\in\ker M\) with \(\widetilde P=P/\kappa\). In particular the determinant of its two first-pool pairs is zero. No value of \(Q\) at any clock or root is inverted.

Start with \(\mathbb Z_{(19)}[a]\) and make only the following finite sequence of localizations. Each listed inverse is justified by the sample in Section 4 before it is used.

1. Invert the leading coefficient of \(\mathcal D\) in \(d\), make it monic, and adjoin \(d\) by that polynomial. This is finite free of rank 13 for \(\zeta=d\) or rank 8 for \(\zeta=0\). Denote this algebra by \(B\).
2. Inside \(B\), invert the required width elements by their multiplication norms over the scalar base: \(a,d,1-d,a-d,H,J_0\); the clock solve pivot \(I_1-zI_0\) or \(I_1-xI_0\); the live primitive interpolation \(C_2-xH,\ d-x\) in the first case or \(C_1-zH,\ z\) in the second; and the four projective slope coefficients \(l_0,l_1,r_0,r_1\) once the width rows are formed. The nominal primitive scales \(a^5/30,(1-d)^5/30\) are already units. All fixed rational coefficient denominators are units at 19. In this sequence, each new norm is formed only after any previous necessary denominators are inverted. Its nonzero numerator is another polynomial in \(a\). If the norm is inverted, the original element is a unit by the multiplication adjugate.
3. Use the \(u,w\) polynomial flank determinants defined over this localized \(B\). Invert the \(B\)-norms of the leading coefficients of the **fixed choices** \(f_{L,0},f_{R,0}\), then adjoin each variable by its corresponding monic quartic. The resulting algebra \(\mathcal A\) is finite free over the scalar base of rank \(13\cdot4\cdot4=208\) or \(8\cdot4\cdot4=128\). The row construction in \(M\) uses only the cleared hull coefficients and outer rows; it inverts neither \(D_L,D_R\) nor any \(u,w\)- or \(Q\)-dependent pivot.

Let \(E(a)\) be the product of the numerators of the finitely many scalar inversions just described (including the initial leading coefficient). Their sample values are nonzero, so \(E\) is a nonzero polynomial. This describes a **finite** localization, not arbitrary inversion of every nonvanishing-at-sample expression. Any actual candidate with \(E(a)\ne0\) defines an evaluation of \(\mathcal A\) in its coefficient field, by sending \(d,u,w\) to their actual clocks. When \(E(a)=0\), no such evaluation is assumed: the entire pole or rank-drop width is retained in the finite exceptional set.

## 3. The genuine obstruction ideal, including rank seven

Define the following finite family of elements of \(\mathcal A\).

* The other flank determinants \(f_{L,1},f_{R,1}\), since these also vanish on any actual evaluation.
* All eight-by-eight minors of \(M\).
* For each selection of seven rows of \(M\), take the signed cofactor vector \(v\in\mathcal A^8\) of that \(7\times8\) submatrix, by deleting one column at a time. Include \(v_0v_5-v_1v_4\) as an obstruction element.

Every member of this family vanishes at an actual candidate of the regular atlas. The eight-row minors vanish because \(M c=0\) with \(c\ne0\). For a seven-row block, if it has rank less than seven then all its maximal cofactors are zero. If it has rank seven, the alternating-minor vector spans its one-dimensional kernel by the determinant identities. The true \(c\), being in that same kernel, is a nonzero multiple of it; the required first-pool proportionality then gives the displayed cofactor obstruction. This implication is evaluated in a field; it does not assert that a scheme-theoretic null vector has a unit entry everywhere. Conversely at a *field point* of the residue atlas with rank eight some eight-row minor is nonzero. At rank seven, any choice of seven independent rows gives a nonzero cofactor spanning the full kernel, so an observed nonproportional first-pool pair makes at least one cofactor obstruction nonzero. This is exactly why the rank-seven cases are not treated as unresolved rank failures.

For a concrete nonzero width polynomial, enumerate this family as \(g_i\). At the sample in Section 4 all residue field components have extension degree dividing \(L=72\) for \(\zeta=d\) or \(L=12\) for \(\zeta=0\). Put \(e=19^L-1\), and define the obstruction mask in the finite free algebra by
\[
 W=1-\prod_i(1-g_i^{\,e}).
\]
At an actual regular candidate all \(g_i\) vanish, so \(W\) maps to zero. At every residue field point at least one \(g_i\) is nonzero and hence has \(e\)-th power 1, so \(W\) is 1 at every field point. The sample algebra is reduced because the width and fixed flank polynomials are all squarefree at the sample; it is a product of finite fields. Consequently **\(W=1\) in that entire algebra**, not merely in one factor and not just modulo a nilradical. In particular the determinant of multiplication by \(W\) on the finite free scalar module specializes to 1.

Let \(N(a)\) be the numerator of that determinant, a nonzero polynomial as verified by this specialization. Its formula uses only the named polynomial matrices and finite product; expanding the potentially huge numerator is not needed for the proof. For a regular actual candidate its determinant must vanish: if not, multiplication by \(W\) after scalar extension would be invertible and \(W\) would be a unit, impossible under the evaluation taking it to zero. Thus every actual width satisfies
\[
 E(a)N(a)=0,\qquad \mathcal D(a,d)=0.
\]
This is a finite algebraic width projection even at zeros of \(E\), because neither scalar polynomial is zero identically and the \(d\)-coefficient gcd check prevents any vertical fiber. It does not decide which of these finite candidates are feasible. Reflection transfers it to \(\zeta=a,1\) using the same actual mixed payments and scaled response moment spaces, without ordinary reverse order eleven.

## 4. Exact specialization witness, not a tableau reduction

The exact standalone replay checks the width polynomial degrees and guard divisions, the bivariate off-diagonal divisibility, the complete rational coefficient gcds, and the rational constant denominators. It then specializes **coefficients only** at prime 19:

* For \(\zeta=d\), take \(a=2\), with \(d\)-factor degrees \(4,9\) and no degree drop.
* For \(\zeta=0\), take \(a=6\), with degrees \(2,3,3\) and no degree drop.

All of the width elements named in step 2 reduce to nonzero at every width residue component; both **fixed first** flank determinants retain degree four there. For each irreducible \(d\)-factor of degree \(k\), a Frobenius representative in \(\mathbb F_{19^{2k}}\) suffices. In every such fiber the two reduced flank gcds have degree four and four simple roots in this field, hence the fixed quartics are squarefree. Every pair of the four left and four right roots is tested, without dropping root collisions or a vanished appearance of any unearned tableau parameter. The 80 checked pairs have 60 rank-eight and 20 rank-seven nonproportional outcomes. Frobenius covers every other geometric point of a given residue component. The exponents in Section 3 correspond to the least common multiples of \(2k\) in the two lists, so that calculation really yields one element equal to 1 on all factors.

These specializations are witnesses that a characteristic-zero coefficient norm is **not the zero polynomial**. They are not assumed to be actual valid widths, and they do not exclude tableaux at arbitrary widths or at zeros of \(E(a)N(a)\). The adjacent Lean file checks the scalar unit-mask identities over a commutative ring. The finite-free, cofactor, and tableau ingress are mathematical.

See the [standalone exact replay](erk11-ten-twelve-finite-central-width/replay_erk11_generic_central_alias_width.py) and [Lean unit-mask lemmas](../lean/RKCert/ReviewedNative/ERK11FiniteAliasUnitMask.lean). The two scalar lemmas checked on all four targeted versions.
