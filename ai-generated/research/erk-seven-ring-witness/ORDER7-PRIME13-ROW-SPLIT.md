# Order seven at 13: finite row-split criterion and two classical obstructions

**Scope.** This concerns regularization of the specified rational Butcher and Shanks nine-stage charts, not nonexistence of all nine-stage ERK over \(\mathbb F_{13}\) or \(\mathbb Z_{(13)}\). Put \(\mathcal O=\mathbb Z_{(13)}\), \(\pi=13\), and \(v=v_{13}\); bars denote reduction. All calculations below are direct identities or hand reductions of the cited entries. No classical chart is reconstructed from a numerical approximation.

## 1. Affine row/tap criterion over a valuation ring

Suppose two stages, earlier receiver \(i\) and later donor \(j\), have padded rows \(r,a\), and write \(\delta=a-r\). Replace their affine parameters \(0,1\) by \(\sigma,\tau\), \(\sigma\ne\tau\). The two-by-two stage-coordinate block and new taps are
\[
 M=\begin{pmatrix}1-\sigma&\sigma\\1-\tau&\tau\end{pmatrix},
 \qquad
 (\widetilde u,\widetilde v)=(u,v)M^{-1},
 \qquad
 \widetilde v=\frac{V-\sigma T}{\tau-\sigma},\quad
 \widetilde u=T-\widetilde v ,
\]
where \(T=u+v\) and \(V=v\) are the original total and first affine moment of a tap. Apply this to each unchanged receiver row using the affected pair and to the output; the internal taps of the two changed rows instead obey the block similarity. Equivalently, let \(S\) be identity outside this block, \(A'=SAS^{-1}\) and \(\mathbf b'^\top=\mathbf b^\top S^{-1}\). The block \(M-I\) has rank at most one. It fixes the all-ones vector. Keeping \(\sigma=0\) is always chronologically safe for the block similarity. If \(\sigma\ne0\), over the fraction field strict chronology requires the donor to use only stages before \(i\) and intervening rows to have no original tap to \(i\): the new upper pair entry would otherwise be \(-\sigma^2 A_{ji}/(\tau-\sigma)\), the unchanged-column entry beyond \(i\) would be \(\sigma A_{jk}\), or the new intermediate tap to \(j\) would be \(-\sigma A_{ki}/(\tau-\sigma)\).

Suppose the pair rows are retuned on the line \(r+z\delta\) in their unchanged predecessor coordinates, as in these chronological cases. If \(\delta\ne0\), and one parameter \(z_0\) gives a finite row, the set of all finite row parameters is exactly \(z_0+\pi^e\mathcal O\), \(e=-\min_k v(\delta_k)\). If there is no such \(z_0\), this line cannot be used. Ignoring separate chronology/conservation constraints on moving the earlier row, two different finite rows and all finite adjusted taps exist precisely when all unchanged entries are finite and each tap in an unchanged receiver row or the output satisfies
\[
       T\in\mathcal O,\qquad V-z_0T\in\pi^e\mathcal O .
\tag{1}
\]
Indeed for a proposed split the denominator has valuation \(\ge e\); conversely choose \(\sigma=z_0,\tau=z_0+\pi^e\) and use the displayed tap formulas. The test is independent of the chosen center \(z_0\). For a fixed finite receiver \(r\), choose \(z_0=\sigma=0\); then a donor row with a pole of order \(e>0\) requires every outgoing donor tap, including its output weight, to be divisible by \(\pi^e\). The \(\delta=0\) case has a constant row instead of a finite ball and cannot regularize a nonfinite row.

If the original two stages have identical **child reads** on \(\mathbf1,\mathbf c,\mathbf c^{\odot2},A\mathbf c\), then the block preserves all rooted outputs through size eight exactly. These are precisely the four child tree columns of sizes at most three. At a root of total size at most eight, at most one child (of size at least four) can distinguish the two rows. Taking the product is therefore affine on their two root factors. Induction using \(A'S=SA\) proves \(\boldsymbol\Phi_t(A')=S\boldsymbol\Phi_t(A)\) and hence equality of \(\mathbf b\cdot\boldsymbol\Phi_t(A)\) in the two tableaus. In particular a unit eighth-order cleared defect survives any such finite split.

Agreement only through child size two does not in general suffice at order seven: two size-three children can first occur together there. The extra quadratic tap moment has error
\[
 (\widetilde u\sigma^2+\widetilde v\tau^2)-V
             =(\sigma+\tau-1)V-\sigma\tau T.
\tag{2}
\]
Where that quadratic coefficient is observed, preserving the constant and affine moments alone is insufficient. With a fixed finite base and \(e>0\), a finite pair preserving a nontrivial quadratic moment must have \(V\in\pi^{2e}\mathcal O\), since the finite new nodes \(\sigma,\tau\) both lie in \(\pi^e\mathcal O\). If two independent pairs \((T,V)\) must each preserve this moment exactly over the fraction field, (2) forces \(\{\sigma,\tau\}=\{0,1\}\). This is a per-tap assertion, not an assertion that all root-level resets must separately pass every nonlinear tap.

## 2. Butcher: coefficients can be made finite, but not order by a pair split

The [published Butcher-9-7 coefficient chart in RKLab](https://raw.githubusercontent.com/drreynolds/rklab/master/butcher.m) has exactly these thirteen-adic coefficient poles:
\[
 A_{85}=-1815/20384,\quad A_{87}=49/1144,\qquad
 b_5=1771561/6289920,\quad b_7=16807/74880.
\]
They are simple, with respective scaled residues \((-1,1,2,-2)\). For instance the denominator parts after dropping \(13\) are \(1568,88,483840,5760\), and the numerators and the denominator parts are units. The other coefficients are regular, including \(A_{98}=21/16\), \(b_8=77/1440\), and \(b_9=11/270\), all units. Rows 5 and 7 are entrywise congruent modulo 13: in their first six coordinates both reduce to \((1,0,4,7,0,0)\). Their clocks are \(c_5=2/11,\ c_7=6/7\), so the clock displacement is \(52/77=13(4/77)\) of valuation one. The first six clock residues are the pairwise distinct \(0,11,9,7,12,5\), respectively.

There is an **exact** same-low-jet receiver for the singular row: stages 1 and 8 both have their four child reads zero. Directly from the rows, \(c_8=0,\ A_8\mathbf c=0,\ A_8\mathbf c^{\odot2}=0\). For the last equality the numerator over 224224 is \(9984-660-16380+7056=0\). In fact the actual stage-order defect is
\[
 g=A\mathbf c-\tfrac12\mathbf c^{\odot2}
       =-\tfrac1{72} e_2 .
\tag{3}
\]
The entries of \(A\mathbf c\) in physical order are \(0,0,1/18,1/8,2/121,2/9,18/49,0,1/2\); in particular the row-8 sum against \(\mathbf c\) has numerator \(19968-3630-24570+8232=0\) over 224224. Row 8 does not tap column 2, so \(A_8 A\mathbf c=0\) as well. Nevertheless (1) cannot move the pole from row 8 to row 1: the two actual outgoing taps \(A_{98},b_8\) are units.

In the opposite direction there is a genuine **finite-coefficient** two-node blow-up: keep row 5 fixed and make new row 7 be \(A_5+(A_7-A_5)/13\); inverse-transform the taps. The new row is regular by congruence. Row-8 taps into 5 and 7 have regular total, their tap into 7 becomes \(13 A_{87}\), and the output is treated similarly. This removes all coefficient poles. It does **not** preserve order even in the residue field.

Indeed the old weight sum of those two clocks and their old first displacement have residues
\[
 \overline{b_5+b_7}=3,\qquad
 \overline{b_7(c_7-c_5)}=8 .
\]
Thus their old contribution on polynomials reduces to the confluent functional
\[
                  3 f(-1)+8 f'(-1).
\tag{4}
\]
This uses ordinary polynomial differentiation, or expand \(f(c_7)\) around \(c_5\) and note that all terms of order two in the gap vanish after weighting and reducing. A finite two-node replacement cannot reproduce (4) even through cubic degree, whether one or both clocks are allowed to move. Center at \(-1\), so the first four moments are \((3,8,0,0)\). A monic node quadratic \(X^2-aX+d\) must be annihilated by the functional, and so must its product with \(X\). The resulting \(8d=0\) and \(-8a+3d=0\) make that quadratic \(X^2\), so both nodes are zero and could not realize first moment 8.

For clarity, the required original paid bush values can be checked without relying on a claimed order. Before replacing any coefficients the full reduced quadrature functional is
\[
  9 f(0)+5 f(1)+6 f(7)+4 f(5)+3 f(-1)+8 f'(-1).
\tag{5}
\]
At \(f=X^j\), \(j=0,\ldots,7\), its values are \(1,7,9,10,8,11,2,9\) in \(\mathbb F_{13}\), by direct evaluation of the four powers and derivative. The first seven are the required \(1/(j+1)\); the original eight-vertex bush has cleared defect \(8\cdot9-1=6\) in the residue field, hence a unit as a scalar read in \(\mathcal O\). A hypothetical order-preserving affine transfer through size eight would preserve this defect; the displayed finite blow-up does not.

## 3. Butcher: no chronological single-row similarity, even with several receivers

Let \(S\) be lower triangular, invertible, \(S\mathbf1=\mathbf1\), and identity except at one row \(j\); take again \(A'=SAS^{-1}\) and \(\mathbf b'^\top=\mathbf b^\top S^{-1}\). If \(j<7\) the pole in \(b_7\) is untouched; if \(j>8\) row 8 is untouched. If \(j=8\), the exact identity
\[
 b'_8 A'_8+\sum_{i<8} b'_i A_i
      =b_8 A_8+\sum_{i<8}b_i A_i
\]
follows by multiplying the changed row by \(b'_8\); on the right the second sum is integral (the only weight poles have opposite residues on the congruent rows 5 and 7), whereas \(b_8 A_8\) has a pole. So finite coefficients are impossible in that case.

For the remaining \(j=7\), write the changed row of \(S\) as \(q e_7^\top+\sum_{i<7}w_i e_i^\top\), \(q\ne0\). If all new coefficients and weights are finite, the exact equality
\(b'_7 A'_{76}=b_7 A_{76}\) makes both factors units: only original row 7 can tap stage 6 in the modified row. Here \(A_{76}=1053/2401\) has valuation one. Therefore \(v(q)=-1\). The old pole cancellation in \(\mathbf b^\top=\mathbf b'^\top S\) makes \(s_i=w_i\) for \(i\ne5,\ i<7\), and \(s_5=w_5+q\), integral, with \(\sum_{i=1}^6s_i=1\). The changed virtual row read is
\[
                 (S V)_7=\sum_{i=1}^6s_i V_i+q(V_7-V_5).
\tag{6}
\]
The relevant virtual stage quantities are all regular: original rows 1 through 7 are finite and rows 5,7 congruent, so their rooted profiles and child reads are congruent. This makes (6) regular whenever used here. The same for other rows follows for the quantities below directly from their displayed polynomial values.

Suppose the regularized tableau pays all rooted orders through seven modulo 13. Define \(x_*=\overline{c'_7}\). Comparing the bush reads (5), whose original read also equals \(\mathbf b'\cdot S(\mathbf c^{\odot r})\), gives
\[
                  \overline{(S f(\mathbf c))_7}=f(x_*)\qquad(\deg f\le6).
\tag{7}
\]
Indeed the new and virtual stage bush columns differ only at row 7, and \(b'_7\) is a unit. Let \(P_6(X)=\prod_{i=1}^6(X-c_i)\). Its virtual read at row 7 is \(q P_6(c_7)\), a unit since exactly one factor, \(c_7-c_5\), has valuation one. By (7), \(x_*\) differs from all six prior clock residues.

Now \(A'\mathbf c'=S A\mathbf c\) exactly. Use the single mixed rooted tree of size four with a leaf and a two-vertex tall child: its profile is \(C A\mathbf c\) and its required scalar weight is \(1/8\). The old scalar weight is indeed \(1/8\) modulo 13 by (3), \(b_2=0\), and the cubic moment in (5). The new and virtual versions again differ only at stage 7. Together with (7) this yields
\[
 \overline{(S((\mathbf c-c_2\mathbf1)\odot g))_7}
   =(x_*-\bar c_2)\,\overline{(Sg)_7}.
\]
The left side is zero by (3). Since \(x_*\ne\bar c_2\), (6) with \(V=g\) and \(g_2\) a unit gives \(\bar s_2=0\). Finally take \(P_5(X)=\prod_{1\le i\le6,\ i\ne2}(X-c_i)\). Its virtual read is \(q P_5(c_7)\) modulo 13, still a unit. In degree six the virtual read of \(X P_5\) is \(\bar c_7\) times that unit. Applying (7) to both polynomials forces \(x_*=\bar c_7=\bar c_5\), the previous contradiction. This rules out every chronological single-row similarity of this form, not just a one-receiver split.

**Additional coefficient restriction for general triangular rank-one similarities.** For \(S=I+u v^\top\) lower triangular, the only unresolved boundary in this chart has \(j=\max\operatorname{supp}v=7\), with possibly several rows changed. Indeed \(j<7\) leaves \(b_7\) untouched, and \(j>8\) leaves row 8 untouched. To check \(j=8\), if regularization were possible normalize \(S=I+u w^\top\), with \(w^\top=\mathbf b^\top-\mathbf b'^\top\) and \(\mathbf b'^\top u=1\) (renormalize the nonzero product). The vector \(u\) is supported on 8,9, \(w\) on the first eight positions. Put \(a=u_8,\ \delta=w_8=b_8-b'_8,\ \nu=1+a\delta\), and \(W=w^\top A=\delta A_8+G\), where \(G\) is integral and supported through column 7 because of cancellation on rows 5 and 7. The new row 8 is \(\nu A_8+aG\). At row 9 the new column 8 coefficient is \(A_{98}/\nu\), so \(v(\nu)\le0\). Since \(A_8\) has a pole, row 8 finiteness forces \(v(a)<0\). On the other hand,
\[
 b_9 A'_9+b'_8 A'_8
       = b_9 A_9+b_8 A_8+G-(b_9 a A_{98}/\nu)w^\top .
\]
The two possibly singular terms can cancel only if \(v(a)=v(\nu)\), since \(b_9,A_{98}\) are units and both \(A_8,w\) have simple poles. As \(v(a)<0\), this forces \(v(\delta)=0\). Then \(\nu A_8\) has a pole one power worse than \(aG\), contradictory. This restriction does not settle a multi-row \(j=7\) transformation.

## 4. Shanks: two confluent pairs, not a single removable mode

In [Shanks, NASA TN D-2920, Formula (15), PDF page 24](https://ntrs.nasa.gov/api/citations/19650022581/downloads/19650022581.pdf#page=24), the implicated strict row denominators are \(151632,1375920,251888\) on rows 7,8,9 and the output denominator is \(2140320\). The [digitized implementation](https://raw.githubusercontent.com/jacobwilliams/rklib/master/src/rklib_fixed_steps.f90) was used only to cross-check the entries against the primary scan. Each listed denominator has \(v=1\). The nonzero scaled residues are confined to columns 5 through 8:
\[
\begin{array}{c|rrrr}
 &5&6&7&8\\
 \overline{\pi A_7}&5&-5&0&0\\
 \overline{\pi A_8}&5&-5&0&0\\
 \overline{\pi A_9}&-1&1&6&-6\\
 \overline{\pi\mathbf b}^{\,\top}&2&-2&-2&2
\end{array}
\]
For example the first row residue comes from the pair \(-284256,1701\) over \(151632\); the common weight pair uses \(635040,-59049\) over \(2140320\). Other denominators or divisible numerators give zero scaled residue. Thus the coefficient pole matrix has rank two and the weight pole has four-site support. The nine rational clocks are all distinct, so no exact same-child-jet pair exists even at child size one.

In fact no single lower-triangular rank-one similarity \(S=I+u v^\top\) can regularize this chart. If \(j=\max\operatorname{supp}v\), lower triangularity puts all changed rows at or after \(j\); rows before \(j\) of \(A\) are unchanged also by right multiplication by \(S^{-1}\), and all entries of the output after \(j\) are unchanged. The first pole row 7 forces \(j\le7\), but then the pole in \(b_8\) survives.

There is a stronger obstruction to simultaneously splitting just the two natural pairs (5,6) and (7,8) by disjoint block-affine similarities. Their two rational clock gaps are both \(13/18\); their common residue centers are respectively \(x=11,y=3\). Their two weight sums reduce to \(2,2\), and their derivative weights reduce to \(D=10,-D=3\). Thus before any split the full reduced quadrature is
\[
  5f(0)+5f(1)+2f(x)+D f'(x)+2f(y)-D f'(y).
\]
For \(1,X,X^2,X^3\) this gives \(1,7,9,10\), exactly the required values. The two inside-pair links \(A_{65}=13104/729\) and \(A_{87}=328536/1375920\) each have valuation one. If the affine earlier-row parameter in one block is \(\sigma\), a finite explicit reduction requires \(v(\sigma)\ge0\): finite row-sum clocks give \(v(\sigma),v(\tau)\ge-1\), and at \(v(\sigma)=-1\) the upper pair entry \(-\sigma^2 A_{ji}/(\tau-\sigma)\) would have valuation \(\le0\), contradicting regularity or strictness modulo 13. Thus the earlier clock stays at its old residue. The old donor weight has a simple pole and the total is finite, so the new parameter gap must have valuation \(-1\) to give finite weights. The new donor's clock displacement in the residue is consequently some nonzero \(d\). Its new weight must act as \(D/d\) (or \(-D/d\) at the other pair) to preserve that pair's first affine moment. The two derivative evaluations are then replaced by two finite differences with increments \(d_1,d_2\ne0\). Preservation of \(X^2\) forces \(D(d_1-d_2)=0\), hence \(d_1=d_2\). At \(X^3\) the remaining difference is \(3D(x-y)d_1\ne0\). Thus even this simultaneous pairwise explicit repair cannot retain order four in the residue.

## Consequence and boundary

The accepted adjacent ten-stage universal construction, in **ai-generated/research/erk-seven-ring-witness/README.md**, uses the different [Shanks Formula (16)](https://ntrs.nasa.gov/api/citations/19650022581/downloads/19650022581.pdf#page=24). Its exactly matched full low jet and divisible outgoing weight remove a denominator 41, and the adaptation has unit order-eight cleared defect \(-1/810\). It is not a nine-stage chart. Neither the exact same-low-jet receiver, a two-node affine split, nor any single-row chronological rank-one similarity yields the desired width-nine order-seven witness at 13 from these charts. The calculations do not exclude unrelated nine-stage constructions, changes involving more general coupled row families, or the as-yet-unsettled multi-row Butcher boundary specified above.
