# Two genuinely dirty ERK10 high rows: only independent, off-mesh donor tilts survive

This conditional result treats the fourteen-row canonical five-opening/four-Lobatto-pair architecture with **two** genuine dirty high rows. Both low donor clocks must be off the high mesh, and the two tilted responses must be independent. No new order-nine tableau, exact order-ten solution, or unrestricted stage floor is asserted. The real-algebraic ERK10 interval remains **14–15**.

## Literal hypotheses

Use the [canonical five opening rows](../erk10-stepanov-five-opening/README.md) with clocks \(0,e,2p/3,p,q\), \(e,p,q\ne0\), \(p\ne q\). The two donor rows at \(p,q\) truly reproduce rooted derivatives through size four. Nine subsequent high physical rows have four pairs at the four interior six-point Lobatto clocks, followed by the unique endpoint \(1\). Only the origin and high physical rows have output weight. Exactly two high rows \(a_d,b_d\) have zero output weight and genuinely reproduce derivatives through size four but not five. Their interior clocks \(a,b\) are distinct from each other and both donors. All six other interior high rows and the endpoint are locally pure through size five. Individual normal pair weight splits, all high taps, and all high interior chronologies are arbitrary. A donor may share a **normal** high clock in the input hypotheses.

Write \(C=\operatorname{diag}(\mathbf c)\), \(B\) for the literal strict high block of \(A\), \(P=X(X-p)(X-q)\), \(E_xf=f(x)\), \(J_xf=\int_0^xf\), and \(E\) for evaluation on all high physical rows. Set
\[
 \mathbf d_j=\mathbf b C^j A-\mathbf b(I-C^{j+1})/(j+1).
\]
The true marked primitive and the corresponding marked source imply
\(\mathbf d_j C^k\boldsymbol\Phi_t=0\) whenever \(|t|+j+1+k\le n\), for true rooted order \(n\). All polynomial integrations here are formal.

## Actual degree-five projection and six-size local purity

The actual two pure size-five tests
\[
 \mathbf q_3=A\mathbf c^3-\mathbf c^4/4,\qquad
 \mathbf v=A^2(A\mathbf c-\mathbf c^2/2)
\]
have independent restrictions on \(p,q\), by the linked canonical donor determinant. Remove their rough opening components by the true pure quadratic and its unary descendant, supported individually on the second and third opening rows. What remains is supported on \(p,q,a,b\). At each genuinely dirty row its two entries are not both zero: their tests include the actual cubic failure and the possible read of the one dirty size-four support at the third row. A local size-four row cannot read the second rough row's pure quadratic.

At order ten the marks \(k=0,1,2\) fit for \(j=0,1,2\), and at nine for \(j=0,1\). Testing the degree-two polynomial \((X-a)(X-b)\) against the two pure tests isolates the donor columns. Their independent determinant gives \(d_{j,p}=d_{j,q}=0\); lower marks then separate the two dirty rows and force \(d_{j,a_d}=d_{j,b_d}=0\). The generic Lean theorem pointwise_four_clock proves this projection without signs. The original two rough pure columns also force the corresponding opening coefficients of every \(\mathbf d_j\) used below to vanish.

The joint stage/model space through size five has the four old pure directions (two rough, two donor) and five polynomial degrees. The numerical rank of the five early physical coordinates is already five at size four, from \(\mathbf1,\mathbf c,\mathbf c^2\) and the two rough pure columns. Consequently the actual early-null polynomial image at size five is all \(X\mathcal P_3\), and its physical high vector is
\[
    \widetilde E H=EH+\mathbf e_{a_d}\psi_a(H)+\mathbf e_{b_d}\psi_b(H),
    \qquad 0\ne\psi_i\in\langle E_p,E_q\rangle .
\]
Indeed the early-zero requirement fixes the two pure donor coefficients by \(H(p),H(q)\); the other historical pure directions do not affect either dirty row. A primitive or mark preserves zero opening physical data by strictness.

At ten, the true \(\mathbf d_j\) tests for \(j\le2\) imply the restricted high row kills \(E(X\mathcal P_3)\), since its two dirty coefficients are zero. The terminal coordinate is zero (clock \(1\), no later tap), so interpolation forces high aggregate zero at the four distinct interiors. The constant test also removes the origin coordinate. Thus \(\mathbf d_j\) is supported on opposed differences only on the two normal pairs. Each dirty clock's sole weighted partner pays upper degree two using strictly later nonzero-weight rows. The exact upper support hull checks imply it needs two other distinct later weighted interiors, besides the terminal. The dirty partners therefore occupy the first two positions when sites are sorted by their last weighted occurrences. Both remaining normal pairs must be active in some \(\mathbf d_j\), \(j\le2\), as their last contributing physical rows have at most one other later weighted interior. The true tests \(\mathbf d_j A,\mathbf d_j C A\) on \(\widetilde E(X\mathcal P_3)\) isolate both pair differences at distinct clocks. Thus the two physical rows of each normal pair read this source identically.

Separately the five true contexts \(\mathbf b C^j A,\ j=0,\ldots,4\), imply that the high weighted group means on this actual tilted source equal \(J\). Compare scalar moments of degree at most nine and invert the Vandermonde at the five distinct high sites; the origin contributes nothing. The two paired equalities above and the single weighted partners imply **every non-dirty high row** acts as \(J_x\) on the actual tilted source, including the endpoint. This gives actual local derivative size **six** at those rows: the discrepancy \(A_i\boldsymbol\Phi-JH(c_i)\) on the joint size-five source vanishes on the early physical kernel, hence factors through the five opening coordinates. It vanishes already on size-at-most-four sources by its local size-five assumption. Their numerical opening values span all five coordinates, so the factored map is zero.

## One true mark makes a projected degree-five hull

Put \(\alpha=d_{3,a_d}\), \(\beta=d_{3,b_d}\), \(\psi_i=\psi_{i,p}E_p+\psi_{i,q}E_q\), and \(s_k=\alpha\psi_{a,k}+\beta\psi_{b,k}\). The actual tests \(\mathbf d_3\) and \(\mathbf d_3 C\) on the early-null model compare a genuine clock mark with scalar multiplication. Taking this difference at \(X,X^2\) yields, by the two-axis Vandermonde,
\[
  (a-k)\alpha\psi_{a,k}+(b-k)\beta\psi_{b,k}=0
  \quad(k=p,q).
\]
Using these axis identities back on \(X,\ldots,X^4\) in the marked equation shows that the row
\[
  \overline{\mathbf d_3^{\rm high}}E+s_p E_p+s_q E_q
\]
kills \(X\mathcal P_4\), where the bar sums at the four interior sites, and \(E\) in this expression is site evaluation. This is an extension of the **scalar** annihilator, not a claim about size-six physical tilted stage values. In particular \(s_pT(p)+s_qT(q)=0\) for \(T=X\prod_{\xi\;\mathrm{interior}}(X-\xi)\). The generic Lean lemmas marked_axes and aligned_hull check these field algebra steps.

Both \(\alpha,\beta\) are nonzero. If one were zero then the two axis identities and nonzero \(\psi_i\) force the other zero. With both zero, the unmarked interpolation forces the high aggregate \(d_3\) everywhere zero. Both dirty weighted partners would individually pay upper degree three and hence require **all three** other weighted interiors after them, impossible for both.

If the two tilts were proportional, the axis identities would force their common direction to be on one donor axis: \((a-p)/(b-p)\ne(a-q)/(b-q)\). On that axis \(s_k\ne0\), or else the mark would force both coefficients zero. The scalar hull therefore forces \(k\) to be a normal high mesh clock. But the first non-dirty row must act as \(J_x\) using earlier reads in the span of \(E_a,E_b,E_k\). This is impossible by the 60 verified predecessor hulls: \(J_x\) cannot act on \(X\mathcal P_3\) from at most three ordinary interior evaluations. If exactly one donor is on mesh, the scalar hull forces \(s_k=0\) for the off-mesh donor and the axis identities remove that axis from both tilts. This is the same forbidden proportional case.

## Both donors on mesh: 288 exact eliminations

If \(p,q\) are both on mesh, they equal the two normal interior clocks. Both dirties precede any clean high row: a lone prior dirty read is supported on at most three interior evaluations, ruled out by the predecessor hulls. Let \(a\) be the first dirty clock, \(b\) the second, \(x\) the first non-dirty high clock and \(y\ne x\) the next distinct non-dirty high clock. Earlier repeats at \(x\) add only \(E_x\); \(x,y\) are interiors.

Let \(\ell_k\) be the cardinal basis of \(X\mathcal P_3\) on the four nonzero sites \(a,b,p,q\). Denote \(A_t=J_t\ell_a,\ B_t=J_t\ell_b,\ K_t=J_t\ell_k\) for \(k=p,q\), all nonzero by the predecessor hulls. Set \(z=\alpha/\beta\) and \(U_k=(b-k)A_x-z(a-k)B_x\). The first exact row has only the two prior tilted reads, so coefficient comparison gives
\[
 U_k\psi_{a,k}=(b-k)K_x,\qquad
 \psi_{b,k}=-z(a-k)\psi_{a,k}/(b-k).
\]
In particular both \(U_k\ne0\). The actual size-four early-null model is \(KP\): the opening donors at that size are pure, and the two rough pure directions remove the rough coordinates. An actual primitive preserves early-zero and has model \(H=JP\) through size five. Strictness at the first high stage forces \((E_a+\psi_a)(H)=0\). Clearing the two nonzero \(U_k\) yields
\[
       F(z)=H(a)U_pU_q+(b-p)(J_x\ell_p)H(p)U_q
                    +(b-q)(J_x\ell_q)H(q)U_p=0.
\]
For the next distinct clean \(y\), compare coefficients of \(J_y\) in the span of the two tilted reads and \(E_x\). If \(x=a\) or \(x=b\), the first or second expression below, respectively, must be independent of \(k=p,q\):
\[
 \frac{K_yU_k}{(b-k)K_x}+z\,\frac{a-k}{b-k}B_y,\qquad
 \frac{K_yU_k}{(a-k)K_x}-\frac{b-k}{a-k}A_y .
\]
If \(x=p\) or \(x=q\), the other donor \(k\) must satisfy \(K_yU_k-K_x((b-k)A_y-z(a-k)B_y)=0\). In every case this is an affine equation \(G(z)=0\). A quadratic \(F_0+F_1z+F_2z^2\) and affine \(G_0+G_1z\) with a common root necessarily have
\[
                  F_0G_1^2-F_1G_0G_1+F_2G_0^2=0 .
\]
The Lean field lemma quad_affine_resultant_zero proves it even when degrees drop. All 288 ordered choices for \(a,b,p,q,x,y\) give **nonzero** results in the exact reduction at 227, so none can vanish over characteristic zero on this mesh. All denominators are units in the reduction. This calculation depends on no particular high tap, individual weight split, or untested approximate root.

## Remaining chart and replay

Only two independent tilts with both donors off mesh remain. On the resulting six nonzero distinct sites, the scalar projected degree-five row is the single barycentric annihilator for degrees 1 through 5, with all six entries nonzero. If the first non-dirty high row \(x\) appears after only the first dirty row \(a\), it must be its own weighted partner at the same clock. Indeed \(J_x\) is then proportional to \(\varphi_a=E_a+\psi_a\). On \(P,XP,JP\) the actual high read gives \(\varphi_a(P)=P(a)\ne0,\ \varphi_a(XP)=aP(a),\ \varphi_a(JP)=0\), the last by strict first-high causality. The formal identity \(J(XP)=XJP-J^2P\) forces \(x=a\) and \(J^2P(a)=0\). This statement uses the actual tilted input at size five and does not assert that either dirty primitive pays size four.

The independent scalar replay authenticates the prior coefficient file (MD5 be9e5e3ba1ff8ed21124ad285d7d2fd5) only to recover its four interior residues \(51,24,204,177\). It uses the verified degree-eight field with \(\sqrt3,\sqrt7,\sqrt{147+42\sqrt7}\) reduced to \(177,190,149\) at 227. The Lean Core file checks all 288 elimination values, 60 predecessor and 28 successor hull values, on versions 4.34.1, 4.35.0, 4.36.0 and 4.37.0-rc1. The Mathlib field lemmas and their typed audit were tested on 4.36.0. The full rooted reduction above is mathematical, not asserted as a single native all-tableau theorem.

    sha256sum -c sources.sha256
    python3 check_matched.py --emit-lean /tmp/ERK10TwoDirtyMatchedMod227.lean
    lean /tmp/ERK10TwoDirtyMatchedMod227.lean
