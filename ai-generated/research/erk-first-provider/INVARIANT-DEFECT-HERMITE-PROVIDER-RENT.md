# Rank of a clock-invariant explicit defect space

Let \(A\) be strictly lower triangular over a field, with clock vector \(\mathbf c=A\mathbf1\) and clock multiplier \(C\). Here **degree** is tree size minus one. Thus \(E_j\) contains tree derivative columns through size \(j+1\), and \(F_j\subseteq E_j\) is the actual numerical image of combinations of those trees with exact model zero. Use the usual exact stage polynomial
\[
     g_t(X)=X^{|t|-1}/\prod_{u\text{ at the root of }t}u!,
     \qquad I_x P=\int_0^xP .
\]
The small integers needed for the rooted operations and primitives are assumed paid. In a Beta or ordinary application separation through degree \(j\) is available from exactness through size \(2j\), with the original factorial budget. The abstract proof below needs only **actual separation through degree \(j\)**, namely
\[
             E_j=P_{\le j}(\mathbf c)\oplus F_j
\]
The polynomial summand has dimension \(j+1\).
Assume \(j\ge2\) and \(CF_j\subseteq F_j\). For any field-side lower bound \(d_j\) on \(\dim F_{j-1}\) for actual ordinary order-\(j\) explicit tableaux in this field, we prove
\[
                     \dim F_j\ge d_j+\left\lfloor\frac j2\right\rfloor .
\]
In \(d_j\), the space \(F_{j-1}\) uses all trees **through size \(j\)**, not just size \(j-1\). Only \(d_j\), not ordinary model separation of the smaller provider, is required on that smaller tableau.

## Chronological compression and actual clock providers

Choose physical stage evaluations on \(E_j\) greedily in chronological order, retaining a row precisely when it raises their rank. For every formerly omitted donor preceding a retained row, its evaluation on \(E_j\) is a linear combination of the earlier retained evaluations. Redirect its coefficient using that exact numerical combination. This gives a smaller strictly triangular matrix. For every \(v\in E_j\) its action on the restricted vector agrees with restriction of the original \(Av\), since each incoming tap was replaced on that space. The new row sums agree with the retained clocks, by testing \(\mathbf1\). Induction on trees proves preservation of all rooted columns through degree \(j\): a child of a nontrivial tree in that range has data in the original \(E_j\), and product at the root commutes with restriction. Restriction is an isomorphism from \(E_j\) to the entire new coordinate space by selection of independent evaluations. Hence the compressed pure spaces through degree \(j\) retain their ranks, the compressed \(F_j\) is still clock-invariant, and the compressed tableau has
\[
                     n=j+1+\dim F_j
\]
rows. Compression is not claimed to preserve higher order or a physical weight vector on unselected rows. Only the rooted data through the stated cap are used.

In this compressed system the annihilator of \(F_j\) splits by clock: a spectral projection in the diagonal \(C\) preserves \(F_j\) and hence the corresponding projection preserves its row annihilator. A vector in one of these clock blocks with sum zero annihilates every polynomial clock evaluation as well as \(F_j\), so is zero by the full compressed coordinate span. Each represented block thus contributes exactly one normalized row \(\lambda_x\), with \(\lambda_x\mathbf1=1\) and support at a single clock \(x\). There are \(j+1\) such distinct clocks by dimension. At zero the row is the literal origin read (which kills every pure defect). Enumerate the remaining \(j\) nonzero clocks \(x_1,\ldots,x_j\) by increasing last nonzero physical index \(i_1<\cdots<i_j\) of \(\lambda_{x_i}\). These indices cannot coincide because their clock supports are disjoint.

The row \(\lambda_x\) gives true evaluation of the nominal model through degree \(j\): its pure differences vanish and its single clock gives \(P(x)\). Hence the row
\[
                          L_x\coloneqq\lambda_x A
\]
has support strictly before the last index of \(\lambda_x\) and gives true primitive \(I_x\) on the actual rooted data through degree \(j-1\). This follows either by unary extension or by applying it to the primitive pure difference \(A P(\mathbf c)-(I P)(\mathbf c)\). These are **actual ordinary order-\(j\) providers on their strict physical prefixes**, not formal data functionals only. Namely at the nonzero clock \(x\), truncate to that prefix, divide its whole matrix and its output row \(L_x\) by \(x\), and retain those literal weights. For any \(|t|\le j\) its stage derivative scales by \(x^{-(|t|-1)}\) and its old primitive is \(I_xg_t=x^{|t|}/t!\). Thus the scaled actual output gives \(1/t!\) at every rooted test. Truncation itself preserves those data by strict lower triangularity; no weight or order assertion is made for the compressed tableau globally.

In particular the prefix before \(i_1\) has restricted \(F_{j-1}\) rank at least \(d_j\). Its pure combinations are exactly restrictions of the same formal combinations on the full compressed stages, and common nonzero dilation preserves their ranks. Every longer prefix therefore retains at least those \(d_j\) literal defect directions.

## Joint rank before a later completion

Fix \(1\le M\le\lfloor j/2\rfloor\). Before the physical index \(i_M\), the following \(2M\) rows are all supported and all annihilate the restriction of \(F_{j-1}\):
\[
 e_{\mathrm{origin}}^{\mathsf T},\qquad
 \lambda_{x_i}\quad(1\le i<M),\qquad
 L_{x_i}\quad(1\le i\le M).
\]
The primitive rows annihilate it since \(AF_{j-1}\subseteq F_j\). The other rows do so directly. Their restrictions to model polynomials \(P\) through degree \(j-1\) act as
\[
          P(0),\quad P(x_i)\ (i<M),\quad I_{x_i}P\ (i\le M).
\]
They are independent. To see this, set \(S\coloneqq IP\) with \(S(0)=0\). On polynomials \(S\) through degree \(2M\), impose \(S(0),S'(0)\), values and derivatives at all earlier \(x_i\) with \(i<M\), and the value at \(x_M\). These \(2M+1\) Hermite conditions are independent: a common-null polynomial would have double roots at zero and all earlier sites and a simple root at the final distinct site, more roots counted with multiplicity than its degree. Restricting to \(S(0)=0\) gives the required \(2M\)-row independence in the available primitive degree \(2M\le j\). This argument works in the paid field without ordering, signs or a distinctness assumption on physical stages beyond the distinct represented labels.

Thus the actual prefix before \(i_M\) contains both at least \(d_j\) independent pure columns and \(2M\) independent annihilating rows. Therefore
\[
                          i_M-1\ge d_j+2M .
\]
After that index there remain \(j-M\) distinct later nonzero-clock completions. The full compressed width is at least \(d_j+2M+1+j-M\). Substituting \(n=j+1+\dim F_j\) yields \(\dim F_j\ge d_j+M\), and maximizing \(M\) proves the claim. The intermediate inequality also prices the actual location of each paid completion.

## Consequences and scope

The elementary pure no-plateau bound on ordinary order-\(j\) providers gives \(d_j\ge j-2\) for \(j\ge3\). This already gives \(\dim F_4\ge4\) for a separated invariant \(F_4\), and improves the earlier invariant endpoint rent \(\lceil3j/2\rceil-3\) by one in even degrees (where that earlier rent applies), without the new size-six result.

By [the unrestricted size-six defect theorem](../erk-dense-width/README.md), for every \(j\ge6\) the first actual ordinary order-\(j\) provider has \(d_j\ge j-1\), even though that provider need not be separated at degree \(j-1\). Apply its size-six result and then the actual strict growth through the remaining paid sizes. The invariant rent becomes
\[
                    \dim F_j\ge j-1+\lfloor j/2\rfloor .
\]
For example the invariant degree-six rank is at least eight, not six. This improves the old invariant rent by two in even degrees and one in odd degrees. If the actual ordinary midpoint space is invariant, the standard forward/reverse dimension inequality gives the conditional floors 19, 21, 22, 24 at orders 12, 13, 14, 15 respectively. None is an unconditional upgrade: invariance of that midpoint function is a genuine extra hypothesis.

This is a source-only proof, not a kernel certificate. The abstract first-provider argument works with any independently certified \(d_j\) at the same paid coefficient field and does not require any held endpoint or finite arithmetic check.
