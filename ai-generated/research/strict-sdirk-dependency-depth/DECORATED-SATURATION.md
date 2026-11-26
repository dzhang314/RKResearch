# Saturation by one exactly paid clock on the full strict chain

This is an alternative mathematical proof for only the \(s=p-1\) branch of the paid-ring \(p\ge11\) floor. The same branch argument in fact works for \(s\ge7\). It uses the sealed characteristic-safe local seven-clock obstruction, and no branching cubic, rectangle split, Schur exclusion, or actual endpoint adjunction.

## Statement and proof

Let \((A,\mathbf b)\) be an \(s\)-stage triangular RK tableau with actual common diagonal \(\gamma\) over a field with paid integer units \(1,\ldots,s+1\). Suppose it satisfies literal rooted order through \(s+1\). For \(s\ge7\), this is impossible.

Put \(B=A-\gamma I\), \(\mathbf c=A\mathbf1\), \(x=\mathbf c-\gamma\mathbf1\), and write \(\lambda_j=\mathbf b\cdot B^j\mathbf1\) when \(j+1\le s+1\). Strict nilpotence gives the paid \(\lambda_s=0\). If \(\gamma=0\), the paid tall value \(\lambda_s=1/(s+1)!\) is already a contradiction. Otherwise \(L=\lambda_{s-1}\ne0\), since two successive paid zeros in
\[
 (j+2)\lambda_{j+1}=(1-2(j+1)\gamma)\lambda_j-j\gamma^2\lambda_{j-1}
\]
descend to \(\lambda_0=0\) using only \(1\le j\le s-1\), contradicting the paid leaf. In particular
\(L=b_s\prod_{j=2}^s B_{j,j-1}\) by the unique full strict path, so \(B_{21}\ne0\).

For each actual slot \(i\in\{1,\ldots,s\}\) the same path gives
\[
 \mathbf b\cdot B^{s-i}\operatorname{diag}(x) B^{i-1}\mathbf1=L x_i .
\]
This word is **exactly paid at \(s+1\)**: \(s-1\) strict hops, one clock factor, and the initial leaf. Its use automatically fails as a paid claim at \(p=s\); that branch is separate. In the conceptual reference model on bounded polynomials use \(J\) for integration from zero, \(X\) for multiplication by the clock variable, \(T=J-\gamma I\), and \(\ell\) for integration from zero to one. The word comparison follows by expanding \(B=A-\gamma I\), where every \(A\) adds a unary ancestor and each clock factor adjoins a leaf to the current root. For \(d=s-1\) and \(a=i-1\), \([X,T]=J^2\), \(X1=J1\) and commutation of \(T\) with \(J^2\) give
\[
 T^{d-a}(X-\gamma I)T^a1=T^{d+1}1+a J^2T^{d-1}1 .
\]
The first term contributes the explicitly paid zero \(\lambda_s\). Therefore
\[
 x_i=(i-1)\delta,\qquad
 \delta=\frac{\ell(J^2T^{s-2}1)}{L}=x_2=B_{21}\ne0 .
\]
This is an arithmetic progression of **all actual physical clocks**, with step \(\delta\). If desired, the top tall row gives the closed step formula \((s-1)\delta=1-2\gamma\), since
\(\ell(J^2T^{s-2}1)=\lambda_s+2\gamma L+\gamma^2\lambda_{s-2}\).
No division by a clock difference was needed to obtain the progression.

There are seven consecutive arithmetic clocks when \(s\ge7\). The local seven-clock obstruction, using the same cyclic nonzero \(L\) and order merely through \(s\), excludes them. Its proof uses only the paid bounded word model, grade at most six on internal gap masks, and the paid reverse recurrence; it requires no characteristic-zero sign or irreducibility. The full marked-word calculation above also stays in degree at most \(s\), with final denominators through \(s+1\). One can do the formal computations over \(\mathbb{Z}[1/(s+1)!]\) and specialize to the field.

For the arbitrary-ring application, the literal bush equations first give those integer units, and a maximal residue field preserves the stage count, rooted equations and actual common diagonal. The preceding field argument covers either image of the diagonal. The statement concerns only the \(s=p-1\) relation and does not by itself exclude \(s=p\).

Source-only proof; no new code, computation, or use of a prospective generic-path Lean module.
