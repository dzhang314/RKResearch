# Nodal cuts with mixed diagonal entries and local Volterra nullity

The [all-order nodal cutoff](nodal-cut-recurrence.md) needs neither global Volterra injectivity nor nonsingular diagonal entries away from the counted side. For a degree-\(q\) mask let \(m=p-2q>0\), and let \(z\) bound the nullity of the Volterra step on the invariant target. The optimal lower rank given by a uniform loss of \(z\) at each paid step is exactly
\[
 \mathcal B_z(m)=
 \begin{cases}
 z+\mathcal B_0(m-2z),&2z<m,\\[2pt]
 \lceil m/2\rceil,&2z\ge m,
 \end{cases} \tag{1}
\]
where \(\mathcal B_0\) is the ordinary nonsingular parity stage floor at positive order. In particular, zero diagonals entirely on the other side of the cut cause no loss. There is also a separate, stronger version when the Hankel form of the actual mask is paid and nondegenerate: it charges its degree once, as in the universal endpoint masks \(x\) and \(1-x\).

## 1. The local loss is exactly a kernel intersection

Work over an arbitrary field, with the genuine reviewed order \(p\) of \(A,b\). Write \(x=A\mathbf1\), \(C=\operatorname{diag}(x)\), \(\beta=b^{\mathsf T}\) and \(R=CA-AC-A^2\). The actual elementary and defect flags are \(E_j,F_j\). For an affordable budget, \(R E_j\subset F_{j+2}\), and \(F_j\) is killed by \(\beta C^a\) if \(a+j+1\le p\), without restrictions on diagonal entries or output weights.

Let \(P\ne0\) be a polynomial of degree \(q\), \(m=p-2q>0\), and let \(w_m(r)=1+\min(r,m-1-r)\) for \(0\le r<m\). For either the primal stage columns or the weighted dual rows, let \(U_r\) be the span of the masked pure block with \(0\le a<w_m(r)\):
\[
 P(C)x^a,\qquad \beta P(C)C^a,
\]
respectively. Denote by \(T\) the corresponding step, \(v\mapsto Rv\) or \(\lambda\mapsto\lambda R\). Define the actual packet by \(W_0=U_0,\ W_1=U_1\) when affordable, and \(W_{r+2}=U_{r+2}+T W_r\). Suppose an invariant subspace \(V\) contains all the prescribed seed blocks, and \(z\ge\dim(V\cap\ker T)\). No assumption on the kernel outside \(V\) is needed.

The pure block at grade \(r\) embeds into the full clock block through degree \(q+w_m(r)-1\), by multiplication by \(P\) in the coefficient polynomial ring. With shifted grade \(r+q\), these columns or rows are independent: the full pure Hankel of this width is paid, since \(2(q+w_m(r)-1)+1\le p\). In either direction, the part \(T W_r\) gives no paired response against the full clock tests of the newly opened width at grade \(r+2+q\). For the column direction, \(W_r\subset E_{r+q}\) and the image is in \(F_{r+q+2}\). For the row direction, every row of \(W_r\) kills a defect of grade \(j\) if \(r+q+j+1\le p\); induct on the defining recursion, using \(R F_j\subset F_{j+2}\). On a clock power of degree at most \(q+w_m(r+2)-1\), its first \(R\) produces an affordable defect, hence the old shifted covector evaluates to zero. Thus the independent pure tests imply, even when \(T W_r\) has lost dimension,
\[
 W_{r+2}=U_{r+2}\oplus T W_r,\qquad
 \dim W_{r+2}=w_m(r+2)+\dim W_r-\dim(W_r\cap\ker T). \tag{2}
\]
Only the second term used injectivity in the original nonsingular proof. Invariance puts every \(W_r\) in \(V\). In particular if \(L_0=w_m(0)\), \(L_1=w_m(1)\) when affordable, and
\[
 L_{r+2}=w_m(r+2)+\max(0,L_r-z), \tag{3}
\]
then \(\dim V\ge\dim W_r\ge L_r\) for each \(r\). Formula (2) is also the local certificate when the kernel bound varies by grade: replace the uniform \(z\) in the lower recurrence by any independently verified bound for that actual kernel intersection.

## 2. Optimizing the uniform recurrence

On one parity, unroll (3). The value at ending grade \(r\) is the maximum of
\[
 z+\sum_{\substack{a\le j\le r\\j\equiv r\ (2)}}(w_m(j)-z)
 \quad\text{over }a\le r,\ a\equiv r\ (2).
 \tag{4}
\]
The possible reset to the last width is precisely the choice \(a=r\). Along a parity the widths are unimodal. If all widths are at most \(z\), the best interval in (4) is a singleton of largest width. Otherwise the strictly positive terms \(w_m(j)-z\) form one contiguous interval and including exactly those terms achieves the optimum on that parity.

When \(m>2z\), the strictly positive widths after subtraction are exactly
\[
 w_m(j)-z=w_{m-2z}(j-z)\qquad(z\le j\le m-1-z).
\]
They sum on the two parities to the two terminal parity censuses of order \(m-2z\), with the parities exchanged if \(z\) is odd. The maximum of their sums is \(\mathcal B_0(m-2z)\). The best positive interval also dominates any singleton of width at most \(z\). When \(m\le 2z\), the largest width is \(\lceil m/2\rceil\), at most \(z\). This proves (1) for every positive effective order, including \(m=1\). One must optimize across affordable grades; for \(z>1\) the largest lower rank may occur before the final grade of a parity.

## 3. Both physical cut directions, including mixed diagonals

Suppose \(A\) is lower triangular with arbitrary diagonal.

* **Physical prefix cut:** choose \(P\) vanishing on the clocks of a prefix. The counted target \(V\) consists of columns zero on the prefix, is \(R\)-invariant, and contains its masked seeds. If its actual Volterra nullity is at most \(z\), at least \(\mathcal B_z(p-2\deg P)\) stages follow the prefix.
* **Active suffix cut:** choose \(P\) vanishing on the clocks of every individually nonzero weight in a suffix. The counted target \(V\) consists of covectors supported on the preceding stages. Because the opposite suffix coordinate subspace is \(R\)-invariant, \(V\) is invariant under right composition with \(R\). The masked measured covectors lie in \(V\) even if there are additional inactive suffix clocks. If the transpose-step nullity on \(V\) is at most \(z\), at least \(\mathcal B_z(p-2\deg P)\) stages precede the suffix.

In either case one may use the number of zero diagonal entries in the **counted** segment for \(z\). The Volterra matrix is lower triangular with diagonal \(-A_{ii}^2\). Its restricted principal block on the counted segment therefore has a nonsingular principal minor on the nonzero-diagonal positions. The column step on the suffix is this block; the covector step on the prefix is the transpose of its prefix block. Equivalently, a nonzero column in its kernel has first nonzero coordinate at a zero diagonal, and a nonzero row in the dual kernel has last nonzero coordinate at a zero diagonal. Restriction to the local zero-diagonal positions is injective on either kernel. The argument also works for an appropriate invariant coordinate set instead of a consecutive segment. A sharper actual block nullity, e.g. after eliminating its nonzero diagonal positions, can be used directly without charging the zero-eigenvalue multiplicity.

Taking \(P\) equal to the nodal polynomial makes the result depend only on the actual cut's distinct physical or individually active clock count. In particular the full nonsingular bound applies if the counted block is nonsingular, even if every diagonal on the discarded side is zero. This is a cut-local restriction, not a new overall stage floor for all mixed DIRK methods.

## 4. A separately paid one-charge mask refinement

Let \(q=\deg P\), and now use the larger effective order \(m=p-q>0\). Keep the same masked blocks but their widths \(w_m(r)\) at this larger \(m\). Use only the ordinary clock tests of degrees \(0,\dots,w_m(r)-1\) against each block, not all tests through the enlarged degree \(q+w_m(r)-1\). Their paired matrix is
\[
 G_w(P)_{ij}=\beta P(C)x^{i+j},\qquad 0\le i,j<w=w_m(r).
\]
Every entry is still paid, since \(q+2(w-1)+1\le p\). The shifted old block is killed by these tests for the same cost computation leading to (2). If \(G_w(P)\) is nonsingular at every required width, the proof of (2)–(3) is unchanged and the cut pays \(\mathcal B_z(p-q)\). More generally the lower recurrence can use \(\operatorname{rank}G_{w_m(r)}(P)\) instead of \(w_m(r)\): the tests are zero on the shifted old block, so this rank is paid in its quotient regardless of singularity of the masked Hankel. This second version makes no unconditional replacement of \(p-2q\) by \(p-q\) for arbitrary masks and fields.

Two useful consequences are uniform:

1. If the discarded clocks are all \(0\), take \(P(X)=X\). The matrix is \(1/(i+j+2)\), nonsingular by the paid Cauchy determinant. If they are all \(1\), take \(P(X)=1-X\) and use \(1-x\) as the clock basis; reflected pure quadrature is already paid. Thus either cut with a single endpoint clock pays \(\mathcal B_z(p-1)\) on the opposite side as soon as \(p\ge2\), with no positivity or weight-sign hypothesis. This includes the suffix case with irrelevant inactive clocks.
2. For a single arbitrary clock \(\xi\), the mask \(X-\xi\) also costs one whenever \(\xi\) is not a root of any monic degree-\(w\) orthogonal polynomial for the paid pure moments at the required widths. Indeed the ordinary \(w\)-square Hankel is invertible, so the one-dimensional monic extension orthogonal to powers of degrees below \(w\) is defined by the paid moments through degree \(2w-1\). A kernel vector for \(G_w(X-\xi)\) gives precisely a multiple of that polynomial divisible by \(X-\xi\), and conversely. Thus at such an exceptional width the loss is exactly one, which can be entered in the rank recurrence instead of discarded across every width.

The companion checker tests the closed nullity recurrence and the exact linear-mask rank formula in finite and rational arithmetic. It draws no conclusion about existence of tableaux.
