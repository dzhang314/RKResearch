# Physical row sums and the low forward flag of the 15-stage midpoint DIRK

This is a **scoped Lean certificate**, not a new bound and not a Lean proof of full exact order twelve over the reals. It supplies the actual triangular matrix layer, the literal hidden block, and the forward client of the complementary-support theorem. The 36 nonterminal live primitive checks and the reverse/grade-six checks are not asserted by this packet.

## Matrix assembly

The zero-based stages are the origin, ghosts 1 through 4, live rows 5 through 13, and the terminal 14. Given an open live-to-live block \(L\), prescribed live clocks, and modes \(\mathbf R,\mathbf S\), Lean defines the origin row, the causal part of \(A\), and in live row \(i<14\) the actual ghost taps
\[
                 A_{ig}=\ell_g(R_i+S_i c_g),\qquad c_g=a p_g.
\]
For the existing real constructor, \(a=1/2\),
\(R_i=c_i(\alpha L_5'(c_i)+\mu L_6'(c_i)+\gamma L_7'(c_i))\),
and \(S_i=c_i\nu L_6'(c_i)\). These modes are parameters in this packet, not fitted by its Lean code. Here \(L_j'\) is the derivative of the shifted Legendre polynomial; it is distinct from the open live block.

The terminal non-origin entry in each column \(j\) is
\[
 A_{14,j}=\frac{b_j(1-c_j)-\sum_{i<14} b_i A_{ij}}{b_{14}}\quad(j\ne 0).
\]
The guard \(b_{14}\ne0\) is required for the actual adjoint conclusion. The origin column is filled by subtraction, so the theorem \(A\mathbf 1=\mathbf c\) holds without inverting any value. All entries above the diagonal vanish; \(A_{00}=0\), and \(A_{11}=a/8\ne0\) if \(a\ne0\). When the paid ordinary scalar moments \(0,1\) are available, they recover the missing origin component of \(A^{\mathsf T}\mathbf b=\mathbf b\odot(\mathbf 1-\mathbf c)\). No unverified reverse equations are used here.

## Verified low forward slice

Portable rational core checks establish the following literal block and tap identities. Write \(\mathbf h=A_g\mathbf p^2-\mathbf p^3/3\), and write juxtaposition with \(\mathbf p\) for componentwise multiplication:
\[
\begin{aligned}
 A_g\mathbf h &= (25/12)\mathbf h-(47/6)\mathbf p\mathbf h,\\
 A_g(\mathbf p\mathbf h)&=(79/144)\mathbf h-(35/18)\mathbf p\mathbf h-(1/2)\mathbf p^2\mathbf h,\\
 \sum_g\ell_g h_g p_g^j&=0\quad(j=0,1,2).
\end{aligned}
\]
The four scaled local entering-power defects are
\(0,\ 3\mathbf h,\ -2\mathbf h+14\mathbf p\mathbf h,\)
and \((91/24)\mathbf h-(95/3)\mathbf p\mathbf h+75\mathbf p^2\mathbf h\).
The actual physical coefficient factors \(a\) and \(a^{m+1}\) are restored in Lean.

The verified bands have widths \(0,0,0,1,2,3\). All low actions of \(A\) and \(C=\operatorname{diag}(\mathbf c)\) have the required membership. The nonterminal live taps annihilate the required first two hidden generators because the additional clock factor uses only the three recorded tap moments. The terminal output of \(A\) on these generators vanishes from the actual adjoint, zero ghost weights, and \(b_{14}\ne0\). The origin and four ghost low primitives are literal checked values, and the zero-incoming-power primitive is zero on every row by definition of \(\mathbf c\).

**Remaining forward instantiation:** for each ordinary nonterminal row \(i=5,\ldots,13\) and entering power \(m=1,2,3,4\), the following equation is the exact stated hypothesis **Feed.LiveBudget**:
\[
 (m+1)\sum_{\text{live }j\le i} L_{ij} c_j^m+
 R_i a^m+\frac{m+1}{m+2}\,S_i a^{m+1}=c_i^{m+1}.
\]
Here the term of degree \(m+2\) covers all ghost mode taps via their paid rational moments; the grade counts use \(m+1\), not \(m+2\). The theorem **Feed.fw_primitive** proves that these are the only remaining low forward primitive tests for this layer: the terminal's true defect has zero weighted sum by the actual adjoint and ordinary scalar moments and hence vanishes there. The actual live-block construction and these 36 equations are not verified natively here. Nor are the second and higher reverse primitives, reverse band shifts/silence, or the single grade-six pair of bridge tests.

## Build and scope

Build in this order: `DIRKOrderTwelveMidpointGhostCore`, `DIRKOrderTwelveMidpointGhostForwardCore`, `DIRK12MidpointCausalRows`, `DIRK12MidpointForwardFlags`; run `AuditDIRK12MidpointForwardFlags.lean`. The first file replaces its previous standalone import header with an exposed public module so that the two clients can import it. Its definitions and proofs are unchanged. Both core files were kernel-checked with Lean 4.34.1, 4.35.0, 4.36.0, and 4.37.0-rc1. The Mathlib-dependent physical modules and typed audit were checked with the repository's matched Lean/Mathlib 4.36.0. Scope for newer Mathlib snapshots is not asserted. The reported axioms are only `propext`, `Classical.choice`, and `Quot.sound`; no native-code oracle or `sorry` is used.
