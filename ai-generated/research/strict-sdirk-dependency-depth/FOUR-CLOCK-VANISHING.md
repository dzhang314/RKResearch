# A four-clock vanishing test for the zero-longest branch at \(s=p\)

This alternative replaces the two-node square, skip calibrations and multiplicativity used in the sealed p≥11 proof. It uses neither a nonzero progression step nor a nonzero individual path weight. Its four tests use one more clock degree than the number of free virtual holes and hence vanish on each physical path. This is a branch result, not an all-chart lower bound below \(p=11\).

## 1. Paid top zero and a literal safe run

Work first over a field with paid integer units \(1,\ldots,s\), with literal order through \(s\), \(s\ge9\), actual common diagonal \(\gamma\ne0\), and \(B=A-\gamma I\). Write \(\lambda_j=\mathbf b\cdot B^j\mathbf1\) for \(j+1\le s\), \(L=\lambda_{s-1}\), \(M=\lambda_{s-2}\). Suppose \(L=0\). The paid consecutive-zero tall argument gives \(M\ne0\). If \(b_s=0\), remove the last row and column: all earlier rooted vectors are unchanged by triangularity, and the unchanged scalar output would give order through \(s\) on \(s-1\ge8\) stages, contrary to the separate decorated saturation proof. Otherwise strict full-path uniqueness supplies an actual broken subdiagonal \(B_{i,i-1}=0\).

A nonzero weighted path omits at least one of the physical pair \(\{i-1,i\}\). In the one-omission bank, only those two holes can have nonzero weights, and their sum is \(M\). For occupied slot \(k\), let \(T'_k\) be the sum of one-hole weights with omitted index at most \(k\). The actual centered clock \(x=\mathbf c-\gamma\mathbf1\) at this slot reads
\[
 M x_k+T'_k(x_{k+1}-x_k)
  =\lambda_{s-1}+(k-1)\kappa,\qquad
 \kappa=\lambda_{s-1}+2\gamma M+\gamma^2\lambda_{s-3}.
\]
The formal evaluation is the identity
\(T^{d-a}(X-\gamma I)T^a1=T^{d+1}1+aJ^2T^{d-1}1\)
at \(d=s-2,a=k-1\), paid at \(1+(s-2)+1=s\).
Thus the actual outer clocks are \(\gamma+(j-1)\delta\) on \(j\le i-2\) and \(\gamma+(j-2)\delta\) on \(j\ge i+1\), where \(\delta=\kappa/M\). Nothing fixes the pair clocks. The top tall row also gives \((s-2)\delta=1-2\gamma\), but we do **not** divide by \(\delta\).

Collapse the pair to one site in the increasing lists only, with virtual size \(m=s-1\). For a nonzero path the retained list has no repeated virtual index; a list with \(h+1\) physical holes has \(h\) virtual holes, including the virtual pair site if both its physical representatives were omitted. The two outer literal runs are arithmetic in the virtual index and have lengths summing to \(s-2\ge7\), so at least one contains four consecutive safe virtual clocks \([r,r+3]\). On this run physical indices are a fixed translation of virtual ones, and no clock is assigned to the ambiguous pair site.

## 2. Four words that vanish before weighting

In a virtual list with \(h\) holes, occupied slot \(j\) has index in \([j,j+h]\). Place \(q\) consecutive marked links starting at occupied slot \(r\). When \(h+q\le3\), every possible endpoint is in the literal four-clock run, and those slots exist because \(r+q+h\le r+3\le m\). For a degree \(d\) mark on such a link use
\[
 P_d(w)=\prod_{a=1}^{d}(w-a\delta),\qquad
 w=c_{\mathrm{receiver}}-c_{\mathrm{donor}} .
\]
If the virtual gap contains \(g\) holes, then \(w=(g+1)\delta\) on every candidate path. A gap with \(g<d\) makes the mark zero, **including for \(\delta=0\)**. All marked gaps are disjoint in their omitted intervals, so if total marked degree is \(h+1\), at least one mark vanishes on each physical candidate.

Use these four choices:
\[
\begin{array}{c|c|c}
\text{desired gap degrees} & h & \text{maximum window size}\\\hline
(1)&0&2\\
(2)&1&3\\
(3)&2&4\\
(1,1)&1&4
\end{array}
\]
Each actual read is zero term by term. This includes any nonzero-weight candidate that deletes both representatives: such a list still has only \(h\) virtual holes. Paths that retain both representatives had physical weight zero before any marks. There is no path-mode cancellation or normalization by an actual skip.

Each of these words is paid at exactly \(s\): leaf \(1\), strict hops \(m-h-1\), mark degree \(h+1\), hence \(m+1=s\). For the formal model let \(J,X,T=J-\gamma I,\ell\) be the bounded word operators. The mark on a link is modeled by \(Q_d(T)\), replacing a zeroth difference power times \(B\) by \(T\) and a \(j\)-th difference power times \(B\) by \(j!J^{j+1}\) for \(j\ge1\), via iterated \([X,T]\). Set \(y=\gamma/T\) only as a cleared polynomial shorthand and \(t=\delta/\gamma\). Then \(Q_d(T)=d!T^{d+1}F_d(y)\), and with \(w=1+y\) the first polynomials are
\[
 F_1=w^2-ty,\qquad
 F_2=w^3-\tfrac32ty w^2+t^2y^2,\qquad
 F_3=w^4-2ty w^3+\tfrac{11}{6}t^2 y^2w^2-t^3y^3 .
\]
Unmarked hops contribute \(m-h-1-q\), and the marked reverse grades sum to \(h+1+q\). The product therefore has base \(T^m=T^{s-1}\), **not** \(T^{m-1}\) as in the conventional one-mark-per-hole tests. Normalize the top-zero functional by the next paid nonzero value:
\[
 \nu(y^j)=\frac{\gamma^j\lambda_{s-1-j}}{\gamma M},\qquad
 \nu(1)=0,\quad \nu(y)=1 .
\]
The four vanishing words, after the paid factorial factors, state
\[
 \nu(F_1)=\nu(F_2)=\nu(F_3)=\nu(F_1^2)=0 .
\]
The normalization uses only \(\gamma M\), not \(L,\delta\) or a subdiagonal factor. Because the absolute model degree is at most \(s-1\), all denominators are paid.

## 3. The scalar contradiction, including zero step

Put \(k=t/2\), \(u=y+1-k\). Then \(F_1=u^2+2k-k^2\), so \(\nu\) vanishes on all even polynomials in \(u\) of degree at most four by the three vanishing tests on \(1,F_1,F_1^2\). The odd coefficients of \(F_2,F_3\) in \(u\), in powers \(u^3,u\), are
\[
 \begin{pmatrix}
  1-3k & k^2(1-k)\\[2pt]
  \tfrac43k(6-23k+16k^2) & \tfrac43 k^3(k-1)(4k-5)
 \end{pmatrix}.
\]
Its determinant is \(\tfrac43 k^3(k-1)(2k-1)^2\) by expansion. Unless \(t\in\{0,1,2\}\), it is nonzero and the two remaining vanishing identities force \(\nu(u)=0\), contradicting \(\nu(u)=\nu(y)=1\).

For the exceptional slopes, put \(\xi=\gamma^{-1}\) and \(v_j=\nu(y^j)\). The same paid reverse tall row 0 gives \(\xi=2+(s-2)t\) from \(v_0=0,v_1=1,v_2=t-2\). Row 1 is
\[
 s-1=(\xi-2(s-2))v_2-(s-3)v_3 .
\]
The vanishing \(F_2\) moment gives the following exact table:
\[
\begin{array}{c|c|c|c|c}
t&v_2&v_3&\xi&\text{right side of row 1}\\\hline
0&-2&3&2&s-3\\
1&-1&1&s&-1\\
2&0&0&2s-2&0
\end{array}
\]
For \(t=0\), \(F_2=(1+y)^3\); for \(t=1\), \(F_2=1+\tfrac32 y+y^2-\tfrac12y^3\); for \(t=2\), \(F_2=1+y^2-2y^3\). Thus the three rows force respectively \(2=0\), \(s=0\), or \(s-1=0\), impossible with the paid units. This excludes the original \(L=0\) branch for \(s\ge9\) without the longer calibrated-product route.

Over a nontrivial commutative ring, use the statement on a maximal residue field after the usual bush/unit and rooted coefficient mapping. This is a replacement branch argument for the stage-floor proof: it makes no nonvanishing assertion for the original ring's top coefficient, since a nonzero ring element can map to zero. Cyclic equality \(L\ne0\) is not treated here. Source-only, no execution or repository change.
