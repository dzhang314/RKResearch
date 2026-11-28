# Full tap rank and a \(10\times5\) exact compatibility bridge

Use the [two-mode ordinary ghost-tap profile](README.md) in the remaining \(m=9,10\) variable-grid cases. Let \(a,b\) be the first two distinct nonzero ordinary live clocks and take their actual first physical rows. Their vectors of four ghost taps are **linearly independent**. Together with the two-mode bound, the entire nonterminal live ghost-tap matrix therefore has exact rank two.

Suppose instead those two row vectors both lie in the line of a covector \(\boldsymbol\zeta\) on the four physical ghosts. For a scalar polynomial \(S\), let the functional of its ghost values be \(\sum_g\zeta_g S(c_g)\). The scalar space \(X(X-a)P_2\) has dimension three; imposing that this functional vanish leaves at least two independent \(S\). For each, all ordinary live inputs through \(a\) are zero, and the ghost contribution at \(a\) is zero by construction. The true scalar primitive is exact on all these live rows through input degree four, because \(F_5=\mathbf hP_2(\mathbf c)\) is ghost-only. Hence \(JS(a)=0\). The primitive space of those \(S\) has dimension at least two and is contained in \(X^2(X-a)^2P_1\) by the two double roots and degree five, so it equals that space. At the actual first \(b\)-row every prior live input again vanishes, and its ghost contribution is zero by the common-line assumption. Exact scalar precision forces \(JS(b)=A_{bb}S(b)\) for those same \(S\), impossible for the two primitives \(B=X^2(X-a)^2\) and \((X-b)B\), as in the [native polynomial receipt](../dirk12-fifteen-rank3-invisible-four-ghost-variable-three-pairs/support-grade-ledger.md). This is an ordinary forward application of the two-receiver idea; no reverse singleton is assumed clean.

## Canonical form and a literal generator of the live \(F_6\) projection

Set \(D_g(X)=\prod_{g\text{ ghost}}(X-c_g)\), and normalize \(\ell_g=1/[h_gD_g'(c_g)]\). Barycentric interpolation gives
\[
 \sum_g \ell_g h_g c_g^j=0\ (j=0,1,2),\qquad
 \sum_g \ell_g h_g c_g^3=1 .
\]
The vectors \(\boldsymbol\ell,C\boldsymbol\ell\) are independent and span the two-dimensional annihilator of \(\mathbf h,C\mathbf h\) on the four ghost coordinates. Thus the earlier \(\boldsymbol\beta\) is \(\mu\boldsymbol\ell+\nu C\boldsymbol\ell\), and every nonterminal live ghost tap is
\[
 A_{ig}=c_i\ell_g\left[(\mu+\nu c_g)L_6'(c_i)
                      +\alpha L_5'(c_i)+\gamma L_7'(c_i)\right].
\]
The rank-two result forces \(\nu\ne0\) and \((\alpha,\gamma)\ne(0,0)\); otherwise the two row vectors just tested would be in one line. In fact it forces
\[
 L_6'(a)\bigl(\alpha L_5'(b)+\gamma L_7'(b)\bigr)
 -L_6'(b)\bigl(\alpha L_5'(a)+\gamma L_7'(a)\bigr)\ne0.
\]
The actual pure \(AC^2\mathbf h\) has nonterminal live polynomial exactly \(\nu X L_6'(X)\), by the displayed barycentric moments. So this actual word, not an abstract extra generator, spans the nonzero live projection of \(F_6\).

If the first live nonzero \(a\) has a fourth ghost \(g_*\) still later in physical chronology, \(L_6'(a)\ne0\) by the earlier two-mode lemma. Causality forces that group's affine clock factor to vanish. At that physical row every ghost coefficient is consequently
\[
                       A_{ig}=a\,\nu L_6'(a)\,\ell_g(c_g-c_{g_*}),
\]
nonzero on each of the three earlier ghosts. More generally, at any nonterminal live nonzero clock with \(L_6'(c_i)\ne0\), at most one of the four ghost taps can vanish. If \(L_6'(c_i)=0\), they vanish together or are all nonzero, since the remaining mode is common times \(\boldsymbol\ell\).

## Ten exact linear equations after fixing the ghost geometry and early live clocks

Let \(a_1,\dots,a_4\) be the first four distinct nonzero ordinary live clocks in their actual stage order. These occur before the literal terminal. Write
\[
   \mathcal L(P)=\sum_g\ell_gP(c_g),\qquad
   P_{k,j}(X)=X^{1+j}\prod_{r=1}^k(X-a_r)
       \quad (1\le k\le4,\ 0\le j\le4-k).
\]
There are \(4+3+2+1\) such inputs, all of degree at most five. Their numerical live inputs up to and including the first \(a_k\)-row are zero. Earlier returns to a numerical clock do not change this statement. The actual scalar primitive discrepancy on live nonterminal rows, for any scalar \(P\in P_5\), is
\[
   (A P(\mathbf c))_i-(JP)(c_i)
        =\eta\,\operatorname{coeff}_5(P)\,c_i L_6'(c_i)
\]
for one real constant \(\eta\): lower-degree discrepancies are ghost-only, and degree five uses the single live \(F_6\) line. Substituting the exact ghost tap modes and dividing only by the nonzero \(a_k\) gives
\[
 \frac{JP_{k,j}(a_k)}{a_k} =
   L_6'(a_k)\left[
       \mu\,\mathcal L(P_{k,j})
       +\nu\,\mathcal L(XP_{k,j})
       -\eta\,\operatorname{coeff}_5(P_{k,j})\right]
   +\left[\alpha L_5'(a_k)+\gamma L_7'(a_k)\right]\mathcal L(P_{k,j}).
\]
This gives a \(10\times5\) exact linear system in \((\mu,\nu,\alpha,\gamma,\eta)\), with one optional additional literal causality equation for a fourth ghost still later than \(a_1\). Besides consistency its solution must have \(\nu\ne0\) and the first-two-mode determinant above nonzero. This **does not yet eliminate variable ghost geometry** or imply a width from a scalar rule.

The accompanying standard-library exact checker takes rational ghost clocks, rational ghost cubic amplitudes and the first four ordered live clocks, and reports whether these necessary equations or linear nonzero guards fail. Its proof applies over real algebraic data as well; the script is just a rational replay interface. It does not enforce reverse weighted rows, later ordinary stage rows, beyond-grade-five order, or global scalar quadrature, so a pass is not a tableau witness. No new native rooted-order theorem is asserted.
