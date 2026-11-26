# Two ways to reduce actual rows in the simultaneous tail

These are reductions of the stated paired construction at a fixed donor input. They do not claim a new unrestricted ERK or SDIRK stage minimum. In particular a stronger donor is not charged at the price of a merely grade-\((m-1)\) decoder.

## 1. One row for the last two grades with a quotient donor

Keep \(p=m+2\), now with \(m\ge4\), and prescribe any \(\gamma\) (zero is allowed). Choose a valid older minus clock \(\xi\); the first prefix clock \(\gamma\) always qualifies, because the only small sibling at this budget is the leaf. Use at least \(m+1\) distinct owners with scalar precision \(p-1\). Then interpolation retains every polynomial needed by a child through \(m+1\), and the dense owner reference gives the exact shifted profile on every paid tree.

Suppose an actual dense prefix supplies the ordinary exact profiles through size \(m+1\). Compose it with polynomial remainder modulo a monic \(H\) of degree \(m-1\) to obtain the decoder \(D\) used by the base. Shift contraction gives the same remainder law for \(G_t\) through that size. Choose \(H\) so that
\[
        \ell(J_\gamma H)=1,\qquad \ell(XJ_\gamma H)=\xi,
                      \qquad H\ne X^{m-1}.                         \tag{1}
\]
There is always such a monic \(H\). The two functionals on its free coefficients are represented by \(1-X-\gamma\) and \((1-X^2)/2-\gamma X\) under the polynomial integral pairing. They are independent on the available polynomials of degree at most \(m-2\), because that space contains all degree-\(\le2\) polynomials and its monomial Gram matrix on that subspace is invertible (the rational Hilbert matrix is positive definite over the reals, so its determinant is a nonzero rational). After the two linear constraints there is still a free parameter; it avoids the one excluded polynomial.

The line of \(J_\gamma H\) is independent from \(H\mathcal P_{\le1}\), where \(\mathcal P_{\le1}\) denotes the polynomials of degree at most one. Indeed \(H\mid I_0H\) for the ordinary lower primitive \(I_0\) would give \(I_0H=(X-a)H/m\) by leading coefficient comparison. Differentiating yields \((X-a)H'=(m-1)H\), hence \(H=(X-a)^{m-1}\); the value at zero gives \(a=0\). The scalar shift term is already a multiple of \(H\). This independence survives owner evaluation since the degrees are at most \(m\).

At size \(m\), \(\boldsymbol\Delta_0(u)=\alpha_u EH\), where \(\alpha_u\) is the leading coefficient of \(G_u\). At a nonunary tree of size \(m+1\), its source lies in \(E(H\mathcal P_{\le1})\), since all children fit the old exact grade. At a unary size-\(m+1\) tree \([u]\), its source lies in
\[
                       E(H\mathcal P_{\le1})-\alpha_u EJ_\gamma H.
\]
The latter term is the missing primitive from the size-\(m\) child, before the actual difference with the base is taken. Choose a row \(E_0\) annihilating \(E(H\mathcal P_{\le1})\) and reading
\[
                   E_0(EJ_\gamma H)=-(1-\gamma-\xi).
\]
A single plus row at the old clock \(\xi\), with source tap \(L_0+E_0\), now satisfies the exact equations. Its constant and one-leaf reads on size \(m\) are (1); its reads on the nonunary size \(m+1\) sources are unchanged; its read on \(\boldsymbol\Delta_0([u])\) picks up exactly \(\alpha_u(1-\gamma-\xi)\), which is the missing depth-two scalar by the weighted adjoint. The paired output of this one row replaces the old two-plus-one count, without separately preserving the missing increment. If \(1-\gamma-\xi\ne0\), the increment is genuinely nonzero. For \(\gamma=0\) one may take \(\xi=0\); for strict \(\gamma=1/2\) and a nonzero example one may use any distinct base owner as \(\xi\).

This is a simultaneous construction with a stronger donor. A full grade-\((m+1)\) decoder is sufficient; the argument actually only uses its remainder modulo \(H\). For strict SDIRK the known weighted-target commutator bound charges at least \(L(m+1)-2\) rows for this quotient through grade \(m+1\), where \(L(d)=\lfloor(d+1)^2/4\rfloor\). The lost first target rank is two, and every subsequent rank is unchanged. Thus relative to a cheaper ordinary donor, the two tail rows saved are not free.

## 2. A parallel \(r\)-row tail from a sparse quotient

More generally let \(p=m+r\), \(2\le r\le m\), and let \(q\ge p-1\) be the number of owner rows. Choose a monic \(H\) of degree \(n=m-1\). Suppose the donor decoder \(D\) recovers the exact shifted profile modulo \(H\) on every tree through size \(p-1\), as obtained by composing any full decoder through that size with remainder. Define the polynomial residual and its primitive contamination by
\[
 \rho_t\coloneqq G_t-D\boldsymbol\Phi_t(B_F),\qquad
 \mathcal U\coloneqq H\mathcal P_{\le r-1},\qquad
 \mathcal V\coloneqq\operatorname{span}\{X^aJ_\gamma(X^bH):a,b\ge0,\ a+b\le r-2\}.
\]
Then \(\rho_t\in\mathcal U\) through grade \(p-1\), and at such a grade the owner difference has the form
\[
                  \boldsymbol\Delta_0(t)=E(\rho_t-v_t),\qquad v_t\in\mathcal V.     \tag{2}
\]
Indeed the dense shifted reference gives \(EG_t\) through \(p\), because the child polynomials always fit the owner interpolation. If \(t\) has one size-\(\ge m\) child \(u\), its base mismatch is the evaluation of \(P J_\gamma\rho_u\), with \(P\) the other product. The degree of \(P\) plus the degree of \(\rho_u/H\) is at most \(|t|-m-1\le r-2\). Otherwise the mismatch is zero. This proves (2).

Assume \(\mathcal U\cap\mathcal V=0\). Both spaces have degree at most \(p-2\), so owner evaluation is injective on their sum. There is one linear read \(\mathcal R\) of the actual source data that takes \(E(\rho-v)\) to \(\rho\). Use any \(r\) distinct base clocks for parallel plus rows with no interaction between them. If \(L_a\) is the cardinal at clock \(a\), give its source tap the functional \(\ell(L_aJ_\gamma\mathcal R(\cdot))\). At a paid root the sibling product has degree at most \(r-1\); interpolation in these cardinals makes the summed correction precisely \(\ell(PJ_\gamma\rho_u)\), as in the exact parallel test. Hence **\(r\)** physical plus rows replace **\(r(r+1)/2\)**, transferring the full rooted order, with no new minus stages.

There is an explicit real or rational choice ensuring the independence if \(m-1\ge r(r-1)\): take the monic \(H\) to have exactly \(r\) nonzero coefficients at exponents \(k_1<\cdots<k_r=m-1\), with adjacent gaps at least \(r\). For example take \(0,r,\ldots,(r-2)r,m-1\) and all coefficients equal to one. To prove independence, move the shift term \(-\gamma H X^{a+b}\) into the putative polynomial multiple of \(H\). A relation now has the form
\[
         H\sum_{j=0}^{r-1}c_j X^j+
            \sum_{a+b\le r-2}d_{a,b}X^a I_0(X^bH)=0.
\]
For a nonzero coefficient of \(H\) at exponent \(k\), its contribution to this expression lives at exponents \(k,k+1,\ldots,k+r-1\); those blocks are disjoint. The offset zero shows \(c_0=0\). At offset \(j+1\), one obtains for each of the \(r\) exponents \(k\)
\[
                      c_{j+1}+\sum_{b=0}^j\frac{d_{j-b,b}}{k+b+1}=0 .
\]
The common denominator has degree \(j+1\); the numerator has degree at most \(j+1<r\). Thus it is identically zero. Its distinct simple poles then show that each \(d_{j-b,b}\) and \(c_{j+1}\) vanishes. This establishes the asserted independence, for every \(\gamma\), including ERK.

This wide-band donor also has a price: in strict SDIRK its full quotient hypothesis forces at least
\[
            \sum_{j\ge0:\ p-1-2j>0}\min(m-1,p-1-2j)
\]
prefix rows by the weighted target version of the same invertible commutator proof. An exact dense decoder through \(p-1\) composed with remainder meets the stated hypothesis but need not be count optimal. The rational precision-\((p-1)\) rule with \(q=p-1\) from the original construction still gives exactness, and works for ERK and rational prescribed diagonal with rational thin donors. No full-method table improvement is claimed for this separated-space sufficient condition.

## 3. Pack the original grades using one reverse word decoder

This variant does **not** strengthen the forward donor beyond grade \(m-1\). Suppose a separate actual reverse tableau of the same class has \(a\) stages, with diagonal \(\gamma\), and a linear dense decoder through size \(r\). Turn its strict part backwards and transpose it to obtain the physical \(T\) of (1) in the first note. More explicitly reverse the chronological order after transposing \(A_R-\gamma I\). Use the reflected actual reverse clocks as the physical plus clocks, \(x=1-c_R\), in that opposite order. Use unit plus weights. For each reflected clock an eligible older minus row is needed; if it is not among the base owners, one extra base row with the same donor feed can supply it. Multiple plus stages at that clock use the same minus row.

After reflection let \(D_R\) denote the reverse decoder acting on coordinates in the physical plus order, but with its model written in \(X=1-Y\). The weighted reverse word that begins at \(\mathbf1\) is decoded by \(D_R\) with the model letter \(J_\gamma^*\) for a transpose transition and multiplication by \(X\) for a clock mark. This follows by forming a unary root, a leaf attachment and a subtraction of the shorter scalar word for the shifted edge. All words in (2) use at most \(r-1\) such letters, counting polynomial marks by degree. They are linear combinations of trees through size \(r\), within this actual decoder. Give the new source tap on each physical plus coordinate \(i\) the row
\[
       S_{ij}\coloneqq\widehat b_j(J_\gamma^*D_R\mathbf e_i)(x_j)  \qquad (1\le j\le q),
\]
where \(\mathbf e_i\) is its coordinate vector. Now reversing every primitive in the dense term of (2) through its precisely paid adjoint gives the physical depth contribution, using this outermost \(J_\gamma^*\) on the source tap. Each adjoint is legal: the final sum of test degree, source grade minus one, and primitive steps is at most \(p-1\). Thus this construction matches all depth terms individually while using the **same physical rows** across them, instead of a physical level for each term. In particular it is a sufficient simultaneous solution, but not a necessary decoder requirement for the exact tensor criterion.

The physical count is \(s_F+q+a\), plus one for each distinct reflected reverse clock not already present as an eligible older minus. Rooted order proof (1) is unchanged. There is no common-diagonal error in the transpose: the reverse tableau is shifted first; the plus and minus physical rows both restore \(\gamma\) only on their own diagonal. The contrast statement remains valid for an ERK reverse chart with \(\gamma=0\). This applies to any genuine supplied reverse chart, not a pseudo-decoder of unobserved columns.

### All reflected clocks can fit in the scalar grid

Let \(d\) be the number of distinct reflected clock sites. One simple uniform scalar choice takes \(q=\max(p+1,d)\) distinct owners containing these sites. Choose weights on any \(p+1\) of them by Vandermonde with the first \(p\) moments exact and degree-\(p\) moment set to zero; the other weights can be zero. There is no division by weights in the contrast. Allowing \(q>p\) does not modify the proof of the reference or its adjoint: the proof uses only precision through \(p-1\) and the polynomial degree on actual data, not interpolation of arbitrary owner vectors by a degree-\(<p\) polynomial.

If all prescribed reflected sites are outside \((0,1)\), one can pay their reuse more cheaply. For \(d<p\), take
\[
 s\coloneqq\max(\lceil(p-d)/2\rceil,m-1-d),\qquad q\coloneqq d+s.
\]
Let \(\Omega\) be the product of the prescribed site factors. It has constant sign inside \((0,1)\); the weighted measure of that sign times \(\Omega\) is positive. Fill the remaining \(s\) owners with a weighted Gaussian rule's distinct interior nodes. If \(d+2s=p\), the added monic hull \(P_s\) is orthogonal for that measure, giving precision \(p-1\) on the total owner rule by division by \(\Omega P_s\). The sign-definite degree-\(p\) polynomial \(\Omega P_s^2\) proves next-moment failure. If \(d+2s>p\), replace \(P_s\) by \(P_s+\varepsilon P_{p-d-s}\) for sufficiently small nonzero rational \(\varepsilon\). The roots stay real and distinct, precision is unchanged through the required degree, and the product of the total hull with \(P_{p-d-s}\) has a nonzero degree-\(p\) integral. The scalar weights are its ordinary interpolatory weights. For \(d\ge p\) take \(q=d\) and use only \(p\) prescribed sites with interpolatory weights; the product of their factors has constant sign and nonzero integral at degree \(p\). The remaining sites have zero scalar weight. All of these claims have the same exactness witness on the physical aggregate clock rule.

For real-algebraic strict SDIRK the cached Laguerre forward and reverse charts give \(s_F=\lfloor m^2/4\rfloor\) and \(a=L(r)\), respectively. At negative \(\gamma\) all reverse clocks are negative, so their reflections are exterior. For arbitrary prescribed real-algebraic \(\gamma\ne0\) the uniform grid above is available. Thus, using \(d\le a\), the counts are at most 70 for \(p=19\) (take \(m=11,r=8\)) and 77 for \(p=20\) (take \(m=12,r=8\)). In the exterior regime the respective bounds are 70 (also \(m=12,r=7\)) and 76. These improve the previous paired-layer construction counts 75 and 82 in that prescribed-diagonal setting but not the specialized unrestricted real-algebraic 54 and 59. No claim about a better asymptotic unrestricted table is made. The construction and algebraic criterion also apply with a genuine ERK reverse decoder; it does not presume a new improvement on the existing ERK exact literals.
